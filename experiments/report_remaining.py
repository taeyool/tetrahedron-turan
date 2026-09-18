"""Audit saved campaign artifacts and draw the two comparison panels."""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction
from pathlib import Path
import statistics
import time

import runtime as rt
import numpy as np
from exactify_order6 import verify


def read(path):
    return rt.json.loads(Path(path).read_text(encoding='utf-8'))


def main(base,output,previous):
    started=time.monotonic()
    data=read(output/'results.json'); old=read(previous/'results.json')
    manifest=data['protocol']; inputs=read(output/'publication-manifest.json')['input_sha256']
    for path,digest in inputs.items():
        assert rt.digest(path)==digest,path
    for relative,digest in manifest['source_sha256'].items():
        assert rt.digest(rt.ROOT/relative)==digest,relative
    assert len(data['runs'])==15 and len(data['groups'])==5
    assert all(g['repetitions']==3 for g in data['groups'])
    history={}
    for row in data['runs']:
        folder=Path(row['run_path'])
        lines=[rt.json.loads(line) for line in (folder/'history.jsonl').read_text(encoding='utf-8').splitlines()]
        eligible=[h for h in lines if h['eligible_for_budget']]
        best=min(h['global_dual_upper'] for h in eligible)
        assert abs(best-row['numerical_global_upper'])<1e-12
        with np.load(folder/'best_dual.npz') as z:
            assert float(z['availability_seconds'])<=3600
            match=[h for h in eligible if h['iteration']==int(z['iteration'])]
            assert len(match)==1 and abs(match[0]['seconds']-float(z['availability_seconds']))<1e-8
            assert abs(best-float(z['global_upper']))<1e-12
        key=(row['model'],row['method'],row['repetition'])
        history[key]=eligible
        for cp in [c for c in data['checkpoints'] if (c['model'],c['method'],c['repetition'])==key]:
            available=[h['global_dual_upper'] for h in eligible if h['seconds']<=cp['target_seconds']]
            if cp['status']=='no_completed_candidate':
                assert not available
            else:
                assert available and abs(min(available)-cp['numerical_upper'])<1e-12
    # Recheck stored M6 integer artifacts. For M7-lift6, match both retained
    # full-scan outputs, not just a boolean copied into a summary.
    certificates={Path(r['certificate_path']) for r in data['runs']}
    certificates.update(Path(r['uncompressed_certificate_path']) for r in data['runs'])
    certificates.update(Path(c['certificate_path']) for c in data['checkpoints'] if c['status']=='verified')
    counts=Counter()
    for path in sorted(certificates):
        cert=read(path)
        if cert.get('model')=='M6':
            verify(cert,base/'cache');counts['M6_integer_artifacts_rechecked']+=1
        else:
            values=[]
            for name in ['exact_result.txt','ordered_result.txt']:
                text=(path.parent/'cache'/name).read_text()
                result=dict(line.split(maxsplit=1) for line in text.splitlines())
                assert int(result['raw_count'])==13051375
                values.append((int(result['max_numerator']),int(result['denominator'])))
            assert values[0]==values[1]==(cert['bound_numerator_unreduced'],cert['common_denominator_unreduced'])
            counts['M7_lift6_paired_full_scan_artifacts_checked']+=1
    # Preserve and audit the six already published runs used in the right panel.
    from summarize_selected import check_certificate
    for row in old['rows']:
        certpath=Path(row['certificate']); folder=certpath.parents[2]
        check_certificate(read(certpath),folder/'best_dual.npz')
        assert rt.digest(certpath)==next(c['certificate_sha256'] for c in old['checkpoints']
            if c['model']==row['model'] and c['rep']==row['rep'] and c['target_seconds']==3600)
        lines=[rt.json.loads(line) for line in (folder/'history.jsonl').read_text(encoding='utf-8').splitlines()]
        history[row['model'],'LP-CUT-CG',row['rep']]=[h for h in lines if h['eligible_for_budget']]

    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    plt.rcParams.update({'font.family':'DejaVu Sans','font.size':9,'axes.titlesize':10,
        'axes.labelsize':9,'legend.fontsize':8,'pdf.fonttype':42,'svg.fonttype':'none',
        'axes.spines.top':False,'axes.spines.right':False})
    fig,axes=plt.subplots(1,2,figsize=(6.65,3.30),layout='constrained')
    colors={'SDP-FULL':'#4477AA','LP-CUT':'#EE7733','SDP-CG':'#AA3377','LP-CUT-CG':'#228833'}
    model_colors={'M6':'#228833','M7-lift6':'#4477AA','M7-no5':'#CC6677','M7-all5':'#AA3377'}
    styles=['-','--',':']
    for method in ['SDP-FULL','LP-CUT','SDP-CG','LP-CUT-CG']:
        for rep in [1,2,3]:
            h=history['M6',method,rep]
            t=np.array([x['seconds'] for x in h]+[3600.])
            u=np.minimum.accumulate([x['global_dual_upper'] for x in h])
            u=np.r_[u,u[-1]]-5/9
            marker=dict(marker='o',markevery=[0],ms=4.5,markerfacecolor='white',zorder=5) if method=='SDP-FULL' else {}
            axes[0].step(t,u,where='post',color=colors[method],linestyle=styles[rep-1],
                lw=1.1,alpha=.85,label=method if rep==1 else None,**marker)
        points=[c for c in data['checkpoints'] if c['model']=='M6' and c['method']==method and c['status']=='verified']
        axes[0].plot([p['target_seconds'] for p in points],[p['exact_bound_decimal']-5/9 for p in points],
            linestyle='none',marker='x',ms=4,mew=.8,color=colors[method])
    axes[0].set(xscale='log',yscale='log',xlim=(.03,4200),ylim=(.0055,.65),
        title='(a) M6: four methods',xlabel='Search budget (s)',ylabel='$U-5/9$')
    axes[0].legend(loc='lower center',bbox_to_anchor=(.5,1.015),ncol=2,
        frameon=False,handlelength=1.5,columnspacing=1.0)
    axes[0].set_title('(a) M6: four methods',pad=32)
    for model in ['M6','M7-lift6','M7-no5','M7-all5']:
        for rep in [1,2,3]:
            h=history[model,'LP-CUT-CG',rep]
            t=[x['seconds'] for x in h]+[3600.]
            u=np.minimum.accumulate([x['global_dual_upper'] for x in h]);u=np.r_[u,u[-1]]
            axes[1].step(t,u,where='post',color=model_colors[model],linestyle=styles[rep-1],
                lw=1.1,alpha=.85,label=model if rep==1 else None)
        if model in ['M6','M7-lift6']:
            points=[c for c in data['checkpoints'] if c['model']==model and c['method']=='LP-CUT-CG' and c['status']=='verified']
            times=[p['target_seconds'] for p in points]; values=[p['exact_bound_decimal'] for p in points]
        else:
            points=[c for c in old['checkpoints'] if c['model']==model and c['verified']]
            times=[p['target_seconds'] for p in points];values=[float(Fraction(p['exact_fraction'])) for p in points]
        axes[1].plot(times,values,linestyle='none',marker='x',ms=4,mew=.8,color=model_colors[model])
    axes[1].set(xscale='log',xlim=(1,4200),ylim=(.558,.5642),
        title='(b) LP-CUT-CG: model detail',xlabel='Search budget (s)',ylabel='Globally evaluated $U$')
    axes[1].ticklabel_format(axis='y',style='plain',useOffset=False)
    axes[1].legend(loc='lower center',bbox_to_anchor=(.5,1.015),ncol=2,
        frameon=False,handlelength=1.5,columnspacing=1.0)
    axes[1].set_title('(b) LP-CUT-CG: model detail',pad=32)
    for ax in axes:
        ax.grid(True,which='major',alpha=.20,lw=.6)
        ax.set_axisbelow(True)
    for extension in ['pdf','svg','png']:
        fig.savefig(output/f'comparison.{extension}',dpi=190)
    plt.close(fig)

    profiles=[]
    for g in data['groups']:
        rows=[r for r in data['runs'] if (r['model'],r['method'])==(g['model'],g['method'])]
        profiles.append(dict(model=g['model'],method=g['method'],
            final_svd_verification_wall_seconds=[read(Path(r['certificate_path']).parent/'supervisor.json')['elapsed_seconds'] for r in rows],
            final_svd_arithmetic_seconds=[read(Path(r['certificate_path']).with_suffix('.summary.json')).get('exactification_verification_seconds') for r in rows],
            uncompressed_factor_counts=[read(Path(r['uncompressed_certificate_path']).with_suffix('.summary.json'))['integer_square_factors'] for r in rows]))
    audit=dict(status='passed',input_hashes_checked=len(inputs),frozen_sources_unchanged=len(manifest['source_sha256']),
        production_runs=15,prior_runs_reused=6,checkpoint_slots=75,verified_checkpoint_slots=63,
        missing_native_early_checkpoints=12,production_exactification_jobs=42,
        checkpoint_history_availability_matches=True,integer_artifact_checks=dict(counts),
        profiles=profiles,reporting_source_sha256=rt.digest(__file__),audit_seconds=time.monotonic()-started)
    # Use the explicit ISO start rather than a hand-maintained epoch in reports.
    import datetime as dt
    audit['campaign_elapsed_including_preparation_seconds']=data['status']['finished_epoch']-dt.datetime.fromisoformat(manifest['request_started_utc']).timestamp()
    rt.write_json(output/'validation.json',audit)
    report=(output/'REPORT.md').read_text(encoding='utf-8').split('\n## Interpretation and validation',1)[0]
    report += '\n## Interpretation and validation\n\n'
    report += ('The LP methods meet the fixed numerical stopping tests early. On M6, LP-CUT-CG retains 305 rather than 964 columns, but takes 139 rather than 58 iterations and is slightly slower. '
        'SCS SDP-FULL reaches its one-million-iteration cap with unresolved PSD residuals; its exported integer certificate remains valid. SCS SDP-CG reaches the internal time limit and misses the common U <= 0.5617 target. '
        'These are measurements of the pinned implementations, not resolved SDP optima or a comparison with every native SDP solver.\n\n'
        'M7-lift6 stops after about 20 minutes and spends about 96.6% of its search in full pricing. Its verified certificate is approximately 1.84e-6 weaker than the M6 LP-CUT-CG certificate; the larger host has not improved this finite-run result. '
        'Adding the three seven-vertex families and then the 23 five-root families gives the larger improvements in the prior six verified runs. Uncompressed rounding preserves the ordering.\n\n'
        'All 15 final SVD and uncompressed certificates and all 63 available checkpoint slots are verified. Twelve early SDP-FULL slots contain no candidate. '
        'Forty-two distinct production exactification jobs suffice because identical saved files reuse verification. A further publication audit rechecks the stored M6 integer artifacts and compares both retained full-scan outputs for M7-lift6. '
        'The two native pilot objective/dual numbers are infeasible-iterate diagnostics and must not be presented as a valid optimum interval.\n\n'
        'The total experimental batch, including preparation and verification, took 6 hours 49 minutes and finished before the 12-hour deadline. No supplementary fast-group exception was needed. '
        'Cold original cache construction was not remeasured. Reported zero stage timings can be below clock resolution. All new certificates remain independent research artifacts, not newly formalized Lean theorems.\n\n'
        '![Algorithm and model comparisons](comparison.svg)\n')
    (output/'REPORT.md').write_text(report,encoding='utf-8')
    publication=read(output/'publication-manifest.json')
    publication.update(validation_sha256=rt.digest(output/'validation.json'),
        prior_results_sha256=rt.digest(previous/'results.json'),
        report_sha256={p.name:rt.digest(p) for p in output.iterdir() if p.is_file() and p.name!='publication-manifest.json'})
    rt.write_json(output/'publication-manifest.json',publication)
    print(rt.json.dumps({k:v for k,v in audit.items() if k!='profiles'}),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--campaign',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--previous',type=Path,required=True)
    a=p.parse_args()
    main(a.campaign.resolve(),a.output.resolve(),a.previous.resolve())
