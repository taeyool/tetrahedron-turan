"""Generate evidence-only tables and plots; never promote missing verification."""
from __future__ import annotations
import argparse
import csv
from fractions import Fraction
from pathlib import Path
import statistics
import numpy as np

import runtime as rt


def read(path, default=None):
    return rt.json.loads(path.read_text(encoding='utf-8')) if path.exists() else default


def check_certificate(cert, source):
    assert cert['reconstruction']['source_dual_sha256']==rt.digest(source)
    exact=cert['exact_verification']
    independent=exact['independent_pricing_full_scan']
    assert exact['raw_count']==independent['complete_raw_count']==13051375
    assert exact['numerator']==independent['maximum_numerator']
    assert Fraction(cert['bound_fraction'])==Fraction(exact['numerator'],exact['denominator'])


def summarize(base, output=None, replacement_run=None):
    base=Path(base).resolve()
    output=Path(output).resolve() if output else base/'summary'
    output.mkdir(parents=True,exist_ok=True)
    status=read(base/'status.json',{})
    manifest=read(base/'protocol/manifest.json',{})
    replacement_run=Path(replacement_run).resolve() if replacement_run else None
    if replacement_run:
        replacement_base=replacement_run.parents[2]
        replacement_status=read(replacement_base/'status.json',{})
        assert replacement_status.get('status')=='finished'
        assert replacement_status.get('ready_for_reporting') is True
        manifest['replacement_selection']=dict(model='M7-all5',rep=3,run=str(replacement_run),
            replaces=str(base/'runs/M7-all5/rep-03'),
            protocol=read(replacement_base/'protocol/manifest.json'),
            campaign_status=replacement_status)
    selected_runs=[]
    rows=[]
    checkpoint_rows=[]
    histories={}
    for name in ['M7-no5','M7-all5']:
        for rep in [1,2,3]:
            run=base/'runs'/name/f'rep-{rep:02d}'
            if replacement_run and (name,rep)==('M7-all5',3): run=replacement_run
            selected_runs.append(run)
            data=read(run/'run.json',{})
            sup=read(run/'supervisor.json',{})
            history=[]
            if (run/'history.jsonl').exists():
                for line in (run/'history.jsonl').read_text(encoding='utf-8').splitlines():
                    try: history.append(rt.json.loads(line))
                    except ValueError: pass
            histories[(name,rep)]=history
            complete = data.get('status') in ('completed','time_limit') and sup.get('status')=='completed'
            candidate = {}
            if (run/'best_dual.npz').exists():
                with np.load(run/'best_dual.npz',allow_pickle=False) as z:
                    candidate={k:float(z[k]) for k in ['global_upper','availability_seconds']}
                    candidate['iteration']=int(z['iteration'])
                matching=[h for h in history if h['iteration']==candidate['iteration']]
                assert len(matching)==1
                assert abs(matching[0]['global_dual_upper']-candidate['global_upper'])<1e-14
                assert abs(matching[0]['seconds']-candidate['availability_seconds'])<1e-9
            bound=None; squares=None; certificate=None
            certpath=run/'exact/final-svd/certificate.json'
            if certpath.exists():
                cert=read(certpath)
                check_certificate(cert,run/'best_dual.npz')
                bound=cert['bound_fraction']; squares=cert['total_integer_square_factors']; certificate=str(certpath)
            target=manifest.get('predeclared_numerical_targets',{}).get(name)
            hits=[h['seconds'] for h in history if target is not None and h.get('eligible_for_budget') and h['global_dual_upper']<=target]
            last=history[-1] if history else data.get('last_iteration',{})
            row=dict(model=name,method='LP-CUT-CG',rep=rep,status=data.get('status','not_run'),
                supervisor_status=sup.get('status'),budget_complete=complete,
                search_seconds=data.get('search_seconds') if complete else last.get('seconds'),
                last_metadata_search_seconds=data.get('search_seconds'),process_seconds=sup.get('elapsed_seconds'),
                initialization_seconds=data.get('construction_initialization_seconds'),
                global_numerical_U=candidate.get('global_upper'),candidate_available_seconds=candidate.get('availability_seconds'),
                candidate_iteration=candidate.get('iteration'),last_metadata_global_U=data.get('best_global_upper'),
                exact_fraction=bound,exact_numerator=Fraction(bound).numerator if bound else None,
                exact_denominator=Fraction(bound).denominator if bound else None,
                exact_decimal=float(Fraction(bound)) if bound else None,squares=squares,certificate=certificate,
                exact_verified=bool(bound),rss_peak_bytes=sup.get('rss_peak_bytes'),
                job_peak_commit_bytes=sup.get('job_peak_commit_bytes'),kernel_memory_cap=sup.get('kernel_job_limit_enforced'),
                iterations=len(history) if history else None,columns=last.get('columns'),cuts=last.get('cuts'),
                minimum_eigenvalue=last.get('minimum_eigenvalue'),stationarity_residual=last.get('stationarity_residual'),
                normalization_residual=last.get('normalization_residual'),target=target,
                numerical_time_to_target=min(hits) if hits else None,
                solver_seconds=sum(h['lp_seconds'] for h in history) if history else None,
                separation_seconds=sum(h['eigen_seconds'] for h in history) if history else None,
                pricing_seconds=sum(h['pricing_seconds'] for h in history) if history else None,
                raw_configurations=13051375,effective_full_universe_count=None,
                verification_seconds=read(run/'exact/final-svd/supervisor.json',{}).get('elapsed_seconds'),
                run_artifact=str(run))
            cutpath=run/'exact/final-cuts/certificate.json'
            cut=read(cutpath,{})
            if cut: check_certificate(cut,run/'best_dual.npz')
            row.update(cut_fraction=cut.get('bound_fraction'),cut_squares=cut.get('total_integer_square_factors'),
                       certificate_sha256=rt.digest(certpath) if certpath.exists() else None,
                       candidate_sha256=rt.digest(run/'best_dual.npz') if candidate else None)
            rows.append(row)
            for target in rt.CHECKPOINTS:
                snap=run/'checkpoints'/f'{target:04d}'
                record=read(snap/'checkpoint.json',{})
                primary=run/'exact'/f'{target:04d}-svd'
                exact_path=primary/'certificate.json'
                reuse=read(primary/'reused-verification.json',{})
                if not exact_path.exists() and reuse: exact_path=Path(reuse['verified_artifact'])
                cert=read(exact_path,{})
                if cert:
                    assert record['candidate_available_seconds']<=target
                    check_certificate(cert,snap/'dual.npz')
                elapsed=read(exact_path.parent/'supervisor.json',{}).get('elapsed_seconds') if cert else None
                checkpoint_rows.append(dict(model=name,rep=rep,target_seconds=target,
                    candidate_available_seconds=record.get('candidate_available_seconds'),
                    numerical_U=record.get('global_upper'),exact_fraction=cert.get('bound_fraction'),
                    squares=cert.get('total_integer_square_factors'),verified=bool(cert),
                    certificate=str(exact_path) if cert else None,
                    certificate_sha256=rt.digest(exact_path) if cert else None,
                    verification_seconds=elapsed,verification_reused=bool(reuse),
                    retrospective_certification_seconds=(record['candidate_available_seconds']+elapsed) if cert and elapsed is not None else None))
    if replacement_run:
        assert all(r['budget_complete'] and r['exact_verified'] and r['cut_fraction'] for r in rows)
        assert all(r['verified'] for r in checkpoint_rows)
    scan_invocations=sum(1 for run in selected_runs for p in (run/'exact').glob('*/supervisor.json')
                         if read(p,{}).get('status')=='completed')
    reused=sum(r['verification_reused'] for r in checkpoint_rows)
    rt.write_json(output/'results.json',dict(campaign_status=status,manifest=manifest,rows=rows,checkpoints=checkpoint_rows,
        selected_verification_invocations=scan_invocations,
        reporting_source_sha256=rt.digest(__file__),
        recovery_note='Candidate NPZ and completed history are authoritative if run.json is stale after a write failure. Failed runs are excluded from one-hour aggregates.'))
    with (output/'results.csv').open('w',newline='',encoding='utf-8') as stream:
        writer=csv.DictWriter(stream,fieldnames=list(rows[0])); writer.writeheader();writer.writerows(rows)
    with (output/'checkpoints.csv').open('w',newline='',encoding='utf-8') as stream:
        writer=csv.DictWriter(stream,fieldnames=list(checkpoint_rows[0]));writer.writeheader();writer.writerows(checkpoint_rows)
    lines=['# Bounded Section 6 campaign: measured results','',
        'This report covers only M7-no5 and M7-all5 under LP-CUT-CG. '
        'Three independent fresh searches of at most 3600 seconds were scheduled per model. '
        'It is a user-authorized subset of the execution brief, not the 14-configuration campaign.',
        '',f"Campaign status: **{status.get('status','unknown')}**.",
        f"Absolute deadline: `{manifest.get('deadline_utc','unknown')}`.",
        '', '## Setup', '',
        'Both models retain stationarity S=3(rho^2-[[d*d]]_1), edge-density objectives, '
        'the same nine order-six blocks and three additional order-seven blocks. '
        'M7-all5 adds all 23 specified five-root types. The same ExpandedMaster coefficient, '
        'cut selection, column-equivalence and pruning routines are used. Initial columns come '
        'from the empty graph and the balanced cyclic three-part construction. No archived '
        'certificate factors, checkpoints or screening directions seed the searches.', '',
        'HiGHS 1.15.1, NumPy 2.0.2, SciPy 1.13.1 and Python 3.12.4 run on Windows 11 '
        'with MinGW GCC 13.2.0. Solver/BLAS threads are one; full pricing uses two threads. '
        'The full package lock, CPU, RAM, power-mode information, source snapshots and hashes '
        'are retained in environment/. The process-tree RSS is sampled every second; '
        'where reported, a Windows Job Object additionally limits tree commit memory to 40 GiB '
        'and records its peak. RSS and commit memory are different measurements.', '',
        'The search budget excludes initialization. A candidate becomes available only after '
        'complete pricing finishes. Evaluations completing after 3600 seconds cannot improve '
        'the one-hour result. A 60-second shutdown grace permits saving completed work; '
        'the absolute campaign deadline takes precedence. Exactification occurs sequentially '
        'after search, at factor scale 2,000,000, with primary SVD relative tolerance 1e-7.', '',
        '## Results', '',
        '| Model | Rep. | Search status | Numerical global U | Exact SVD bound | Squares |',
        '|---|---:|---|---:|---|---:|']
    for row in rows:
        value=f"{row['global_numerical_U']:.12f}" if row['global_numerical_U'] is not None else 'not available'
        lines.append(f"| {row['model']} | {row['rep']} | {row['status']} | {value} | {row['exact_fraction'] or 'not verified'} | {row['squares'] if row['squares'] is not None else '—'} |")
    lines += ['', 'Each rational bound above is accepted only when its saved certificate matches '
              'the candidate hash and both complete integer scans. Floating-point U, restricted '
              'objectives and approximate primal feasibility are not exact optimum proofs.', '',
        '## Replication and interpretation', '',
        'Only the selected runs that completed the allocated search budget enter the following aggregates.', '']
    for name in ['M7-no5','M7-all5']:
        selected=[r for r in rows if r['model']==name and r['budget_complete']]
        values=[r['global_numerical_U'] for r in selected if r['global_numerical_U'] is not None]
        exacts=[float(Fraction(r['exact_fraction'])) for r in selected if r['exact_fraction']]
        if values:
            lines.append(f"- {name}: {len(values)} numerical results; median U {statistics.median(values):.12f}, range [{min(values):.12f}, {max(values):.12f}].")
        if exacts:
            lines.append(f"- {name}: {len(exacts)} exactly verified final SVD candidates; decimal range [{min(exacts):.12f}, {max(exacts):.12f}].")
        for field in ['candidate_available_seconds','rss_peak_bytes','job_peak_commit_bytes','solver_seconds','separation_seconds','pricing_seconds','numerical_time_to_target','verification_seconds']:
            vals=[r[field] for r in selected if r[field] is not None]
            if vals: lines.append(f"- {name}, {field}: median {statistics.median(vals):.6f}; range [{min(vals):.6f}, {max(vals):.6f}].")
    if replacement_run:
        lines += ['', '## Selected-run provenance', '',
            f'The third M7-all5 result is the user-authorized fresh replacement at `{replacement_run}`. '
            'It completed the same one-hour numerical protocol, with unchanged solver settings, '
            'ordered bases, starting columns and arithmetic sources. Only JSON persistence was '
            'hardened against transient Windows file-sharing errors. The previous interrupted '
            'attempt remains in the original campaign archive and is not included in these '
            'six-run statistics or curves. The replacement manifest records both paths and '
            'executed source hashes. No result was selected by comparing the quality of '
            'multiple completed replacements.']
    else:
        partial=[r for r in rows if not r['budget_complete']]
        if partial:
            lines += ['', '## Attempts outside the complete-run aggregates', '']
            for row in partial:
                lines.append(f"- {row['model']} rep {row['rep']}: {row['status']}; raw records: `{row['run_artifact']}`.")
    lines += ['', '## Verification coverage and rounding', '',
        f"{sum(r['verified'] for r in checkpoint_rows)} of {len(checkpoint_rows)} planned selected-run checkpoints are exactly verified. "
        f"All {sum(bool(r['exact_fraction'] and r['cut_fraction']) for r in rows)} selected final candidates have both SVD and original-cut roundings. "
        f'The selected runs contain {scan_invocations} verification invocations (each containing two full '
        'integer scans), plus the separate archived-reference verification. '
        f'{reused} checkpoint records reuse byte-identical verification. The checkpoint CSV '
        'retains candidate availability, separate verification cost, and retrospective '
        'availability-plus-verification time; none of these is the actual queued wall-clock '
        'finish time of the campaign.', '',
        '| Model | Rep. | Exact cut-factor bound | Cut factors | Exact SVD bound | SVD factors |',
        '|---|---:|---|---:|---|---:|']
    for row in rows:
        lines.append(f"| {row['model']} | {row['rep']} | {row['cut_fraction']} | {row['cut_squares']} | {row['exact_fraction']} | {row['squares']} |")
    lines += ['', 'These deterministic repetitions assess solver/timing variability; they are not '
        'independent random-graph samples. A comparison concerns finite-budget certificates '
        'from these two models. No speedup over a direct SDP solver, no strict separation '
        'of model optima, and no new Lean theorem is established.', '',
        '## Verification and remaining work', '',
        'The original headline certificate was independently reproduced on this machine: '
        '78151799925597/140000000000000, 629 square factors, two complete scans of '
        '13,051,375 raw extensions. See exact/reference-verified.summary.json. '
        'Construction, signed-dual pricing, ordered five-root coefficients and exporter '
        'validation are in validation/models/. The raw extension count is not an '
        'isomorphism-class count.', '',
        'The other 12 method/model configurations, six-hour continuations, and historical '
        'optimization replay were excluded by the user-approved time-limited scope. '
        'Missing exact checkpoints and runs are missing results, never zero measurements. '
        'Failures and limit conditions are retained in each run and supervisor record.']
    if status.get('error'): lines += ['',f"Campaign error: `{status['error']}`."]
    if status.get('stopping_reason'): lines += ['',status['stopping_reason']]
    (output/'REPORT.md').write_text('\n'.join(lines)+'\n',encoding='utf-8')
    if any(histories.values()):
        import matplotlib
        matplotlib.use('Agg')
        import matplotlib.pyplot as plt
        plt.rcParams.update({'font.family':'serif','font.size':10,'pdf.fonttype':42,'svg.fonttype':'none'})
        fig,axes=plt.subplots(1,2,figsize=(7.4,3.2))
        for ax in axes:
            for name,color in [('M7-no5','#1b5b91'),('M7-all5','#c34d24')]:
                for rep,style in [(1,'-'),(2,'--'),(3,':')]:
                    hist=[h for h in histories[(name,rep)] if h.get('eligible_for_budget') and h.get('best_global_upper') is not None]
                    row=next(r for r in rows if r['model']==name and r['rep']==rep)
                    label=f'{name}, r{rep}'+(' (partial)' if not row['budget_complete'] else '')
                    if hist:
                        times=[h['seconds']/60 for h in hist]; values=[h['best_global_upper'] for h in hist]
                        if row['budget_complete']: times.append(60); values.append(values[-1])
                        ax.step(times,values,where='post',color=color,linestyle=style,linewidth=1.1,label=label)
                    for checkpoint in checkpoint_rows:
                        if checkpoint['model']==name and checkpoint['rep']==rep and checkpoint['verified']:
                            ax.scatter(checkpoint['target_seconds']/60,float(Fraction(checkpoint['exact_fraction'])),
                                       marker='x',s=24,color=color,zorder=5)
                    if row['exact_fraction'] and not row['budget_complete']:
                        ax.scatter(row['candidate_available_seconds']/60,row['exact_decimal'],marker='s',s=25,
                                   facecolors='white',edgecolors=color,zorder=6)
            ax.set_xlabel('Search time (minutes)');ax.set_xlim(0,61);ax.set_xticks([0,15,30,45,60]);ax.grid(alpha=.22)
        axes[0].set_title('Complete trajectory');axes[0].set_ylabel('Best global coefficient maximum')
        axes[1].set_title('Detail near the final bounds');axes[1].set_ylim(.5584,.5648)
        axes[0].legend(fontsize=8.2,loc='upper right')
        fig.tight_layout()
        for ext in ['pdf','svg','png']: fig.savefig(output/f'convergence.{ext}',dpi=160)
        plt.close(fig)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('campaign',type=Path)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--replacement-run',type=Path)
    args=parser.parse_args()
    summarize(args.campaign,args.output,args.replacement_run)
