"""Publish only hash-matched, fully verified results of the bounded new batch."""
from __future__ import annotations
import argparse
import csv
from fractions import Fraction
from pathlib import Path
import statistics
import runtime as rt


def certificate(folder,source,model):
    reuse=folder/'reused-verification.json'
    path=folder/'certificate.json'
    if reuse.exists():
        record=rt.json.loads(reuse.read_text(encoding='utf-8'))
        assert record['source_dual_sha256']==rt.digest(source)
        path=Path(record['verified_artifact'])
    cert=rt.json.loads(path.read_text(encoding='utf-8'))
    summary=rt.json.loads(path.with_suffix('.summary.json').read_text(encoding='utf-8'))
    assert cert['reconstruction']['source_dual_sha256']==rt.digest(source)
    bound=Fraction(cert['bound_numerator_unreduced'],cert['common_denominator_unreduced'])
    assert bound==Fraction(cert['bound_fraction'])==Fraction(summary['bound_fraction'])
    assert bound>=Fraction(5,9)
    if model=='M6':
        assert cert['host_order']==6 and summary['raw_count']==964
        assert cert['independent_full_scan_agrees']
    else:
        assert summary['raw_count']==13051375
        assert cert['reconstruction']['ordered_root_full_scan_agrees']
        assert all(not cert[key] for key in ['order7_s1_factors','order7_s3_nonedge_factors','order7_s3_edge_factors'])
    return cert,summary,path


def summarize(base,output):
    state=rt.json.loads((base/'status.json').read_text(encoding='utf-8'))
    manifest=rt.json.loads((base/'protocol/manifest.json').read_text(encoding='utf-8'))
    assert state['status']=='finished' and state['ready_for_reporting']
    rows=[]; checkpoints=[]; hashes={}
    for group in state['completed_groups']:
        model,method=group['model'],group['method']
        for rep in [1,2,3]:
            folder=base/'runs'/model/method/f'rep-{rep:02d}'
            run=rt.json.loads((folder/'run.json').read_text(encoding='utf-8'))
            supervisor=rt.json.loads((folder/'supervisor.json').read_text(encoding='utf-8'))
            history=[rt.json.loads(line) for line in (folder/'history.jsonl').read_text(encoding='utf-8').splitlines()]
            cert,summary,cert_path=certificate(folder/'exact/final-svd',folder/'best_dual.npz',model)
            uncompressed,uc_summary,uc_path=certificate(folder/'exact/final-cuts',folder/'best_dual.npz',model)
            target=manifest['predeclared_numerical_targets'][model]
            reached=[h['seconds'] for h in history if h['eligible_for_budget'] and h['best_global_upper']<=target]
            last=run['last_iteration']
            record=dict(model=model,method=method,repetition=rep,status=run['status'],
                backend_status=run['backend_status'],search_budget_seconds=3600,
                search_seconds=run['search_seconds'],initialization_seconds=run['construction_initialization_seconds'],
                numerical_global_upper=run['best_global_upper'],
                exact_bound_fraction=summary['bound_fraction'],exact_bound_decimal=summary['decimal'],
                uncompressed_bound_fraction=uc_summary['bound_fraction'],
                uncompressed_bound_decimal=uc_summary['decimal'],factors=summary['integer_square_factors'],
                raw_configuration_count=summary['raw_count'],
                solver_seconds=sum(h['lp_seconds']+h['native_seconds'] for h in history),
                eigen_seconds=sum(h['eigen_seconds'] for h in history),
                pricing_seconds=sum(h['pricing_seconds'] for h in history),
                iterations=len(history),final_columns=last['columns'],final_cuts=last['cuts'],
                final_minimum_eigenvalue=last['minimum_eigenvalue'],
                final_stationarity_residual=last['stationarity_residual'],
                final_normalization_residual=last['normalization_residual'],
                final_pricing_gap=last['pricing_gap'],
                rss_peak_bytes=supervisor['rss_peak_bytes'],job_peak_commit_bytes=supervisor['job_peak_commit_bytes'],
                common_numerical_target=target,time_to_target_seconds=min(reached) if reached else None,
                target_censored=not bool(reached),run_path=str(folder),certificate_path=str(cert_path),
                certificate_sha256=rt.digest(cert_path),uncompressed_certificate_path=str(uc_path))
            rows.append(record)
            for p in [folder/'run.json',folder/'supervisor.json',folder/'history.jsonl',
                      folder/'best_dual.npz',cert_path,uc_path]:
                hashes[str(p)]=rt.digest(p)
            for target in rt.CHECKPOINTS:
                snap=folder/'checkpoints'/f'{target:04d}'
                meta=rt.json.loads((snap/'checkpoint.json').read_text(encoding='utf-8'))
                row=dict(model=model,method=method,repetition=rep,target_seconds=target,
                    status=meta.get('status','verified'))
                if (snap/'dual.npz').exists():
                    c,s,p=certificate(folder/'exact'/f'{target:04d}-svd',snap/'dual.npz',model)
                    assert meta['candidate_available_seconds']<=target
                    row.update(candidate_available_seconds=meta['candidate_available_seconds'],
                        numerical_upper=meta['global_upper'],exact_bound_fraction=s['bound_fraction'],
                        exact_bound_decimal=s['decimal'],factors=s['integer_square_factors'],
                        certificate_path=str(p),certificate_sha256=rt.digest(p))
                    hashes[str(p)]=rt.digest(p)
                checkpoints.append(row)
    groups=[]
    for model,method in sorted({(r['model'],r['method']) for r in rows}):
        selected=[r for r in rows if (r['model'],r['method'])==(model,method)]
        assert len(selected)==3 and sorted(r['repetition'] for r in selected)==[1,2,3]
        stats=dict(model=model,method=method,repetitions=3,
            statuses=[r['status'] for r in selected],
            exact_fractions=[r['exact_bound_fraction'] for r in selected])
        for key in ['search_seconds','numerical_global_upper','exact_bound_decimal','factors',
                    'solver_seconds','eigen_seconds','pricing_seconds','rss_peak_bytes','job_peak_commit_bytes']:
            values=[r[key] for r in selected]
            stats[key]=dict(median=statistics.median(values),minimum=min(values),maximum=max(values))
        groups.append(stats)
    output.mkdir(parents=True,exist_ok=True)
    for filename,data in [('results.csv',rows),('checkpoints.csv',checkpoints)]:
        if data:
            fields=list(dict.fromkeys(k for row in data for k in row))
            with (output/filename).open('w',encoding='utf-8',newline='') as stream:
                writer=csv.DictWriter(stream,fieldnames=fields);writer.writeheader();writer.writerows(data)
    rt.write_json(output/'results.json',dict(campaign=str(base),status=state,protocol=manifest,
        groups=groups,runs=rows,checkpoints=checkpoints))
    lines=['# Remaining Section 6 experiments','',
        'Only verified new groups are summarized below. Previously published M7-no5 and M7-all5 LP-CUT-CG runs remain in results_20260910.',
        '', '| Model | Method | Repeats | Median search (s) | Median exact upper bound | Statuses |',
        '| --- | --- | ---: | ---: | ---: | --- |']
    for g in groups:
        lines.append(f"| {g['model']} | {g['method']} | 3 | {g['search_seconds']['median']:.3f} | {g['exact_bound_decimal']['median']:.12f} | {', '.join(g['statuses'])} |")
    lines += ['', 'Native solver residuals and termination statuses are retained in results.csv. A verified rational certificate does not assert exact SDP optimality or primal feasibility.',
        'Missing early native checkpoints mean no candidate was available by that time. Early completed candidates may be carried forward.',
        '', 'Pending full/native seven-vertex configurations: '+', '.join(manifest['pending_seven_vertex_comparisons'])+'.',
        'Deferred groups: '+rt.json.dumps(state['deferred_groups'])+'.',
        'M7-three5 was excluded by the user. Six-hour continuations are outside this bounded batch.', '']
    (output/'REPORT.md').write_text('\n'.join(lines),encoding='utf-8')
    rt.write_json(output/'publication-manifest.json',dict(input_sha256=hashes,
        report_sha256={p.name:rt.digest(p) for p in output.iterdir() if p.name!='publication-manifest.json' and p.is_file()}))
    print(rt.json.dumps(dict(groups=len(groups),runs=len(rows),checkpoints=len(checkpoints),output=str(output))),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--campaign',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    summarize(a.campaign.resolve(),a.output.resolve())
