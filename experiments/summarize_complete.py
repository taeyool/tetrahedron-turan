"""Audit the final selected campaign and publish measured tables and plots.

Read-only with respect to all experiment inputs. No optimization is performed.
"""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import csv
import statistics
import datetime

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
HASHES = {}
CERTS = {}

def digest(p):
    p = Path(p)
    if str(p) not in HASHES:
        HASHES[str(p)] = hashlib.sha256(p.read_bytes()).hexdigest()
    return HASHES[str(p)]

def read(p):
    digest(p)
    return json.loads(Path(p).read_text(encoding='utf-8'))

def write(p, value):
    Path(p).write_text(json.dumps(value, indent=2, ensure_ascii=False)+'\n', encoding='utf-8')

def csvwrite(p, rows):
    keys = list(dict.fromkeys(k for r in rows for k in r))
    with Path(p).open('w', encoding='utf-8', newline='') as f:
        w = csv.DictWriter(f, fieldnames=keys); w.writeheader()
        w.writerows({k:json.dumps(v,ensure_ascii=False) if isinstance(v,(dict,list)) else v for k,v in r.items()} for r in rows)

def integer_entries(value):
    if isinstance(value, int): return 1
    if isinstance(value, list): return sum(integer_entries(v) for v in value)
    return 0

def certificate(folder, source, model, kind='svd'):
    folder = Path(folder); p = folder/'certificate.json'
    reuse = folder/'reused-verification.json'
    if reuse.exists():
        rr = read(reuse)
        assert rr.get('source_dual_sha256',rr.get('dual_sha256')) == digest(source)
        p = Path(rr['verified_artifact'])
    if str(p) not in CERTS:
        c = read(p); sm = read(p.with_suffix('.summary.json'))
        frac = Fraction(c['bound_numerator_unreduced'], c['common_denominator_unreduced'])
        assert frac == Fraction(c['bound_fraction']) == Fraction(sm['bound_fraction'])
        assert c['scale'] == 2000000 and frac >= Fraction(5,9)
        expected = 964 if model=='M6' else 13051375
        assert sm['raw_count'] == expected
        if model == 'M6':
            assert c['host_order']==6 and c['independent_full_scan_agrees']
            entries = c['integer_entries']
        else:
            if c.get('order7_s5_blocks'):
                independent = c['exact_verification']['independent_pricing_full_scan']
                assert Fraction(independent['maximum_numerator'],c['common_denominator_unreduced']) == frac
                assert independent['complete_raw_count']==expected
            else:
                assert c['reconstruction']['ordered_root_full_scan_agrees']
                scans = [l for l in (p.parent/'process.log').read_text(encoding='utf-8').splitlines() if l.startswith('raw ')]
                assert len(scans)==2 and scans[0]==scans[1]
                digest(p.parent/'process.log')
            entries = sum(integer_entries(c.get(k,[])) for k in ['order6_factors_by_block','order7_s1_factors','order7_s3_nonedge_factors','order7_s3_edge_factors'])
            entries += sum(integer_entries(b['factors']) for b in c.get('order7_s5_blocks',[]))
        sup = read(p.parent/'supervisor.json')
        assert sup['returncode']==0
        CERTS[str(p)] = dict(bound_fraction=str(frac), bound_numerator=frac.numerator,
            bound_denominator=frac.denominator, bound_decimal=float(frac),
            factors=sm['integer_square_factors'],integer_entries=entries,raw_count=expected,
            certificate_path=str(p),certificate_sha256=digest(p),
            source_dual_sha256=c['reconstruction']['source_dual_sha256'],
            factorization=c['reconstruction']['factorization'],verification_seconds=sup['elapsed_seconds'],
            independent_full_scans_agree=True,formalized_in_Lean=False)
    result = dict(CERTS[str(p)])
    assert result['source_dual_sha256']==digest(source)
    assert result['factorization']==kind
    result['verification_reused'] = reuse.exists()
    return result

def history(folder):
    p=Path(folder)/'history.jsonl'; digest(p)
    return [json.loads(l) for l in p.read_text(encoding='utf-8').splitlines()]

def stats(values):
    vals=[v for v in values if v is not None]
    return dict(median=statistics.median(vals),minimum=min(vals),maximum=max(vals),observed=len(vals)) if vals else dict(median=None,minimum=None,maximum=None,observed=0)

def collect(task, target):
    a=task['attempts'][-1]; folder=Path(a['path'])
    run=read(folder/'run.json'); sup=read(folder/'supervisor.json'); hist=history(folder)
    budget=run['search_budget_seconds']; eligible=[h for h in hist if h['eligible_for_budget'] and h['seconds']<=budget]
    best=min(h['global_dual_upper'] for h in eligible)
    assert abs(best-run['best_global_upper'])<1e-10
    assert sup['returncode']==0 and run['status'] in ['completed','time_limit']
    svd=certificate(folder/'exact/final-svd',folder/'best_dual.npz',run['model'])
    cuts=certificate(folder/'exact/final-cuts',folder/'best_dual.npz',run['model'],'cuts')
    if (folder/'roundtrip/validation.json').exists(): assert read(folder/'roundtrip/validation.json')['status']=='passed'
    last=run['last_iteration']; reached=[h['seconds'] for h in eligible if h['global_dual_upper']<=target]
    info=read(folder/'native-owned/info.json') if (folder/'native-owned/info.json').exists() else {}
    row=dict(task_id=task['id'],model=run['model'],method=run['method'],repetition=run['repetition'],
        phase=task.get('phase',run.get('phase')),attempt=a['attempt'],status=run['status'],backend_status=run['backend_status'],
        initialization=run['initialization'],search_budget_seconds=budget,search_seconds=run['search_seconds'],
        initialization_seconds=run['construction_initialization_seconds'],candidate_available_seconds=run['best_candidate_available_seconds'],
        numerical_global_upper=best,exact_bound_fraction=svd['bound_fraction'],exact_bound_decimal=svd['bound_decimal'],
        uncompressed_bound_fraction=cuts['bound_fraction'],uncompressed_bound_decimal=cuts['bound_decimal'],
        factors=svd['factors'],uncompressed_factors=cuts['factors'],integer_entries=svd['integer_entries'],
        raw_configuration_count=svd['raw_count'],effective_full_universe_count=run['effective_full_universe_count'],
        solver_seconds=sum(h.get('lp_seconds',0)+h.get('native_seconds',0) for h in hist),
        eigen_seconds=sum(h['eigen_seconds'] for h in hist),pricing_seconds=sum(h['pricing_seconds'] for h in hist),
        update_seconds=sum(h.get('update_seconds',0) for h in hist),
        recycling_seconds=sum(h.get('lp_recycling_seconds',0) for h in hist),
        iterations=len(hist),final_columns=last['columns'],final_cuts=last['cuts'],primal_support=last['primal_support'],
        final_minimum_eigenvalue=last['minimum_eigenvalue'],final_stationarity_residual=last['stationarity_residual'],
        final_normalization_residual=last['normalization_residual'],final_pricing_gap=last['pricing_gap'],
        last_iteration_eligible_for_budget=last['eligible_for_budget'],
        rss_peak_bytes=sup['rss_peak_bytes'],job_peak_commit_bytes=sup['job_peak_commit_bytes'],
        overshoot_seconds=run['time_limit_overshoot_seconds'],common_numerical_target=target,
        time_to_target_seconds=min(reached) if reached else None,target_censored=not bool(reached),
        verification_seconds=svd['verification_seconds'],uncompressed_verification_seconds=cuts['verification_seconds'],
        run_path=str(folder),certificate_path=svd['certificate_path'],certificate_sha256=svd['certificate_sha256'],
        uncompressed_certificate_path=cuts['certificate_path'],svd=svd,uncompressed=cuts,
        settings=run['settings'],native_info=info,last_iteration=last,
        source_sha256=run['source_sha256'],ordered_blocks=run.get('ordered_blocks'),
        cold_features_seconds=run.get('shared_cold_feature_construction_seconds'),
        cold_native_packing_seconds=run.get('shared_cold_native_packed_construction_seconds'),
        full_coefficient_bytes=run.get('full_coefficient_bytes'),native_packed_matrix_bytes=run.get('native_packed_matrix_bytes'),
        native_build_manifest_sha256=run.get('native_owned_build_manifest_sha256'))
    checkpoints=[]
    for snap in sorted((folder/'checkpoints').iterdir()):
        if not snap.is_dir():continue
        meta=read(snap/'checkpoint.json'); seconds=meta['target_seconds']
        cp=dict(task_id=task['id'],model=row['model'],method=row['method'],repetition=row['repetition'],phase=row['phase'],target_seconds=seconds,status=meta.get('status','verified'))
        prior=[h for h in eligible if h['seconds']<=seconds]
        if (snap/'dual.npz').exists():
            assert meta['candidate_available_seconds']<=seconds and prior
            assert abs(min(h['global_dual_upper'] for h in prior)-meta['global_upper'])<1e-10
            cert=certificate(folder/'exact'/f'{seconds:04d}-svd',snap/'dual.npz',row['model'])
            cp.update(cert, candidate_available_seconds=meta['candidate_available_seconds'],numerical_upper=meta['global_upper'],
                retrospective_certification_seconds=meta['candidate_available_seconds']+cert['verification_seconds'])
        else: assert not prior and meta['status']=='no_completed_candidate'
        checkpoints.append(cp)
    return row,checkpoints

def main(base,output):
    state=read(base/'status.json'); protocol=read(base/'protocol/manifest.json')
    assert state['ready_for_reporting'] and state['status']=='finished' and all(t['status']=='complete' for t in state['tasks'])
    output.mkdir(parents=True,exist_ok=True)
    rows=[]; checkpoints=[]; attempts=[]
    for t in state['tasks']:
        for a in t.get('attempts',[]):
            attempts.append(dict(task_id=t['id'],task_status=t['status'],kind=t['kind'],phase=t.get('phase'),
                **{k:v for k,v in a.items() if k!='source_sha256'}))
        if t.get('phase') in ['production','long'] or t['id']=='reference-M6-SDP-FULL-1h':
            row,cps=collect(t,protocol['target_values'].get(t.get('model'),0.5617));rows.append(row);checkpoints+=cps
    assert len([r for r in rows if r['phase']=='production'])==18 and len(rows)==22
    old=read(HERE/'results_20260910/results.json'); remaining=read(HERE/'results_remaining_20260910/results.json')
    prior=[]
    for r in old['rows']:
        rr=dict(model=r['model'],method=r['method'],repetition=r['rep'],phase='production',status=r['status'],
            search_seconds=r['search_seconds'],initialization_seconds=r['initialization_seconds'],
            numerical_global_upper=r['global_numerical_U'],exact_bound_fraction=r['exact_fraction'],exact_bound_decimal=r['exact_decimal'],
            uncompressed_bound_fraction=r['cut_fraction'],uncompressed_bound_decimal=float(Fraction(r['cut_fraction'])),factors=r['squares'],
            solver_seconds=r['solver_seconds'],eigen_seconds=r['separation_seconds'],pricing_seconds=r['pricing_seconds'],
            final_columns=r['columns'],final_cuts=r['cuts'],iterations=r['iterations'],
            final_minimum_eigenvalue=r['minimum_eigenvalue'],final_stationarity_residual=r['stationarity_residual'],final_normalization_residual=r['normalization_residual'],
            rss_peak_bytes=r['rss_peak_bytes'],job_peak_commit_bytes=r['job_peak_commit_bytes'],
            common_numerical_target=r['target'],time_to_target_seconds=r['numerical_time_to_target'],target_censored=r['numerical_time_to_target'] is None,
            run_path=r['run_artifact'],certificate_path=r['certificate'],certificate_sha256=r['certificate_sha256'],verification_seconds=r['verification_seconds'])
        assert digest(rr['certificate_path'])==rr['certificate_sha256'];prior.append(rr)
    for r in remaining['runs']:
        rr=dict(r,phase='production');assert digest(rr['certificate_path'])==rr['certificate_sha256'];prior.append(rr)
    for cp in old['checkpoints']:
        checkpoints.append(dict(model=cp['model'],method='LP-CUT-CG',repetition=cp['rep'],phase='production',
            target_seconds=cp['target_seconds'],status='verified',candidate_available_seconds=cp['candidate_available_seconds'],
            bound_fraction=cp['exact_fraction'],bound_decimal=float(Fraction(cp['exact_fraction'])),numerical_upper=cp['numerical_U']))
    for cp in remaining['checkpoints']:
        checkpoints.append(dict(cp,phase='production',bound_fraction=cp.get('exact_bound_fraction'),bound_decimal=cp.get('exact_bound_decimal')))
    mainrows=prior+[r for r in rows if r['phase']=='production'];assert len(mainrows)==39
    groups=[]
    for model,method in sorted({(r['model'],r['method']) for r in mainrows}):
        selected=[r for r in mainrows if (r['model'],r['method'])==(model,method)]
        assert sorted(r['repetition'] for r in selected)==[1,2,3]
        group=dict(model=model,method=method,repetitions=3,statuses=[r['status'] for r in selected])
        for k in ['search_seconds','numerical_global_upper','exact_bound_decimal','uncompressed_bound_decimal','factors','solver_seconds',
            'eigen_seconds','pricing_seconds','initialization_seconds','rss_peak_bytes','job_peak_commit_bytes','time_to_target_seconds',
            'final_columns','final_cuts','iterations','verification_seconds','final_minimum_eigenvalue']:
            group[k]=stats([r.get(k) for r in selected])
        groups.append(group)
    write(output/'results.json',dict(campaign=str(base),generated_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        main_runs=mainrows,new_runs=rows,groups=groups,checkpoints=checkpoints,protocol=protocol,
        elapsed_campaign_hours=(state['finished_epoch']-datetime.datetime.fromisoformat(state['started_utc']).timestamp())/3600))
    csvwrite(output/'results.csv',mainrows);csvwrite(output/'long-runs.csv',[r for r in rows if r['phase']!='production'])
    csvwrite(output/'checkpoints.csv',checkpoints);csvwrite(output/'attempts.csv',attempts)
    write(output/'attempt-provenance.json',state['tasks'])
    write(output/'validation.json',dict(main_configurations=len(groups),main_repetitions=len(mainrows),new_productions=18,
        long_runs=3,independent_m6_reference=1,new_checkpoint_slots=sum(c.get('task_id') is not None for c in checkpoints),
        production_checkpoint_slots=sum(c['phase']=='production' for c in checkpoints),
        production_verified_checkpoints=sum(c['phase']=='production' and c['status']=='verified' for c in checkpoints),
        new_unique_certificates_audited=len(CERTS),all_source_dual_hashes_and_exact_fractions_agree=True,
        no_late_candidate_selected=True))
    write(output/'publication-manifest.json',dict(input_sha256=HASHES))
    print(json.dumps(dict(groups=groups,validation=read(output/'validation.json')),ensure_ascii=False))

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--campaign',type=Path,required=True);ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();main(args.campaign,args.output)
