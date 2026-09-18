"""Durable sequential queue for the remaining Section 6 comparisons.

Failed attempts remain immutable. Independent jobs continue; repair requests can
be resumed without repeating completed jobs. Limits are outcomes, not convergence.
"""
import argparse
import datetime as dt
import os
from pathlib import Path
import random
import sys
import time
import traceback
import runtime as rt
from run_overnight import watch,environment

MEMORY=40*1024**3


def task_matrix():
    tasks=[dict(id='model-validation',kind='validation',deps=[])]
    for name in ['M7-no5','M7-all5']:
        tasks.append(dict(id=f'pilot-{name}-SDP-CG',kind='search',model=name,method='SDP-CG',phase='pilot',seconds=600,rep=1,deps=['model-validation']))
        tasks.append(dict(id=f'features-{name}',kind='features',model=name,deps=['model-validation']))
        tasks.append(dict(id=f'full-validation-{name}',kind='full-validation',model=name,deps=[f'features-{name}']))
        for method in ['LP-CUT','SDP-FULL']:
            tasks.append(dict(id=f'pilot-{name}-{method}',kind='search',model=name,method=method,phase='pilot',seconds=600,rep=1,deps=[f'full-validation-{name}']))
    groups=[(name,method) for name in ['M7-no5','M7-all5'] for method in ['SDP-FULL','LP-CUT','SDP-CG']]
    random.Random(611).shuffle(groups)
    for rep in [1,2,3]:
        order=groups[rep-1:]+groups[:rep-1]
        for name,method in order:
            tasks.append(dict(id=f'production-{name}-{method}-rep-{rep:02d}',kind='search',model=name,method=method,phase='production',seconds=3600,rep=rep,deps=[f'pilot-{name}-{method}']))
    for name in ['M7-no5','M7-all5']:
        tasks.append(dict(id=f'long-{name}-LP-CUT-CG',kind='search',model=name,method='LP-CUT-CG',phase='long',seconds=21600,rep=1,deps=['model-validation']))
    tasks.append(dict(id='long-M6-SDP-FULL',kind='long-reference',model='M6',method='SDP-FULL',phase='long',seconds=21600,rep=1,deps=[]))
    return [{**t,'status':'pending','attempts':[]} for t in tasks]


def main(base):
    state_path=base/'status.json'
    state=rt.json.loads(state_path.read_text(encoding='utf-8'))
    # The lock stores both pid and creation time, protecting against PID reuse.
    import psutil
    lock=base/'controller.lock'
    if lock.exists():
        prior=rt.json.loads(lock.read_text())
        try:
            p=psutil.Process(prior['pid'])
            if abs(p.create_time()-prior['create_time'])<1:raise RuntimeError('Campaign controller already running')
        except psutil.NoSuchProcess:pass
        lock.unlink()
    rt.write_json(lock,dict(pid=os.getpid(),create_time=psutil.Process().create_time()))
    state.update(controller_pid=os.getpid(),status='running',active=None)
    if 'tasks' not in state:
        state['tasks']=task_matrix()
        environment(base)
        rt.write_json(base/'protocol/manifest.json',dict(
            revision='4d2310b',scope=state['scope'],long_runs=state['long_runs'],excluded_models=['M7-three5'],
            repetitions=3,main_search_seconds=3600,pilot_search_seconds=600,long_search_seconds=21600,
            memory_cap_bytes=MEMORY,initialization_limit_seconds=3600,shutdown_grace_seconds=60,
            schedule_seed=611,stationarity=True,lp_backend='HiGHS 1.15.1',native_backend='SCS 3.2.8 via CVXPY 1.6.5',
            native_settings=dict(eps_abs=1e-8,eps_rel=1e-8,eps_infeas=1e-8,max_iters=20000000,use_indirect=True,inner_seconds=300),
            native_reference_settings=dict(use_indirect=False,max_iters=20000000),
            target_values={'M7-no5':.5628,'M7-all5':.5646},targets_origin='Previously declared within-model pilot levels; all remaining methods use those same levels.',
            checkpoint_seconds=[60,300,900,1800,3600],long_checkpoint_seconds=[3600,7200,14400,21600],
            factor_scale=2000000,svd_relative_tolerance=1e-7,final_uncompressed=True,
            long_initialization='Separate fresh repetition 1; previous M7 master and M6 SCS internal iterates unavailable. Retain matched 1-hour and 6-hour checkpoints; do not count as a fourth main repetition.',
            source_sha256=rt.sources(),catalogue_source_sha256=rt.digest(rt.HERE/'seven_catalog.cpp'),
            catalogue_manifest=rt.json.loads((base/'cache/seven-catalog.json').read_text()),
            availability_review_utc=state['availability_review_utc'],hard_overall_deadline=None,
            outcome_policy='Time-limited trials with valid certified candidates are retained as time_limit, not relabeled converged. Process, implementation, export and numerical failures enter repair/retry without replacing old attempts.'))
    if os.name=='nt':
        import ctypes
        ctypes.windll.kernel32.SetThreadExecutionState(0x80000001)
    verified=state.setdefault('verified_duals',{})

    def publish():rt.write_json(state_path,state)

    def execute(command,output,seconds=7200,search=None):
        result=watch(command,output,time.time()+seconds,MEMORY,search_limit=search,initialization_limit=3600)
        assert result['kernel_job_limit_enforced'],'Kernel process-tree memory cap missing'
        if result['returncode']!=0:raise RuntimeError(f"{result['status']}: {output}; see process.log")
        return result

    def exact(model,source,output,factorization):
        key=rt.digest(source)+'/'+factorization
        if key in verified and Path(verified[key]).exists():
            rt.write_json(output/'reused-verification.json',dict(dual_sha256=key.split('/')[0],factorization=factorization,verified_artifact=verified[key]));return
        if model=='M6':
            command=[sys.executable,'-X','utf8',str(rt.HERE/'exactify_order6.py'),str(source),'--cache',str(base/'cache'),'--output',str(output/'certificate.json'),'--factorization',factorization]
        else:
            script='exactify_five_root.py' if model=='M7-all5' else 'exactify_reconstructed_dual.py'
            command=[sys.executable,'-X','utf8',str(rt.HERE/'runtime.py'),str(rt.RESEARCH/script),str(source),'--factorization',factorization,'--svd-relative-tolerance','1e-7','--scale','2000000','--threads','2','--cache',str(output/'cache'),'--output',str(output/'certificate.json')]
            if model=='M7-all5':command.append('--cross-check-pricing')
        execute(command,output,seconds=14400)
        assert (output/'certificate.json').exists()
        verified[key]=str(output/'certificate.json');publish()

    try:
        for t in state['tasks']:
            if t['status']=='running':
                t['status']='needs_repair';t['error']='Previous controller interrupted; inspect attempt before retry.'
            if t.get('retry_requested'):
                t['status']='pending';t.pop('retry_requested')
        publish()
        for task in state['tasks']:
            if task['status']=='complete':continue
            if task['status']=='needs_repair':continue
            done={t['id'] for t in state['tasks'] if t['status']=='complete'}
            if any(d not in done for d in task['deps']):
                task['status']='waiting_for_dependency';publish();continue
            attempt=len(task['attempts'])+1
            output=base/'jobs'/task['id']/f'attempt-{attempt:02d}'
            record=dict(attempt=attempt,path=str(output),started_epoch=time.time(),source_sha256=rt.sources())
            task['attempts'].append(record);task['status']='running'
            state.update(active=task['id'],active_attempt=attempt);publish()
            try:
                kind=task['kind'];command=[sys.executable,'-X','utf8']
                if kind=='validation':
                    execute(command+[str(rt.HERE/'validate_selected.py'),'--cache',str(base/'cache'),'--output',str(output/'data')],output)
                elif kind=='features':
                    execute(command+[str(rt.HERE/'seven_full.py'),'--cache',str(base/'cache'),'--model',task['model']],output,seconds=14400)
                elif kind=='full-validation':
                    execute(command+[str(rt.HERE/'validate_seven_full.py'),'--cache',str(base/'cache'),'--model',task['model'],'--output',str(output/'validation.json')],output,seconds=3600)
                elif kind=='no5-lp-memory-validation':
                    execute(command+[str(rt.HERE/'validate_no5_lp_memory.py'),'--output',str(output/'data')],output,seconds=300)
                elif kind=='lp-recycle-validation':
                    execute(command+[str(rt.HERE/'validate_recycle_highs.py'),'--output',str(output/'data')],output,seconds=600)
                elif kind=='lp-memory-validation':
                    execute(command+[str(rt.HERE/'validate_lp_memory.py'),'--output',str(output/'data')],output,seconds=300)
                elif kind=='owned-native-validation':
                    execute(command+[str(rt.HERE/'validate_owned_scs.py'),'--cache',str(base/'cache'),'--output',str(output/'data')],output,seconds=7200)
                elif kind=='native-packed-features':
                    execute(command+[str(rt.HERE/'seven_full_native.py'),'--cache',str(base/'cache'),'--model',task['model']],output,seconds=14400)
                elif kind=='full-adapter-validation':
                    execute(command+[str(rt.HERE/'validate_full_adapters.py'),'--cache',str(base/'cache'),'--model',task['model'],'--output',str(output/'validation.json')],output,seconds=7200)
                else:
                    if kind=='long-reference':
                        command+=[str(rt.HERE/'run_long_reference.py'),'--cache',str(base/'cache'),'--output',str(output),'--seconds',str(task['seconds'])]
                    else:
                        command+=[str(rt.HERE/'run_seven_method.py'),'--model',task['model'],'--method',task['method'],'--phase',task['phase'],'--rep',str(task['rep']),'--cache',str(base/'cache'),'--output',str(output),'--seconds',str(task['seconds'])]
                    if task.get('resume_checkpoint'):
                        assert task['phase']=='pilot' and task['method']=='LP-CUT-CG' and task['model']=='M7-all5'
                        command += ['--resume-checkpoint',task['resume_checkpoint']]
                    execute(command,output,seconds=task['seconds']+3660,search=task['seconds'])
                    run=rt.json.loads((output/'run.json').read_text())
                    record['search_status']=run['status']
                    if task.get('require_progress_from_stall'):
                        updates=[rt.json.loads(line) for line in (output/'updates.jsonl').read_text().splitlines()]
                        history=[rt.json.loads(line) for line in (output/'history.jsonl').read_text().splitlines()]
                        assert len(history)>=2 and sum(u['added_cuts'] for u in updates)>0, 'Recovery pilot did not add PSD cuts'
                        assert run['best_global_upper'] < task['stalled_global_upper']-1e-9, 'Recovery pilot did not improve the stalled bound'
                        rt.write_json(output/'stall-recovery-validation.json',dict(
                            status='passed',initialization='diagnostic checkpoint, not a fresh benchmark repetition',
                            checkpoint_sha256=rt.digest(Path(task['resume_checkpoint'])),
                            prior_stalled_global_upper=task['stalled_global_upper'],
                            best_global_upper=run['best_global_upper'],
                            completed_iterations=len(history),
                            actual_added_cuts=sum(u['added_cuts'] for u in updates),
                            duplicate_pricing_psd_fallbacks=run.get('duplicate_pricing_psd_fallbacks',0),
                            convergence_tolerances_unchanged=True))
                    if task.get('require_recycling_solves'):
                        history=[rt.json.loads(line) for line in (output/'history.jsonl').read_text().splitlines()]
                        recycled_solves=[row for row in history if row.get('lp_recycling_seconds',0)>0 and row['eligible_for_budget']]
                        assert len(recycled_solves)>=task['require_recycling_solves'], 'Full-memory pilot did not complete enough verified recycling/solve cycles'
                        rt.write_json(output/'recycling-pilot-validation.json',dict(status='passed',completed_recycling_solves=len(recycled_solves),required=task['require_recycling_solves']))
                    source=output/'best_dual.npz';assert source.exists(),'No globally evaluated candidate'
                    state['active']=task['id']+'/verification';publish()
                    if task['model']!='M6':
                        execute([sys.executable,'-X','utf8',str(rt.HERE/'validate_seven_candidate.py'),'--cache',str(base/'cache'),'--model',task['model'],'--source',str(source),'--output',str(output/'roundtrip/validation.json')],output/'roundtrip',seconds=1800)
                    exact(task['model'],source,output/'exact/final-svd','svd')
                    if run['status'] not in ['completed','time_limit']:
                        raise RuntimeError(f"Unresolved solver termination {run['status']}; certificate retained but numerical repair required")
                    if task['phase']!='pilot':
                        exact(task['model'],source,output/'exact/final-cuts','cuts')
                        for snap in sorted((output/'checkpoints').glob('*/dual.npz')):
                            exact(task['model'],snap,output/'exact'/f'{snap.parent.name}-svd','svd')
                task['status']='complete';record.update(status='complete',finished_epoch=time.time())
                state['completed']=[t['id'] for t in state['tasks'] if t['status']=='complete'];publish()
            except Exception as exc:
                traceback.print_exc()
                task.update(status='needs_repair',error=repr(exc));record.update(status='failed',error=repr(exc),finished_epoch=time.time());publish()
        pending=[t['id'] for t in state['tasks'] if t['status']!='complete']
        state.update(status='needs_repair' if pending else 'finished',active=None,pending=pending,ready_for_reporting=not pending,finished_epoch=time.time());publish()
    finally:
        if os.name=='nt':ctypes.windll.kernel32.SetThreadExecutionState(0x80000000)
        if lock.exists():lock.unlink()


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--campaign',type=Path,required=True)
    main(p.parse_args().campaign.resolve())
