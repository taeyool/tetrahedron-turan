"""Durable, bounded production queue for validated remaining Section 6 arms."""
from __future__ import annotations
import argparse
import datetime as dt
import os
from pathlib import Path
import random
import sys
import time

import runtime as rt
from run_overnight import watch, environment
from pilot_remaining import ARMS


def exact_command(base,name,source,output,factorization,corruption=False):
    if name=='M6':
        command=[sys.executable,'-X','utf8',str(rt.HERE/'exactify_order6.py'),str(source),
            '--cache',str(base/'cache'),'--output',str(output/'certificate.json'),
            '--factorization',factorization]
        if corruption: command.append('--corruption-test')
        return command
    import numpy as np
    with np.load(source) as z:
        assert str(z['model'])=='M7-lift6' and len(z['dimensions'])==9
        for b,d in enumerate([7,236,191],9):
            assert z[f'factors{b}'].shape==(0,d) and not np.any(z[f'gram{b-9}'])
    return [sys.executable,'-X','utf8',str(rt.HERE/'runtime.py'),
        str(rt.RESEARCH/'exactify_reconstructed_dual.py'),str(source),
        '--factorization',factorization,'--svd-relative-tolerance','1e-7',
        '--scale','2000000','--threads','2','--cache',str(output/'cache'),
        '--output',str(output/'certificate.json')]


def main(base,deadline,label):
    path=base/'status.json'
    if path.exists():
        raise FileExistsError('Existing campaign state; inspect it rather than rerunning')
    state=dict(status='waiting_for_pilots',pid=os.getpid(),started_epoch=time.time(),
        deadline_epoch=deadline,active=label,completed_searches=[],exact_checks=[],
        completed_groups=[],deferred_groups=[],ready_for_reporting=False)
    rt.write_json(path,state)
    memory=40*1024**3
    if os.name=='nt':
        import ctypes
        ctypes.windll.kernel32.SetThreadExecutionState(0x80000001)
    verified={}

    def exact(name,source,output,factorization,corruption=False):
        if time.time()+30>=deadline:
            raise TimeoutError('Campaign deadline before exact verification')
        key=(rt.digest(source),factorization)
        if key in verified:
            rt.write_json(output/'reused-verification.json',dict(source_dual_sha256=key[0],
                factorization=factorization,verified_artifact=str(verified[key]),
                note='Identical candidate bytes and rounding policy; not an independent timing measurement'))
            return
        state.update(status='exact_verification',active=str(output.relative_to(base)))
        rt.write_json(path,state)
        result=watch(exact_command(base,name,source,output,factorization,corruption),
            output,deadline-15,memory)
        state['exact_checks'].append(dict(path=str(output.relative_to(base)),status=result['status']))
        rt.write_json(path,state)
        if result['returncode']!=0 or not (output/'certificate.json').exists():
            raise RuntimeError(f'Exact verification failed: {output}')
        verified[key]=output/'certificate.json'

    try:
        while True:
            pilot=rt.json.loads((base/f'{label}-status.json').read_text(encoding='utf-8'))
            if pilot['status']=='finished': break
            if pilot['status'] not in ['pilot','validating']:
                raise RuntimeError(f'Pilot gate failed: {pilot}')
            if time.time()>=deadline:
                raise TimeoutError('Campaign deadline during pilot')
            time.sleep(1)
        state.update(status='validating',active='pilot roundtrips'); rt.write_json(path,state)
        check=base/'validation/pilot-roundtrips'
        command=[sys.executable,'-X','utf8',str(rt.HERE/'validate_remaining_pilots.py'),
            '--campaign',str(base),'--label',label,'--output',str(base/'validation/pilot-gate.json')]
        result=watch(command,check,min(deadline,time.time()+600),memory)
        assert result['returncode']==0,'Pilot coefficient or interval consistency gate failed'
        for name,method in ARMS:
            source=base/label/name/method/'best_dual.npz'
            output=base/'validation/exact-pilots'/name/method
            exact(name,source,output,'svd',corruption=name=='M6' and method=='SDP-FULL')
        import math
        pilots=[rt.json.loads((base/label/name/method/'run.json').read_text(encoding='utf-8')) for name,method in ARMS]
        targets={name:math.ceil(min(p['best_global_upper'] for p in pilots if p['model']==name)*10000)/10000
                 for name in ['M6','M7-lift6']}
        # Admit complete groups of three. Randomized group order avoids choosing
        # the order after inspecting production results; no inter-arm warm starts.
        order=list(ARMS)
        random.Random(610).shuffle(order)
        metadata=environment(base)
        assert memory<=metadata['physical_ram_bytes']*.75
        gate=rt.json.loads((base/'validation/pilot-gate.json').read_text(encoding='utf-8'))
        manifest=dict(scope_models=['M6','M7-lift6','M7-no5','M7-all5'],
            excluded_models=['M7-three5'],repetitions=3,search_seconds=3600,
            eligible_production_groups=order,group_order_seed=610,
            order_policy='Randomize method groups before production; run three fresh repetitions consecutively so a group is admitted only when its full worst-case budget fits.',
            already_completed=['M7-no5/LP-CUT-CG','M7-all5/LP-CUT-CG'],
            pending_seven_vertex_comparisons=[f'{name}/{method}' for name in ['M7-no5','M7-all5']
                for method in ['SDP-FULL','LP-CUT','SDP-CG']],
            pending_reason='Full/native seven-vertex adapters are not validated in this bounded batch; no resource-failure or completion claim.',
            deadline_utc=dt.datetime.fromtimestamp(deadline,dt.timezone.utc).isoformat(),
            deadline_epoch=deadline,request_started_utc='2026-09-10T13:58:23+00:00',
            total_budget_includes_preparation=True,memory_cap_bytes=memory,
            initialization_limit_seconds=900,shutdown_grace_seconds=60,
            checkpoint_targets=rt.CHECKPOINTS,stationarity=True,
            factor_scale=2000000,primary_factorization='svd',svd_relative_tolerance=1e-7,
            final_uncompressed_rounding=True,predeclared_numerical_targets=targets,
            target_policy='Best pilot global value within each model rounded upward to 1e-4; shared across methods, with unachieved targets censored.',
            cache_policy='Warm copy of the previously validated components cache; independent permutation counting is timed separately. Cold original cache generation is not remeasured.',
            selected_pilot_set=label,native_backend='SCS',
            unresolved_native_pilot_tolerance=gate['unresolved_native_tolerance'],
            pilot_adjustments=['Clarabel trials retained separately: inaccurate convergence and a chordal-decomposition panic; SCS selected before production.',
                'Two interrupted SCS pilot preparations excluded; pilot-06 is the uncontended selected pilot set.',
                'Five seconds reserved inside native solve budgets for factor export and complete pricing.',
                'The 900-second initialization cap matches the previous overnight subset rather than the brief default of 3600 seconds.'],
            model_validation_sha256=rt.digest(base/'validation/models.json'),
            pilot_gate_sha256=rt.digest(base/'validation/pilot-gate.json'),
            source_sha256=rt.sources(),frozen_epoch=time.time())
        rt.write_json(base/'protocol/manifest.json',manifest)
        for name,method in order:
            exact_reserve=600 if name=='M6' else 2400
            required=3*(3600+900+60)+exact_reserve+60
            if time.time()+required>deadline:
                state['deferred_groups'].append(dict(model=name,method=method,
                    reason='Insufficient remaining time to admit three full repetitions and verification'))
                rt.write_json(path,state)
                continue
            group=[]
            for rep in [1,2,3]:
                output=base/'runs'/name/method/f'rep-{rep:02d}'
                state.update(status='searching',active=f'{name}/{method}/rep-{rep:02d}')
                rt.write_json(path,state)
                command=[sys.executable,'-X','utf8',str(rt.HERE/'run_remaining_method.py'),
                    '--model',name,'--method',method,'--cache',str(base/'cache'),
                    '--output',str(output),'--seconds','3600','--rep',str(rep)]
                result=watch(command,output,deadline-exact_reserve,memory,search_limit=3600)
                run=rt.json.loads((output/'run.json').read_text(encoding='utf-8'))
                if (method.startswith('SDP') and run['status']=='numerical_failure'
                        and run.get('search_seconds',0)>=3590
                        and 'reached time_limit_secs' in (output/'solver.log').read_text(encoding='utf-8')):
                    rt.shutil.copy2(output/'run.json',output/'run-before-classification.json')
                    run.update(status='time_limit',original_runner_status='numerical_failure',
                        termination_classification_note='The SCS log explicitly reports time_limit_secs at the search budget; the remaining seconds were reserved for complete pricing.')
                    rt.write_json(output/'run.json',run)
                state['completed_searches'].append(dict(model=name,method=method,rep=rep,
                    supervisor_status=result['status'],status=run['status'],path=str(output.relative_to(base))))
                rt.write_json(path,state)
                assert result['kernel_job_limit_enforced'],'Required kernel memory cap was not attached'
                assert result['returncode']==0 and run['status'] in ['completed','time_limit','numerical_failure'],(name,method,rep,result,run['status'])
                assert (output/'best_dual.npz').exists(),(name,method,rep,'no eligible candidate')
                group.append(output)
            for factorization in ['svd','cuts']:
                for output in group:
                    exact(name,output/'best_dual.npz',output/'exact'/f'final-{factorization}',factorization)
            for target in rt.CHECKPOINTS:
                for output in group:
                    source=output/'checkpoints'/f'{target:04d}'/'dual.npz'
                    if source.exists():
                        exact(name,source,output/'exact'/f'{target:04d}-svd','svd')
            state['completed_groups'].append(dict(model=name,method=method,repetitions=3))
            rt.write_json(path,state)
        state.update(status='finished',active=None,finished_epoch=time.time(),ready_for_reporting=True)
    except Exception as exc:
        import traceback
        traceback.print_exc()
        state.update(status='failed',error=repr(exc),finished_epoch=time.time(),ready_for_reporting=False)
    finally:
        rt.write_json(path,state)
        if os.name=='nt':
            ctypes.windll.kernel32.SetThreadExecutionState(0x80000000)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--campaign',type=Path,required=True)
    p.add_argument('--deadline',required=True)
    p.add_argument('--pilot-label',default='pilot-06')
    a=p.parse_args()
    main(a.campaign.resolve(),dt.datetime.fromisoformat(a.deadline).timestamp(),a.pilot_label)
