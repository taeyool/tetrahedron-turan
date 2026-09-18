"""One user-authorized fresh replacement, with the original numerical settings."""
from __future__ import annotations
import argparse
import datetime as dt
import os
from pathlib import Path
import sys
import time

import runtime as rt
from run_overnight import environment, watch


def main(args):
    original = args.original.resolve()
    base = args.output.resolve()
    if base.exists() and any(base.iterdir()):
        raise FileExistsError('Replacement output must be fresh')
    base.mkdir(parents=True, exist_ok=True)
    deadline = dt.datetime.fromisoformat(args.deadline).timestamp()
    if time.time() + 4200 > deadline:
        raise ValueError('Reserve one hour plus verification before the deadline')
    original_manifest = rt.json.loads((original/'protocol/manifest.json').read_text(encoding='utf-8'))
    metadata = environment(base)
    # The replacement changes JSON persistence only, not numerical code/settings.
    numerical_sources = ['experiments/run_selected.py',
        'search/expand_seven_optimization.py', 'search/reconstruct_optimization.py',
        'search/five_root_oracle.py', 'search/five_root_oracle.cpp',
        'search/optimization_oracle.cpp', 'search/optimization_oracle_tail.inc']
    previous_hashes = {k.replace('\\','/'):v for k,v in original_manifest['source_sha256'].items()}
    for name in numerical_sources:
        assert rt.digest(rt.ROOT/name) == previous_hashes[name], name
    memory = original_manifest['memory_cap_bytes']
    run = base/'runs/M7-all5/rep-03'
    manifest = dict(original_campaign=str(original), model='M7-all5', repetition=3,
        initialization='fresh', method='LP-CUT-CG', search_seconds=3600,
        deadline_utc=args.deadline, authorized_replacement=True,
        replaced_attempt=str(original/'runs/M7-all5/rep-03'),
        numerical_sources_unchanged=True, source_sha256=metadata['source_sha256'],
        settings_note='Original numerical settings and cache; unique JSON temp files and bounded retry on Windows sharing errors.',
        original_manifest_sha256=rt.digest(original/'protocol/manifest.json'))
    rt.write_json(base/'protocol/manifest.json', manifest)
    state = dict(status='searching', pid=os.getpid(), started_epoch=time.time(),
        deadline_epoch=deadline, active=str(run), exact_checks=[])
    rt.write_json(base/'status.json', state)
    if os.name == 'nt':
        import ctypes
        ctypes.windll.kernel32.SetThreadExecutionState(0x80000001)
    try:
        command = [sys.executable,'-X','utf8',str(rt.HERE/'run_selected.py'),
            '--model','M7-all5','--cache',str(original/'cache'),'--output',str(run),
            '--seconds','3600','--rep','3']
        result = watch(command,run,deadline,memory,search_limit=3600)
        state['search_supervisor'] = result
        saved = rt.json.loads((run/'run.json').read_text(encoding='utf-8'))
        if result['status'] != 'completed' or saved['status'] not in ('time_limit','completed'):
            raise RuntimeError('Replacement search did not complete normally; do not promote it')
        jobs = [(run/'best_dual.npz',run/'exact'/f'final-{mode}',mode) for mode in ['svd','cuts']]
        jobs += [(run/'checkpoints'/f'{target:04d}'/'dual.npz',
                  run/'exact'/f'{target:04d}-svd','svd') for target in [1800,900,300,60,3600]]
        verified = {}
        for source, output, mode in jobs:
            if time.time() + 60 > deadline:
                raise TimeoutError('Deadline before all replacement verifications completed')
            key = (rt.digest(source), mode)
            if key in verified:
                rt.write_json(output/'reused-verification.json',dict(source_dual_sha256=key[0],
                    verified_artifact=str(verified[key]),factorization=mode,
                    note='Identical candidate and rounding policy; verification reused'))
                continue
            state.update(status='exact_verification',active=str(output))
            rt.write_json(base/'status.json',state)
            command = [sys.executable,'-X','utf8',str(rt.HERE/'runtime.py'),
                str(rt.RESEARCH/'exactify_five_root.py'),str(source),'--factorization',mode,
                '--svd-relative-tolerance','1e-7','--scale','2000000','--cross-check-pricing',
                '--threads','2','--cache',str(output/'cache'),'--output',str(output/'certificate.json')]
            result = watch(command,output,deadline-30,memory)
            state['exact_checks'].append(dict(path=str(output),status=result['status']))
            if result['status'] != 'completed':
                raise RuntimeError(f'Exact verification did not complete: {output}')
            cert = rt.json.loads((output/'certificate.json').read_text(encoding='utf-8'))
            assert cert['reconstruction']['source_dual_sha256'] == key[0]
            assert cert['exact_verification']['raw_count'] == 13051375
            assert cert['exact_verification']['independent_pricing_full_scan']['complete_raw_count'] == 13051375
            verified[key] = output/'certificate.json'
        state.update(status='finished',active=None,finished_epoch=time.time(),
                     replacement_run=str(run),ready_for_reporting=True)
    except Exception as exc:
        import traceback
        traceback.print_exc()
        state.update(status='failed',error=repr(exc),finished_epoch=time.time(),ready_for_reporting=False)
    finally:
        rt.write_json(base/'status.json',state)
        if os.name == 'nt':
            ctypes.windll.kernel32.SetThreadExecutionState(0x80000000)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--original',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--deadline',required=True)
    main(parser.parse_args())
