"""Instrumented fresh LP-CUT-CG search for the selected overnight models.

Reuses ExpandedMaster's coefficient, column-merging, dual and pruning code.
An external supervisor is required for hard initialization/time/memory limits.
"""
from __future__ import annotations
import argparse
from pathlib import Path
import time
from types import SimpleNamespace

import runtime as rt
import numpy as np
from scipy.linalg import eigh
import reconstruct_optimization as ro
from expand_seven_optimization import ExpandedMaster


def run(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    if (output / 'run.json').exists():
        raise FileExistsError('Refusing to overwrite any prior attempt')
    constructed = time.monotonic()
    record = dict(model=args.model, method='LP-CUT-CG', repetition=args.rep,
                  phase=args.phase, status='initializing', initialization='fresh',
                  search_budget_seconds=args.seconds, checkpoints=rt.CHECKPOINTS,
                  stationarity=True, source_sha256=rt.sources(), started_epoch=time.time())
    rt.write_json(output / 'run.json', record)
    oracle, blocks, objective, stat, metadata = rt.model(args.cache.resolve(), args.model)
    settings = SimpleNamespace(resume_checkpoint=None, warm_dual=None, warm_columns=None,
        screen_directions=None, seed_turan=True, seed_certificate=False, stationarity_face=False,
        save_dual_history=False, price_first=True, checkpoint=False, threads=2, price_top=8,
        max_cuts=80, keep_cuts=3000, psd_tolerance=1e-7, price_tolerance=1e-7,
        lp_solver='choose', max_iter=1000000, seconds=args.seconds, output_dir=output)
    master = ExpandedMaster(oracle, blocks, objective, stat, 'with', settings)
    record.update(ordered_blocks=metadata, five_root_types=oracle.type_masks,
        dimensions=list(ro.DIMS), raw_configuration_count=oracle.raw_count,
        effective_full_universe_count=None,
        effective_count_note='Only generated columns are merged by complete feature equality; no isomorphism-class count is asserted.',
        initial_columns=len(master.masks), initial_cuts=len(master.cuts),
        initial_columns_sha256=rt.hashlib.sha256(np.asarray(master.masks, '<u8').tobytes()).hexdigest(),
        construction_initialization_seconds=time.monotonic()-constructed,
        settings={k: str(v) if isinstance(v, Path) else v for k,v in vars(settings).items()},
        oracle_binary_sha256={p.name: rt.digest(p) for p in args.cache.glob('*.dylib')},
        lp_backend_version=master.h.version())
    # Solver log is retained separately from the iteration data.
    master.h.setOptionValue('output_flag', True)
    master.h.setOptionValue('log_to_console', False)
    master.h.setOptionValue('log_file', str(output / 'solver.log'))
    start = time.monotonic()
    record.update(status='running', search_started_epoch=time.time())
    rt.write_json(output / 'run.json', record)
    saved_targets = set()
    last = None
    status = 'time_limit'
    best_available = None
    history_path = output / 'history.jsonl'
    for iteration in range(1000000):
        remaining = args.seconds - (time.monotonic()-start)
        if remaining <= 0:
            break
        # HiGHS counts solver run time cumulatively; use the current runtime.
        master.h.setOptionValue('time_limit', master.h.getRunTime()+remaining)
        s = time.monotonic()
        master.h.run()
        solve_seconds = time.monotonic()-s
        backend = master.h.modelStatusToString(master.h.getModelStatus())
        record['backend_status'] = backend
        if master.h.getModelStatus() != master.highspy.HighsModelStatus.kOptimal:
            status = 'time_limit' if 'time' in backend.lower() else 'numerical_failure'
            break
        sol = master.h.getSolution()
        y, x, matrices = rt.moments(master, sol)
        s = time.monotonic()
        negative, minima = [], []
        for b, matrix in enumerate(matrices):
            vals, vec = eigh((matrix+matrix.T)/2,
                subset_by_index=(0, min(80, len(matrix))-1), driver='evr')
            minima.append(float(vals[0]))
            negative.extend((float(vals[j]), b, vec[:, j]) for j in np.flatnonzero(vals < -1e-7))
        negative.sort(key=lambda t:t[0])
        separation_seconds = time.monotonic()-s
        s = time.monotonic()
        six, grams, tau, weights = master.dual(sol)
        values, priced_masks = oracle.price(six, grams, threads=2, top=8)
        pricing_seconds = time.monotonic()-s
        evaluated = time.monotonic()-start
        upper = float(values.max())
        objective_value = master.h.getObjectiveValue()
        gap = upper-objective_value
        within_budget = evaluated <= args.seconds
        row = dict(iteration=iteration, seconds=evaluated, restricted_objective=objective_value,
            global_dual_upper=upper, pricing_gap=gap, tau=tau, lp_seconds=solve_seconds,
            eigen_seconds=separation_seconds, pricing_seconds=pricing_seconds,
            minimum_eigenvalue=min(minima), block_minimum_eigenvalues=minima,
            stationarity_residual=float(stat@x), normalization_residual=float(y.sum()-1),
            columns=len(master.masks), cuts=len(master.cuts), primal_support=int(np.count_nonzero(y > 1e-9)),
            eligible_for_budget=within_budget, backend_status=backend)
        # Late completed evaluations are logged, but cannot improve a budget checkpoint.
        if within_budget and upper < master.best_upper:
            master.best_upper = upper
            best_available = evaluated
            master.best_dual = dict(six=six, tau=tau, global_upper=upper,
                iteration=iteration, availability_seconds=evaluated, face_multipliers=np.array([]),
                **{f'gram{i}':q for i,q in enumerate(grams)}, **master.extra_metadata)
            for b,d in enumerate(ro.DIMS):
                master.best_dual[f'factors{b}'] = np.asarray([
                    np.sqrt(w)*v for w,(bb,v) in zip(weights,master.cuts) if bb == b and w > 0]).reshape(-1,d)
            ro.atomic_savez(output / 'best_dual.npz', **master.best_dual)
        row['best_global_upper'] = master.best_upper if np.isfinite(master.best_upper) else None
        # At target t, save the last candidate whose evaluation finished by t.
        # The previous iteration's best is retained in an immutable NPZ, so crossing
        # a target never backdates a newly completed global evaluation.
        for target in rt.CHECKPOINTS:
            if evaluated >= target and target not in saved_targets:
                snap = output / 'checkpoints' / f'{target:04d}'
                snap.mkdir(parents=True, exist_ok=True)
                previous = output / 'eligible_previous.npz'
                source = output / 'best_dual.npz' if evaluated == target and within_budget else previous
                if source.exists():
                    rt.shutil.copy2(source, snap / 'dual.npz')
                    with np.load(source) as z:
                        available = float(z['availability_seconds'])
                        assert available <= target
                        rt.write_json(snap / 'checkpoint.json', dict(target_seconds=target,
                            candidate_available_seconds=available, global_upper=float(z['global_upper']),
                            dual_sha256=rt.digest(snap / 'dual.npz')))
                else:
                    rt.write_json(snap / 'checkpoint.json', dict(target_seconds=target, status='no_completed_candidate'))
                saved_targets.add(target)
        if (output / 'best_dual.npz').exists():
            rt.shutil.copy2(output / 'best_dual.npz', output / 'eligible_previous.npz')
        master.history.append(row)
        with history_path.open('a', encoding='utf-8') as stream:
            stream.write(rt.json.dumps(row, allow_nan=False)+'\n')
        last = dict(masks=np.asarray(master.masks,np.uint64), weights=y,
                    **master.extra_metadata, **{f'moment{i}':m for i,m in enumerate(matrices)})
        ro.atomic_savez(output / 'last_primal.npz', **last)
        record.update(completed_iterations=iteration+1, best_global_upper=row['best_global_upper'],
                      best_candidate_available_seconds=best_available, last_iteration=row,
                      search_seconds=time.monotonic()-start)
        rt.write_json(output / 'run.json', record)
        print(rt.json.dumps({k:v for k,v in row.items() if k != 'block_minimum_eigenvalues'}), flush=True)
        if not negative and gap <= 1e-7:
            status = 'completed'
            break
        if not within_budget:
            break
        update_start = time.monotonic()
        added = master.add_columns(priced_masks[values > objective_value+1e-7])
        if iteration % 10 == 0:
            master.prune(sol)
        if gap <= 1e-7:
            master.add_cuts([(b,v) for _,b,v in negative[:80]])
        row['added_columns'] = added
        row['update_seconds'] = time.monotonic()-update_start
        with (output / 'updates.jsonl').open('a', encoding='utf-8') as stream:
            stream.write(rt.json.dumps(dict(iteration=iteration, added_columns=added,
                added_cuts=min(80,len(negative)) if gap <= 1e-7 else 0,
                retained_columns=len(master.masks), retained_cuts=len(master.cuts),
                update_seconds=row['update_seconds']))+'\n')
    # Carry an early-converged/last completed candidate forward, never an overshoot.
    for target in rt.CHECKPOINTS:
        if target <= args.seconds and target not in saved_targets:
            snap = output / 'checkpoints' / f'{target:04d}'
            snap.mkdir(parents=True, exist_ok=True)
            if master.best_dual is not None and best_available <= target:
                ro.atomic_savez(snap / 'dual.npz', **master.best_dual)
                rt.write_json(snap / 'checkpoint.json', dict(target_seconds=target,
                    candidate_available_seconds=best_available, global_upper=master.best_upper,
                    dual_sha256=rt.digest(snap / 'dual.npz'), early_termination=status))
    record.update(status=status, search_seconds=time.monotonic()-start,
        time_limit_overshoot_seconds=max(0,time.monotonic()-start-args.seconds), finished_epoch=time.time())
    rt.write_json(output / 'run.json', record)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--model', choices=['M7-no5','M7-all5'], required=True)
    parser.add_argument('--cache', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--seconds', type=float, default=3600)
    parser.add_argument('--rep', type=int, default=1)
    parser.add_argument('--phase', choices=['pilot','production'], default='production')
    args = parser.parse_args()
    try:
        run(args)
    except Exception as exc:
        import traceback
        traceback.print_exc()
        path = args.output / 'run.json'
        record = rt.json.loads(path.read_text(encoding='utf-8')) if path.exists() else {}
        record.update(status='implementation_failure', error=repr(exc))
        rt.write_json(path, record)
        raise
