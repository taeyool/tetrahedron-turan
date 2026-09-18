"""Instrumented complete seven-vertex algorithm comparison and long LP runs.

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
from seven_native import solve as native_solve
from lp_memory import prune_for_memory, ENTRY_LIMIT
from recycle_highs import recycle as recycle_lp
from no5_lp_memory import admit_cuts, NO5_ENTRY_LIMIT
from seven_full_streamed import install as install_full, moments as full_moments
from seven_full_native import solve as full_native_solve


def save_checkpoint(master,output,elapsed,args):
    vectors=np.zeros((len(master.cuts),max(ro.DIMS)))
    for i,(b,v) in enumerate(master.cuts):vectors[i,:len(v)]=v
    data=dict(masks=np.asarray(master.masks,np.uint64),blocks=np.asarray([b for b,v in master.cuts],np.int32),vectors=vectors,
        stationarity=True,stationarity_face=False,elapsed_search_seconds=elapsed,method=args.method,**master.extra_metadata)
    basis=master.h.getBasis()
    if basis.valid and args.method.startswith('LP'):
        data.update(basis_columns=np.asarray([int(v) for v in basis.col_status]),basis_rows=np.asarray([int(v) for v in basis.row_status]))
    ro.atomic_savez(output/'master_checkpoint.npz',**data)


def run(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    if (output / 'run.json').exists():
        raise FileExistsError('Refusing to overwrite any prior attempt')
    native=args.method.startswith('SDP')
    full=args.method in ('SDP-FULL','LP-CUT')
    recycle_enabled=args.model=='M7-no5' and args.method=='LP-CUT'
    entry_limit=NO5_ENTRY_LIMIT if recycle_enabled else ENTRY_LIMIT
    if args.seconds>3600:
        rt.CHECKPOINTS=[60,300,900,1800,3600,7200,14400,21600]
    constructed = time.monotonic()
    record = dict(model=args.model, method=args.method, repetition=args.rep,
                  phase=args.phase, status='initializing', initialization='fresh',
                  search_budget_seconds=args.seconds, checkpoints=rt.CHECKPOINTS,
                  stationarity=True, source_sha256=rt.sources(), started_epoch=time.time())
    rt.write_json(output / 'run.json', record)
    oracle, blocks, objective, stat, metadata = rt.model(args.cache.resolve(), args.model)
    resume = getattr(args, 'resume_checkpoint', None)
    if resume is not None:
        assert args.phase == 'pilot' and args.model == 'M7-all5' and args.method == 'LP-CUT-CG'
        resume = resume.resolve()
        record.update(initialization='diagnostic_checkpoint_pilot',
                      resume_checkpoint_sha256=rt.digest(resume))
    long_stall_policy = (args.model == 'M7-all5' and args.method == 'LP-CUT-CG'
                         and (args.phase == 'long' or resume is not None))
    if long_stall_policy:
        record['duplicate_pricing_psd_policy'] = ('Admit violated PSD cuts when no new column is added, '
            'even if the numerical global pricing gap exceeds tolerance; convergence tests are unchanged.')
        record['duplicate_pricing_psd_fallbacks'] = 0
    settings = SimpleNamespace(resume_checkpoint=resume, warm_dual=None, warm_columns=None,
        screen_directions=None, seed_turan=resume is None, seed_certificate=False, stationarity_face=False,
        save_dual_history=False, price_first=True, checkpoint=False, threads=2, price_top=8,
        max_cuts=80, keep_cuts=3000, psd_tolerance=1e-7, price_tolerance=1e-7,
        lp_solver='choose', max_iter=1000000, seconds=args.seconds, output_dir=output)
    master = ExpandedMaster(oracle, blocks, objective, stat, 'with', settings)
    if resume is not None:
        record['checkpoint_restored_basis'] = master.provenance.get('restored_basis', False)
    if full:
        record.update(install_full(master,args.cache.resolve(),args.model))
    record.update(ordered_blocks=metadata, five_root_types=oracle.type_masks,
        dimensions=list(ro.DIMS), raw_configuration_count=oracle.raw_count,
        effective_full_universe_count=len(master.masks) if full else None,
        effective_count_note='Full arms retain every canonical seven-vertex class; generated arms merge only equal complete features.',
        initial_columns=len(master.masks), initial_cuts=len(master.cuts),
        initial_columns_sha256=rt.hashlib.sha256(np.asarray(master.masks, '<u8').tobytes()).hexdigest(),
        construction_initialization_seconds=time.monotonic()-constructed,
        settings={k: str(v) if isinstance(v, Path) else v for k,v in vars(settings).items()},
        oracle_binary_sha256={p.name: rt.digest(p) for p in args.cache.glob('*.dylib')},
        lp_backend_version=master.h.version())
    if not native:
        record['lp_memory_pruning_policy'] = dict(dense_entry_admission_limit=entry_limit,
            keep_every_dual_active_cut=True, dual_active_tolerance=1e-10,
            fill_available_capacity_with_newest_inactive_cuts=True,
            same_guard_for_both_LP_methods=not recycle_enabled, no5_full_model_storage_override=recycle_enabled, full_configuration_universe_retained=True,
            ordinary_pruning_unchanged_below_memory_threshold=True)
    if recycle_enabled:
        record['lp_recycling_policy']='After memory-triggered cut deletion, export the full LP in bounded column chunks, release the old HiGHS instance, restore coefficients/bounds/costs with hash checks and the saved basis statuses. Internal scaling, factorization and edge weights restart; all overhead counts in search time.'
        record['lp_recycling_calls']=0
        record['lp_cut_admission_policy']='M7-no5 full LP: at most 300 million projected coefficients, keep every dual-active cut, admit the largest fitting prefix of up to 80 eigenvalue-ranked new cuts. Others retain their existing 500 million threshold.'
    if native:
        import scs,cvxpy
        record.update(native_backend='SCS',native_backend_version=scs.__version__,cvxpy_version=cvxpy.__version__,native_settings=dict(eps_abs=1e-8,eps_rel=1e-8,eps_infeas=1e-8,max_iters=20000000,use_indirect=True,inner_seconds=300,evaluation_reserve_seconds=150 if args.model=='M7-all5' else 30))
    if native:
        record['native_settings']['rho_x']=100.0 if full else 1e-6
    if native and full:
        record['native_full_conditioning_policy']='Pilot-frozen rho_x=100 for the full-native SCS pipeline; retained earlier full-native attempts used 1e-6 or 0.01, while the generated-SDP pipeline retains 1e-6. Mathematical constraints and feasibility targets unchanged.'
    if native and not full and args.model=='M7-all5':
        record['native_iteration_admission_policy']='After the first completed iteration, require remaining budget > 1.15 times the largest observed complete iteration + 30 seconds; retain unused time and time_limit status.'
    if native and full:
        from seven_full_native import directory as packed_directory
        packed_path=packed_directory(args.cache,args.model)/'manifest.json'
        packed_meta=rt.json.loads(packed_path.read_text())
        record['native_interface']='Private SCS 3.2.8 executable, GCC 13.2, existing OpenBLAS DLL; file-loaded owned CSC; same auxiliary-marginal SDP'
        record['native_packed_manifest_sha256']=rt.digest(packed_path)
        record['native_packed_matrix_bytes']=packed_meta['matrix_bytes']
        record['shared_cold_native_packed_construction_seconds']=packed_meta['construction_seconds']
        record['native_owned_build_manifest_sha256']=rt.digest(args.cache/'owned-scs-v4/manifest.json')
        record['native_full_deadline_policy']='Subtract input/setup; check admission after each projection using 1.15 times observed iteration cost plus one second; stock convergence schedule and targets retained'
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
    max_native_iteration_seconds=0.0
    recycle_pending=False
    max_recycling_seconds=0.0
    for iteration in range(1000000):
        remaining = args.seconds - (time.monotonic()-start)
        if remaining <= 0:
            break
        # SCS can enforce its wall limit only after an expensive batch of PSD
        # projections. Do not begin another all5 restricted solve when the
        # observed iteration cost would consume the final checkpoint reserve.
        if (native and not full and args.model=='M7-all5'
                and max_native_iteration_seconds>0
                and remaining<=1.15*max_native_iteration_seconds+30):
            record['stopping_reason']='Insufficient remaining budget for another observed-cost native iteration and final checkpoint'
            record['native_iteration_admission_reserve_seconds']=1.15*max_native_iteration_seconds+30
            record['unused_search_budget_seconds']=remaining
            break
        iteration_started=time.monotonic()
        recycling_seconds=0.0
        if recycle_enabled and recycle_pending:
            reserve=max(120.,1.15*max_recycling_seconds+30.)
            if remaining<=reserve:
                record['stopping_reason']='Insufficient remaining time for checked solver recycling'
                record['unused_search_budget_seconds']=remaining
                break
            sol=None  # Release any binding that could retain the previous solver.
            recycled=recycle_lp(master,output/'lp-recycling'/f'iteration-{iteration:06d}',start+args.seconds)
            recycling_seconds=recycled['seconds']
            max_recycling_seconds=max(max_recycling_seconds,recycling_seconds)
            record['lp_recycling_calls']+=1
            with (output/'lp-recycling.jsonl').open('a',encoding='utf-8') as stream:
                stream.write(rt.json.dumps(dict(iteration=iteration,**recycled))+'\n')
            if not recycled['applied']:
                record['stopping_reason']='Snapshot completed, but insufficient time remained for verified import'
                record['unused_search_budget_seconds']=max(0,args.seconds-(time.monotonic()-start))
                break
            recycle_pending=False
            remaining=args.seconds-(time.monotonic()-start)
            if remaining<=0:
                break
        # HiGHS counts solver run time cumulatively; use the current runtime.
        master.h.setOptionValue('time_limit', master.h.getRunTime()+remaining)
        s = time.monotonic()
        diagnostics={'lp_recycling_seconds':recycling_seconds}
        if native:
            solved=(full_native_solve if full else native_solve)(master,remaining,output,full=full)
            backend=solved['backend_status'];record['backend_status']=backend
            if not solved['success']:
                status='time_limit' if backend=='insufficient_time_for_export_and_pricing' else 'numerical_failure'
                break
            solve_seconds=solved['solve_seconds'];sol=SimpleNamespace(col_value=solved['y'])
            diagnostics={k:solved[k] for k in ['psd_repairs','assembly_seconds','backend_solve_seconds','backend_iterations','marginal_equality_residual']}
            if full:
                diagnostics.update(backend_raw_status=solved['backend_raw_status'],backend_time_limit_reached=solved['backend_time_limit_reached'])
        else:
            master.h.run()
            solve_seconds = time.monotonic()-s
            backend = master.h.modelStatusToString(master.h.getModelStatus())
            record['backend_status'] = backend
            if master.h.getModelStatus() != master.highspy.HighsModelStatus.kOptimal:
                status = 'time_limit' if 'time' in backend.lower() else 'numerical_failure'
                break
            sol = master.h.getSolution()
        y, x, matrices = (full_moments if full else rt.moments)(master, sol)
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
        if native:
            six,grams,tau=solved['six'],solved['grams'],solved['tau']
            factors=solved['factors']
        else:
            six, grams, tau, weights = master.dual(sol)
        values, priced_masks = oracle.price(six, grams, threads=2, top=8)
        pricing_seconds = time.monotonic()-s
        evaluated = time.monotonic()-start
        upper = float(values.max())
        objective_value = solved['objective'] if native else master.h.getObjectiveValue()
        gap = upper-objective_value
        within_budget = evaluated <= args.seconds
        row = dict(iteration=iteration, seconds=evaluated, restricted_objective=objective_value,
            global_dual_upper=upper, pricing_gap=gap, tau=tau, lp_seconds=0 if native else solve_seconds,
            native_seconds=solve_seconds if native else 0,
            eigen_seconds=separation_seconds, pricing_seconds=pricing_seconds,
            minimum_eigenvalue=min(minima), block_minimum_eigenvalues=minima,
            stationarity_residual=float(stat@x), normalization_residual=float(y.sum()-1),
            columns=len(master.masks), cuts=len(master.cuts), primal_support=int(np.count_nonzero(y > 1e-9)),
            eligible_for_budget=within_budget, backend_status=backend,**diagnostics)
        # Late completed evaluations are logged, but cannot improve a budget checkpoint.
        if within_budget and upper < master.best_upper:
            master.best_upper = upper
            best_available = evaluated
            master.best_dual = dict(six=six, tau=tau, global_upper=upper,
                iteration=iteration, availability_seconds=evaluated, face_multipliers=np.array([]),
                **{f'gram{i}':q for i,q in enumerate(grams)}, **master.extra_metadata)
            for b,d in enumerate(ro.DIMS):
                master.best_dual[f'factors{b}'] = factors[b] if native else np.asarray([
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
        if not negative and gap <= 1e-7 and abs(stat@x)<=1e-7 and abs(y.sum()-1)<=1e-7 and y.min()>=-1e-7:
            status = 'completed'
            break
        if not within_budget:
            break
        update_start = time.monotonic()
        added = 0 if full else master.add_columns(priced_masks[values > objective_value+1e-7])
        duplicate_pricing_fallback = bool(long_stall_policy and added == 0
                                          and gap > 1e-7 and negative)
        if duplicate_pricing_fallback:
            record['duplicate_pricing_psd_fallbacks'] += 1
        admit_psd_cuts = not native and (gap <= 1e-7 or duplicate_pricing_fallback)
        selected_cuts = [(b,v) for _,b,v in negative[:80]] if admit_psd_cuts else []
        cut_admission = None
        if recycle_enabled:
            cut_admission = admit_cuts(master, sol, len(selected_cuts), entry_limit)
            selected_cuts = selected_cuts[:cut_admission['admitted']]
        memory_pruning = dict(triggered=False)
        if not native:
            memory_pruning = prune_for_memory(master, sol, len(selected_cuts), entry_limit=entry_limit)
            if recycle_enabled and memory_pruning.get('cuts_removed',0)>0:
                recycle_pending=True
            if not memory_pruning['triggered'] and iteration % 10 == 0:
                master.prune(sol)
        cut_count_before = len(master.cuts)
        if selected_cuts:
            master.add_cuts(selected_cuts)
        actual_added_cuts = len(master.cuts) - cut_count_before
        row['added_columns'] = added
        row['update_seconds'] = time.monotonic()-update_start
        with (output / 'updates.jsonl').open('a', encoding='utf-8') as stream:
            stream.write(rt.json.dumps(dict(iteration=iteration, added_columns=added,
                added_cuts=actual_added_cuts,
                duplicate_pricing_psd_fallback=duplicate_pricing_fallback,
                memory_pruning=memory_pruning, cut_admission=cut_admission,
                retained_columns=len(master.masks), retained_cuts=len(master.cuts),
                update_seconds=row['update_seconds']))+'\n')
        if iteration % 5 == 0:
            save_checkpoint(master,output,time.monotonic()-start,args)
        max_native_iteration_seconds=max(max_native_iteration_seconds,time.monotonic()-iteration_started)
        if native and full:
            status='time_limit' if solved['backend_time_limit_reached'] else 'numerical_failure'
            break
    save_checkpoint(master,output,time.monotonic()-start,args)
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
    parser.add_argument('--method',choices=['SDP-FULL','LP-CUT','SDP-CG','LP-CUT-CG'],required=True)
    parser.add_argument('--model', choices=['M7-no5','M7-all5'], required=True)
    parser.add_argument('--cache', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--seconds', type=float, default=3600)
    parser.add_argument('--resume-checkpoint', type=Path,
                        help='Diagnostic all5 LP-CUT-CG pilot only; main and long trials remain fresh')
    parser.add_argument('--rep', type=int, default=1)
    parser.add_argument('--phase', choices=['pilot','production','long'], default='production')
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
