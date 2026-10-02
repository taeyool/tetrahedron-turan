"""Resumable LP-CUT-CG search on the native 32-block model, run until numerical convergence.

There is no wall-time deadline and no production iteration limit. The worker
stops only on (a) a fresh final audit passing every convergence test, (b) a
user stop request (RUN_DIR/STOP), or (c) a diagnosed failure. An external
supervisor (supervise_unlimited32.py) owns memory limits, hang detection,
restarts from the newest valid checkpoint and exact verification.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
import time
import traceback

import runtime as rt
import numpy as np
from scipy.linalg import eigh
import reconstruct_optimization as ro
import model32
from lp_memory import prune_for_memory, ENTRY_LIMIT

TOLERANCE = 1e-7
BASELINE = rt.ROOT / 'certificate' / 'legacy' / 'K4_turan_order7_six_hour_certificate.json'
BASELINE_SHA256 = 'c3b0e0b9364f669763bdb8fd1e3914bcd55acdee17fe7a5adbbb2e92da22beb4'
BASELINE_FRACTION = '312372062889819/560000000000000'
BASELINE_MAXIMIZER = 4840262484
EXIT_CONVERGED, EXIT_FAILURE, EXIT_INTERRUPTED, EXIT_NUMERICAL, EXIT_SMOKE = 0, 1, 3, 4, 0


class StopRequested(Exception):
    pass


def sha(path):
    return rt.digest(path)


# ----------------------------------------------------------------- state files

def save_native_dual(path, model, tau, factors, **scalars):
    assert len(factors) == 32 and all(f.shape[1] == d for f, d in zip(factors, model.dims))
    ro.atomic_savez(path, **model.identity(), tau=float(tau), stationarity=True, stationarity_face=False,
                    **{f'factors{b}': f for b, f in enumerate(factors)}, **scalars)


def load_native_dual(path, model):
    with np.load(path, allow_pickle=False) as data:
        model.check_identity(data)
        assert bool(data['stationarity']) and not bool(data['stationarity_face'])
        factors = [np.asarray(data[f'factors{b}'], float).reshape(-1, d) for b, d in enumerate(model.dims)]
        assert {k for k in data.files if k.startswith('factors')} == {f'factors{b}' for b in range(32)}
        scalars = {k: data[k].item() for k in data.files if data[k].ndim == 0 and not k.startswith('model')}
    return float(scalars['tau']), factors, scalars


def checkpoint_files(state):
    return sorted(state.glob('checkpoint-*.npz'))


def save_checkpoint(master, state, counters, settings, keep_generations=3):
    state.mkdir(parents=True, exist_ok=True)
    model = master.model
    vectors = np.zeros((len(master.cuts), max(model.dims)))
    for i, (b, v) in enumerate(master.cuts):
        vectors[i, :len(v)] = v
    data = dict(model.identity(), masks=np.asarray(master.masks, np.uint64),
                cut_blocks=np.asarray([b for b, _ in master.cuts], np.int32), cut_vectors=vectors,
                stationarity=True, stationarity_face=False, counters=np.asarray(json.dumps(counters)),
                settings=np.asarray(json.dumps(settings)))
    basis = master.h.getBasis()
    if basis.valid and len(basis.col_status) == len(master.masks) and len(basis.row_status) == master.neq+len(master.cuts):
        data.update(basis_columns=np.asarray([int(v) for v in basis.col_status], np.int8),
                    basis_rows=np.asarray([int(v) for v in basis.row_status], np.int8))
    path = state / f"checkpoint-{counters['completed_iterations']:08d}.npz"
    ro.atomic_savez(path, **data)
    digest = sha(path)
    rt.write_json(state / 'latest.json', dict(path=path.name, sha256=digest, completed_iterations=counters['completed_iterations'],
                                               saved_epoch=time.time(), columns=len(master.masks), directions=len(master.cuts)))
    rt.write_json(path.with_suffix('.json'), dict(sha256=digest, counters=counters))
    for old in checkpoint_files(state)[:-keep_generations]:
        old.unlink()
        old.with_suffix('.json').unlink(missing_ok=True)
    return path


def newest_valid_checkpoint(state, model):
    """Newest checkpoint whose recorded hash, identity and arrays are intact."""
    rejected = []
    for path in reversed(checkpoint_files(state)):
        try:
            sidecar = json.loads(path.with_suffix('.json').read_text(encoding='utf-8'))
            if sha(path) != sidecar['sha256']:
                raise ValueError('sha256 mismatch')
            with np.load(path, allow_pickle=False) as data:
                model.check_identity(data)
                assert len(data['cut_blocks']) == len(data['cut_vectors']) and len(data['masks'])
            return path, rejected
        except Exception as exc:  # a torn or corrupt generation falls back to the previous one
            rejected.append(dict(path=path.name, error=repr(exc)))
    return None, rejected


def restore_checkpoint(master, path):
    model = master.model
    with np.load(path, allow_pickle=False) as data:
        model.check_identity(data)
        assert bool(data['stationarity']) and not bool(data['stationarity_face'])
        masks = data['masks']
        blocks = data['cut_blocks'].astype(int)
        assert blocks.min(initial=0) >= 0 and blocks.max(initial=0) < 32
        cuts = [(int(b), v[:model.dims[int(b)]].copy()) for b, v in zip(blocks, data['cut_vectors'])]
        counters = json.loads(str(data['counters']))
        basis = (data['basis_columns'].astype(int), data['basis_rows'].astype(int)) if 'basis_columns' in data else None
    master.add_columns(masks, preserve_order=True)
    master.add_cuts(cuts)
    restored = False
    # The basis is reused only when row/column identities and ordering are exactly those saved.
    if (basis is not None and np.array_equal(masks, np.asarray(master.masks, np.uint64))
            and len(basis[0]) == master.h.getNumCol() and len(basis[1]) == master.h.getNumRow()
            and len(cuts) == len(master.cuts)):
        restored = set_basis(master, *basis)
    return counters, restored


def set_basis(master, columns, rows):
    basis = master.highspy.HighsBasis()
    basis.col_status = [master.highspy.HighsBasisStatus(int(v)) for v in columns]
    basis.row_status = [master.highspy.HighsBasisStatus(int(v)) for v in rows]
    return master.h.setBasis(basis) == master.highspy.HighsStatus.kOk


# ------------------------------------------------------------- initialization

def unit_directions(model, factors):
    out = []
    for b, rows in enumerate(factors):
        for v in rows:
            norm = np.linalg.norm(v)
            if norm:
                out.append((b, v/norm))
    return out


def add_missing_directions(master, directions):
    """Add directions not already represented (up to sign) in the same block."""
    present = {}
    for b, v in master.cuts:
        present.setdefault(b, []).append(v)
    present = {b: np.array(vs) for b, vs in present.items()}
    fresh = []
    for b, v in directions:
        if b in present and np.max(np.abs(present[b] @ v)) > 1-1e-12:
            continue
        fresh.append((b, v))
    master.add_cuts(fresh)
    return len(fresh), len(directions)-len(fresh)


def migrate_legacy_dual(model, path):
    """35-slot numerical dual -> native factors. Returns None if excluded blocks are nonzero."""
    with np.load(path, allow_pickle=False) as data:
        assert list(map(int, data['dimensions'])) == model32.LEGACY_DIMS + model32.FIVE_DIMS
        np.testing.assert_array_equal(data['five_root_type_masks'], model.oracle.type_masks)
        assert not np.any(data['face_multipliers'])
        excluded_rows = {old: int(np.count_nonzero(np.abs(data[f'factors{old}']).sum(axis=1))) if data[f'factors{old}'].size else 0
                         for old in model32.EXCLUDED_LEGACY}
        factors = [np.asarray(data[f'factors{old}'], float).reshape(-1, d)
                   for old, d in zip(model32.LEGACY_INDICES, model.dims)]
        info = dict(tau=float(data['tau']), claimed_upper=float(data['global_upper']), excluded_nonzero_rows=excluded_rows)
    return (None if any(excluded_rows.values()) else factors), info


def initialize_from_legacy(master, args, record):
    model = master.model
    checkpoint, best = args.legacy_checkpoint.resolve(), args.legacy_best_dual.resolve()
    provenance = dict(kind='continuation_with_block_model_migration', legacy_checkpoint=str(checkpoint),
                      legacy_checkpoint_sha256=sha(checkpoint), legacy_best_dual=str(best), legacy_best_dual_sha256=sha(best))
    with np.load(checkpoint, allow_pickle=False) as data:
        assert bool(data['stationarity']) and not bool(data['stationarity_face'])
        assert list(map(int, data['dimensions'])) == model32.LEGACY_DIMS + model32.FIVE_DIMS
        np.testing.assert_array_equal(data['five_root_type_masks'], model.oracle.type_masks)
        masks, blocks, vectors = data['masks'], data['blocks'].astype(int), data['vectors']
        legacy_dims = list(map(int, data['dimensions']))
        basis = (data['basis_columns'].astype(int), data['basis_rows'].astype(int)) if 'basis_columns' in data else None
    excluded = np.isin(blocks, model32.EXCLUDED_LEGACY)
    provenance.update(legacy_masks=len(masks), legacy_directions=len(blocks), legacy_directions_in_excluded_blocks=int(excluded.sum()),
                      legacy_direction_counts=np.bincount(blocks, minlength=35).tolist())
    cuts = [(model32.LEGACY_TO_NEW[int(b)], v[:legacy_dims[int(b)]].copy())
            for b, v, drop in zip(blocks, vectors, excluded) if not drop]
    master.add_columns(masks, preserve_order=True)
    master.add_cuts(cuts)
    restored = False
    if (basis is not None and not excluded.any() and np.array_equal(masks, np.asarray(master.masks, np.uint64))
            and len(basis[0]) == master.h.getNumCol() and len(basis[1]) == master.h.getNumRow()):
        # No row was dropped, so the legacy LP has identical row/column identities and order.
        restored = set_basis(master, *basis)
    provenance['legacy_basis_restored_after_exact_identity_check'] = restored
    factors, info = migrate_legacy_dual(model, best)
    provenance['legacy_best_dual'] = info
    inherited = None
    if factors is not None:
        added, skipped = add_missing_directions(master, unit_directions(model, factors))
        provenance.update(best_dual_directions_added=added, best_dual_directions_already_present=skipped)
        # The inherited value is never trusted: recompute the complete coefficient maximum.
        values, priced = model.evaluate(info['tau'], factors, args.scan_threads, args.price_top)
        upper = float(values.max())
        provenance['inherited_repriced_upper'] = upper
        provenance['inherited_repriced_minus_claimed'] = upper-info['claimed_upper']
        inherited = dict(tau=info['tau'], factors=factors, upper=upper)
        provenance['inherited_maximizer'] = int(priced[int(np.argmax(values))])
    else:
        provenance['inherited_best_dual_rejected'] = 'nonzero excluded blocks; baseline certificate remains the incumbent'
    record['initialization'] = provenance
    return inherited


def baseline_native(model):
    """The pinned exact certificate as native float factors (a/M) and tau."""
    assert sha(BASELINE) == BASELINE_SHA256, 'baseline certificate bytes changed'
    cert = json.loads(BASELINE.read_text(encoding='utf-8'))
    assert cert['bound_fraction'] == BASELINE_FRACTION
    for old in model32.EXCLUDED_LEGACY:
        assert cert['order6_factors_by_block'][old] == [], 'excluded block is nonzero in the baseline'
    scale = cert['scale']
    seven = dict(zip((9, 10, 11), ('order7_s1_factors', 'order7_s3_nonedge_factors', 'order7_s3_edge_factors')))
    five = {b['type_mask']: b for b in cert['order7_s5_blocks']}
    factors = []
    for m in model.meta:
        old = m['legacy_index']
        if old < 9:
            source = cert['order6_blocks'][old]
            assert (source['s'], source['l'], source['sigma'], source['flags']) == (m['s'], m['l'], m['sigma'], m['flags'])
            rows = cert['order6_factors_by_block'][old]
        elif old < 12:
            rows = cert[seven[old]]  # ordered bases are those of fs.flags_for_type, as in the verifier
        else:
            block = five[m['sigma']]
            assert block['flags'] == m['flags'] and block['dimension'] == m['dimension']
            rows = block['factors']
        factors.append(np.asarray(rows, float).reshape(-1, m['dimension'])/scale)
    tau = cert['stationarity']['tau_numerator']/cert['stationarity']['tau_denominator']
    return tau, factors, cert


def initialize_from_baseline(master, args, record):
    model = master.model
    tau, factors, cert = baseline_native(model)
    master.add_columns(ro.turan_blowup_masks(7))
    master.add_columns([BASELINE_MAXIMIZER, int(cert['example_maximizing_raw_mask'])])
    if args.warm_masks is not None:
        with np.load(args.warm_masks, allow_pickle=False) as data:
            master.add_columns(data['masks'])
    added, skipped = add_missing_directions(master, unit_directions(model, factors))
    values, priced = model.evaluate(tau, factors, args.scan_threads, args.price_top)
    upper = float(values.max())
    master.add_columns(priced[values >= upper-1e-9])
    record['initialization'] = dict(kind='seed_from_committed_exact_certificate', baseline_sha256=BASELINE_SHA256,
        seeded_directions=added, duplicate_directions=skipped, baseline_float_repriced_upper=upper,
        baseline_fraction=BASELINE_FRACTION, warm_masks=str(args.warm_masks) if args.warm_masks else None)
    return dict(tau=tau, factors=factors, upper=upper)


# ------------------------------------------------------------------ iteration

def solve_lp(master, log):
    """Require a successful solve. Recoverable ladder: clear solver state, then rebuild."""
    hp = master.highspy
    attempts = []
    for step in ('warm', 'clear_solver', 'rebuild'):
        if step == 'clear_solver':
            master.h.clearSolver()
        elif step == 'rebuild':
            options = {k: master.h.getOptionValue(k)[1] for k in ('log_file', 'output_flag', 'log_to_console')}
            master.h = master.rebuild_solver()
            for k, v in options.items():
                master.h.setOptionValue(k, v)
        started = time.monotonic()
        master.h.run()
        status = master.h.getModelStatus()
        name = master.h.modelStatusToString(status)
        attempts.append(dict(step=step, status=name, seconds=time.monotonic()-started))
        if status == hp.HighsModelStatus.kOptimal:
            sol = master.h.getSolution()
            if np.isfinite(sol.col_value).all() and np.isfinite(sol.row_dual).all():
                log['lp_attempts'] = attempts
                return sol, name
            attempts[-1]['status'] = 'nonfinite_solution'
    log['lp_attempts'] = attempts
    raise model32.NumericalDiagnostic(f'LP solve failed after recovery ladder: {attempts}')


def evaluate(master, args, audit=False):
    """One complete evaluation: LP, all 32 eigenproblems, dual, full-universe scan."""
    model = master.model
    out = dict(audit=audit)
    started = time.monotonic()
    sol, backend = solve_lp(master, out)
    out['lp_seconds'] = time.monotonic()-started
    info = master.h.getInfo()
    y = np.asarray(sol.col_value, float)
    x, matrices = master.moments(y)
    started = time.monotonic()
    negative, minima = [], []
    for b, matrix in enumerate(matrices):
        sym = (matrix+matrix.T)/2
        if audit:  # independent full spectrum
            vals, vec = np.linalg.eigh(sym)
        else:
            vals, vec = eigh(sym, subset_by_index=(0, min(args.max_cuts, len(sym))-1), driver='evr')
        minima.append(float(vals[0]))
        negative.extend((float(vals[j]), b, vec[:, j].copy()) for j in np.flatnonzero(vals < -TOLERANCE)[:args.max_cuts])
    negative.sort(key=lambda t: t[0])
    out['eigen_seconds'] = time.monotonic()-started
    started = time.monotonic()
    six, grams, tau, multipliers, factors = master.dual(sol)
    values, priced = model.oracle.price(six, grams, threads=args.scan_threads, top=args.price_top)
    out['pricing_seconds'] = time.monotonic()-started
    cost = np.asarray(master.deck @ model.objective)
    B = float(master.h.getObjectiveValue())
    L = float(cost @ y)
    U = float(values.max())
    # Certificate-side coefficients of the retained graphs (same tau and Grams as the scan).
    retained = np.asarray(master.deck @ six + master.feat @ np.concatenate([q.ravel() for q in grams]))
    row_activity = None
    if audit and master.cuts:
        row_activity = float((master.coefficients(master.deck, master.feat, master.cuts, master.sixcuts).T @ y).min())
    raw_multipliers = -np.asarray(sol.row_dual[master.neq:])
    out.update(backend_status=backend, restricted_objective=B, primal_objective_L=L, global_dual_upper=U,
        pricing_gap=U-B, gap_U_minus_L=U-L, B_minus_L=B-L, tau=tau,
        minimum_eigenvalue=min(minima), block_minimum_eigenvalues=minima,
        normalization_residual=float(y.sum()-1), stationarity_residual=float(model.stationarity @ x),
        minimum_y=float(y.min()), primal_support=int(np.count_nonzero(y > 1e-9)),
        minimum_cut_multiplier=float(raw_multipliers.min(initial=0)),
        active_directions=int(np.count_nonzero(multipliers > 1e-10)),
        retained_maximum_minus_B=float(retained.max()-B), U_minus_retained_maximum=float(U-retained.max()),
        minimum_cut_row_activity=row_activity,
        highs_max_primal_infeasibility=float(info.max_primal_infeasibility),
        highs_max_dual_infeasibility=float(info.max_dual_infeasibility),
        simplex_iterations=int(info.simplex_iteration_count),
        columns=len(master.masks), directions=len(master.cuts), direction_counts=master.direction_counts())
    finite = all(np.isfinite(v) for v in (B, L, U, tau, *minima)) and np.isfinite(y).all()
    tests = dict(lp_succeeded_and_finite=bool(finite), complete_scan_finished=bool(np.isfinite(values).all() and len(values) == 964*args.price_top),
        gap=abs(U-L) <= TOLERANCE, psd=min(minima) >= -TOLERANCE, normalization=abs(y.sum()-1) <= TOLERANCE,
        stationarity=abs(float(model.stationarity @ x)) <= TOLERANCE, nonnegative_y=y.min() >= -TOLERANCE)
    if audit:
        tests.update(certificate_weights_nonnegative=raw_multipliers.min(initial=0) >= -TOLERANCE,
            B_consistent_with_L=abs(B-L) <= TOLERANCE, retained_graphs_within_B=retained.max()-B <= TOLERANCE,
            cut_rows_feasible=row_activity is None or row_activity >= -TOLERANCE)
    out['convergence_tests'] = {k: bool(v) for k, v in tests.items()}
    out['converged'] = all(tests.values())
    out['materially_negative_gap'] = bool(U-L < -TOLERANCE)
    return out, dict(sol=sol, y=y, negative=negative, values=values, priced=priced, tau=tau, factors=factors)


def public(row):
    return {k: v for k, v in row.items() if k not in ('block_minimum_eigenvalues', 'direction_counts', 'lp_attempts')}


def run(args):
    run_dir = args.run_dir.resolve()
    attempt = args.attempt_dir.resolve()
    attempt.mkdir(parents=True, exist_ok=True)
    if (attempt / 'run.json').exists():
        raise FileExistsError('Refusing to overwrite a preserved attempt')
    state, incumbent = run_dir / 'state', run_dir / 'incumbent'
    incumbent.mkdir(parents=True, exist_ok=True)
    unlimited = args.mode == 'until_converged'
    assert unlimited or args.max_iterations is not None, 'only the bounded smoke mode takes an iteration limit'
    assert not (unlimited and args.max_iterations is not None), 'production has no iteration limit'
    settings = dict(mode=args.mode, time_limit_seconds=None, iteration_limit=None if unlimited else args.max_iterations,
        policy='LP-CUT-CG with duplicate-candidate PSD fallback', price_top=args.price_top, max_cuts=args.max_cuts,
        keep_cuts=args.keep_cuts, psd_tolerance=TOLERANCE, price_tolerance=TOLERANCE, convergence_tolerance=TOLERANCE,
        lp_feasibility_tolerance=args.lp_tolerance, lp_small_matrix_value=args.small_matrix_value,
        lp_solver=args.lp_solver, lp_threads=1, blas_threads=1, max_price_top=args.max_price_top,
        scan_threads=args.scan_threads, checkpoint_every_iterations=args.checkpoint_every,
        dense_entry_admission_limit=ENTRY_LIMIT, stationarity=True, stationarity_face=False)
    record = dict(model=model32.MODEL_ID, method='LP-CUT-CG', status='initializing', settings=settings,
                  pid=os.getpid(), started_epoch=time.time(), source_sha256=rt.sources(), argv=sys.argv,
                  process_power_throttling=model32.full_speed_process())
    rt.write_json(attempt / 'run.json', record)

    def heartbeat(stage, check_stop=True, **extra):
        rt.write_json(attempt / 'heartbeat.json', dict(stage=stage, epoch=time.time(), pid=os.getpid(), **extra))
        if check_stop and (run_dir / 'STOP').exists():
            raise StopRequested

    constructed = time.monotonic()
    model = model32.Model32(args.cache.resolve())
    model.check()
    rt.write_json(attempt / 'model_manifest.json', model.manifest())
    master = model32.Master32(model, keep_cuts=args.keep_cuts, lp_solver=args.lp_solver, feasibility_tolerance=args.lp_tolerance,
                              small_matrix_value=args.small_matrix_value)
    master.h.setOptionValue('output_flag', True)
    master.h.setOptionValue('log_to_console', False)
    master.h.setOptionValue('log_file', str(attempt / 'solver.log'))
    counters = dict(completed_iterations=0, elapsed_search_seconds=0.0, duplicate_pricing_psd_fallbacks=0,
                    attempts=0, audits_failed=0, prunes=0, pruned_directions=0)
    best_upper, best_path = float('inf'), incumbent / 'best_numerical.npz'
    inherited = None
    heartbeat('initializing', check_stop=False)
    if args.init == 'resume':
        path, rejected = newest_valid_checkpoint(state, model)
        if path is None:
            raise FileNotFoundError(f'no valid native checkpoint in {state}: {rejected}')
        counters, restored = restore_checkpoint(master, path)
        record['initialization'] = dict(kind='native_checkpoint_resume', checkpoint=str(path), checkpoint_sha256=sha(path),
                                        rejected_newer_checkpoints=rejected, basis_restored_after_exact_identity_check=restored)
    elif args.init == 'legacy-checkpoint':
        assert not checkpoint_files(state), 'native checkpoints exist; resume instead of migrating again'
        inherited = initialize_from_legacy(master, args, record)
    else:
        assert not checkpoint_files(state), 'native checkpoints exist; resume instead of reseeding'
        inherited = initialize_from_baseline(master, args, record)
    model.check()
    assert all(0 <= b < 32 and model.meta[b]['legacy_index'] not in model32.EXCLUDED_LEGACY for b, _ in master.cuts)
    if best_path.exists():
        tau0, factors0, scalars0 = load_native_dual(best_path, model)
        # Never adopt a stored value: recompute the complete coefficient maximum.
        values0, _ = model.evaluate(tau0, factors0, args.scan_threads, 1)
        best_upper = float(values0.max())
        record['incumbent_reloaded'] = dict(path=str(best_path), sha256=sha(best_path), stored_upper=scalars0['global_upper'],
                                            recomputed_upper=best_upper)
    if inherited is not None and inherited['upper'] < best_upper:
        best_upper = inherited['upper']
        save_native_dual(best_path, model, inherited['tau'], inherited['factors'], global_upper=best_upper,
                         source=np.asarray(record['initialization']['kind']), completed_iterations=counters['completed_iterations'])
    counters['attempts'] += 1
    record.update(status='running', initial_columns=len(master.masks), initial_directions=len(master.cuts),
        initial_direction_counts=master.direction_counts(), initial_best_numerical_upper=best_upper if np.isfinite(best_upper) else None,
        construction_initialization_seconds=time.monotonic()-constructed, lp_backend_version=master.h.version(),
        oracle_binary_sha256={p.name: sha(p) for p in args.cache.glob('*.dylib')}, search_started_epoch=time.time(),
        counters_at_start=dict(counters))
    rt.write_json(attempt / 'run.json', record)
    save_checkpoint(master, state, counters, settings)
    base_elapsed = counters['elapsed_search_seconds']
    start = time.monotonic()
    status, exit_code = 'running', EXIT_FAILURE
    pending_audit = False
    iterations_this_attempt = 0
    stalls = 0

    def elapsed():
        return base_elapsed + time.monotonic() - start

    try:
        while True:
            if not unlimited and iterations_this_attempt >= args.max_iterations:
                status, exit_code = 'smoke_iteration_limit', EXIT_SMOKE
                break
            iteration = counters['completed_iterations']
            heartbeat('lp_and_evaluation', iteration=iteration)
            audit = pending_audit
            if audit:
                # Fresh audit: new solver instance, all coefficients recomputed from W and the directions,
                # full spectra and a complete scan. Rows/columns are identical by construction, so the
                # previous basis statuses are reused as a starting point only.
                options = {k: master.h.getOptionValue(k)[1] for k in ('log_file', 'output_flag', 'log_to_console')}
                previous = master.h.getBasis()
                statuses = ([int(v) for v in previous.col_status], [int(v) for v in previous.row_status]) if previous.valid else None
                master.h = master.rebuild_solver()
                for k, v in options.items():
                    master.h.setOptionValue(k, v)
                if statuses and len(statuses[0]) == master.h.getNumCol() and len(statuses[1]) == master.h.getNumRow():
                    set_basis(master, *statuses)
            iteration_started = time.monotonic()
            row, work = evaluate(master, args, audit=audit)
            row.update(iteration=iteration, attempt=counters['attempts'], seconds=elapsed(), epoch=time.time())
            U = row['global_dual_upper']
            if U < best_upper:
                best_upper = U
                save_native_dual(best_path, model, work['tau'], work['factors'], global_upper=U,
                    restricted_objective=row['restricted_objective'], completed_iterations=iteration,
                    elapsed_search_seconds=row['seconds'], source=np.asarray('search'))
                row['new_numerical_incumbent'] = True
            row['best_global_upper'] = best_upper
            if row['materially_negative_gap']:
                row['warning'] = 'U-L is materially negative: numerical or mapping problem, not convergence'
            converged_now = row['converged']
            update = dict(iteration=iteration, audit=audit)
            if converged_now and audit:
                status, exit_code = 'converged', EXIT_CONVERGED
                save_native_dual(run_dir / 'incumbent' / 'final_converged.npz', model, work['tau'], work['factors'],
                    global_upper=U, restricted_objective=row['restricted_objective'], completed_iterations=iteration,
                    elapsed_search_seconds=row['seconds'], source=np.asarray('final_audit'))
                ro.atomic_savez(run_dir / 'incumbent' / 'final_primal.npz', **model.identity(),
                                masks=np.asarray(master.masks, np.uint64), weights=work['y'])
                rt.write_json(run_dir / 'final_audit.json', row)
            elif converged_now:
                pending_audit = True
                update['scheduled_fresh_final_audit'] = True
            else:
                if audit:
                    counters['audits_failed'] += 1
                    update['audit_failed_continuing'] = True
                pending_audit = False
                B = row['restricted_objective']
                good = work['values'] > B+TOLERANCE
                added = master.add_columns(work['priced'][good])
                gap = row['pricing_gap']
                fallback = bool(added == 0 and gap > TOLERANCE and work['negative'])
                if fallback:
                    counters['duplicate_pricing_psd_fallbacks'] += 1
                admit = gap <= TOLERANCE or fallback
                selected = [(b, v) for _, b, v in work['negative'][:args.max_cuts]] if admit else []
                memory = prune_for_memory(master, work['sol'], len(selected))
                pruned = memory.get('cuts_removed', 0)
                if not memory['triggered'] and iteration % 10 == 0:
                    pruned = master.prune(work['sol'])
                if pruned:
                    counters['prunes'] += 1
                    counters['pruned_directions'] += pruned
                before = len(master.cuts)
                master.add_cuts(selected)
                if added == 0 and not selected:
                    # Nothing changed the LP: enlarge the candidate quota (allowed policy change), then fail loudly.
                    stalls += 1
                    if args.price_top < args.max_price_top:
                        args.price_top = min(args.max_price_top, 2*args.price_top)
                        update['policy_change'] = f'candidate quota per six-vertex representative raised to {args.price_top}'
                    elif stalls >= 3:
                        raise model32.NumericalDiagnostic('search stalled: no new graph, no violated direction, tests not met')
                else:
                    stalls = 0
                update.update(candidate_graphs_above_tolerance=int(good.sum()), added_columns=added, price_top=args.price_top,
                    added_directions=len(master.cuts)-before, duplicate_pricing_psd_fallback=fallback,
                    pruned_directions=pruned, memory_pruning=memory, retained_columns=len(master.masks),
                    retained_directions=len(master.cuts),
                    stalled_without_update=bool(added == 0 and not selected))
            row['iteration_seconds'] = time.monotonic()-iteration_started
            counters['completed_iterations'] = iteration+1
            counters['elapsed_search_seconds'] = elapsed()
            iterations_this_attempt += 1
            with (attempt / 'history.jsonl').open('a', encoding='utf-8') as stream:
                stream.write(json.dumps(row, allow_nan=False)+'\n')
            with (attempt / 'updates.jsonl').open('a', encoding='utf-8') as stream:
                stream.write(json.dumps(update, allow_nan=False)+'\n')
            record.update(counters=dict(counters), best_global_upper=best_upper, last_iteration=public(row), last_update=update)
            rt.write_json(attempt / 'run.json', record)
            rt.write_json(run_dir / 'worker_status.json', dict(attempt=str(attempt), pid=os.getpid(), status=status,
                counters=counters, best_global_upper=best_upper, last_iteration=public(row), last_update=update,
                block_minimum_eigenvalues=row['block_minimum_eigenvalues']))
            print(json.dumps(public(row)), flush=True)
            if status == 'converged':
                break
            if (iteration+1) % args.checkpoint_every == 0:
                heartbeat('checkpoint', iteration=iteration)
                save_checkpoint(master, state, counters, settings)
    except StopRequested:
        status, exit_code = 'interrupted_by_user_stop_request', EXIT_INTERRUPTED
    except model32.NumericalDiagnostic as exc:
        status, exit_code = 'numerical_failure', EXIT_NUMERICAL
        record['error'] = repr(exc)
    counters['elapsed_search_seconds'] = elapsed()
    save_checkpoint(master, state, counters, settings)
    record.update(status=status, counters=dict(counters), finished_epoch=time.time(),
                  convergence_established=status == 'converged', iterations_this_attempt=iterations_this_attempt)
    rt.write_json(attempt / 'run.json', record)
    return exit_code


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cache', type=Path, required=True)
    parser.add_argument('--run-dir', type=Path, required=True)
    parser.add_argument('--attempt-dir', type=Path, required=True)
    parser.add_argument('--init', choices=['resume', 'legacy-checkpoint', 'baseline-certificate'], required=True)
    parser.add_argument('--legacy-checkpoint', type=Path)
    parser.add_argument('--legacy-best-dual', type=Path)
    parser.add_argument('--warm-masks', type=Path)
    parser.add_argument('--mode', choices=['until_converged', 'smoke'], default='until_converged')
    parser.add_argument('--max-iterations', type=int, help='bounded smoke mode only')
    parser.add_argument('--scan-threads', type=int, default=2)
    parser.add_argument('--price-top', type=int, default=8)
    parser.add_argument('--max-cuts', type=int, default=80)
    parser.add_argument('--keep-cuts', type=int, default=3000)
    parser.add_argument('--lp-tolerance', type=float, default=1e-9)
    parser.add_argument('--small-matrix-value', type=float, default=1e-12)
    parser.add_argument('--max-price-top', type=int, default=64)
    parser.add_argument('--lp-solver', choices=['choose', 'simplex', 'ipm'], default='choose')
    parser.add_argument('--checkpoint-every', type=int, default=5)
    arguments = parser.parse_args()
    try:
        code = run(arguments)
    except Exception as exc:
        traceback.print_exc()
        path = arguments.attempt_dir / 'run.json'
        saved = json.loads(path.read_text(encoding='utf-8')) if path.exists() else {}
        saved.update(status='implementation_failure', error=repr(exc), finished_epoch=time.time())
        rt.write_json(path, saved)
        raise
    sys.exit(code)
