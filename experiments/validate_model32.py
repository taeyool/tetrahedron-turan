"""Preflight checks of the native 32-block model against the historical 35-slot implementation.

Covers: manifest, pinned baseline and its migration, coefficient matrices of
all 32 blocks on deterministic graphs (old implementation, independent Python
enumeration and ordered five-root sums), stationarity sign/normalization,
whole-candidate evaluation with zero-embedded deleted slots, and rejection of
misindexed or corrupted exports.
"""
from __future__ import annotations

import argparse
import copy
import json
from pathlib import Path
import time

import runtime as rt
import numpy as np
import reconstruct_optimization as ro
import exactify_five_root as exact
from analyze_certificate import stat_numerators
import model32
import run_unlimited32 as ru
from export_legacy35 import export

GRAPHS = [0, 1, 27552015, 31837153552, 33554400, ru.BASELINE_MAXIMIZER]


def old_moment_matrices(oracle, blocks, dims, offsets, masks):
    """Historical 35-slot coefficient matrices A_b(G), exactly as rt.moments forms them."""
    deck, feat = oracle.features(masks)
    out = []
    for i in range(len(masks)):
        x = np.asarray(deck[i].todense()).ravel()
        flat = np.asarray(feat[i].todense()).ravel()
        matrices = [np.einsum('h,hij->ij', x, b) for b in blocks]
        matrices += [flat[a:b].reshape(d, d) for a, b, d in zip(offsets[:-1], offsets[1:], dims[9:])]
        out.append(matrices)
    return out


def main(args):
    started = time.monotonic()
    args.output.mkdir(parents=True, exist_ok=True)
    cache = args.cache.resolve()
    result = dict(status='running', source_sha256=rt.sources())
    model = model32.Model32(cache)
    model.check()
    manifest = model.manifest()
    rt.write_json(args.output / 'model_manifest.json', manifest)
    # --- 1. manifest against the historical model metadata
    oracle_old, blocks_old, objective_old, stat_old, meta_old = rt.model(cache, 'M7-all5')
    dims_old, offsets_old = list(ro.DIMS), np.asarray(ro.OFFSETS)
    assert len(meta_old) == 35 and len(model.meta) == 32
    for m in model.meta:
        old = meta_old[m['legacy_index']]
        assert (old['s'], old['l'], old['sigma'], old['dimension']) == (m['s'], m['l'], m['sigma'], m['dimension'])
        assert list(old['flags']) == m['flags'] and old['ordered_basis_sha256'] == m['ordered_basis_sha256']
    excluded = [meta_old[i] for i in model32.EXCLUDED_LEGACY]
    assert [(b['s'], b['l'], b['sigma'], b['dimension']) for b in excluded] == [(1, 3, 0, 2), (3, 4, 0, 8), (3, 4, 1, 7)]
    assert all(2*b['l']-b['s'] == 5 for b in excluded)
    assert sorted(2*m['l']-m['s'] for m in model.meta).count(5) == 0
    if args.legacy_run_json is not None:
        legacy_blocks = json.loads(args.legacy_run_json.read_text(encoding='utf-8'))['ordered_blocks']
        for m in model.meta:
            assert legacy_blocks[m['legacy_index']]['ordered_basis_sha256'] == m['ordered_basis_sha256']
        result['ordered_bases_match_six_hour_run'] = True
    np.testing.assert_array_equal(model.objective, objective_old)
    np.testing.assert_array_equal(model.stationarity, stat_old)
    reps = oracle_old.cert['H_representatives']
    np.testing.assert_allclose(model.stationarity, stat_numerators(list(reps))/60, atol=1e-15, rtol=0)
    result['manifest'] = dict(block_count=32, six_vertex_table_blocks=model.n_six, seven_vertex_product_blocks=model.n_seven,
                              five_root_types=len(model.oracle.type_masks), no_active_2l_minus_s_5=True)
    # --- 2. coefficient matrices on deterministic graphs
    support = ro.turan_blowup_masks(7)
    construction = sorted(support)[:3] + sorted(support)[-2:]
    graphs = list(dict.fromkeys(GRAPHS + construction + args.extra_masks))
    assert all(ro.fs.is_k4free(g, 7) for g in graphs)
    master = model32.Master32(model)
    master.add_columns(graphs, preserve_order=True)
    kept = list(master.masks)
    old_matrices = old_moment_matrices(oracle_old, blocks_old, dims_old, offsets_old, kept)
    maximum = 0.0
    for i, g in enumerate(kept):
        y = np.zeros(len(kept))
        y[i] = 1
        _, new = master.moments(y)
        for m, a in zip(model.meta, new):
            np.testing.assert_array_equal(a, old_matrices[i][m['legacy_index']])
            maximum = max(maximum, float(np.abs(a-a.T).max()))
    # Independent Python enumeration of the one- and three-root seven-vertex blocks.
    direct = ro.fs.build_blocks(7, kept, include_s=[1, 3], verbose=False)
    for j, block in enumerate(direct):
        m = model.meta[model.n_six+j]
        assert block.flags == m['flags'] and (block.s, block.l, block.sigma) == (m['s'], m['l'], m['sigma'])
        start, stop = m['feature_slice']
        np.testing.assert_allclose(master.feat[:, start:stop].toarray(), block.A.reshape(len(kept), -1), atol=1e-13, rtol=0)
    # Independent enumeration of the six-vertex table blocks at order six.
    direct6 = ro.fs.build_blocks(6, list(map(int, reps)), include_s=[0, 2, 4], verbose=False)
    by_key = {(b.s, b.l, b.sigma): b for b in direct6}
    for m, table in zip(model.meta[:model.n_six], model.six_blocks):
        block = by_key[(m['s'], m['l'], m['sigma'])]
        assert block.flags == m['flags']
        np.testing.assert_allclose(table, block.A, atol=1e-13, rtol=0)
    # Ordered five-root sums with an asymmetric integer test factor in every type.
    cert = copy.deepcopy(oracle_old.cert)
    cert['order7_s5_blocks'] = []
    q5 = []
    for entry in model.oracle.entries:
        v = np.zeros(entry['dimension'], np.int64)
        v[0], v[1], v[-1] = 2, 5, -3
        cert['order7_s5_blocks'].append(dict(type_mask=entry['sigma'], flags=entry['flags'], dimension=entry['dimension'],
                                             denominator=5040, factors=[v.tolist()]))
        q5.append(np.outer(v, v).astype(float))
    five = exact.five_gram_data(cert)
    five_start = model.meta[9]['feature_slice'][0]
    for i, g in enumerate(kept[:8]):
        sparse_value = float((master.feat[i, five_start:] @ np.concatenate([q.ravel() for q in q5]))[0])
        np.testing.assert_allclose(sparse_value, sum(exact.five_at(int(g), five).values())/5040, atol=1e-12, rtol=0)
    # Stationarity sign and normalization: S = -3 [[f^2]] with f in the one-root seven-vertex block.
    f = np.array([0, -1, -2, -3, 3, 2, 1], float)/3
    start, stop = model.meta[6]['feature_slice']
    s_values = np.asarray(master.deck @ model.stationarity)
    np.testing.assert_allclose(s_values, -3*np.asarray(master.feat[:, start:stop] @ np.outer(f, f).ravel()), atol=1e-13, rtol=0)
    weights = np.asarray([support[g] for g in sorted(support)], float)/3**7
    deck_c, _ = model.oracle.features(sorted(support))
    assert abs(float(weights @ (deck_c @ model.stationarity))) < 5e-13 and abs(float(weights @ (deck_c @ model.objective))-5/9) < 5e-13
    result['coefficients'] = dict(graphs=list(map(int, kept)), blocks_compared_per_graph=32, identical_to_historical_implementation=True,
                                  independent_enumeration_blocks=[0, 1, 2, 3, 4, 5, 6, 7, 8], ordered_five_root_checks=min(8, len(kept)),
                                  stationarity_identity_checked=True, maximum_asymmetry=maximum)
    # --- 3. LP coefficients and whole-candidate evaluation with zero-embedded deleted slots
    rng = np.random.default_rng(20260918)
    factors = [rng.normal(0, .002, (3, d)) for d in model.dims]
    tau = -.371
    cuts = [(b, v/np.linalg.norm(v)) for b, rows in enumerate(factors) for v in rows]
    master.add_cuts(cuts)
    new_coefficients = master.coefficients(master.deck, master.feat, master.cuts, master.sixcuts)
    deck_old, feat_old = oracle_old.features(kept)
    for k, (b, v) in enumerate(cuts):
        old = model.meta[b]['legacy_index']
        for i in range(len(kept)):
            np.testing.assert_allclose(new_coefficients[i, k], v @ old_matrices[i][old] @ v, atol=1e-15, rtol=0)
    legacy_factors = [np.empty((0, d)) for d in dims_old]
    for m, rows in zip(model.meta, factors):
        legacy_factors[m['legacy_index']] = rows
    six_old = objective_old + tau*stat_old
    for table, rows in zip(blocks_old, legacy_factors[:9]):
        six_old = six_old + np.einsum('hij,ij->h', table, rows.T @ rows)
    grams_old = [rows.T @ rows for rows in legacy_factors[9:]]
    values_old, masks_old = oracle_old.price(six_old, grams_old, threads=args.threads, top=2)
    values_new, masks_new = model.evaluate(tau, factors, threads=args.threads, top=2)
    np.testing.assert_allclose(values_new, values_old, atol=1e-13, rtol=0)
    np.testing.assert_array_equal(masks_new, masks_old)
    pd, pf = model.oracle.features(masks_new)
    recomputed = pd @ model.six_coefficients(tau, factors) + pf @ np.concatenate([q.ravel() for q in model.grams(factors)])
    np.testing.assert_allclose(values_new, recomputed, atol=2e-13, rtol=0)
    result['whole_candidate'] = dict(random_signed_tau=tau, priced_values=len(values_new),
                                     max_difference_from_historical=float(np.abs(values_new-values_old).max()),
                                     max_difference_from_sparse_recomputation=float(np.abs(values_new-recomputed).max()))
    # --- 4. pinned baseline: hash, empty excluded slots, migration preserves its value
    tau_b, factors_b, cert_b = ru.baseline_native(model)
    assert sum(len(f) for f in factors_b) == cert_b['total_integer_square_factors'] == 794
    values_b, masks_b = model.evaluate(tau_b, factors_b, threads=args.threads, top=1)
    baseline_decimal = 312372062889819/560000000000000
    assert abs(float(values_b.max())-baseline_decimal) <= 1e-12
    native = args.output / 'baseline-native.npz'
    ru.save_native_dual(native, model, tau_b, factors_b, global_upper=float(values_b.max()), source=np.asarray('pinned_baseline'))
    info = export(native, args.output / 'baseline-legacy-compatible.npz', model, args.threads)
    rounded = exact.round_dual(args.output / 'baseline-legacy-compatible.npz', cert_b['scale'], 'cuts', 1e-7)
    assert rounded['order6_factors_by_block'] == cert_b['order6_factors_by_block']
    for key in exact.BASE_FIELDS:
        assert rounded[key] == cert_b[key]
    assert [b['factors'] for b in rounded['order7_s5_blocks']] == [b['factors'] for b in cert_b['order7_s5_blocks']]
    assert rounded['stationarity']['tau_numerator'] == cert_b['stationarity']['tau_numerator']
    result['baseline'] = dict(sha256=ru.BASELINE_SHA256, fraction=ru.BASELINE_FRACTION, excluded_slots_empty=True,
        float_repriced_upper=float(values_b.max()), float_maximizer=int(masks_b[int(np.argmax(values_b))]),
        export=info, integer_roundtrip_identical=True)
    # --- 5. misindexed and corrupted inputs
    rejected = {}
    with np.load(native, allow_pickle=False) as data:
        arrays = {k: data[k] for k in data.files}
    try:  # renumbered factors0..31 handed directly to the historical exactifier
        exact.round_dual(native, 2000000, 'cuts', 1e-7)
        rejected['renumbered_native_to_old_exactifier'] = False
    except (ValueError, KeyError):
        rejected['renumbered_native_to_old_exactifier'] = True
    swapped = dict(arrays)
    swapped['factors9'], swapped['factors10'] = arrays['factors10'], arrays['factors9']
    ro.atomic_savez(args.output / 'corrupt-misindexed.npz', **swapped)
    wrong_identity = dict(arrays)
    wrong_identity['legacy_indices'] = np.asarray(list(range(32)), np.int32)
    ro.atomic_savez(args.output / 'corrupt-identity.npz', **wrong_identity)
    for name in ('corrupt-misindexed', 'corrupt-identity'):
        try:
            export(args.output / f'{name}.npz', args.output / f'{name}-export.npz', model, args.threads)
            rejected[name] = False
        except AssertionError:
            rejected[name] = True
    perturbed = dict(arrays)
    perturbed['factors7'] = arrays['factors7'].copy()
    perturbed['factors7'][0, 0] += 1e-3
    perturbed.pop('global_upper')
    ro.atomic_savez(args.output / 'corrupt-perturbed.npz', **perturbed)
    info_p = export(args.output / 'corrupt-perturbed.npz', args.output / 'corrupt-perturbed-export.npz', model, args.threads)
    rejected['perturbed_value_disagrees'] = abs(info_p['repriced_upper']-baseline_decimal) > 1e-9
    claimed_wrong = dict(arrays)
    claimed_wrong['global_upper'] = np.asarray(float(arrays['global_upper'])-1e-6)
    ro.atomic_savez(args.output / 'corrupt-claim.npz', **claimed_wrong)
    try:
        export(args.output / 'corrupt-claim.npz', args.output / 'corrupt-claim-export.npz', model, args.threads)
        rejected['stale_claimed_upper'] = False
    except AssertionError:
        rejected['stale_claimed_upper'] = True
    assert all(rejected.values()), rejected
    result['corruption_checks'] = rejected
    result.update(status='passed', seconds=time.monotonic()-started)
    rt.write_json(args.output / 'validation.json', result)
    print(json.dumps({k: v for k, v in result.items() if k != 'source_sha256'}, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cache', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--legacy-run-json', type=Path)
    parser.add_argument('--extra-masks', type=int, nargs='*', default=[])
    parser.add_argument('--threads', type=int, default=2)
    main(parser.parse_args())
