"""Mathematical and portability checks for the selected two-model campaign."""
import argparse
import copy
from pathlib import Path
import time

import runtime as rt
import numpy as np
from scipy.linalg import eigh
import reconstruct_optimization as ro
import exactify_five_root as exact


def main(args):
    start = time.monotonic()
    args.output.mkdir(parents=True, exist_ok=True)
    result = dict(status='running', models={}, source_sha256=rt.sources())
    for name in ['M7-no5', 'M7-all5']:
        oracle, blocks, objective, stat, meta = rt.model(args.cache, name)
        if name == 'M7-no5':
            ro.validate(oracle.base, args.cache, blocks, args.output / 'reference-coefficients.json')
        support = ro.turan_blowup_masks(7)
        masks = list(support)
        weights = np.asarray(list(support.values()), float) / 3**7
        deck, features = oracle.features(masks)
        x = deck.T @ weights
        flat = features.T @ weights
        matrices = [np.einsum('h,hij->ij',x,b) for b in blocks]
        matrices += [flat[a:b].reshape(d,d) for a,b,d in zip(ro.OFFSETS[:-1], ro.OFFSETS[1:],ro.DIMS[9:])]
        eig = [float(eigh((m+m.T)/2, subset_by_index=(0,0), eigvals_only=True)[0]) for m in matrices]
        assert abs(weights.sum()-1) < 1e-13
        assert abs(objective@x-5/9) < 5e-13 and abs(stat@x) < 5e-13 and min(eig) > -5e-13
        np.testing.assert_allclose(deck@objective, [int(m).bit_count()/35 for m in masks], atol=5e-15, rtol=0)
        ed, ef = oracle.features([0])
        empty_matrices = [np.einsum('h,hij->ij', np.asarray(ed.toarray()[0]), b) for b in blocks]
        emptyflat = ef.toarray()[0]
        empty_matrices += [emptyflat[a:b].reshape(d,d) for a,b,d in zip(ro.OFFSETS[:-1], ro.OFFSETS[1:],ro.DIMS[9:])]
        assert all(float(eigh((m+m.T)/2, subset_by_index=(0,0), eigvals_only=True)[0]) > -1e-13 for m in empty_matrices)
        assert abs(float((ed@stat)[0])) < 1e-15
        # A zero-square certificate must price an omitted dense configuration above
        # the construction density; this checks pricing direction and full coverage.
        zeros = [np.zeros((d,d)) for d in ro.DIMS[9:]]
        values, found = oracle.price(objective, zeros, threads=2, top=1)
        assert values.max() > 5/9 + 1e-3
        pd, pf = oracle.features(found)
        np.testing.assert_allclose(values, pd@objective, atol=1e-14, rtol=0)
        assert int(found[np.argmax(values)]).bit_count()/35 == values.max() or abs(int(found[np.argmax(values)]).bit_count()/35-values.max()) < 1e-14
        # Nonzero, signed tau and factors exercise dual signs and off-diagonal
        # weights. Check the entire pricing return against sparse feature evaluation.
        rng = np.random.default_rng(20260910)
        factors = [rng.normal(0,.001,(2,d)) for d in ro.DIMS]
        grams = [f.T@f for f in factors]
        tau = -.123
        six = objective+tau*stat
        for b,q in zip(blocks,grams[:9]):
            six += np.einsum('hij,ij->h',b,q)
        values, found = oracle.price(six, grams[9:], threads=2, top=1)
        pd,pf = oracle.features(found)
        computed = pd@six+pf@np.concatenate([q.ravel() for q in grams[9:]])
        np.testing.assert_allclose(values,computed,atol=2e-13,rtol=0)
        saved = args.output / f'{name}-roundtrip.npz'
        ro.atomic_savez(saved, six=six, tau=tau, dimensions=ro.DIMS,
            five_root_type_masks=np.array(oracle.type_masks,np.int32), face_multipliers=np.array([]),
            **{f'factors{i}':f for i,f in enumerate(factors)},
            **{f'gram{i}':q for i,q in enumerate(grams[9:])})
        with np.load(saved) as z:
            np.testing.assert_array_equal(z['six'],six)
            for i,f in enumerate(factors):
                np.testing.assert_array_equal(z[f'factors{i}'],f)
        rounded = exact.round_dual(saved, 2000000, 'svd', 1e-7)
        assert [b['type_mask'] for b in rounded['order7_s5_blocks']] == oracle.type_masks
        # Corrupted dimensions must fail independently in the exact exporter.
        with np.load(saved) as z:
            corrupt = {k:z[k] for k in z.files}
        corrupt['dimensions'] = np.asarray(ro.DIMS)+1
        bad = args.output / f'{name}-deliberately-corrupt.npz'
        ro.atomic_savez(bad, **corrupt)
        rejected = False
        try:
            exact.round_dual(bad, 2000000, 'svd', 1e-7)
        except ValueError:
            rejected = True
        assert rejected
        # Ordered five-root enumeration, independent of the sparse feature builder.
        direct_checks = {}
        if name == 'M7-all5':
            cert = copy.deepcopy(oracle.cert)
            cert['order7_s5_blocks'] = []
            q5 = []
            for entry in oracle.entries:
                d = entry['dimension']
                v = np.zeros(d, np.int64)
                v[0],v[-1] = 2,-3
                cert['order7_s5_blocks'].append(dict(type_mask=entry['sigma'], flags=entry['flags'],
                    dimension=d, denominator=5040, factors=[v.tolist()]))
                q5.append(np.outer(v,v))
            five = exact.five_gram_data(cert)
            for mask in [0,1,27552015,int(found[np.argmax(values)])]:
                _, f = oracle.features([mask])
                sparse_value = float((f[:,ro.OFFSETS[3]:] @ np.concatenate([q.ravel() for q in q5]))[0])
                integer = sum(exact.five_at(mask,five).values())
                np.testing.assert_allclose(sparse_value,integer/5040,atol=1e-13,rtol=0)
                direct_checks[str(mask)] = dict(ordered_numerator=integer, denominator=5040)
        result['models'][name] = dict(block_count=len(ro.DIMS), ordered_blocks=meta,
            type_masks=oracle.type_masks, construction_density=float(objective@x),
            construction_stationarity=float(stat@x), minimum_construction_eigenvalue=min(eig),
            initial_labelled_construction_masks=len(masks), empty_graph_checked=True,
            full_raw_count=oracle.raw_count, priced_values_recomputed=len(values),
            random_signed_tau_max_error=float(np.max(np.abs(values-computed))),
            corrupted_export_rejected=rejected, direct_five_root_checks=direct_checks)
        ro.atomic_savez(args.output / 'initial-construction.npz', masks=np.asarray(masks,np.uint64),weights=weights)
        rt.write_json(args.output / 'validation.json', result)
        print(name, 'validated', flush=True)
    result.update(status='passed', seconds=time.monotonic()-start)
    rt.write_json(args.output / 'validation.json', result)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cache', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    main(parser.parse_args())
