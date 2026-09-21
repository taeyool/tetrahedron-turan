"""Nine-block M6 and deletion-lift models, with independent ordered counting."""
from __future__ import annotations
import itertools
from pathlib import Path
import time

import runtime as rt
import numpy as np
from scipy import sparse
import reconstruct_optimization as ro
from analyze_certificate import CERT, stat_numerators

DIMS = [2, 2, 11, 8, 7, 64, 56, 50, 45]


def source_data(cache):
    cert = rt.json.loads((CERT / 'legacy/K4_turan_order7_exact_certificate.json').read_text())
    with np.load(cache / 'components.npz') as z:
        blocks = [z[f'block{i}'].copy() for i in range(9)]
        objective = z['edge'] / (720 * cert['scale']**2)
        stat = z['stat_unscaled'] / 60
    reps = np.asarray(cert['H_representatives'], dtype=np.uint32)
    np.testing.assert_allclose(objective, [int(h).bit_count()/20 for h in reps], atol=1e-15, rtol=0)
    np.testing.assert_allclose(stat, stat_numerators(reps.tolist())/60, atol=1e-15, rtol=0)
    assert [b.shape[1] for b in blocks] == DIMS and len(reps) == 964
    metadata = [dict(b) for b in cert['order6_blocks']]
    for i, b in enumerate(metadata):
        b['block_index'] = i
        b['ordered_basis_sha256'] = rt.hashlib.sha256(rt.json.dumps(b['flags'], separators=(',', ':')).encode()).hexdigest()
    return cert, reps, blocks, objective, stat, metadata


def prepare(cache):
    """Count using all 720 vertex permutations, separately from build_blocks.

    A fixed pair of disjoint flags in a random ordered permutation has the
    prescribed uniform ordered-root distribution, including the unused vertex.
    Thus counts here have denominator 720 for every block.
    """
    started = time.monotonic()
    cert, reps, blocks, objective, stat, metadata = source_data(cache)
    permutations = list(itertools.permutations(range(6)))
    labeled = np.zeros((720, 964), dtype=np.uint32)
    for j, p in enumerate(permutations):
        for old, new in enumerate(ro.fs.permutation_edge_map(6, p)):
            labeled[j] |= ((reps >> old) & 1) << new
    np.testing.assert_array_equal(labeled.min(axis=0), reps)
    canonical = np.full(1 << 20, -1, dtype=np.int32)
    for row in labeled:
        previous = canonical[row]
        assert np.all((previous == -1) | (previous == np.arange(964)))
        canonical[row] = np.arange(964)
    all_masks = np.arange(1 << 20, dtype=np.uint32)
    admissible = np.ones(len(all_masks), dtype=bool)
    for forbidden in ro.fs.k4_masks(6):
        admissible &= (all_masks & forbidden) != forbidden
    np.testing.assert_array_equal(canonical >= 0, admissible)

    def induced(vertices):
        result = np.zeros_like(labeled)
        for k, triple in enumerate(ro.fs.triples(len(vertices))):
            edge = tuple(sorted(vertices[t] for t in triple))
            result |= ((labeled >> ro.fs.edge_index(6)[edge]) & 1) << k
        return result

    edge_a=induced((0,1,2))
    independent = dict(edge720=edge_a.sum(axis=0,dtype=np.int64),
        stat720=3*((edge_a*induced((3,4,5))).sum(axis=0,dtype=np.int64)
                  -(edge_a*induced((0,3,4))).sum(axis=0,dtype=np.int64)))
    np.testing.assert_allclose(objective*720,independent['edge720'],atol=1e-13,rtol=0)
    np.testing.assert_allclose(stat*720,independent['stat720'],atol=1e-13,rtol=0)
    for b, (a, meta) in enumerate(zip(blocks, metadata)):
        s, l, sigma, d = (meta[k] for k in ['s', 'l', 'sigma', 'dimension'])
        r = l-s
        canon = ro.fs.rooted_canon_table(l, s)
        flags = ro.fs.flags_for_type(s, l, sigma, canon)
        assert flags == meta['flags']
        lookup = np.full(len(canon), -1, dtype=np.int32)
        lookup[flags] = np.arange(d)
        first = lookup[canon[induced(tuple(range(l)))]]
        second = lookup[canon[induced(tuple(range(s))+tuple(range(l, l+r)))]]
        valid = induced(tuple(range(s))) == sigma
        assert np.all(first[valid] >= 0) and np.all(second[valid] >= 0)
        counts = np.zeros((964, d, d), dtype=np.int32)
        host = np.broadcast_to(np.arange(964), labeled.shape)
        np.add.at(counts, (host[valid], first[valid], second[valid]), 1)
        np.testing.assert_allclose(a*720, counts, atol=2e-13, rtol=0)
        independent[f'count{b}'] = counts
    ro.atomic_savez(cache/'order6-independent.npz', canonical=canonical, representatives=reps,
                    **independent)
    result = dict(status='passed', six_vertex_classes=964,
        admissible_labeled_six_vertex_graphs=int(admissible.sum()),
        all_permutations_per_class=720, all_nine_coefficient_arrays_agree=True,
        ordered_blocks=metadata, seconds=time.monotonic()-started,
        components_sha256=rt.digest(cache/'components.npz'),
        independent_counts_sha256=rt.digest(cache/'order6-independent.npz'))
    rt.write_json(cache/'order6-validation.json', result)
    return result


class SixOracle:
    order = 6
    raw_count = 964
    deck_denominator = 1
    feature_denominator = 1

    def __init__(self, cache, cert):
        self.cert = cert
        self.reps = np.asarray(cert['H_representatives'], dtype=np.uint64)
        with np.load(cache/'order6-independent.npz') as z:
            self.canonical = z['canonical'].copy()

    def features(self, masks):
        masks = np.asarray(list(masks), dtype=np.uint32)
        indices = self.canonical[masks]
        assert np.all(indices >= 0)
        n = len(masks)
        return sparse.csr_matrix((np.ones(n), (np.arange(n), indices)), shape=(n, 964)), sparse.csr_matrix((n, 0))

    def price(self, six, grams, threads=2, top=8):
        assert not grams and np.all(np.isfinite(six))
        indices = np.argsort(-six, kind='stable')[:top]
        return six[indices], self.reps[indices]


class LiftOracle:
    order = 7
    deck_denominator = 7
    feature_denominator = 1

    def __init__(self, cache):
        self.base = ro.Oracle(cache)
        self.cert, self.raw_count = self.base.cert, self.base.raw_count
        self.zeros = [np.zeros((d,d)) for d in [7,236,191]]

    def features(self, masks):
        masks = np.ascontiguousarray(list(masks), dtype=np.uint64)
        n = len(masks)
        decks = np.zeros((n,7), np.uint16)
        one, three = np.zeros((n,28),np.uint16), np.zeros((n,105),np.uint32)
        self.base.lib.get_features(masks, n, decks, one, three)
        assert np.all(decks < 964)
        deck = sparse.csr_matrix((np.full(n*7,1/7), (np.repeat(np.arange(n),7), decks.ravel())), shape=(n,964))
        deck.sort_indices()
        return deck, sparse.csr_matrix((n,0))

    def price(self, six, grams, threads=2, top=8):
        assert not grams
        return self.base.price(six, self.zeros, threads=threads, top=top)


def model(cache, name):
    cert, reps, blocks, objective, stat, metadata = source_data(cache)
    if name == 'M6':
        oracle = SixOracle(cache, cert)
    elif name == 'M7-lift6':
        oracle = LiftOracle(cache)
    else:
        raise ValueError(name)
    ro.DIMS = list(DIMS)
    ro.OFFSETS = np.array([0])
    return oracle, blocks, objective, stat, metadata


def validate_models(cache, output):
    started = time.monotonic()
    result = prepare(cache)
    for name in ['M6', 'M7-lift6']:
        oracle, blocks, objective, stat, metadata = model(cache, name)
        support = ro.turan_blowup_masks(oracle.order)
        masks = list(support)
        weights = np.asarray(list(support.values())) / 3**oracle.order
        deck, _ = oracle.features(masks)
        x = deck.T@weights
        assert abs(float(objective@x)-5/9) < 1e-14
        assert abs(float(stat@x)) < 1e-14
        minima = [float(np.linalg.eigvalsh(np.einsum('h,hij->ij', x, b))[0]) for b in blocks]
        assert min(minima) > -1e-13
        np.testing.assert_allclose(deck@objective, [m.bit_count()/(20 if oracle.order==6 else 35) for m in masks], atol=1e-15, rtol=0)
        empty, _ = oracle.features([0])
        assert (empty@objective)[0] == (empty@stat)[0] == 0
        rng = np.random.default_rng(610)
        six = objective - .37*stat
        for b in blocks:
            f = rng.normal(size=(2,b.shape[1]))*.01
            six += np.einsum('hij,ij->h', b, f.T@f)
        values, priced = oracle.price(six, [], top=8)
        pd, _ = oracle.features(priced)
        np.testing.assert_allclose(values, pd@six, atol=5e-13, rtol=0)
        # An empty-only restricted master omits a strictly violated column.
        assert values.max() > float((empty@six)[0])+1e-7
        result[name] = dict(status='passed', construction_density=float(objective@x),
            construction_stationarity=float(stat@x), construction_minimum_eigenvalue=min(minima),
            all_returned_prices_checked=len(values), omitted_violating_column_recovered=True,
            block_count=len(metadata), raw_configuration_count=oracle.raw_count)
    result['total_seconds'] = time.monotonic()-started
    rt.write_json(output, result)
    print(rt.json.dumps(result), flush=True)


if __name__ == '__main__':
    import argparse
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cache',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    validate_models(a.cache.resolve(), a.output.resolve())
