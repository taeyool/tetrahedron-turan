"""Native 32-block seven-vertex model M7-all5-32 (no 2*l-s=5 blocks).

The historical 35-slot model carries three six-vertex blocks with 2*l-s=5
(legacy indices 1, 3, 4). This adapter never loads, optimizes, separates or
serializes them. Every block-dependent quantity is driven by explicit
metadata: six blocks are evaluated through six-vertex coefficient tables and
26 blocks through seven-vertex products, in the validated oracle order.
Historical entry points and the module globals ro.DIMS/ro.OFFSETS are not used.
"""
from __future__ import annotations

import hashlib
import json

import runtime as rt
import numpy as np
from scipy import sparse

MODEL_ID = 'M7-all5-32'
EXCLUDED_LEGACY = (1, 3, 4)
LEGACY_INDICES = [0, 2, 5, 6, 7, 8, 9, 10, 11] + list(range(12, 35))
LEGACY_TO_NEW = {old: new for new, old in enumerate(LEGACY_INDICES)}
LEGACY_DIMS = [2, 2, 11, 8, 7, 64, 56, 50, 45, 7, 236, 191]
FIVE_DIMS = [1024, 896, 800, 728, 720, 784, 712, 652, 644, 594, 545, 700, 640,
             634, 584, 578, 637, 580, 532, 526, 573, 527, 483]
# (s, l, sigma, dimension) for all 32 active blocks, in native order.
EXPECTED = ([(0, 3, 0, 2), (2, 4, 0, 11), (4, 5, 0, 64), (4, 5, 1, 56), (4, 5, 3, 50), (4, 5, 7, 45),
             (1, 4, 0, 7), (3, 5, 0, 236), (3, 5, 1, 191)] +
            [(5, 6, sigma, d) for sigma, d in zip(rt.TYPES, FIVE_DIMS)])
EXPECTED_EXCLUDED = {1: (1, 3, 0, 2), 3: (3, 4, 0, 8), 4: (3, 4, 1, 7)}
SIX_TABLE = 'six_vertex_table'
SEVEN_PRODUCT = 'seven_vertex_product'


def full_speed_process():
    """Opt this process out of Windows power throttling (EcoQoS).

    Hidden processes that are not descendants of a foreground application are
    otherwise scheduled as background work (efficiency cores, reduced clocks),
    which was measured to double every stage time. Process-local; no system
    setting is changed. Returns a small record for the run log.
    """
    import os
    if os.name != 'nt':
        return dict(applied=False, reason='not Windows')
    import ctypes
    from ctypes import wintypes

    class PowerThrottling(ctypes.Structure):
        _fields_ = [('Version', wintypes.ULONG), ('ControlMask', wintypes.ULONG), ('StateMask', wintypes.ULONG)]

    kernel = ctypes.WinDLL('kernel32', use_last_error=True)
    kernel.GetCurrentProcess.restype = wintypes.HANDLE
    kernel.SetProcessInformation.argtypes = [wintypes.HANDLE, ctypes.c_int, ctypes.c_void_p, wintypes.DWORD]
    state = PowerThrottling(1, 0x1, 0)  # control EXECUTION_SPEED, throttling off
    ok = bool(kernel.SetProcessInformation(kernel.GetCurrentProcess(), 4, ctypes.byref(state), ctypes.sizeof(state)))
    return dict(applied=ok, error=None if ok else ctypes.get_last_error(), setting='ProcessPowerThrottling EXECUTION_SPEED off')


def basis_digest(flags):
    return hashlib.sha256(json.dumps(flags, separators=(',', ':')).encode()).hexdigest()


class Model32:
    """Oracle, coefficient tables and metadata of the 32 active blocks."""

    def __init__(self, cache):
        import reconstruct_optimization as ro
        from five_root_oracle import Oracle5, OLD_SIZE
        base = ro.Oracle(cache)
        self.oracle = Oracle5(base, rt.TYPES, cache)
        assert self.oracle.dimensions == FIVE_DIMS and self.oracle.type_masks == rt.TYPES
        legacy_six = [old for old in LEGACY_INDICES if old < 9]
        assert legacy_six == [0, 2, 5, 6, 7, 8]
        with np.load(cache / 'components.npz', allow_pickle=False) as data:
            # Excluded arrays may exist in the immutable cache; they are never read.
            self.six_blocks = [data[f'block{old}'].copy() for old in legacy_six]
            self.objective = data['edge'] / (720 * base.cert['scale']**2)
            self.stationarity = data['stat_unscaled'] / 60
        np.testing.assert_allclose(self.objective, [int(h).bit_count() / 20 for h in base.cert['H_representatives']],
                                   atol=1e-15, rtol=0)
        for old, expected in EXPECTED_EXCLUDED.items():
            b = base.cert['order6_blocks'][old]
            assert (b['s'], b['l'], b['sigma'], b['dimension']) == expected and 2*b['l']-b['s'] == 5
        meta = []
        for old in legacy_six:
            b = base.cert['order6_blocks'][old]
            meta.append(dict(s=b['s'], l=b['l'], sigma=b['sigma'], flags=list(b['flags']), dimension=b['dimension'],
                             evaluation=SIX_TABLE, legacy_index=old))
        fs = ro.fs
        for old, (s, l, sigma) in zip((9, 10, 11), [(1, 4, 0), (3, 5, 0), (3, 5, 1)]):
            flags = fs.flags_for_type(s, l, sigma, fs.rooted_canon_table(l, s))
            meta.append(dict(s=s, l=l, sigma=sigma, flags=list(map(int, flags)), dimension=len(flags),
                             evaluation=SEVEN_PRODUCT, legacy_index=old))
        for old, entry in enumerate(self.oracle.entries, 12):
            meta.append(dict(s=5, l=6, sigma=entry['sigma'], flags=list(map(int, entry['flags'])),
                             dimension=entry['dimension'], evaluation=SEVEN_PRODUCT, legacy_index=old))
        self.n_six = sum(m['evaluation'] == SIX_TABLE for m in meta)
        self.n_seven = len(meta) - self.n_six
        # Seven-vertex oracle features/Grams keep their validated order j=0..25;
        # native index n_six+j. The offsets are those of the oracle feature matrix.
        offsets = np.cumsum([0] + [m['dimension']**2 for m in meta[self.n_six:]])
        assert int(offsets[3]) == OLD_SIZE and np.array_equal(offsets, self.oracle.offsets)
        for i, m in enumerate(meta):
            m['block_index'] = i
            m['ordered_basis_sha256'] = basis_digest(m['flags'])
            if m['evaluation'] == SEVEN_PRODUCT:
                j = i - self.n_six
                m['oracle_gram_index'] = j
                m['feature_slice'] = [int(offsets[j]), int(offsets[j+1])]
            else:
                m['six_table_index'] = i
        self.meta = meta
        self.dims = [m['dimension'] for m in meta]
        self.feature_size = int(offsets[-1])
        self.check()

    def check(self):
        """Startup/resume assertion: exactly the 32 blocks with 2*l-s in {6,7}."""
        assert len(self.meta) == 32 and self.n_six == 6 and self.n_seven == 26
        assert [(m['s'], m['l'], m['sigma'], m['dimension']) for m in self.meta] == EXPECTED
        assert [m['legacy_index'] for m in self.meta] == LEGACY_INDICES
        for i, m in enumerate(self.meta):
            assert m['l'] > m['s'] and 2*m['l']-m['s'] in (6, 7) and 2*m['l']-m['s'] != 5
            assert m['legacy_index'] not in EXCLUDED_LEGACY and len(m['flags']) == m['dimension']
            assert (m['evaluation'] == SIX_TABLE) == (2*m['l']-m['s'] == 6) == (i < self.n_six)
        assert len(self.six_blocks) == self.n_six
        assert all(b.shape == (964, d, d) for b, d in zip(self.six_blocks, self.dims))

    def manifest(self):
        return dict(model_id=MODEL_ID, block_count=len(self.meta), six_vertex_table_blocks=self.n_six,
                    seven_vertex_product_blocks=self.n_seven, excluded_legacy_indices=list(EXCLUDED_LEGACY),
                    excluded_legacy_blocks={str(k): dict(zip(('s', 'l', 'sigma', 'dimension'), v))
                                            for k, v in EXPECTED_EXCLUDED.items()},
                    legacy_indices=LEGACY_INDICES, five_root_types=list(self.oracle.type_masks),
                    raw_configuration_count=int(self.oracle.raw_count),
                    blocks=[{k: v for k, v in m.items() if k != 'flags'} for m in self.meta])

    def identity(self):
        """Arrays stored in every native file; verified again on every load."""
        return dict(model_id=np.asarray(MODEL_ID), dimensions=np.asarray(self.dims, np.int32),
                    legacy_indices=np.asarray(LEGACY_INDICES, np.int32),
                    five_root_type_masks=np.asarray(self.oracle.type_masks, np.int32),
                    ordered_basis_sha256=np.asarray([m['ordered_basis_sha256'] for m in self.meta]))

    def check_identity(self, data):
        assert str(data['model_id']) == MODEL_ID, 'not a native 32-block file'
        np.testing.assert_array_equal(data['dimensions'], self.dims)
        np.testing.assert_array_equal(data['legacy_indices'], LEGACY_INDICES)
        np.testing.assert_array_equal(data['five_root_type_masks'], self.oracle.type_masks)
        assert list(map(str, data['ordered_basis_sha256'])) == [m['ordered_basis_sha256'] for m in self.meta]

    def grams(self, factors):
        """The 26 seven-vertex Grams in oracle order, from 32 native factor arrays."""
        assert len(factors) == 32
        return [np.einsum('ri,rj->ij', f, f, optimize=False) if len(f) else np.zeros((d, d))
                for f, d in zip(factors[self.n_six:], self.dims[self.n_six:])]

    def six_coefficients(self, tau, factors):
        """Aggregate six-vertex coefficient vector of objective, stationarity and six-table blocks."""
        six = self.objective + tau*self.stationarity
        for table, f in zip(self.six_blocks, factors[:self.n_six]):
            if len(f):
                six = six + np.einsum('hij,ri,rj->h', table, f, f, optimize=True)
        return six

    def evaluate(self, tau, factors, threads=2, top=8):
        """Complete-universe coefficient maximum of a native candidate."""
        return self.oracle.price(self.six_coefficients(tau, factors), self.grams(factors), threads, top)


class NumericalDiagnostic(RuntimeError):
    """Recoverable solver-side condition (not convergence, not an implementation bug)."""


class Master32:
    """Restricted LP over retained graphs W and directions V_b of the 32 blocks."""

    def __init__(self, model, keep_cuts=3000, lp_solver='choose', feasibility_tolerance=1e-9, small_matrix_value=1e-12):
        import highspy
        self.highspy = highspy
        self.model, self.oracle = model, model.oracle
        self.keep_cuts, self.lp_solver, self.feasibility_tolerance = keep_cuts, lp_solver, feasibility_tolerance
        # HiGHS discards matrix coefficients below small_matrix_value (default 1e-9); 1e-12 is the
        # smallest value it accepts.
        self.small_matrix_value = small_matrix_value
        self.neq = 2  # normalization and degree stationarity; no face equalities
        self.masks, self.seen, self.signatures = [], set(), set()
        self.deck = sparse.csr_matrix((0, 964))
        self.feat = sparse.csr_matrix((0, model.feature_size))
        self.cuts, self.sixcuts = [], []
        self.h = self.new_solver()
        self.add_columns([0])

    def new_solver(self):
        h = self.highspy.Highs()
        assert h.setOptionValue('small_matrix_value', self.small_matrix_value) == self.highspy.HighsStatus.kOk
        for key, value in {'output_flag': False, 'primal_feasibility_tolerance': self.feasibility_tolerance,
                           'dual_feasibility_tolerance': self.feasibility_tolerance, 'threads': 1,
                           'solver': self.lp_solver}.items():
            h.setOptionValue(key, value)
        h.changeObjectiveSense(self.highspy.ObjSense.kMaximize)
        h.addRow(1, 1, 0, np.array([], np.int32), np.array([], float))
        h.addRow(0, 0, 0, np.array([], np.int32), np.array([], float))
        return h

    def equality_rows(self, deck):
        return np.array([np.ones(deck.shape[0]), np.asarray(deck @ self.model.stationarity)])

    def add_columns(self, masks, preserve_order=False):
        fresh = ([m for m in dict.fromkeys(map(int, masks)) if m not in self.seen]
                 if preserve_order else sorted(set(map(int, masks)) - self.seen))
        self.seen.update(fresh)
        if not fresh:
            return 0
        deck, feat = self.oracle.features(fresh)
        assert feat.shape[1] == self.model.feature_size
        keep = []
        for i in range(len(fresh)):
            d, f = deck.getrow(i), feat.getrow(i)
            # Equal full moment features and deletion marginals are identical model columns.
            key = hashlib.sha256(d.indices.tobytes() + np.round(d.data*self.oracle.deck_denominator).astype(np.int16).tobytes() +
                                 f.indices.tobytes() + np.round(f.data*self.oracle.feature_denominator).astype(np.int16).tobytes()).digest()
            if key not in self.signatures:
                self.signatures.add(key)
                keep.append(i)
        if not keep:
            return 0
        deck, feat = deck[keep], feat[keep]
        cost = np.asarray(deck @ self.model.objective)
        coeff = self.equality_rows(deck)
        if self.cuts:
            coeff = np.vstack([coeff, self.coefficients(deck, feat, self.cuts, self.sixcuts).T])
        matrix = sparse.csc_matrix(coeff)
        status = self.h.addCols(len(keep), cost, np.zeros(len(keep)), np.full(len(keep), self.highspy.kHighsInf),
                                matrix.nnz, matrix.indptr.astype(np.int32), matrix.indices.astype(np.int32), matrix.data)
        assert status != self.highspy.HighsStatus.kError
        self.deck = sparse.vstack([self.deck, deck], format='csr')
        self.feat = sparse.vstack([self.feat, feat], format='csr')
        self.masks.extend(fresh[i] for i in keep)
        return len(keep)

    def six_cut(self, b, v):
        m = self.model.meta[b]
        if m['evaluation'] == SIX_TABLE:
            return np.einsum('i,hij,j->h', v, self.model.six_blocks[m['six_table_index']], v, optimize=True)
        return np.zeros(964)

    def coefficients(self, deck, feat, cuts, six):
        result = np.asarray(deck @ np.array(six).T)
        for m in self.model.meta:
            if m['evaluation'] != SEVEN_PRODUCT:
                continue
            b = m['block_index']
            indices = [i for i, (bb, _) in enumerate(cuts) if bb == b]
            if not indices:
                continue
            start, stop = m['feature_slice']
            features = feat[:, start:stop]
            for first in range(0, len(indices), 32):
                selected = indices[first:first+32]
                products = np.array([np.outer(cuts[i][1], cuts[i][1]).ravel() for i in selected])
                result[:, selected] = features @ products.T
        return result

    def add_cuts(self, cuts):
        if not cuts:
            return
        for b, v in cuts:
            assert 0 <= b < 32 and len(v) == self.model.dims[b] and np.isfinite(v).all()
        six = [self.six_cut(b, v) for b, v in cuts]
        values = self.coefficients(self.deck, self.feat, cuts, six)
        mat = sparse.csr_matrix(values.T)
        status = self.h.addRows(len(cuts), np.zeros(len(cuts)), np.full(len(cuts), self.highspy.kHighsInf),
                                mat.nnz, mat.indptr.astype(np.int32), mat.indices.astype(np.int32), mat.data)
        assert status != self.highspy.HighsStatus.kError
        self.cuts.extend(cuts)
        self.sixcuts.extend(six)

    def rebuild_solver(self):
        """Fresh HiGHS instance with the identical rows and columns; no inherited basis."""
        h = self.new_solver()
        if self.masks:
            cost = np.asarray(self.deck @ self.model.objective)
            coeff = self.equality_rows(self.deck)
            if self.cuts:
                coeff = np.vstack([coeff, self.coefficients(self.deck, self.feat, self.cuts, self.sixcuts).T])
                status = h.addRows(len(self.cuts), np.zeros(len(self.cuts)), np.full(len(self.cuts), self.highspy.kHighsInf),
                                   0, np.zeros(len(self.cuts)+1, np.int32), np.array([], np.int32), np.array([], float))
                assert status != self.highspy.HighsStatus.kError
            matrix = sparse.csc_matrix(coeff)
            n = len(self.masks)
            status = h.addCols(n, cost, np.zeros(n), np.full(n, self.highspy.kHighsInf), matrix.nnz,
                               matrix.indptr.astype(np.int32), matrix.indices.astype(np.int32), matrix.data)
            assert status != self.highspy.HighsStatus.kError
        assert h.getNumCol() == len(self.masks) and h.getNumRow() == self.neq + len(self.cuts)
        return h

    def moments(self, y):
        x = self.deck.T @ y
        flat = self.feat.T @ y
        matrices = [np.einsum('h,hij->ij', x, table) for table in self.model.six_blocks]
        for m in self.model.meta[self.model.n_six:]:
            start, stop = m['feature_slice']
            matrices.append(flat[start:stop].reshape(m['dimension'], m['dimension']))
        assert len(matrices) == 32
        return x, matrices

    def dual(self, sol):
        multipliers = -np.asarray(sol.row_dual[self.neq:])
        if len(multipliers) != len(self.cuts) or not np.isfinite(multipliers).all():
            raise NumericalDiagnostic('row duals are missing or nonfinite')
        if multipliers.min(initial=0) <= -1e-7:
            raise NumericalDiagnostic(f'materially negative cut multiplier {multipliers.min()}')
        multipliers = np.maximum(multipliers, 0)
        tau = float(-sol.row_dual[1])
        factors = [[] for _ in range(32)]
        for w, (b, v) in zip(multipliers, self.cuts):
            if w > 0:
                factors[b].append(np.sqrt(w)*v)
        factors = [np.asarray(rows, float).reshape(-1, d) for rows, d in zip(factors, self.model.dims)]
        six = self.model.objective + tau*self.model.stationarity
        if len(multipliers):
            six = six + np.einsum('r,rh->h', multipliers, np.array(self.sixcuts), optimize=False)
        grams = [np.zeros((d, d)) for d in self.model.dims[self.model.n_six:]]
        for w, (b, v) in zip(multipliers, self.cuts):
            if w and b >= self.model.n_six:
                grams[self.model.meta[b]['oracle_gram_index']] += w*np.outer(v, v)
        return six, grams, tau, multipliers, factors

    def delete_cuts(self, keep):
        keep_set = set(keep)
        remove = np.array([self.neq+i for i in range(len(self.cuts)) if i not in keep_set], np.int32)
        if not len(remove):
            return 0
        before = self.h.getNumRow()
        status = self.h.deleteRows(len(remove), remove)
        assert status != self.highspy.HighsStatus.kError and self.h.getNumRow() == before-len(remove)
        self.cuts = [self.cuts[i] for i in keep]
        self.sixcuts = [self.sixcuts[i] for i in keep]
        return len(remove)

    def prune(self, sol):
        """Recorded policy: above keep_cuts, drop dual-inactive cuts older than the newest keep_cuts/2."""
        limit = self.keep_cuts
        if limit <= 0 or len(self.cuts) <= limit:
            return 0
        dual = np.asarray(sol.row_dual[self.neq:])
        recent = limit//2
        keep = [i for i in range(len(self.cuts)) if abs(dual[i]) > 1e-10 or i >= len(self.cuts)-recent]
        if len(keep) >= len(self.cuts)*.85:
            return 0
        return self.delete_cuts(keep)

    def direction_counts(self):
        return np.bincount([b for b, _ in self.cuts], minlength=32).tolist()
