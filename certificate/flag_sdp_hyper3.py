from __future__ import annotations

import itertools
import math
import pickle
import time
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence

import numpy as np

_TRIPLES: dict[int, list[tuple[int, int, int]]] = {}
_EDGE_INDEX: dict[int, dict[tuple[int, int, int], int]] = {}
_K4_MASKS: dict[int, list[int]] = {}
_PERMUTE_MAPS: dict[tuple[int, tuple[int, ...]], list[int]] = {}


def triples(n: int) -> list[tuple[int, int, int]]:
    if n not in _TRIPLES:
        _TRIPLES[n] = list(itertools.combinations(range(n), 3))
    return _TRIPLES[n]


def edge_index(n: int) -> dict[tuple[int, int, int], int]:
    if n not in _EDGE_INDEX:
        _EDGE_INDEX[n] = {e: i for i, e in enumerate(triples(n))}
    return _EDGE_INDEX[n]


def k4_masks(n: int) -> list[int]:
    if n not in _K4_MASKS:
        ix = edge_index(n)
        masks = []
        for q in itertools.combinations(range(n), 4):
            m = 0
            for e in itertools.combinations(q, 3):
                m |= 1 << ix[e]
            masks.append(m)
        _K4_MASKS[n] = masks
    return _K4_MASKS[n]


def is_k4free(mask: int, n: int) -> bool:
    return all(mask & f != f for f in k4_masks(n))


def permutation_edge_map(n: int, perm: Sequence[int]) -> list[int]:
    key = (n, tuple(perm))
    if key not in _PERMUTE_MAPS:
        ix = edge_index(n)
        _PERMUTE_MAPS[key] = [
            ix[tuple(sorted((perm[a], perm[b], perm[c])))]
            for a, b, c in triples(n)
        ]
    return _PERMUTE_MAPS[key]


def permute_mask(mask: int, n: int, perm: Sequence[int]) -> int:
    mp = permutation_edge_map(n, perm)
    out = 0
    mm = mask
    while mm:
        lb = mm & -mm
        i = lb.bit_length() - 1
        out |= 1 << mp[i]
        mm ^= lb
    return out


def unlabeled_type_reps(s: int) -> list[int]:
    if s < 3:
        return [0]
    seen: set[int] = set()
    reps: list[int] = []
    perms = list(itertools.permutations(range(s)))
    for mask in range(1 << math.comb(s, 3)):
        if mask in seen or not is_k4free(mask, s):
            continue
        orbit = [permute_mask(mask, s, p) for p in perms]
        seen.update(orbit)
        reps.append(min(orbit))
    return sorted(reps)


def rooted_canon_table(l: int, s: int) -> np.ndarray:
    m = math.comb(l, 3)
    table = np.empty(1 << m, dtype=np.int32)
    free = tuple(range(s, l))
    perms = [tuple(range(s)) + pf for pf in itertools.permutations(free)]
    for mask in range(1 << m):
        table[mask] = min(permute_mask(mask, l, p) for p in perms)
    return table


def root_restriction(mask: int, n: int, root: tuple[int, ...]) -> int:
    ix = edge_index(n)
    out = 0
    for i, local_edge in enumerate(triples(len(root))):
        e = tuple(sorted(root[j] for j in local_edge))
        if (mask >> ix[e]) & 1:
            out |= 1 << i
    return out


def induced_mask(mask: int, n: int, vertices_ordered: tuple[int, ...]) -> int:
    ix = edge_index(n)
    out = 0
    for i, local_edge in enumerate(triples(len(vertices_ordered))):
        e = tuple(sorted(vertices_ordered[j] for j in local_edge))
        if (mask >> ix[e]) & 1:
            out |= 1 << i
    return out


def flags_for_type(s: int, l: int, sigma: int, canon_table: np.ndarray) -> list[int]:
    all_ix = edge_index(l)
    out: set[int] = set()
    for mask in range(1 << math.comb(l, 3)):
        if not is_k4free(mask, l):
            continue
        ok = True
        for i, e in enumerate(triples(s)):
            bit = (mask >> all_ix[e]) & 1
            if bit != ((sigma >> i) & 1):
                ok = False
                break
        if ok:
            out.add(int(canon_table[mask]))
    return sorted(out)


def falling(n: int, s: int) -> int:
    out = 1
    for i in range(s):
        out *= n - i
    return out


@dataclass
class Block:
    s: int
    l: int
    sigma: int
    flags: list[int]
    denominator: int
    counts: np.ndarray  # (num_H,d,d), int32
    A: np.ndarray       # counts / denominator, float64


def build_blocks(N: int, H_reps: list[int], include_s: Iterable[int] | None = None, verbose: bool = True) -> list[Block]:
    if include_s is None:
        include_s = range(0, N - 1)
    blocks: list[Block] = []
    canon_tables: dict[tuple[int, int], np.ndarray] = {}
    for s in include_s:
        l = (N + s) // 2
        r = l - s
        if 2 * r > N - s:
            continue
        key = (l, s)
        if key not in canon_tables:
            canon_tables[key] = rooted_canon_table(l, s)
        ctab = canon_tables[key]
        for sigma in unlabeled_type_reps(s):
            fs = flags_for_type(s, l, sigma, ctab)
            d = len(fs)
            fmap = {f: i for i, f in enumerate(fs)}
            denom = falling(N, s) * math.comb(N - s, r) * math.comb(N - s - r, r)
            counts = np.zeros((len(H_reps), d, d), dtype=np.int32)
            roots = list(itertools.permutations(range(N), s)) if s else [()]
            for hi, H in enumerate(H_reps):
                for root in roots:
                    if s and root_restriction(H, N, root) != sigma:
                        continue
                    remain = tuple(v for v in range(N) if v not in root)
                    for U in itertools.combinations(remain, r):
                        Uset = set(U)
                        rest2 = tuple(v for v in remain if v not in Uset)
                        f1mask = induced_mask(H, N, tuple(root) + tuple(U))
                        i = fmap[int(ctab[f1mask])]
                        for V in itertools.combinations(rest2, r):
                            f2mask = induced_mask(H, N, tuple(root) + tuple(V))
                            j = fmap[int(ctab[f2mask])]
                            counts[hi, i, j] += 1
            if not np.array_equal(counts, counts.transpose(0, 2, 1)):
                raise RuntimeError(f'non-symmetric block s={s} sigma={sigma}')
            A = counts.astype(np.float64) / float(denom)
            blocks.append(Block(s=s, l=l, sigma=sigma, flags=fs, denominator=denom, counts=counts, A=A))
            if verbose:
                print(f'block s={s} l={l} sigma={sigma} d={d} denom={denom}', flush=True)
    return blocks


def objective_coefficients(N: int, H_reps: list[int], lam: float | int) -> tuple[np.ndarray, list[Fraction], np.ndarray, np.ndarray]:
    ix = edge_index(N)
    p_float = np.zeros(len(H_reps))
    q_float = np.zeros(len(H_reps))
    exact: list[Fraction] = []
    lam_frac = Fraction(lam)
    for hi, H in enumerate(H_reps):
        p = Fraction(H.bit_count(), math.comb(N, 3))
        sum_dfall = 0
        for u, v in itertools.combinations(range(N), 2):
            d = 0
            for z in range(N):
                if z in (u, v):
                    continue
                e = tuple(sorted((u, v, z)))
                d += (H >> ix[e]) & 1
            sum_dfall += d * (d - 1)
        q = Fraction(sum_dfall, math.comb(N, 2) * (N - 2) * (N - 3))
        p_float[hi] = float(p)
        q_float[hi] = float(q)
        exact.append(q + lam_frac * p)
    return q_float + float(lam) * p_float, exact, p_float, q_float


def add_cut(highs, g: np.ndarray, lower: float = 0.0, upper: float | None = None) -> None:
    from scipy.optimize._highspy._core import kHighsInf
    if upper is None:
        upper = kHighsInf
    nz = np.flatnonzero(np.abs(g) > 1e-14).astype(np.int32)
    highs.addRow(lower, upper, len(nz), nz, np.ascontiguousarray(g[nz], dtype=np.float64))


def solve_cutting_plane(
    c: np.ndarray,
    blocks: list[Block],
    max_iter: int = 300,
    tol: float = 1e-8,
    add_all_negative: bool = True,
    seed_cuts: list[tuple[int, np.ndarray]] | None = None,
    equality_rows: list[tuple[np.ndarray, float]] | None = None,
    verbose: bool = True,
):
    from scipy.optimize._highspy._core import _Highs, ObjSense, kHighsInf

    nH = len(c)
    highs = _Highs()
    highs.setOptionValue('output_flag', False)
    highs.setOptionValue('presolve', 'on')
    highs.setOptionValue('primal_feasibility_tolerance', 1e-9)
    highs.setOptionValue('dual_feasibility_tolerance', 1e-9)
    highs.addVars(nH, np.zeros(nH), np.full(nH, kHighsInf))
    inds = np.arange(nH, dtype=np.int32)
    highs.changeColsCost(nH, inds, c.astype(np.float64))
    highs.changeObjectiveSense(ObjSense.kMaximize)
    highs.addRow(1.0, 1.0, nH, inds, np.ones(nH))

    if equality_rows:
        for g, rhs in equality_rows:
            add_cut(highs, np.asarray(g, dtype=float), rhs, rhs)

    cut_records: list[tuple[int, np.ndarray]] = []
    seen_cut_hashes: set[tuple[int, bytes]] = set()

    # Diagonal square inequalities.
    for bi, block in enumerate(blocks):
        d = len(block.flags)
        for i in range(d):
            v = np.eye(d)[i]
            g = block.A[:, i, i]
            add_cut(highs, g)
            cut_records.append((bi, v))
            seen_cut_hashes.add((bi, np.round(v, 9).tobytes()))

    if seed_cuts:
        for bi, v0 in seed_cuts:
            v = np.asarray(v0, dtype=float)
            if len(v) != len(blocks[bi].flags):
                continue
            j = int(np.argmax(np.abs(v)))
            if v[j] < 0:
                v = -v
            key = (bi, np.round(v, 9).tobytes())
            if key in seen_cut_hashes:
                continue
            g = np.einsum('i,hij,j->h', v, blocks[bi].A, v, optimize=True)
            add_cut(highs, g)
            cut_records.append((bi, v.copy()))
            seen_cut_hashes.add(key)

    if verbose:
        print('initial cuts', len(cut_records), flush=True)

    history = []
    for it in range(max_iter):
        highs.run()
        model_status = highs.getModelStatus()
        if 'Optimal' not in highs.modelStatusToString(model_status):
            raise RuntimeError(highs.modelStatusToString(model_status))
        sol = highs.getSolution()
        x = np.asarray(sol.col_value, dtype=np.float64)
        bound = float(highs.getObjectiveValue())

        worst = 0.0
        violations = []
        eig_summary = []
        for bi, block in enumerate(blocks):
            M = np.tensordot(x, block.A, axes=(0, 0))
            M = (M + M.T) / 2
            vals, vecs = np.linalg.eigh(M)
            eig_summary.append(float(vals[0]))
            neg_ids = np.where(vals < -tol)[0]
            if len(neg_ids):
                worst = min(worst, float(vals[0]))
                ids = neg_ids if add_all_negative else neg_ids[:1]
                for idx in ids:
                    v = vecs[:, idx]
                    g = np.einsum('i,hij,j->h', v, block.A, v, optimize=True)
                    violations.append((float(vals[idx]), bi, v, g))
        history.append({'iter':it,'bound':bound,'worst_eig':worst,'cuts':len(cut_records),'support':int(np.count_nonzero(x>1e-10))})
        if verbose and (it < 10 or it % 5 == 0 or not violations):
            print(f'iter={it:03d} bound={bound:.12f} worst={worst:.3e} new={len(violations)} cuts={len(cut_records)} support={np.count_nonzero(x>1e-10)}', flush=True)
        if not violations:
            return highs, x, history, cut_records, eig_summary

        violations.sort(key=lambda z: z[0])
        added = 0
        for _, bi, v, g in violations:
            j = int(np.argmax(np.abs(v)))
            if v[j] < 0:
                v = -v
            key = (bi, np.round(v, 9).tobytes())
            if key in seen_cut_hashes:
                continue
            seen_cut_hashes.add(key)
            add_cut(highs, g)
            cut_records.append((bi, v.copy()))
            added += 1
        if added == 0:
            if verbose:
                print('numerical stagnation: no new distinct cuts', flush=True)
            return highs, x, history, cut_records, eig_summary

    if verbose:
        print('max_iter reached', flush=True)
    return highs, x, history, cut_records, eig_summary


def save_solution(path: Path, H_reps, c, p, q, x, history, highs, cuts) -> None:
    np.savez_compressed(
        path,
        H_reps=np.asarray(H_reps, dtype=np.int64),
        c=c,
        p=p,
        q=q,
        x=x,
        history=np.asarray([[h['bound'],h['worst_eig'],h['cuts'],h['support']] for h in history], dtype=float),
        row_dual=np.asarray(highs.getSolution().row_dual, dtype=float),
    )
    with open(str(path)+'.cuts.pkl','wb') as fh:
        pickle.dump(cuts,fh)


def load_reps(path: str | Path) -> list[int]:
    return [int(x) for x in Path(path).read_text().split()]


if __name__ == '__main__':
    import argparse
    ap=argparse.ArgumentParser()
    ap.add_argument('--N',type=int,default=6)
    ap.add_argument('--lambda_',type=float,default=5.0)
    ap.add_argument('--reps',default='/mnt/data/h6_reps.txt')
    ap.add_argument('--out',default='')
    args=ap.parse_args()
    H=load_reps(args.reps)
    print('H reps',len(H))
    t=time.time(); blocks=build_blocks(args.N,H); print('blocks built',time.time()-t)
    c,ce,p,q=objective_coefficients(args.N,H,args.lambda_)
    highs,x,hist,cuts,eigs=solve_cutting_plane(c,blocks)
    out=Path(args.out or f'/mnt/data/flag_sdp_N{args.N}_lambda{args.lambda_:g}.npz')
    save_solution(out,H,c,p,q,x,hist,highs,cuts)
    print('FINAL',float(c@x),'saved',out)
