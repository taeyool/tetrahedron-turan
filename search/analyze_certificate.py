#!/usr/bin/env python3
"""Reproduce certificate diagnostics for the paper's discovery-method audit.

This is an analysis tool, not part of the Lean proof or the released verifier.
Run from any directory: python search/analyze_certificate.py
Only NumPy is required. All coefficient evaluations use integer arithmetic.
"""
from __future__ import annotations

import argparse
import hashlib
import functools
import itertools
import json
import sys
from fractions import Fraction
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
CERT = ROOT / "certificate"
sys.path.insert(0, str(CERT))
import flag_sdp_hyper3 as fs
from verify_K4_turan_order7_certificate import gram, stat_numerators


def rebuild_components(cert):
    """Six-vertex edge, square and stationarity numerators over 720 scale^2."""
    scale = int(cert["scale"])
    reps = cert["H_representatives"]
    blocks = fs.build_blocks(6, reps, verbose=False)
    edge = np.array([bin(h).count("1") * 36 * scale**2 for h in reps], dtype=np.int64)
    squares = np.zeros(len(reps), dtype=np.int64)
    for block, factors, meta in zip(blocks, cert["order6_factors_by_block"], cert["order6_blocks"]):
        assert block.flags == meta["flags"] and block.denominator == meta["denominator"]
        if not factors:
            continue
        q = gram(factors, len(block.flags))
        # Confirm the conservative product-sum bound fits signed int64.
        assert int(np.max(np.abs(q))) * int(np.max(block.counts.sum(axis=(1, 2)))) < 2**63
        squares += (720 // block.denominator) * np.einsum("hij,ij->h", block.counts.astype(np.int64), q)
    stat = int(cert["stationarity"]["tau_numerator"]) * stat_numerators(reps) * 12
    return blocks, edge, squares, stat


def root_permutations(flags):
    lookup = {f: i for i, f in enumerate(flags)}
    canon = fs.rooted_canon_table(5, 3)
    return [np.array([lookup[int(canon[fs.permute_mask(f, 5, p + (3, 4))])] for f in flags])
            for p in itertools.permutations(range(3))]


def root_gram(cert, sigma):
    flags = fs.flags_for_type(3, 5, sigma, fs.rooted_canon_table(5, 3))
    field = "order7_s3_edge_factors" if sigma else "order7_s3_nonedge_factors"
    q = gram(cert[field], len(flags))
    # Sum, rather than average: allows unordered roots in the audit oracle.
    orbit_sum = sum(q[np.ix_(p, p)] for p in root_permutations(flags))
    return flags, q, orbit_sum


@functools.lru_cache(maxsize=1)
def six_class_lookup(reps):
    lookup = {}
    for p in itertools.permutations(range(6)):
        for r, h in enumerate(reps):
            lookup[fs.permute_mask(h, 6, p)] = r
    return lookup


def components_at(mask, cert, six, root_data):
    """Independent direct counting, with all ordered roots, at one raw mask."""
    assert fs.is_k4free(mask, 7)
    lookup = six_class_lookup(tuple(cert["H_representatives"]))
    totals = [0] * 6
    for v in range(7):
        h = fs.induced_mask(mask, 7, tuple(w for w in range(7) if w != v))
        i = lookup[h]
        for j in range(3):
            totals[j] += int(six[j][i])
    q1 = gram(cert["order7_s1_factors"], 7)
    canon1 = fs.rooted_canon_table(4, 1)
    flags1 = fs.flags_for_type(1, 4, 0, canon1)
    index1 = {f: i for i, f in enumerate(flags1)}
    for r in range(7):
        rem = set(range(7)) - {r}
        for u in itertools.combinations(sorted(rem), 3):
            v = tuple(sorted(rem - set(u)))
            i = index1[int(canon1[fs.induced_mask(mask, 7, (r,) + u)])]
            j = index1[int(canon1[fs.induced_mask(mask, 7, (r,) + v)])]
            totals[3] += 36 * int(q1[i, j])
    canon3 = fs.rooted_canon_table(5, 3)
    index3 = [{f: i for i, f in enumerate(data[0])} for data in root_data]
    for roots in itertools.permutations(range(7), 3):
        rem = set(range(7)) - set(roots)
        sig = fs.root_restriction(mask, 7, roots)
        q = root_data[sig][1]
        for u in itertools.combinations(sorted(rem), 2):
            v = tuple(sorted(rem - set(u)))
            i = index3[sig][int(canon3[fs.induced_mask(mask, 7, roots + u)])]
            j = index3[sig][int(canon3[fs.induced_mask(mask, 7, roots + v)])]
            totals[4 + sig] += 4 * int(q[i, j])
    return totals


def matrix_stats(factors, dimension):
    f = np.asarray(factors, dtype=np.int64).reshape(-1, dimension)
    q = gram(factors, dimension)
    return {"dimension": dimension, "factors": len(factors),
            "factor_entries": int(f.size), "factor_nonzeros": int(np.count_nonzero(f)),
            "gram_entries": int(q.size), "gram_nonzeros": int(np.count_nonzero(q)),
            "numerical_factor_rank": int(np.linalg.matrix_rank(f)) if f.size else 0}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("certificate_diagnostics.json"))
    parser.add_argument("--cache", type=Path, default=ROOT / ".research-repro/cache")
    args = parser.parse_args()
    args.cache.mkdir(parents=True, exist_ok=True)
    path = CERT / "legacy/K4_turan_order7_exact_certificate.json"
    cert = json.loads(path.read_text())
    print("Rebuilding order-six coefficient components", flush=True)
    blocks, edge, squares, stat = rebuild_components(cert)
    roots = [root_gram(cert, sig) for sig in (0, 1)]
    den = int(cert["common_denominator_unreduced"])
    # Cached arrays also feed the exhaustive C++ component audit.
    np.savez(args.cache / "components.npz", edge=edge, squares=squares, stat=stat,
             stat_unscaled=stat_numerators(cert["H_representatives"]),
             **{f"block{i}": b.A for i, b in enumerate(blocks)})
    with (args.cache / "components.bin").open("wb") as out:
        import struct
        out.write(struct.pack("<QqIII", cert["scale"], cert["stationarity"]["tau_numerator"], len(edge), 236, 191))
        for array in (edge, squares, stat):
            np.asarray(array, dtype="<i8").tofile(out)
        q1 = gram(cert["order7_s1_factors"], 7)
        np.asarray([q1[i, j] for i in range(7) for j in range(i, 7)], dtype="<i8").tofile(out)
        for data in roots:
            np.asarray(data[2], dtype="<i8").tofile(out)
    all_reps = [int(x) for x in (CERT / "h6_all_reps.txt").read_text().split()]
    indices = {h: i for i, h in enumerate(all_reps)}
    (args.cache / "support.txt").write_text("\n".join(str(indices[h]) for h in cert["H_representatives"]) + "\n")
    result = {"certificate_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
              "coefficient_denominator": den,
              "component_order": ["edge", "order6", "stationarity", "order7_s1", "order7_s3_nonedge", "order7_s3_edge"],
              "stationarity_convention": "stored tau multiplies S=3D, where D=edge_density^2-root_degree_second_moment",
              "order6": [matrix_stats(f, b["dimension"]) for f, b in zip(cert["order6_factors_by_block"], cert["order6_blocks"])],
              "order7": [matrix_stats(cert[k], n) for k, n in [("order7_s1_factors", 7), ("order7_s3_nonedge_factors", 236), ("order7_s3_edge_factors", 191)]],
              "direct_checks": {}}
    for mask in [cert["example_maximizing_raw_mask"], 27552015]:
        values = components_at(mask, cert, (edge, squares, stat), roots)
        assert sum(values) == cert["bound_numerator_unreduced"]
        result["direct_checks"][str(mask)] = {"numerators": values, "sum": sum(values),
                                               "value": str(Fraction(sum(values), den))}
        print("Direct exact check", mask, values, flush=True)
    ablation_path = Path(__file__).with_name("component_ablation.json")
    if ablation_path.exists():
        ablation = json.loads(ablation_path.read_text())
        retained = {"full": range(6), "no_stationarity": [0, 1, 3, 4, 5],
                    "no_order7": [0, 1, 2], "no_order6": [0, 2, 3, 4, 5],
                    "no_s1": [0, 1, 2, 4, 5], "no_s3_nonedge": [0, 1, 2, 3, 5],
                    "no_s3_edge": [0, 1, 2, 3, 4], "order6_only": [0, 1],
                    "no_s3": [0, 1, 2, 3]}
        for name, item in ablation["variants"].items():
            mask = item["max_mask"]
            key = str(mask)
            if key not in result["direct_checks"]:
                values = components_at(mask, cert, (edge, squares, stat), roots)
                result["direct_checks"][key] = {"numerators": values, "sum": sum(values),
                                               "value": str(Fraction(sum(values), den))}
            values = result["direct_checks"][key]["numerators"]
            assert sum(values[j] for j in retained[name]) == item["max_numerator"], name
        result["ablation_maximizers_directly_checked"] = list(retained)
    for name in ["K4_turan_order7_symmetry_compressed_certificate.json"]:
        compressed = json.loads((CERT / "legacy" / name).read_text())
        result["compression"] = {"factors_before": cert["total_integer_square_factors"],
                                 "factors_after": compressed["total_integer_square_factors"],
                                 "bound_increase": str(Fraction(compressed["bound_fraction"]) - Fraction(cert["bound_fraction"]))}
    rows = cert["order6_source_rows"]
    result["source_rows"] = {"retained_count": len(rows), "largest_row_id": max(r["row"] for r in rows),
                             "smallest_positive_weight": min(r["alpha"] for r in rows),
                             "max_recovery_error": max(r["recovery_error"] for r in rows)}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print("Saved", args.output, flush=True)


if __name__ == "__main__":
    main()
