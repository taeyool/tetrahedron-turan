#!/usr/bin/env python3
"""Round and exhaustively verify selected five-root extensions of the seven-vertex SDP.

The independent verifier retains the original ordered one-/three-root arithmetic.
For five roots it enumerates flags and type automorphisms independently in C++,
then checks all 13,051,375 raw seven-vertex extensions. Python separately checks
all ordered root assignments at the maximizing and representative masks. This
produces a computational certificate, not a new Lean theorem.

Dual NPZ: factors0..11 in the established block order, factors12.. for the sorted
labeled six-vertex flags of each entry of five_root_type_masks, and scalar tau.
Use --certificate FILE instead of a dual to verify existing integer factors.
"""
from __future__ import annotations

import argparse
import copy
from fractions import Fraction
import hashlib
import io
import itertools
import json
import math
from pathlib import Path
import struct
import subprocess
import sys
import time

import numpy as np

from analyze_certificate import CERT, components_at, fs, gram, rebuild_components, root_gram
from portable_raw_oracle import portable_ordered_source

BASE_DIMS = [2, 2, 11, 8, 7, 64, 56, 50, 45, 7, 236, 191]
BASE_FIELDS = ["order7_s1_factors", "order7_s3_nonedge_factors", "order7_s3_edge_factors"]
I64 = 2**63 - 1
I128 = 2**127 - 1
RAW_COUNT = 13_051_375
DEFAULT_CERT = CERT / "legacy/K4_turan_order7_reconstructed_certificate.json"
EXECUTED_SCRIPT_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def flags_for_type(sigma):
    """Enumerate 1,024 possible links; one unlabelled vertex needs no quotient."""
    if not isinstance(sigma, int) or not 0 <= sigma < 1024 or not fs.is_k4free(sigma, 5):
        raise ValueError(f"invalid five-root type {sigma}")
    if sigma != min(fs.permute_mask(sigma, 5, p) for p in itertools.permutations(range(5))):
        raise ValueError(f"type {sigma} must use the minimum labelled mask")
    ix6 = fs.edge_index(6)
    base = sum(1 << ix6[e] for bit, e in enumerate(fs.triples(5)) if sigma & (1 << bit))
    links = [ix6[(a, b, 5)] for a, b in itertools.combinations(range(5), 2)]
    candidates = [base | sum(1 << links[i] for i in range(10) if ext & (1 << i))
                  for ext in range(1024)]
    return sorted(mask for mask in candidates if fs.is_k4free(mask, 6))


def integer_factors(rows, dimension):
    if not isinstance(rows, list) or any(not isinstance(row, list) or len(row) != dimension for row in rows):
        raise ValueError(f"factor rows must have dimension {dimension}")
    if any(type(v) is not int or not -I64 <= v <= I64 for row in rows for v in row):
        raise ValueError("factor entries must be signed 64-bit integers")
    return sum(max((abs(v) for v in row), default=0)**2 for row in rows)


def five_gram_data(cert):
    result = []
    seen = set()
    for block in cert.get("order7_s5_blocks", []):
        sigma = block["type_mask"]
        if sigma in seen:
            raise ValueError("duplicate five-root types")
        seen.add(sigma)
        flags = flags_for_type(sigma)
        if block["flags"] != flags or block["dimension"] != len(flags) or block["denominator"] != 5040:
            raise ValueError("five-root flag order, dimension, or denominator mismatch")
        bound = integer_factors(block["factors"], len(flags))
        aut = sum(fs.permute_mask(sigma, 5, p) == sigma for p in itertools.permutations(range(5)))
        if aut * bound > I64:
            raise OverflowError("automorphism-summed five-root Gram may overflow int64")
        result.append((sigma, flags, gram(block["factors"], len(flags)), bound, aut))
    return result


def validate_arithmetic(cert):
    baseline = json.loads(DEFAULT_CERT.read_text())
    for key in ("H_representatives", "order6_blocks"):
        if cert.get(key) != baseline[key]:
            raise ValueError(f"{key} must match the original complete ordered six-vertex model")
    scale = cert["scale"]
    tau = cert["stationarity"]["tau_numerator"]
    if type(scale) is not int or scale <= 0 or scale > I64:
        raise ValueError("invalid positive integer scale")
    if type(tau) is not int or abs(tau) > I64 or cert["stationarity"]["tau_denominator"] != scale**2:
        raise ValueError("invalid stationarity integer coefficient")
    factors = cert["order6_factors_by_block"] + [cert[k] for k in BASE_FIELDS]
    if len(factors) != 12:
        raise ValueError("expected nine six-vertex and three original seven-vertex blocks")
    bounds = [integer_factors(f, d) for f, d in zip(factors, BASE_DIMS)]
    if any(6*b > I64 for b in bounds):
        raise OverflowError("original root-orbit Gram may overflow int64")
    if 720*(scale**2 + sum(bounds[:9])) + 8640*abs(tau) > I64:
        raise OverflowError("six-vertex coefficient arithmetic may overflow int64")
    five = five_gram_data(cert)
    # The unsigned support/deck fields and every int64 coefficient have bounds
    # above. This additionally bounds signed128 accumulation and denominator.
    if 7*I64 + 5040*sum(bounds[9:] + [b for _, _, _, b, _ in five]) > I128 or 5040*scale**2 > I128:
        raise OverflowError("exhaustive numerator or denominator may overflow int128")
    return factors, five


def five_at(mask, five):
    """Independent direct sum over all 7P5 ordered roots and both complements."""
    if not fs.is_k4free(mask, 7):
        raise ValueError("check mask is not K4-free")
    lookup = {sigma: ({flag: i for i, flag in enumerate(flags)}, q) for sigma, flags, q, _, _ in five}
    totals = {str(sigma): 0 for sigma, *_ in five}
    for roots in itertools.permutations(range(7), 5):
        sigma = fs.root_restriction(mask, 7, roots)
        if sigma not in lookup:
            continue
        ids, q = lookup[sigma]
        outside = tuple(v for v in range(7) if v not in roots)
        a = ids[fs.induced_mask(mask, 7, roots + (outside[0],))]
        b = ids[fs.induced_mask(mask, 7, roots + (outside[1],))]
        totals[str(sigma)] += int(q[a, b]) + int(q[b, a])
    return totals


def generate_verifier():
    source = portable_ordered_source((CERT / "exact_certificate_raw_oracle.cpp").read_text())
    def replace(old, new):
        nonlocal source
        if source.count(old) != 1:
            raise ValueError(f"original verifier template changed: {old}")
        source = source.replace(old, new)
    replace("struct ThreadBest{", Path(__file__).with_name("five_root_exact_oracle.hpp").read_text() + "\nstruct ThreadBest{")
    replace(" auto t6=triples(6),t7=triples(7);", " FiveExact five(cf);\n auto t6=triples(6),t7=triples(7);")
    replace("   best[tid].count++;", "   num += five.value(m7);\n   best[tid].count++;")
    replace(' cerr<<"raw "', ''' o<<"five_at_max "<<i128str(five.value(ans.mask))<<"\\n";
 for(size_t i=0;i<five.check_masks.size();++i) o<<"five_check_"<<i<<" "<<i128str(five.value(five.check_masks[i]))<<"\\n";
 cerr<<"raw "''')
    return source


def round_dual(path, scale, factorization, tolerance, requested_types=None):
    raw = path.read_bytes()
    source = np.load(io.BytesIO(raw), allow_pickle=False)
    if "face_multipliers" in source and np.any(source["face_multipliers"]):
        raise ValueError("nonzero face multipliers require a separate PSD conversion")
    types = [int(t) for t in source["five_root_type_masks"]] if "five_root_type_masks" in source else []
    if requested_types is not None:
        if types and types != requested_types:
            raise ValueError("explicit type order disagrees with dual metadata")
        types = requested_types
    if len(types) != len(set(types)):
        raise ValueError("duplicate five-root types")
    flag_lists = [flags_for_type(sigma) for sigma in types]
    dims = BASE_DIMS + list(map(len, flag_lists))
    if "dimensions" in source and list(source["dimensions"]) != dims:
        raise ValueError("dual dimensions disagree with independently enumerated flags")
    expected = {f"factors{i}" for i in range(len(dims))}
    if {key for key in source.files if key.startswith("factors")} != expected:
        raise ValueError("dual factor fields do not match the declared blocks")
    factors, original_counts = [], []
    for i, d in enumerate(dims):
        rows = np.asarray(source[f"factors{i}"], dtype=float)
        if rows.ndim != 2 or rows.shape[1] != d or not np.isfinite(rows).all():
            raise ValueError(f"invalid factors{i}")
        original_counts.append(len(rows))
        if factorization == "svd" and len(rows):
            _, singular, right = np.linalg.svd(rows, full_matrices=False)
            keep = singular > tolerance*singular[0]
            rows = singular[keep, None]*right[keep]
        scaled = np.rint(rows*scale)
        if not np.isfinite(scaled).all() or np.max(np.abs(scaled), initial=0) >= 2**63:
            raise OverflowError("rounded factors exceed signed64")
        factors.append(scaled.astype(np.int64).tolist())
    tau_float = float(source["tau"])
    if not math.isfinite(tau_float):
        raise ValueError("nonfinite stationarity coefficient")
    cert = copy.deepcopy(json.loads(DEFAULT_CERT.read_text()))
    cert["scale"] = scale
    cert["order6_factors_by_block"] = factors[:9]
    cert.update(dict(zip(BASE_FIELDS, factors[9:12])))
    cert["stationarity"].update(tau_numerator=round(tau_float*scale**2), tau_denominator=scale**2)
    cert["stationarity"]["tau_decimal"] = cert["stationarity"]["tau_numerator"]/scale**2
    cert["order7_s5_blocks"] = [dict(type_mask=sigma, dimension=len(flags), flags=flags,
                                         denominator=5040, factors=factors[12+i])
                                   for i, (sigma, flags) in enumerate(zip(types, flag_lists))]
    for key in ("rounding_thresholds", "source_numerical_dual", "status_note", "maximizer_note",
                "exact_verification", "order6_source_rows"):
        cert.pop(key, None)
    cert["reconstruction"] = dict(source_dual=str(path), source_dual_sha256=hashlib.sha256(raw).hexdigest(),
                                  formalized_in_Lean=False, factorization=factorization,
                                  original_factor_counts=original_counts,
                                  svd_relative_tolerance=tolerance if factorization == "svd" else None,
                                  stationarity_used=bool(cert["stationarity"]["tau_numerator"]))
    return cert


def verify(cert, cache, threads, extra_masks=(), cross_check_pricing=False):
    if sys.byteorder != "little":
        raise RuntimeError("binary oracle input currently requires a little-endian machine")
    factors, five = validate_arithmetic(cert)
    _, edge, squares, stat = rebuild_components(cert)
    roots = [root_gram(cert, sigma) for sigma in (0, 1)]
    q1 = gram(factors[9], 7)
    checks = list(dict.fromkeys([0, 1, 27552015, int(cert["example_maximizing_raw_mask"]), *extra_masks]))
    if len(checks) > 100 or any(type(m) is not int or not 0 <= m < 2**35 or not fs.is_k4free(m, 7) for m in checks):
        raise ValueError("invalid representative check masks")
    binary = cache / "candidate.bin"
    with binary.open("wb") as out:
        out.write(struct.pack("<QqIII", cert["scale"], cert["stationarity"]["tau_numerator"], len(edge), 236, 191))
        for array in (edge+squares+stat, [q1[i, j] for i in range(7) for j in range(i, 7)], roots[0][1], roots[1][1]):
            np.asarray(array, dtype="<i8").tofile(out)
        out.write(struct.pack("<I", len(five)))
        for sigma, flags, q, _, _ in five:
            out.write(struct.pack("<HI", sigma, len(flags)))
            np.asarray(flags, dtype="<u4").tofile(out)
            np.asarray(q, dtype="<i8").tofile(out)
        out.write(struct.pack("<I", len(checks)))
        np.asarray(checks, dtype="<u8").tofile(out)
    all_reps = list(map(int, (CERT / "h6_all_reps.txt").read_text().split()))
    lookup = {h: i for i, h in enumerate(all_reps)}
    support = cache / "support.txt"
    support.write_text("".join(f"{lookup[h]}\n" for h in cert["H_representatives"]))
    cpp = cache / "independent_exact_oracle.cpp"
    cpp.write_text(generate_verifier())
    exe = cache / "independent_exact_oracle"
    subprocess.run(["c++", "-O3", "-std=c++17", "-pthread", str(cpp), "-o", str(exe)], check=True)
    result_path = cache / "exact_result.txt"
    # A failed C++ output stream must not leave a previous run's result usable.
    result_path.unlink(missing_ok=True)
    started = time.time()
    subprocess.run([str(exe), str(CERT / "h6_all_reps.txt"), str(support), str(binary), str(result_path), str(threads)], check=True)
    fields = dict(line.split(maxsplit=1) for line in result_path.read_text().splitlines())
    numerator, denominator, maximizing = (int(fields[k]) for k in ("max_numerator", "denominator", "max_mask"))
    if int(fields["raw_count"]) != RAW_COUNT or denominator != 5040*cert["scale"]**2:
        raise ValueError("incomplete exhaustive enumeration or wrong denominator")
    cross_check = None
    if cross_check_pricing:
        import five_root_oracle
        import reconstruct_optimization
        q1_upper = np.asarray([q1[i, j] for i in range(7) for j in range(i, 7)], dtype=np.int64)
        q3_orbit = np.concatenate([data[2].ravel() for data in roots])
        if 72*max(map(abs, map(int, q1_upper)), default=0) > I64 or 8*max(map(abs, map(int, q3_orbit)), default=0) > I64:
            raise OverflowError("independent pricing coefficient weighting would overflow int64")
        base = reconstruct_optimization.Oracle(cache / "pricing-cross-check")
        oracle = five_root_oracle.Oracle5(base, [sigma for sigma, *_ in five], cache / "pricing-cross-check")
        values, masks = oracle.price_exact(edge+squares+stat, 72*q1_upper, 8*q3_orbit,
                                          [data[2] for data in five], threads=threads, top=1)
        highest = int(np.argmax(values))
        if int(values[highest]) != numerator:
            raise ValueError("independent optimization pricing full scan disagrees")
        other_max = int(masks[highest])
        if other_max not in checks:
            checks.append(other_max)
        cross_check = dict(complete_raw_count=int(oracle.raw_count), maximum_numerator=int(values[highest]),
                           maximizing_mask=other_max,
                           source_sha256={name: sha256(Path(__file__).with_name(name)) for name in
                                          ("five_root_oracle.py", "five_root_oracle.cpp", "optimization_oracle.cpp",
                                           "optimization_oracle_tail.inc", "optimization_order8.inc")})
    direct = {}
    for mask in dict.fromkeys(checks + [maximizing]):
        added = five_at(mask, five)
        check_key = f"five_check_{checks.index(mask)}" if mask in checks else None
        expected = int(fields["five_at_max"]) if mask == maximizing else (int(fields[check_key]) if check_key in fields else None)
        if expected is not None and sum(added.values()) != expected:
            raise ValueError(f"independent ordered five-root check disagrees at {mask}")
        original = components_at(mask, cert, (edge, squares, stat), roots)
        total = sum(original) + sum(added.values())
        if total > numerator or (mask in [maximizing, cross_check["maximizing_mask"] if cross_check else None] and total != numerator):
            raise ValueError(f"independent full coefficient check disagrees at {mask}")
        direct[str(mask)] = dict(original_component_numerators=original,
                                 five_root_numerators=added, total_numerator=total)
    return dict(numerator=numerator, denominator=denominator, maximizing=maximizing,
                raw_count=RAW_COUNT, elapsed_seconds=time.time()-started,
                maximizer_deck=list(map(int, fields["deck"].split())), direct_checks=direct,
                oracle_source_sha256=sha256(cpp), candidate_binary_sha256=sha256(binary),
                independent_pricing_full_scan=cross_check)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("dual", type=Path, nargs="?")
    parser.add_argument("--certificate", type=Path, help="verify existing integer certificate instead of rounding a dual")
    parser.add_argument("--types", help="comma-separated canonical type masks in factors12+ order")
    parser.add_argument("--scale", type=int, default=2_000_000)
    parser.add_argument("--factorization", choices=["cuts", "svd"], default="cuts")
    parser.add_argument("--svd-relative-tolerance", type=float, default=1e-7)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cache", type=Path, required=True, help="separate working directory per simultaneous candidate")
    parser.add_argument("--threads", type=int, default=4)
    parser.add_argument("--cross-check-pricing", action="store_true",
                        help="also require agreement with the optimization oracle's full integer scan")
    args = parser.parse_args()
    if bool(args.dual) == bool(args.certificate):
        parser.error("provide exactly one dual or --certificate")
    if args.scale <= 0 or args.threads <= 0 or not 0 <= args.svd_relative_tolerance < 1:
        parser.error("invalid scale, thread count, or SVD tolerance")
    args.cache.mkdir(parents=True, exist_ok=True)
    types = None if args.types is None else [int(t) for t in args.types.split(",") if t.strip()]
    if args.certificate:
        if types is not None:
            parser.error("--types applies only to numerical duals")
        input_certificate_bytes = args.certificate.read_bytes()
        input_certificate_sha256 = hashlib.sha256(input_certificate_bytes).hexdigest()
        cert = json.loads(input_certificate_bytes)
        original_bound = Fraction(cert["bound_fraction"])
    else:
        cert = round_dual(args.dual, args.scale, args.factorization, args.svd_relative_tolerance, types)
        original_bound = None
    result = verify(cert, args.cache, args.threads, cross_check_pricing=args.cross_check_pricing)
    bound = Fraction(result["numerator"], result["denominator"])
    if original_bound is not None and original_bound != bound:
        raise ValueError("integer certificate's claimed bound disagrees with the full scan")
    if args.certificate:
        if cert["bound_numerator_unreduced"] != result["numerator"] or cert["common_denominator_unreduced"] != result["denominator"]:
            raise ValueError("integer certificate's unreduced bound disagrees with the full scan")
        claimed_maximum = result["direct_checks"][str(cert["example_maximizing_raw_mask"])]["total_numerator"]
        if claimed_maximum != result["numerator"]:
            raise ValueError("integer certificate's alleged maximizing mask does not attain its bound")
    factors, five = validate_arithmetic(cert)
    counts = [len(f) for f in factors]
    five_counts = [len(b["factors"]) for b in cert.get("order7_s5_blocks", [])]
    tau = Fraction(cert["stationarity"]["tau_numerator"], cert["scale"]**2)
    cert.update(bound_fraction=str(bound), bound_decimal=float(bound),
                bound_numerator_unreduced=result["numerator"], common_denominator_unreduced=result["denominator"],
                example_maximizing_raw_mask=result["maximizing"], raw_labeled_extensions_checked=RAW_COUNT,
                theorem=f"pi(K4^(3)) <= {bound}", total_integer_square_factors=sum(counts+five_counts),
                factor_counts=dict(order6=sum(counts[:9]), s1=counts[9], s3_nonedge=counts[10], s3_edge=counts[11],
                                   s5_by_type={str(b["type_mask"]): len(b["factors"]) for b in cert.get("order7_s5_blocks", [])}),
                maximizing_deletion_deck_support_indices=result["maximizer_deck"],
                gap_below_comparison_fraction=str(Fraction(1123, 2000)-bound),
                gap_below_comparison_decimal=float(Fraction(1123, 2000)-bound),
                gap_above_5_over_9_fraction=str(bound-Fraction(5, 9)),
                gap_above_5_over_9_decimal=float(bound-Fraction(5, 9)),
                mathematical_scope="Nonnegative flag squares" + (" plus tau*S for a stationary edge-density maximizer." if tau else ", without stationarity."))
    cert["exact_verification"] = dict(arithmetic="Exact integer Gram construction and signed128 exhaustive coefficient scan.",
        independent_five_root_construction="C++ independently enumerates all labeled six-vertex flags and root automorphisms.",
        independent_ordered_root_checks="Python enumerates every ordered one-, three-, and five-root product at the maximizing and representative masks.",
        verifier_script_sha256=EXECUTED_SCRIPT_SHA256, **result)
    cert.setdefault("reconstruction", {})["formalized_in_Lean"] = False
    if args.certificate:
        cert["reconstruction"]["input_integer_certificate_sha256"] = input_certificate_sha256
        cert["reconstruction"]["verification_note"] = "This verification run does not establish a Lean theorem; the input certificate may independently have one."
    summary = dict(bound_fraction=str(bound), decimal=float(bound), raw_count=RAW_COUNT,
                   five_root_types=[sigma for sigma, *_ in five], integer_square_factors=sum(counts+five_counts),
                   factor_counts=counts+five_counts, stationarity_multiplier_fraction=str(tau),
                   maximizer=result["maximizing"], formalized_in_Lean=False,
                   below_previous_480_bound=bound < Fraction(469677514672523, 840000000000000),
                   exact_verification=result)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(cert, indent=2)+"\n")
    args.output.with_suffix(".summary.json").write_text(json.dumps(summary, indent=2)+"\n")
    print(json.dumps({k: v for k, v in summary.items() if k != "exact_verification"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
