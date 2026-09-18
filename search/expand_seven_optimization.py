#!/usr/bin/env python3
"""Add selected five-root blocks to the seven-vertex cut-and-column search.

The old snapshots are preserved. Complete pricing covers the same raw universe,
with column equivalence refined by every selected new moment matrix.
"""
from __future__ import annotations

import argparse
import copy
import datetime
import hashlib
import json
from pathlib import Path
import sys
import time

import numpy as np
from scipy.linalg import eigh

import reconstruct_optimization as ro
from five_root_oracle import Oracle5

OLD_DIMS = list(ro.DIMS)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


class ExpandedMaster(ro.Master):
    def __init__(self, oracle, blocks, objective, stationarity, mode, args):
        # Old checkpoint dimensions and dual arity differ from the expanded
        # model. Load them explicitly, preserving columns and LP basis order.
        initial = copy.copy(args)
        initial.resume_checkpoint = None
        initial.warm_dual = None
        initial.warm_columns = None
        initial.seed_certificate = False
        initial.seed_turan = False
        super().__init__(oracle, blocks, objective, stationarity, mode, initial)
        self.args = args
        self.provenance.update({
            "arguments": {k: str(v) if isinstance(v, Path) else v for k, v in vars(args).items()},
            "driver_sha256": digest(__file__),
            "base_driver_sha256": digest(ro.__file__),
            "five_root_type_masks": list(oracle.type_masks),
            "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "oracle_sources_sha256": {name: digest(ro.HERE/name) for name in
                ("five_root_oracle.py", "five_root_oracle.cpp", "optimization_oracle.cpp",
                 "optimization_oracle_tail.inc", "optimization_order8.inc")},
        })
        self.extra_metadata = {"five_root_type_masks": np.asarray(oracle.type_masks, np.int32),
                               "dimensions": np.asarray(ro.DIMS, np.int32)}
        checkpoint = args.resume_checkpoint
        if checkpoint:
            with np.load(checkpoint, allow_pickle=False) as data:
                assert bool(data["stationarity"]) == (mode == "with")
                assert not bool(data.get("stationarity_face", False))
                dimensions = list(map(int, data["dimensions"]))
                assert dimensions == OLD_DIMS or dimensions == ro.DIMS
                if len(dimensions) > len(OLD_DIMS):
                    np.testing.assert_array_equal(data["five_root_type_masks"], oracle.type_masks)
                self.add_columns(data["masks"], preserve_order=True)
                self.add_cuts([(int(b), v[:dimensions[int(b)]])
                               for b, v in zip(data["blocks"], data["vectors"])])
                if ("basis_columns" in data and np.array_equal(data["masks"], self.masks)
                        and len(data["basis_rows"]) == self.h.getNumRow()):
                    basis = self.highspy.HighsBasis()
                    basis.col_status = [self.highspy.HighsBasisStatus(int(v)) for v in data["basis_columns"]]
                    basis.row_status = [self.highspy.HighsBasisStatus(int(v)) for v in data["basis_rows"]]
                    self.provenance["restored_basis"] = self.h.setBasis(basis) == self.highspy.HighsStatus.kOk
                self.provenance["resume_checkpoint_sha256"] = digest(checkpoint)
        dual = args.warm_dual
        if dual is None and checkpoint and checkpoint.name.endswith("_checkpoint.npz"):
            sibling = checkpoint.with_name(checkpoint.name.removesuffix("_checkpoint.npz") + "_best_dual.npz")
            if sibling.exists():
                dual = sibling
        if dual:
            with np.load(dual, allow_pickle=False) as source:
                prior = {k: source[k].copy() for k in source.files}
            assert not np.any(prior.get("face_multipliers", []))
            assert mode == "with" or float(prior["tau"]) == 0
            if "five_root_type_masks" in prior:
                np.testing.assert_array_equal(prior["five_root_type_masks"], oracle.type_masks)
            elif any(f"factors{b}" in prior for b in range(12, len(ro.DIMS))):
                raise ValueError("Expanded dual must identify its five-root types")
            # Seed the saved best directions as well as the checkpoint's latest
            # directions: pruning may have removed some earlier useful rows.
            warm = []
            for b, d in enumerate(ro.DIMS):
                rows = np.asarray(prior.get(f"factors{b}", np.empty((0, d)))).reshape(-1, d)
                prior[f"factors{b}"] = rows
                for v in rows:
                    norm = np.linalg.norm(v)
                    if norm:
                        warm.append((b, v / norm))
                if b >= 12 and f"gram{b-9}" not in prior:
                    # Keep supplied Grams unchanged. Compute missing ones only;
                    # non-BLAS contraction avoids spurious floating-status
                    # warnings seen with this platform's matrix multiply.
                    q = np.einsum("ri,rj->ij", rows, rows, optimize=False)
                    if not np.isfinite(q).all():
                        raise ValueError(f"Nonfinite reconstructed Gram in block {b}")
                    prior[f"gram{b-9}"] = q
            # This occurs after restoring the original basis; HiGHS extends it
            # when the extra rows are added.
            self.add_cuts(warm)
            grams = [prior[f"gram{i}"] for i in range(len(ro.DIMS)-9)]
            values, masks = oracle.price(prior["six"], grams, args.threads, args.price_top)
            self.best_upper = float(values.max())
            self.best_dual = prior
            self.best_dual["global_upper"] = self.best_upper
            self.best_dual.update(self.extra_metadata)
            self.add_columns(masks)
            self.provenance["inherited_best_dual_sha256"] = digest(dual)
            self.provenance["inherited_repriced_upper"] = self.best_upper
        if args.seed_turan:
            self.add_columns(ro.turan_blowup_masks(7))
        if args.warm_columns:
            with np.load(args.warm_columns, allow_pickle=False) as data:
                self.add_columns(data["masks"])
        if args.screen_directions:
            with np.load(args.screen_directions, allow_pickle=False) as data:
                cuts = []
                for b, sigma in enumerate(oracle.type_masks, 12):
                    vectors = data[f"vectors_{sigma}"]
                    values = data[f"eigenvalues_{sigma}"]
                    for j in np.flatnonzero(values < -args.psd_tolerance)[:args.initial_directions_per_type]:
                        v = vectors[:, j]
                        cuts.append((b, v / np.linalg.norm(v)))
                self.add_cuts(cuts)
                self.provenance["screen_directions_sha256"] = digest(args.screen_directions)
                self.provenance["initial_five_root_directions"] = len(cuts)

    def save(self, status):
        if self.best_dual is not None:
            self.best_dual.update(self.extra_metadata)
        super().save(status)
        path = self.args.output_dir / f"order7_{self.mode}_stationarity.json"
        data = json.loads(path.read_text())
        data["five_root_type_masks"] = list(self.oracle.type_masks)
        data["eigensolver"] = "scipy.linalg.eigh, lowest max_cuts eigenpairs per block"
        temporary = path.with_suffix(".json.tmp")
        temporary.write_text(json.dumps(data, indent=2) + "\n")
        temporary.replace(path)
        if self.args.checkpoint:
            path = self.args.output_dir / f"order7_{self.mode}_checkpoint.npz"
            with np.load(path, allow_pickle=False) as saved:
                data = {k: saved[k].copy() for k in saved.files}
            data.update(self.extra_metadata)
            ro.atomic_savez(path, **data)

    def run(self):
        start = time.monotonic()
        y = moments = None
        status = "running"
        for iteration in range(self.args.max_iter):
            solve_start = time.monotonic()
            self.h.run()
            solve_seconds = time.monotonic() - solve_start
            if self.h.getModelStatus() != self.highspy.HighsModelStatus.kOptimal:
                status = self.h.modelStatusToString(self.h.getModelStatus())
                break
            sol = self.h.getSolution()
            y = np.asarray(sol.col_value)
            snapshot_masks = np.asarray(self.masks, np.uint64)
            x = self.deck.T @ y
            flat = self.feat.T @ y
            moments = [np.einsum("h,hij->ij", x, b) for b in self.blocks]
            moments += [flat[a:b].reshape(d, d)
                        for a, b, d in zip(ro.OFFSETS[:-1], ro.OFFSETS[1:], ro.DIMS[9:])]
            minima, negative = [], []
            eigen_start = time.monotonic()
            for b, matrix in enumerate(moments):
                vals, vec = eigh((matrix + matrix.T)/2,
                                 subset_by_index=(0, min(self.args.max_cuts, len(matrix))-1),
                                 check_finite=True, driver="evr")
                minima.append(float(vals[0]))
                negative.extend((float(vals[j]), b, vec[:, j])
                                for j in np.flatnonzero(vals < -self.args.psd_tolerance))
            negative.sort(key=lambda t: t[0])
            row = {"iteration": iteration, "restricted_objective": self.h.getObjectiveValue(),
                   "lp_seconds": solve_seconds, "eigen_seconds": time.monotonic()-eigen_start,
                   "minimum_eigenvalue": min(minima), "block_minimum_eigenvalues": minima,
                   "columns": len(self.masks), "cuts": len(self.cuts),
                   "primal_support": int(np.count_nonzero(y > 1e-9)),
                   "stationarity_residual": float(np.einsum("h,h->", self.stationarity, x))}
            pstart = time.monotonic()
            six, grams, tau, weights = self.dual(sol)
            values, masks = self.oracle.price(six, grams, self.args.threads, self.args.price_top)
            upper = float(values.max())
            gap = upper-row["restricted_objective"]
            row.update({"global_dual_upper": upper, "pricing_gap": gap, "tau": tau,
                        "pricing_seconds": time.monotonic()-pstart})
            if upper < self.best_upper:
                self.best_upper = upper
                self.best_dual = {"six": six, "tau": tau, "global_upper": upper,
                                  "iteration": iteration, "face_multipliers": np.array([]),
                                  **{f"gram{i}": q for i, q in enumerate(grams)}, **self.extra_metadata}
                for b, d in enumerate(ro.DIMS):
                    self.best_dual[f"factors{b}"] = np.asarray([
                        np.sqrt(w)*v for w, (bb, v) in zip(weights, self.cuts) if bb == b and w > 0
                    ]).reshape(-1, d)
            added = self.add_columns(masks[values > row["restricted_objective"]+self.args.price_tolerance])
            row["added_columns"] = added
            if not negative and gap <= self.args.price_tolerance:
                status = "numerical_tolerances_met"
            newcuts = [(b, v) for _, b, v in negative[:self.args.max_cuts]] if gap <= self.args.price_tolerance else []
            row["seconds"] = time.monotonic()-start
            self.history.append(row)
            print(self.mode, {k: v for k, v in row.items() if k != "block_minimum_eigenvalues"}, flush=True)
            self.save(status)
            if status == "numerical_tolerances_met":
                break
            if iteration % 10 == 0:
                self.prune(sol)
            self.add_cuts(newcuts)
            if time.monotonic()-start >= self.args.seconds:
                status = "time_limit"
                break
        else:
            status = "iteration_limit"
        if y is not None:
            ro.atomic_savez(self.args.output_dir/f"order7_{self.mode}_primal.npz",
                            masks=snapshot_masks, weights=y, **self.extra_metadata,
                            **{f"moment{i}": m for i, m in enumerate(moments)})
        self.save(status)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--types", default="", help="Comma-separated canonical five-root type masks; empty is the matched control")
    p.add_argument("--cache", type=Path, required=True)
    p.add_argument("--deps", type=Path)
    p.add_argument("--output-dir", type=Path, required=True)
    p.add_argument("--mode", choices=["with", "without"], default="with")
    p.add_argument("--resume-checkpoint", type=Path)
    p.add_argument("--warm-dual", type=Path)
    p.add_argument("--warm-columns", type=Path)
    p.add_argument("--screen-directions", type=Path)
    p.add_argument("--initial-directions-per-type", type=int, default=8)
    p.add_argument("--seed-turan", action="store_true")
    p.add_argument("--seconds", type=float, default=1800)
    p.add_argument("--max-iter", type=int, default=1000)
    p.add_argument("--threads", type=int, default=2)
    p.add_argument("--price-top", type=int, default=8)
    p.add_argument("--max-cuts", type=int, default=80)
    p.add_argument("--keep-cuts", type=int, default=1800)
    p.add_argument("--psd-tolerance", type=float, default=1e-7)
    p.add_argument("--price-tolerance", type=float, default=1e-7)
    p.add_argument("--lp-solver", choices=["choose", "simplex", "ipm"], default="choose")
    p.add_argument("--checkpoint", action="store_true")
    args = p.parse_args()
    assert args.max_cuts > 0 and args.threads > 0 and args.price_top > 0
    assert args.seconds >= 0 and args.max_iter >= 0
    args.seed_certificate = args.stationarity_face = args.save_dual_history = False
    args.price_first = True
    if args.deps:
        sys.path.insert(0, str(args.deps))
    args.output_dir.mkdir(parents=True, exist_ok=True)
    if (args.output_dir/f"order7_{args.mode}_stationarity.json").exists():
        raise FileExistsError("Choose a fresh output directory to preserve experiment provenance")
    types = [int(s, 0) for s in args.types.split(",") if s.strip()]
    assert len(types) == len(set(types))
    base = ro.Oracle(args.cache)
    oracle = Oracle5(base, types, args.cache)
    ro.DIMS = OLD_DIMS + list(oracle.dimensions)
    ro.OFFSETS = np.cumsum([0] + [d*d for d in ro.DIMS[9:]])
    with np.load(args.cache/"components.npz", allow_pickle=False) as data:
        blocks = [data[f"block{i}"] for i in range(9)]
        objective = data["edge"]/(720*base.cert["scale"]**2)
        stat = data["stat_unscaled"]/60
    started = time.monotonic()
    master = ExpandedMaster(oracle, blocks, objective, stat, args.mode, args)
    master.provenance["initialization_seconds"] = time.monotonic()-started
    master.provenance["budget_note"] = "The seconds budget covers the run loop; initialization and inherited-dual repricing are recorded separately."
    master.run()


if __name__ == "__main__":
    main()
