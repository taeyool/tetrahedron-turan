#!/usr/bin/env python3
"""Build the 49 FullSevenLong coefficient sweeps in bounded batches.

The module prefix comes from full_seven_long_common.py. It is a
resource-control helper, not a
replacement for the headline builds and the axiom audit. Run from any
directory with the pinned lake toolchain available. Lake checks its normal
dependency traces when reusing each module. Source hashes are of LF text.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

from full_seven_long_common import PREFIX, ROOT, SWEEP_COUNT, text_sha


def dependencies(module, found=None):
    found = {} if found is None else found
    path = ROOT / (module.replace(".", "/") + ".lean")
    if module not in found and path.exists():
        found[module] = text_sha(path)
        for name in re.findall(r"^import ([\w.]+)", path.read_text(encoding="utf-8"), re.M):
            dependencies(name, found)
    return found


def build_batches(lake, threads, batch_size, output, start=0, stop=SWEEP_COUNT):
    if not (1 <= batch_size <= SWEEP_COUNT and 1 <= threads and 0 <= start < stop <= SWEEP_COUNT):
        raise ValueError(f"Require positive threads/batch size and 0 <= start < stop <= {SWEEP_COUNT}")
    output.mkdir(parents=True, exist_ok=True)
    report_path = output / f"sweep-report-{start:02d}-{stop-1:02d}.json"
    # Retire a previous success before dependency reads or builds can fail.
    if report_path.exists():
        report_path.replace(output / f"previous-sweep-report-{start:02d}-{stop-1:02d}.json")
    before = dependencies(PREFIX + "TetrahedronOrder7Bound")
    env = dict(os.environ, LEAN_NUM_THREADS=str(threads))
    batches = []

    def run(targets, log_name):
        began = time.monotonic()
        print("Building:", ", ".join(targets), flush=True)
        with (output / log_name).open("w", encoding="utf-8") as log:
            subprocess.run([lake, "build", *targets], cwd=ROOT, env=env,
                           stdout=log, stderr=subprocess.STDOUT, check=True)
        if dependencies(PREFIX + "TetrahedronOrder7Bound") != before:
            raise RuntimeError("Sweep sources or dependencies changed during the build")
        return {"targets": targets, "seconds": time.monotonic() - began,
                "log": log_name,
                "log_sha256": hashlib.sha256((output / log_name).read_bytes()).hexdigest()}

    # Build shared prerequisites before launching a batch of native checks.
    batches.append(run([PREFIX + "TetrahedronOrder7Check"], "sweep-prerequisites.log"))
    for first in range(start, stop, batch_size):
        last = min(first + batch_size, stop)
        batches.append(run([PREFIX + f"TetrahedronOrder7Sweep7_{i:02d}"
                            for i in range(first, last)], f"sweeps-{first:02d}-{last-1:02d}.log"))
    report = {"status": "SWEEPS_PASS", "chain": PREFIX.rstrip("."), "scope": [start, stop],
              "note": "Coefficient sweeps only; the full Lean formalization and audit are separate.",
              "batch_size": batch_size, "lean_num_threads": threads,
              "source_sha256": before, "batches": batches}
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default=shutil.which("lake") or "lake")
    parser.add_argument("--threads", type=int, default=2)
    parser.add_argument("--batch-size", type=int, default=2)
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--stop", type=int, default=SWEEP_COUNT)
    parser.add_argument("--output-dir", type=Path,
                        default=ROOT / ".research-repro/full-seven-long-lean/sweeps")
    args = parser.parse_args()
    build_batches(args.lake, args.threads, args.batch_size, args.output_dir.resolve(), args.start, args.stop)
    print("Requested coefficient sweeps passed. Headline builds and axiom audit remain separate.", flush=True)


if __name__ == "__main__":
    main()
