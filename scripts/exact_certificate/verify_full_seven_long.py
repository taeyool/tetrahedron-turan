#!/usr/bin/env python3
"""Build and audit the FullSevenLong Lean headlines, retaining a hashed record.

Every pinned value (certificate, hash, bound, namespace, targets, audit file,
generators) comes from full_seven_long_common.py. It runs the existing
generated sources; it does not regenerate them or trust an external
numerical checker. A report with status PASS is written only after the
complete build (all 49 sweeps and both headlines), the axiom audit, the
literal-fraction witnesses and the source-stability checks all succeed. Source hashes are of LF-normalized text; the certificate
is hashed as raw bytes.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

from build_full_seven_long_sweeps import build_batches
from full_seven_long_common import (AUDIT, BOUND, CERT, CERT_SHA, FIVE_ROOT_MODULES, GENERATED,
                                    HEADLINE_TARGETS as TARGETS, LEAN_BOUND, NS, ROOT,
                                    SWEEP_COUNT, SWEEP_TARGETS, TEMPLATES, TOTAL_ENTRIES,
                                    TOTAL_FACTORS, VERIFICATION, raw_sha, text_sha)

STANDARD = {"propext", "Classical.choice", "Quot.sound"}
COMPILED = STANDARD | {"Lean.ofReduceBool", "Lean.trustCompiler"}
# Local support files read or imported by the generators. These are frozen at
# verification time, not asserted to be their historical generation versions.
GENERATION_SUPPORT = [
    "search/analyze_certificate.py",
    "search/exactify_five_root.py",
    "certificate/flag_sdp_hyper3.py",
    "certificate/verify_K4_turan_order7_certificate.py",
    "certificate/portable_raw_oracle.py",
    "certificate/legacy/K4_turan_order7_reconstructed_certificate.json",
    "certificate/legacy/K4_turan_order7_symmetry_compressed_certificate.json",
]
SCRIPTS = Path(__file__).resolve().parent


def source_hashes(targets):
    seen = {}

    def visit(module):
        path = ROOT / (module.replace(".", "/") + ".lean")
        if module in seen or not path.exists():
            return
        seen[module] = text_sha(path)
        for dep in re.findall(r"^import ([\w.]+)", path.read_text(encoding="utf-8"), re.M):
            visit(dep)

    for target in targets:
        visit(target)
    return seen


def parse_axioms(text):
    footprints = {name: {a.strip() for a in axioms.split(",") if a.strip()}
                  for name, axioms in re.findall(
                      r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, re.S)}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
        footprints[name] = set()
    return footprints


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default=shutil.which("lake") or "lake")
    parser.add_argument("--threads", type=int, default=4)
    parser.add_argument("--sweep-batch-size", type=int, default=2,
                        help="maximum sweep targets per Lake invocation")
    parser.add_argument("--output-dir", type=Path, default=VERIFICATION)
    parser.add_argument("--check-only", action="store_true",
                        help="run the input, manifest and source preflight checks, then stop "
                             "without building or writing a report")
    args = parser.parse_args()
    if args.threads < 1:
        parser.error("--threads must be positive")
    if not 1 <= args.sweep_batch_size <= SWEEP_COUNT:
        parser.error(f"--sweep-batch-size must be between 1 and {SWEEP_COUNT}")
    output = args.output_dir.resolve()
    report_path = output / "formalization.json"
    if not args.check_only:
        output.mkdir(parents=True, exist_ok=True)
        # Retire a prior success before any acceptance preflight can fail, including
        # the optimized-Python guard, missing inputs, and mismatched source hashes.
        if report_path.exists():
            report_path.replace(output / "previous-formalization.json")
    if not __debug__:
        raise RuntimeError("Run without -O or PYTHONOPTIMIZE; verification assertions must be enabled")
    certificate_bytes = CERT.read_bytes()
    assert hashlib.sha256(certificate_bytes).hexdigest() == CERT_SHA, "The pinned certificate changed"
    certificate = json.loads(certificate_bytes)
    assert certificate["bound_fraction"] == BOUND
    assert certificate["total_integer_square_factors"] == TOTAL_FACTORS
    manifest_paths = [GENERATED / "manifest.json", GENERATED / "five_root_manifest.json"]
    main_manifest, five_manifest = [json.loads(p.read_text(encoding="utf-8")) for p in manifest_paths]
    for manifest, field in [(main_manifest, "generated_sha256"), (five_manifest, "outputs")]:
        assert manifest["certificate_sha256"] == CERT_SHA, "Generation used a different certificate"
        assert manifest["chain"] == NS, "The manifests describe a different chain"
        for name, digest in manifest[field].items():
            assert text_sha(GENERATED / name) == digest, "Generated source changed: " + name
    assert main_manifest["bound"] == BOUND
    assert main_manifest["total_integer_square_factors"] == TOTAL_FACTORS
    assert main_manifest["total_integer_entries"] == TOTAL_ENTRIES
    assert sorted(main_manifest["handwritten_modules"]) == sorted(n + ".lean" for n in FIVE_ROOT_MODULES)
    for name, entry in main_manifest["templates"].items():
        template = ROOT / entry["template"]
        assert template.parent == TEMPLATES and template.stem == name, name
        assert text_sha(template) == entry["template_sha256"], name
    for name, digest in main_manifest["handwritten_modules"].items():
        assert text_sha(GENERATED / name) == digest, "Handwritten module changed: " + name
    generators = [SCRIPTS / name for name in
                  ["derive_full_seven_long_chain.py", "derive_full_seven_long_five_root.py",
                   "full_seven_assembly.py", "full_seven_long_common.py"]]
    assert text_sha(generators[0]) == main_manifest["generator_sha256"]
    assert text_sha(generators[1]) == five_manifest["generator_sha256"]
    assert text_sha(generators[2]) == main_manifest["assembly_transform_sha256"]
    assert text_sha(generators[3]) == main_manifest["common_sha256"] == five_manifest["common_sha256"]
    assert text_sha(AUDIT) == main_manifest["axiom_audit_sha256"], "The generated axiom audit changed"
    # The audit and the generated sweeps must name the pinned targets.
    audit_text = AUDIT.read_text(encoding="utf-8")
    assert all(f"import {target}\n" in audit_text for target in TARGETS)
    assert audit_text.count(f"({LEAN_BOUND} : ℝ)") == 2
    for target in SWEEP_TARGETS:
        assert (ROOT / (target.replace(".", "/") + ".lean")).exists(), target
    before = source_hashes(TARGETS)
    assert all(target in before for target in SWEEP_TARGETS), "The sweeps are not in the headline closure"
    assert all(target in before for target in TARGETS)
    templates = [ROOT / entry["template"] for _, entry in sorted(main_manifest["templates"].items())]
    auxiliary = [ROOT / "lean-toolchain", ROOT / "lake-manifest.json", ROOT / "lakefile.lean",
                 AUDIT, Path(__file__).resolve(), SCRIPTS / "build_full_seven_long_sweeps.py",
                 *manifest_paths, *generators, *templates,
                 *(ROOT / name for name in GENERATION_SUPPORT)]
    fixed = {p.relative_to(ROOT).as_posix(): text_sha(p) for p in auxiliary}
    fixed[CERT.relative_to(ROOT).as_posix()] = CERT_SHA
    if args.check_only:
        print(f"Preflight passed: {len(before)} modules in the headline closure, "
              f"{len(fixed)} frozen inputs. No build was run and no report was written.")
        return
    started = dt.datetime.now(dt.timezone.utc).isoformat()
    env = dict(os.environ, LEAN_NUM_THREADS=str(args.threads))
    started_commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()

    def run(command, filename):
        print("Running:", " ".join(command), flush=True)
        with (output / filename).open("w", encoding="utf-8") as log:
            subprocess.run(command, cwd=ROOT, env=env, stdout=log,
                           stderr=subprocess.STDOUT, check=True)

    sweep_report = build_batches(args.lake, args.threads, args.sweep_batch_size, output / "sweeps")
    run([args.lake, "build", *TARGETS], "lean-headline.log")
    run([args.lake, "env", "lean", str(AUDIT)], "lean-axioms.log")
    # Independently type-check the pinned fraction for both routes. Names and
    # axiom footprints alone cannot distinguish a stale, weaker theorem.
    witness = output / "PinnedHeadline.lean"
    witness.write_text("".join("import " + target + "\n" for target in TARGETS) + "\n" +
        "".join(f"example : {NS}.tetraTuranDensity ≤ ({LEAN_BOUND} : ℝ) :=\n"
                f"  {NS}.{name}\n\n" for name in
                ["tetraTuranDensity_le_certValue", "tetraTuranDensity_le_certValue_finite"]),
        encoding="utf-8", newline="\n")
    run([args.lake, "env", "lean", str(witness)], "lean-pinned-headline.log")
    assert before == source_hashes(TARGETS), "Lean sources changed during verification"
    after_fixed = {p.relative_to(ROOT).as_posix(): text_sha(p) for p in auxiliary}
    after_fixed[CERT.relative_to(ROOT).as_posix()] = raw_sha(CERT)
    assert fixed == after_fixed, \
        "Build configuration, generation inputs, manifest, audit, or verifier changed during verification"
    assert started_commit == subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    text = (output / "lean-axioms.log").read_text(encoding="utf-8")
    assert "error" not in text.lower(), "The axiom audit reported an error"
    footprints = parse_axioms(text)
    required = ["tetraTuranDensity_le_certValue", "maxDens_eq_exTetra",
                "tendsto_tetraTuranDensity", "edge_le_certBound_of_stationary",
                "columnValue_le_columnBound", "finiteBoost",
                "tetraTuranDensity_le_certValue_finite",
                "turanDensity_le_of_stationary_bound",
                "isDegreeStationary_of_maximizer", "maximizerIsStationary",
                "fiveRootSOS_nonneg", "fiveRootElt_eq_scaled",
                "s5ColumnNum_eq_ordered", "s5ColumnNum_eq_ordered_sum"]
    assert all(NS + "." + name in footprints for name in required), footprints
    assert all(a <= COMPILED for a in footprints.values()), footprints
    for name in ["tetraTuranDensity_le_certValue", "tetraTuranDensity_le_certValue_finite"]:
        assert footprints[NS + "." + name] == COMPILED, footprints
    for name in ["maxDens_eq_exTetra", "tendsto_tetraTuranDensity",
                 "turanDensity_le_of_stationary_bound",
                 "isDegreeStationary_of_maximizer", "maximizerIsStationary"]:
        assert footprints[NS + "." + name] == STANDARD, footprints
    assert footprints["FlagAlgebras.Core.isStationary_of_maximizer"] == STANDARD
    for name in ["FlagAlgebras.Core.Tetrahedron.gamma56_eq_rooting5040",
                 "FlagAlgebras.Core.sum_injective_filter_eq_rootSubset_perm"]:
        assert footprints[name] == STANDARD, footprints
    report = {
        "status": "PASS", "chain": NS,
        "headline": NS + ".tetraTuranDensity_le_certValue",
        "headline_finite": NS + ".tetraTuranDensity_le_certValue_finite",
        "build_targets": TARGETS, "sweep_targets": SWEEP_TARGETS,
        "certificate": CERT.relative_to(ROOT).as_posix(),
        "certificate_sha256": CERT_SHA,
        "bound_fraction": BOUND,
        "total_integer_square_factors": TOTAL_FACTORS,
        "total_integer_entries": TOTAL_ENTRIES,
        "lean_version": subprocess.check_output(
            [args.lake, "env", "lean", "--version"], cwd=ROOT, text=True).strip(),
        "source_base_commit": started_commit,
        "repository_module_count": len(before), "repository_source_sha256": before,
        "verification_inputs_sha256": fixed,
        "hash_convention": "certificate: raw bytes; Lean, Python and JSON sources: UTF-8 text with CRLF normalized to LF",
        "verification_inputs_note":
            "These hashes freeze local build configuration, templates, generator support inputs, "
            "and audit files during verification. They do not establish historical generator-time "
            "versions or replay generation. Lean builds, literal-statement checks, and the axiom "
            "audit establish proof acceptance; regeneration evidence is separate.",
        "axioms": {name: sorted(a) for name, a in footprints.items()},
        "pinned_statement_source_sha256": text_sha(witness),
        "verification_logs_sha256": {name: raw_sha(output / name) for name in
                                     ["lean-headline.log", "lean-axioms.log", "lean-pinned-headline.log"]},
        "started_utc": started, "completed_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "lean_num_threads": args.threads,
        "sweep_batch_size": args.sweep_batch_size,
        "sweep_verification": sweep_report,
        "timing_note": "Lake may reuse prerequisites; elapsed time is not a clean-build benchmark.",
    }
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print("PASS:", report_path, flush=True)


if __name__ == "__main__":
    main()
