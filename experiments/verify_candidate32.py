"""Exactify and independently verify one immutable native 32-block candidate.

Pipeline: immutable snapshot -> labeled legacy-35-slot serialization (empty
padding in slots 1, 3, 4) -> exactify_five_root.py (integer rounding, complete
independent 13,051,375-extension scan, optimization-oracle cross-check, ordered
direct checks) -> exact rational comparison with the pinned baseline and with
the strongest previously verified certificate of this run.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time

import runtime as rt
import model32
from export_legacy35 import export

BASELINE_FRACTION = Fraction(312372062889819, 560000000000000)
BASELINE_SHA256 = 'c3b0e0b9364f669763bdb8fd1e3914bcd55acdee17fe7a5adbbb2e92da22beb4'


def best_record(run_dir):
    path = run_dir / 'exact' / 'best_verified.json'
    if path.exists():
        return json.loads(path.read_text(encoding='utf-8'))
    return dict(fraction=str(BASELINE_FRACTION), decimal=float(BASELINE_FRACTION), source='pinned baseline certificate',
                certificate=str(rt.ROOT / 'certificate' / 'legacy' / 'K4_turan_order7_six_hour_certificate.json'),
                certificate_sha256=BASELINE_SHA256, improves_on_baseline=False)


def main(args):
    run_dir = args.run_dir.resolve()
    native = args.native.resolve()
    digest = rt.digest(native)
    label = args.label or f'{digest[:12]}-{args.factorization}-M{args.scale}'
    folder = run_dir / 'candidates' / label
    if (folder / 'verification.json').exists():
        print(f'already verified: {folder}', flush=True)
        return 0
    folder.mkdir(parents=True, exist_ok=True)
    started = time.time()
    record = dict(label=label, status='running', started_epoch=started, source_native=str(native), native_sha256=digest,
                  process_power_throttling=model32.full_speed_process(),
                  factorization=args.factorization, scale=args.scale, svd_relative_tolerance=args.svd_tolerance)
    rt.write_json(folder / 'verification.json.partial', record)
    snapshot = folder / 'native.npz'
    shutil.copy2(native, snapshot)
    assert rt.digest(snapshot) == digest, 'candidate changed while being copied'
    model = model32.Model32(args.cache.resolve())
    record['export'] = export(snapshot, folder / 'legacy-compatible-dual.npz', model, args.threads)
    command = [sys.executable, '-X', 'utf8', str(rt.HERE / 'runtime.py'), str(rt.RESEARCH / 'exactify_five_root.py'),
               str(folder / 'legacy-compatible-dual.npz'), '--cache', str(folder / 'exact-cache'),
               '--output', str(folder / 'certificate.json'), '--factorization', args.factorization,
               '--svd-relative-tolerance', repr(args.svd_tolerance), '--scale', str(args.scale),
               '--threads', str(args.threads), '--cross-check-pricing']
    record['command'] = command
    with (folder / 'exactify.log').open('w', encoding='utf-8') as log:
        completed = subprocess.run(command, cwd=rt.ROOT, stdout=log, stderr=subprocess.STDOUT)
    record['exactifier_returncode'] = completed.returncode
    if completed.returncode != 0 or not (folder / 'certificate.json').exists():
        # Overflow guards and verifier disagreements are failures of this candidate, never bypassed.
        record.update(status='exactification_failed', finished_epoch=time.time())
        rt.write_json(folder / 'verification.json', record)
        (folder / 'verification.json.partial').unlink(missing_ok=True)
        return 2
    cert = json.loads((folder / 'certificate.json').read_text(encoding='utf-8'))
    summary = json.loads((folder / 'certificate.summary.json').read_text(encoding='utf-8'))
    for old in model32.EXCLUDED_LEGACY:
        assert cert['order6_factors_by_block'][old] == [], 'padding slot became nonzero'
    verification = cert['exact_verification']
    assert verification['raw_count'] == 13051375 and verification['independent_pricing_full_scan']['complete_raw_count'] == 13051375
    assert verification['independent_pricing_full_scan']['maximum_numerator'] == verification['numerator']
    bound = Fraction(cert['bound_fraction'])
    assert bound == Fraction(verification['numerator'], verification['denominator'])
    previous = best_record(run_dir)
    previous_bound = Fraction(previous['fraction'])
    record.update(status='verified', bound_fraction=str(bound), bound_decimal=float(bound),
        numerical_upper=record['export'].get('repriced_upper'), rounding_loss=float(bound)-record['export'].get('repriced_upper', float('nan')),
        integer_square_factors=summary['integer_square_factors'], factor_counts=summary['factor_counts'],
        maximizer=summary['maximizer'], stationarity_multiplier_fraction=summary['stationarity_multiplier_fraction'],
        certificate_sha256=rt.digest(folder / 'certificate.json'), baseline_fraction=str(BASELINE_FRACTION),
        improves_on_baseline=bound < BASELINE_FRACTION, baseline_minus_bound=str(BASELINE_FRACTION-bound),
        baseline_minus_bound_decimal=float(BASELINE_FRACTION-bound), previous_best_fraction=str(previous_bound),
        improves_on_previous_best=bound < previous_bound, complete_independent_scan=True, pricing_cross_check=True,
        direct_ordered_root_checks=len(verification['direct_checks']), elapsed_seconds=time.time()-started,
        finished_epoch=time.time())
    rt.write_json(folder / 'verification.json', record)
    (folder / 'verification.json.partial').unlink(missing_ok=True)
    if bound < previous_bound:
        exact_dir = run_dir / 'exact'
        exact_dir.mkdir(parents=True, exist_ok=True)
        target = exact_dir / f'certificate-{label}.json'
        shutil.copy2(folder / 'certificate.json', target)
        rt.write_json(exact_dir / 'best_verified.json', dict(fraction=str(bound), decimal=float(bound), source=label,
            certificate=str(target), certificate_sha256=rt.digest(target), candidate_folder=str(folder),
            native_sha256=digest, integer_square_factors=summary['integer_square_factors'], scale=args.scale,
            factorization=args.factorization, improves_on_baseline=bound < BASELINE_FRACTION,
            baseline_minus_bound=str(BASELINE_FRACTION-bound), baseline_minus_bound_decimal=float(BASELINE_FRACTION-bound),
            verified_epoch=time.time()))
    (run_dir / 'exact').mkdir(parents=True, exist_ok=True)
    with (run_dir / 'exact' / 'verifications.jsonl').open('a', encoding='utf-8') as stream:
        stream.write(json.dumps({k: record[k] for k in ('label', 'native_sha256', 'bound_fraction', 'bound_decimal', 'numerical_upper',
            'integer_square_factors', 'improves_on_baseline', 'improves_on_previous_best', 'scale', 'factorization', 'finished_epoch')})+'\n')
    print(json.dumps({k: v for k, v in record.items() if k not in ('command', 'export', 'factor_counts')}, indent=2), flush=True)
    return 0


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run-dir', type=Path, required=True)
    parser.add_argument('--cache', type=Path, required=True)
    parser.add_argument('--native', type=Path, required=True)
    parser.add_argument('--label')
    parser.add_argument('--factorization', choices=['svd', 'cuts'], default='svd')
    parser.add_argument('--svd-tolerance', type=float, default=1e-7)
    parser.add_argument('--scale', type=int, default=2000000)
    parser.add_argument('--threads', type=int, default=2)
    sys.exit(main(parser.parse_args()))
