"""Write RUN_DIR/REPORT.md for the unlimited 32-block search from the files on disk."""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path
import time

BASELINE = Fraction(312372062889819, 560000000000000)


def read(path, default=None):
    try:
        return json.loads(Path(path).read_text(encoding='utf-8'))
    except (OSError, ValueError):
        return default


def lines_of(path):
    try:
        return [json.loads(line) for line in Path(path).read_text(encoding='utf-8').splitlines() if line.strip()]
    except OSError:
        return []


def stamp(epoch):
    return time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(epoch)) if epoch else 'n/a'


def main(run_dir):
    status = read(run_dir / 'status.json', {})
    config = read(run_dir / 'config.json', {})
    state = read(run_dir / 'supervisor_state.json', {})
    attempts = sorted((run_dir / 'attempts').glob('attempt-*')) if (run_dir / 'attempts').exists() else []
    first = read(attempts[0] / 'run.json', {}) if attempts else {}
    manifest = read(attempts[0] / 'model_manifest.json', {}) if attempts else {}
    audit = read(run_dir / 'final_audit.json')
    best = read(run_dir / 'exact' / 'best_verified.json')
    environment = run_dir / 'environment'
    revision = (environment / 'revision').read_text(encoding='utf-8').strip() if (environment / 'revision').exists() else 'n/a'
    worktree = (environment / 'worktree-status').read_text(encoding='utf-8').strip() if (environment / 'worktree-status').exists() else ''
    out = ['# Unlimited 32-block seven-vertex search (M7-all5-32, LP-CUT-CG)', '',
           f'Report written {stamp(time.time())}. Run directory: `{run_dir}`.', '',
           '## Stopping status', '',
           f"- Supervisor status: **{status.get('status')}**; numerical convergence established: **{status.get('convergence_established')}**.",
           '- Mode `until_converged`: no wall-time deadline and no iteration limit were configured '
           f"(`time_limit_seconds={config.get('time_limit_seconds')}`, `iteration_limit={config.get('iteration_limit')}`)."]
    counters = status.get('counters') or {}
    out += [f"- Completed iterations: {counters.get('completed_iterations')}; cumulative search time: "
            f"{(counters.get('elapsed_search_seconds') or 0)/3600:.2f} h over {len(attempts)} attempt(s); duplicate-candidate "
            f"PSD fallbacks: {counters.get('duplicate_pricing_psd_fallbacks')}; failed audits: {counters.get('audits_failed')}; "
            f"prune events: {counters.get('prunes')} ({counters.get('pruned_directions')} directions)."]
    if status.get('status') != 'converged':
        out.append('- Convergence has NOT been established. The state in `state/` is resumable with the launch command in `COMMANDS.md`.')
    out += ['', '## Source, environment and model', '',
            f'- Source revision `{revision}`; local changes at launch:', '', '```text', worktree or '(clean)', '```', '',
            f"- Python `{config.get('python')}`; memory ceiling {config.get('memory_ceiling_bytes', 0)/1024**3:.0f} GiB; "
            f"worker options {config.get('worker_options')}.",
            f"- Model `{manifest.get('model_id')}`: {manifest.get('block_count')} blocks "
            f"({manifest.get('six_vertex_table_blocks')} six-vertex-table blocks, {manifest.get('seven_vertex_product_blocks')} "
            f"seven-vertex-product blocks); excluded legacy indices {manifest.get('excluded_legacy_indices')} (the three `2*l-s=5` "
            'blocks) are not loaded, optimized, separated or serialized. Full manifest: `attempts/attempt-001/model_manifest.json`.',
            '', '## Initialization', '', '```json', json.dumps(first.get('initialization'), indent=2), '```', '',
            f"Initial |W| = {first.get('initial_columns')}, initial directions = {first.get('initial_directions')}, "
            f"recomputed inherited numerical value = {first.get('initial_best_numerical_upper')}.", '',
            '## Policy and recorded deviations from the inherited six-hour settings', '']
    settings = first.get('settings', {})
    out += [f"- `{k}` = `{v}`" for k, v in settings.items()]
    changes = []
    for attempt in attempts:
        for update in lines_of(attempt / 'updates.jsonl'):
            if 'policy_change' in update:
                changes.append(f"- {attempt.name}, iteration {update['iteration']}: {update['policy_change']}")
    out += ['', 'Runtime policy changes:', ''] + (changes or ['- none'])
    out += ['', '## Attempts', '', '| attempt | init | start | end | worker status | supervisor reason | iterations | peak RSS (GiB) |',
            '| --- | --- | --- | --- | --- | --- | --- | --- |']
    for info in state.get('attempts', []):
        out.append(f"| {info.get('number')} | {info.get('init')} | {stamp(info.get('started_epoch'))} | {stamp(info.get('finished_epoch'))} | "
                   f"{info.get('worker_status')} | {info.get('supervisor_reason')} | {info.get('completed_iterations_at_start')} -> "
                   f"{info.get('completed_iterations_at_end')} | {(info.get('rss_peak_bytes') or 0)/1024**3:.2f} |")
    last = audit or status.get('last_iteration') or {}
    out += ['', '## Final audit' if audit else '## Last completed iteration (not a convergence audit)', '',
            f"- B = {last.get('restricted_objective')}, L = {last.get('primal_objective_L')}, U = {last.get('global_dual_upper')}",
            f"- U-L = {last.get('gap_U_minus_L')}, B-L = {last.get('B_minus_L')}, minimum eigenvalue over 32 blocks = {last.get('minimum_eigenvalue')}",
            f"- sum(y)-1 = {last.get('normalization_residual')}, sum(y s) = {last.get('stationarity_residual')}, min(y) = {last.get('minimum_y')}, "
            f"minimum cut multiplier = {last.get('minimum_cut_multiplier')}",
            f"- max retained coefficient minus B = {last.get('retained_maximum_minus_B')}, HiGHS max primal/dual infeasibility = "
            f"{last.get('highs_max_primal_infeasibility')} / {last.get('highs_max_dual_infeasibility')}",
            f"- |W| = {last.get('columns')}, directions = {last.get('directions')}, tau = {last.get('tau')}",
            f"- tests: {last.get('convergence_tests')}",
            '', 'An approximately feasible y does not prove a lower bound on the SDP optimum; numerical convergence and the exact '
            'upper-bound certificate below are separate deliverables, not a proved SDP optimum.', '',
            '## Numerical and exact bounds', '',
            f"- Best numerical upper value U: {status.get('best_numerical_upper')} (`incumbent/best_numerical.npz`)",
            f'- Pinned baseline: {BASELINE} = {float(BASELINE)!r}']
    if best:
        bound = Fraction(best['fraction'])
        out += [f"- Strongest verified certificate of this run: **{best['fraction']}** = {float(bound)!r} ({best['source']}), "
                f"{best.get('integer_square_factors')} integer factor rows, scale {best.get('scale')}, {best.get('factorization')}.",
                f"- Exact comparison: new < baseline is **{bound < BASELINE}**; baseline - new = {BASELINE-bound} = {float(BASELINE-bound):.6e}.",
                f"- Certificate: `{best['certificate']}` (sha256 `{best['certificate_sha256']}`)."]
    else:
        out.append('- No certificate of this run improves on the baseline so far; the pinned baseline remains the strongest verified bound.')
    out += ['', '## Exact verifications', '', '| label | numerical U | verified fraction | decimal | factors | improves baseline |', '| --- | --- | --- | --- | --- | --- |']
    for row in lines_of(run_dir / 'exact' / 'verifications.jsonl'):
        out.append(f"| {row['label']} | {row['numerical_upper']} | {row['bound_fraction']} | {row['bound_decimal']!r} | "
                   f"{row['integer_square_factors']} | {row['improves_on_baseline']} |")
    out += ['', 'Every accepted certificate passed: rational factor rows, the independent complete scan of 13,051,375 raw extensions, '
            'agreement with the optimization oracle full integer scan (`--cross-check-pricing`), the exactifier direct ordered-root checks, '
            'and an exact rational comparison. Legacy slots 1, 3 and 4 are empty serialization padding only.', '',
            'Paper updates and Lean formalization are separate follow-up tasks; a new computational certificate is not a Lean theorem.', '']
    addendum = run_dir / 'ADDENDUM.md'
    if addendum.exists():
        out += ['', addendum.read_text(encoding='utf-8').rstrip(), '']
    (run_dir / 'REPORT.md').write_text('\n'.join(out), encoding='utf-8')
    print(run_dir / 'REPORT.md')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run-dir', type=Path, required=True)
    main(parser.parse_args().run_dir.resolve())
