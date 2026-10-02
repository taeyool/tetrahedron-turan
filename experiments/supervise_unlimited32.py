"""Durable supervisor of the unlimited 32-block search (no total-time deadline).

Subcommands
  prepare    snapshot environment/sources, write config.json and COMMANDS.md
  launch     start `supervise` as an independently owned hidden process (WMI on Windows)
  supervise  run the worker until convergence; resume transient failures from the newest
             valid checkpoint; enforce the memory ceiling; detect hung stages; schedule
             exact verification; keep status.json and PROGRESS.md current
  stop       request a graceful stop (checkpoint, status `interrupted`, never `converged`)

Stage-hang, memory and disk guards may end an attempt. They never relabel a run
as converged, and there is no inherited one-/six-hour or campaign deadline.
"""
from __future__ import annotations

import argparse
import csv
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

import runtime as rt
import psutil

WORKER = rt.HERE / 'run_unlimited32.py'
VERIFIER = rt.HERE / 'verify_candidate32.py'
BASELINE_FRACTION = '312372062889819/560000000000000'
TERMINAL = ('converged', 'interrupted_by_user_stop_request', 'blocked_reproducible_failure', 'blocked_memory_limit',
            'blocked_disk_space')


def read_json(path, default=None):
    try:
        return json.loads(Path(path).read_text(encoding='utf-8'))
    except (OSError, ValueError):
        return default


def alive(pid, marker=None):
    try:
        process = psutil.Process(int(pid))
        if not process.is_running() or process.status() == psutil.STATUS_ZOMBIE:
            return False
        return marker is None or any(marker in part for part in process.cmdline())
    except (psutil.NoSuchProcess, psutil.AccessDenied, TypeError, ValueError):
        return False


# ---------------------------------------------------------------------- prepare

def prepare(args):
    from run_overnight import environment
    run_dir = args.run_dir.resolve()
    run_dir.mkdir(parents=True, exist_ok=True)
    if (run_dir / 'config.json').exists():
        raise FileExistsError('config.json exists; this run directory is already prepared')
    report = environment(run_dir)
    compiler = shutil.which('c++')
    memory = min(40*1024**3, int(report['physical_ram_bytes']*.70))
    config = dict(model='M7-all5-32', method='LP-CUT-CG', mode='until_converged', time_limit_seconds=None,
        iteration_limit=None, supervisor_deadline=None, python=sys.executable, repository_root=str(rt.ROOT),
        cache=str(args.cache.resolve()), init=args.init,
        legacy_checkpoint=str(args.legacy_checkpoint.resolve()) if args.legacy_checkpoint else None,
        legacy_best_dual=str(args.legacy_best_dual.resolve()) if args.legacy_best_dual else None,
        worker_options=dict(scan_threads=2, price_top=8, max_cuts=80, keep_cuts=3000, lp_tolerance=1e-9,
                            lp_solver='choose', checkpoint_every=5),
        memory_ceiling_bytes=memory, minimum_free_disk_bytes=20*1024**3, stage_hang_seconds=6*3600,
        verification=dict(first_after_seconds=1800, interval_seconds=3*3600, factorization='svd',
                          svd_relative_tolerance=1e-7, scale=2000000, threads=2),
        restart_policy='Resume from the newest valid checkpoint after a failed attempt that completed at least one '
                       'iteration; two consecutive attempts without a completed iteration block the run for diagnosis.',
        path_prepend=[str(Path(compiler).parent)] if compiler else [], created_epoch=time.time(),
        note='Edits to worker_options and verification take effect at the next attempt/verification and are logged.')
    rt.write_json(run_dir / 'config.json', config)
    write_commands(run_dir, config)
    print(f'prepared {run_dir}')


def write_commands(run_dir, config):
    py, me = config['python'], str(Path(__file__).resolve())
    q = lambda s: f'"{s}"'
    text = f"""# Commands for this run (Windows, run from the repository root)

Run directory: `{run_dir}`
Model `M7-all5-32`, method `LP-CUT-CG`, mode `until_converged` (no time or iteration limit).

## Launch or relaunch the durable supervisor (independent of any chat/app session)

```powershell
& {q(py)} -X utf8 {q(me)} launch --run-dir {q(run_dir)}
```

The supervisor is created through WMI (`Win32_Process.Create`), so it is owned by the WMI host,
not by the launching shell or app, and keeps running after they close. It starts the worker
hidden, and resumes from `state/` when native checkpoints exist. A second supervisor refuses to
start while `supervisor.lock` names a live supervisor.

## Monitor

```powershell
Get-Content {q(run_dir / 'PROGRESS.md')}
Get-Content {q(run_dir / 'status.json')}
Get-Content {q(run_dir / 'supervisor.log')} -Tail 40
```

Per-attempt logs: `attempts/attempt-NNN/` (`history.jsonl`, `updates.jsonl`, `run.json`, `solver.log`,
`process.log`, `resources.csv`). Exact verification: `candidates/*/verification.json`, `exact/best_verified.json`.

## Stop gracefully (checkpoints; marks the run interrupted, never converged)

```powershell
& {q(py)} -X utf8 {q(me)} stop --run-dir {q(run_dir)}
```

This creates `STOP`. The worker checkpoints at the next stage boundary, the supervisor verifies the
strongest unverified numerical candidate and exits with status `interrupted_by_user_stop_request`.

## Resume after a stop, reboot or crash

Delete the `STOP` file if present, then run the launch command again. Initialization is used only
when `state/` holds no native checkpoint; afterwards every attempt resumes the newest valid one.

## Verify a candidate by hand

```powershell
& {q(py)} -X utf8 {q(str(VERIFIER))} --run-dir {q(run_dir)} --cache {q(config['cache'])} --native {q(run_dir / 'incumbent' / 'best_numerical.npz')}
```

Create `VERIFY_NOW` in the run directory to make the supervisor verify the current numerical incumbent.
"""
    (run_dir / 'COMMANDS.md').write_text(text, encoding='utf-8')


# ----------------------------------------------------------------------- launch

def launch(args):
    run_dir = args.run_dir.resolve()
    config = read_json(run_dir / 'config.json')
    assert config, 'run prepare first'
    lock = read_json(run_dir / 'supervisor.lock')
    if lock and alive(lock.get('pid'), 'supervise_unlimited32'):
        raise RuntimeError(f"a supervisor is already running with PID {lock['pid']}")
    python = Path(config['python'])
    hidden = python.with_name('pythonw.exe')
    executable = hidden if hidden.exists() else python
    command = f'"{executable}" -X utf8 "{Path(__file__).resolve()}" supervise --run-dir "{run_dir}"'
    if os.name == 'nt':
        script = ("$s = New-CimInstance -ClassName Win32_ProcessStartup -ClientOnly -Property @{ShowWindow=[uint16]0}; "
                  "$r = Invoke-CimMethod -ClassName Win32_Process -MethodName Create -Arguments @{CommandLine=$env:U32_COMMAND; "
                  "CurrentDirectory=$env:U32_CWD; ProcessStartupInformation=$s}; "
                  "Write-Output ('{0} {1}' -f $r.ReturnValue, $r.ProcessId)")
        env = dict(os.environ, U32_COMMAND=command, U32_CWD=str(rt.ROOT))
        out = subprocess.run(['powershell', '-NoProfile', '-NonInteractive', '-Command', script], env=env,
                             capture_output=True, text=True, check=True).stdout.split()
        assert out and out[0] == '0', f'WMI process creation failed: {out}'
        pid = int(out[1])
        method = 'WMI Win32_Process.Create (owned by WmiPrvSE, hidden window)'
    else:
        process = subprocess.Popen([str(python), '-X', 'utf8', str(Path(__file__).resolve()), 'supervise', '--run-dir', str(run_dir)],
                                   cwd=rt.ROOT, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                                   start_new_session=True)
        pid, method = process.pid, 'setsid'
    with (run_dir / 'launches.jsonl').open('a', encoding='utf-8') as stream:
        stream.write(json.dumps(dict(epoch=time.time(), supervisor_pid=pid, method=method, command=command))+'\n')
    print(f'supervisor PID {pid} via {method}')


def stop(args):
    run_dir = args.run_dir.resolve()
    (run_dir / 'STOP').write_text(json.dumps(dict(requested_epoch=time.time(), reason=args.reason))+'\n', encoding='utf-8')
    print('stop requested; the worker checkpoints at its next stage boundary')


# -------------------------------------------------------------------- supervise

class Supervisor:
    def __init__(self, run_dir):
        self.run = run_dir
        self.config = read_json(run_dir / 'config.json')
        assert self.config and self.config['mode'] == 'until_converged' and self.config['time_limit_seconds'] is None
        for folder in self.config.get('path_prepend', []):
            os.environ['PATH'] = folder + os.pathsep + os.environ.get('PATH', '')
        self.state = read_json(run_dir / 'supervisor_state.json') or dict(attempts=[], verifications=[],
            consecutive_attempts_without_progress=0, last_verification_started_epoch=None, last_verified_native_sha256=None,
            first_started_epoch=time.time())
        self.verifier = None
        self.verifier_label = None

    def log(self, message):
        line = f"{time.strftime('%Y-%m-%d %H:%M:%S')} {message}"
        with (self.run / 'supervisor.log').open('a', encoding='utf-8') as stream:
            stream.write(line+'\n')

    def save(self):
        rt.write_json(self.run / 'supervisor_state.json', self.state)

    # -- worker
    def start_worker(self):
        self.config = read_json(self.run / 'config.json') or self.config
        number = len(list((self.run / 'attempts').glob('attempt-*')))+1 if (self.run / 'attempts').exists() else 1
        attempt = self.run / 'attempts' / f'attempt-{number:03d}'
        attempt.mkdir(parents=True)
        native = sorted((self.run / 'state').glob('checkpoint-*.npz')) if (self.run / 'state').exists() else []
        init = 'resume' if native else self.config['init']
        options = self.config['worker_options']
        command = [self.config['python'], '-X', 'utf8', str(WORKER), '--cache', self.config['cache'], '--run-dir', str(self.run),
                   '--attempt-dir', str(attempt), '--init', init, '--mode', 'until_converged',
                   '--scan-threads', str(options['scan_threads']), '--price-top', str(options['price_top']),
                   '--max-cuts', str(options['max_cuts']), '--keep-cuts', str(options['keep_cuts']),
                   '--lp-tolerance', repr(options['lp_tolerance']), '--lp-solver', options['lp_solver'],
                   '--checkpoint-every', str(options['checkpoint_every'])]
        if init == 'legacy-checkpoint':
            command += ['--legacy-checkpoint', self.config['legacy_checkpoint'], '--legacy-best-dual', self.config['legacy_best_dual']]
        log = open(attempt / 'process.log', 'w', encoding='utf-8')
        process = subprocess.Popen(command, cwd=rt.ROOT, stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                                   creationflags=subprocess.CREATE_NO_WINDOW if os.name == 'nt' else 0)
        job, enforced, error = None, False, None
        try:
            from run_overnight import WindowsJob
            job = WindowsJob(process, self.config['memory_ceiling_bytes'])
            enforced = bool(job.handle)
        except Exception as exc:  # never claim a kernel cap that was not attached
            error = repr(exc)
        start_iterations = (read_json(self.run / 'state' / 'latest.json') or {}).get('completed_iterations', 0)
        info = dict(number=number, attempt=str(attempt), command=command, pid=process.pid, init=init, started_epoch=time.time(),
                    kernel_job_memory_limit_enforced=enforced, job_error=error, completed_iterations_at_start=start_iterations,
                    worker_options=options, status='running')
        self.state['attempts'].append(info)
        self.save()
        rt.write_json(attempt / 'supervisor.json', info)
        self.log(f'attempt {number} started pid={process.pid} init={init}')
        return process, job, log, attempt, info

    def tree_rss(self, pid):
        try:
            parent = psutil.Process(pid)
            members = [parent]+parent.children(recursive=True)
        except psutil.NoSuchProcess:
            return 0, []
        total = 0
        for member in members:
            try:
                total += member.memory_info().rss
            except (psutil.NoSuchProcess, psutil.AccessDenied):
                pass
        return total, members

    # -- verification
    def maybe_verify(self, force=False, blocking=False):
        if self.verifier is not None:
            if self.verifier.poll() is None:
                if not blocking:
                    return
                self.verifier.wait()
            self.finish_verification()
        best = self.run / 'incumbent' / 'best_numerical.npz'
        if not best.exists():
            return
        settings = self.config['verification']
        trigger = self.run / 'VERIFY_NOW'
        now = time.time()
        last = self.state['last_verification_started_epoch']
        due = (now-self.state['first_started_epoch'] >= settings['first_after_seconds'] if last is None
               else now-last >= settings['interval_seconds'])
        if not (force or trigger.exists() or due):
            return
        try:
            digest = rt.digest(best)
        except OSError:
            return
        if trigger.exists():
            trigger.unlink()
        if digest == self.state['last_verified_native_sha256']:
            self.state['last_verification_started_epoch'] = now
            return
        staging = self.run / 'candidates' / 'staging'
        staging.mkdir(parents=True, exist_ok=True)
        snapshot = staging / f'{digest[:12]}.npz'
        shutil.copy2(best, snapshot)
        if rt.digest(snapshot) != digest:
            snapshot.unlink()
            return  # replaced while copying; the next pass takes the newer incumbent
        label = f"{time.strftime('%Y%m%d-%H%M%S')}-{digest[:12]}-{settings['factorization']}-M{settings['scale']}"
        command = [self.config['python'], '-X', 'utf8', str(VERIFIER), '--run-dir', str(self.run), '--cache', self.config['cache'],
                   '--native', str(snapshot), '--label', label, '--factorization', settings['factorization'],
                   '--svd-tolerance', repr(settings['svd_relative_tolerance']), '--scale', str(settings['scale']),
                   '--threads', str(settings['threads'])]
        (self.run / 'candidates' / label).mkdir(parents=True, exist_ok=True)
        log = open(self.run / 'candidates' / label / 'process.log', 'w', encoding='utf-8')
        self.verifier = subprocess.Popen(command, cwd=rt.ROOT, stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                                         creationflags=(subprocess.CREATE_NO_WINDOW | subprocess.BELOW_NORMAL_PRIORITY_CLASS) if os.name == 'nt' else 0)
        self.verifier_label, self.verifier_digest, self.verifier_log = label, digest, log
        self.state['last_verification_started_epoch'] = now
        self.save()
        self.log(f'verification {label} started pid={self.verifier.pid}')
        if blocking:
            self.verifier.wait()
            self.finish_verification()

    def finish_verification(self):
        code = self.verifier.returncode
        self.verifier_log.close()
        result = read_json(self.run / 'candidates' / self.verifier_label / 'verification.json') or {}
        entry = dict(label=self.verifier_label, native_sha256=self.verifier_digest, returncode=code, status=result.get('status'),
                     bound_fraction=result.get('bound_fraction'), bound_decimal=result.get('bound_decimal'),
                     numerical_upper=result.get('numerical_upper'), improves_on_baseline=result.get('improves_on_baseline'),
                     improves_on_previous_best=result.get('improves_on_previous_best'))
        self.state['verifications'].append(entry)
        if code == 0:
            self.state['last_verified_native_sha256'] = self.verifier_digest
        self.save()
        self.log(f'verification finished: {entry}')
        self.verifier = None

    # -- reporting
    def report(self, status, active=None):
        worker = read_json(self.run / 'worker_status.json') or {}
        best = read_json(self.run / 'exact' / 'best_verified.json')
        last = worker.get('last_iteration') or {}
        latest = read_json(self.run / 'state' / 'latest.json') or {}
        summary = dict(status=status, updated_epoch=time.time(), updated_local=time.strftime('%Y-%m-%d %H:%M:%S'),
            supervisor_pid=os.getpid(), mode='until_converged', time_limit_seconds=None, active_attempt=active,
            attempts=len(self.state['attempts']), convergence_established=status == 'converged',
            best_numerical_upper=worker.get('best_global_upper'), counters=worker.get('counters'), last_iteration=last,
            last_update=worker.get('last_update'), block_minimum_eigenvalues=worker.get('block_minimum_eigenvalues'),
            best_verified=best or dict(fraction=BASELINE_FRACTION, source='pinned baseline certificate', improves_on_baseline=False),
            baseline_fraction=BASELINE_FRACTION, restart_checkpoint=latest, verifications=self.state['verifications'][-5:],
            verification_running=self.verifier_label if self.verifier is not None else None)
        rt.write_json(self.run / 'status.json', summary)
        tests = last.get('convergence_tests', {})
        verified = summary['best_verified']
        lines = ['# Unlimited 32-block search: progress', '',
            f"- Updated: {summary['updated_local']} (supervisor PID {os.getpid()})",
            f"- Status: **{status}**; convergence established: {status == 'converged'}",
            f"- Active attempt: {active}; attempts so far: {len(self.state['attempts'])}",
            f"- Completed iterations: {(worker.get('counters') or {}).get('completed_iterations')}; "
            f"search seconds: {(worker.get('counters') or {}).get('elapsed_search_seconds')}",
            f"- Best numerical upper value U: {worker.get('best_global_upper')}",
            f"- Best verified fraction: {verified.get('fraction')} ({verified.get('source')}); improves on baseline: {verified.get('improves_on_baseline')}",
            f"- Baseline: {BASELINE_FRACTION} = 0.5578072551603911",
            f"- Last iteration: B={last.get('restricted_objective')}, L={last.get('primal_objective_L')}, U={last.get('global_dual_upper')}, "
            f"U-L={last.get('gap_U_minus_L')}, min eigenvalue={last.get('minimum_eigenvalue')}",
            f"- Residuals: sum(y)-1={last.get('normalization_residual')}, stationarity={last.get('stationarity_residual')}, min(y)={last.get('minimum_y')}",
            f"- |W|={last.get('columns')}, directions={last.get('directions')}",
            f"- Convergence tests: {tests}",
            f"- Restart location: state/{latest.get('path')} (iteration {latest.get('completed_iterations')})",
            f"- Verification running: {summary['verification_running']}", '',
            'A run is finished only when Status is `converged`. `interrupted` or `blocked` states are resumable and are not convergence.', '']
        (self.run / 'PROGRESS.md').write_text('\n'.join(lines), encoding='utf-8')

    # -- main loop
    def main(self):
        lock_path = self.run / 'supervisor.lock'
        lock = read_json(lock_path)
        if lock and lock.get('pid') != os.getpid() and alive(lock.get('pid'), 'supervise_unlimited32'):
            raise RuntimeError(f"supervisor already running: {lock['pid']}")
        rt.write_json(lock_path, dict(pid=os.getpid(), started_epoch=time.time()))
        if os.name == 'nt':
            import ctypes
            ctypes.windll.kernel32.SetThreadExecutionState(0x80000001)  # no automatic sleep while supervising
        self.log(f'supervisor started pid={os.getpid()}')
        final = None
        try:
            while final is None:
                if (self.run / 'STOP').exists():
                    final = 'interrupted_by_user_stop_request'
                    break
                final = self.run_attempt()
            self.log(f'terminal status {final}; verifying the strongest unverified candidate')
            self.report(final if final != 'converged' else 'converged_final_verification_running')
            self.maybe_verify(force=True, blocking=True)
            converged = self.run / 'incumbent' / 'final_converged.npz'
            if final == 'converged' and converged.exists():
                self.verify_file(converged, 'final-converged')
            self.report(final)
        except Exception as exc:
            import traceback
            self.log('supervisor failure: '+repr(exc)+'\n'+traceback.format_exc())
            self.report('supervisor_failure')
            raise
        finally:
            if os.name == 'nt':
                ctypes.windll.kernel32.SetThreadExecutionState(0x80000000)
            lock_path.unlink(missing_ok=True)
        self.log(f'supervisor finished: {final}')

    def verify_file(self, path, prefix):
        settings = self.config['verification']
        label = f"{prefix}-{rt.digest(path)[:12]}-{settings['factorization']}-M{settings['scale']}"
        command = [self.config['python'], '-X', 'utf8', str(VERIFIER), '--run-dir', str(self.run), '--cache', self.config['cache'],
                   '--native', str(path), '--label', label, '--factorization', settings['factorization'],
                   '--svd-tolerance', repr(settings['svd_relative_tolerance']), '--scale', str(settings['scale']),
                   '--threads', str(settings['threads'])]
        (self.run / 'candidates' / label).mkdir(parents=True, exist_ok=True)
        with open(self.run / 'candidates' / label / 'process.log', 'w', encoding='utf-8') as log:
            code = subprocess.run(command, cwd=rt.ROOT, stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                                  creationflags=subprocess.CREATE_NO_WINDOW if os.name == 'nt' else 0).returncode
        result = read_json(self.run / 'candidates' / label / 'verification.json') or {}
        self.state['verifications'].append(dict(label=label, returncode=code, status=result.get('status'),
            bound_fraction=result.get('bound_fraction'), bound_decimal=result.get('bound_decimal'),
            numerical_upper=result.get('numerical_upper'), improves_on_baseline=result.get('improves_on_baseline')))
        self.save()
        self.log(f'verification {label} finished with code {code}: {result.get("bound_fraction")}')

    def run_attempt(self):
        process, job, log, attempt, info = self.start_worker()
        reason = None
        last_report = last_resource = 0
        with (attempt / 'resources.csv').open('w', newline='', encoding='utf-8') as stream:
            writer = csv.writer(stream)
            writer.writerow(['epoch', 'tree_rss_bytes', 'processes', 'disk_free_bytes'])
            peak = 0
            while process.poll() is None:
                now = time.time()
                rss, members = self.tree_rss(process.pid)
                peak = max(peak, rss)
                if now-last_resource >= 30:
                    free = shutil.disk_usage(self.run).free
                    writer.writerow([now, rss, len(members), free])
                    stream.flush()
                    last_resource = now
                    if free < self.config['minimum_free_disk_bytes'] and not (self.run / 'STOP').exists():
                        (self.run / 'STOP').write_text(json.dumps(dict(requested_epoch=now, reason='disk_space_guard'))+'\n', encoding='utf-8')
                        reason = 'disk_space'
                heartbeat = read_json(attempt / 'heartbeat.json')
                if rss > self.config['memory_ceiling_bytes']:
                    reason = 'memory_limit'
                elif heartbeat and now-heartbeat['epoch'] > self.config['stage_hang_seconds']:
                    reason = 'stage_hang'
                elif not heartbeat and now-info['started_epoch'] > self.config['stage_hang_seconds']:
                    reason = 'initialization_hang'
                if reason in ('memory_limit', 'stage_hang', 'initialization_hang'):
                    self.log(f'terminating attempt {info["number"]}: {reason}')
                    if job is not None and job.handle:
                        job.kill()
                    else:
                        for member in reversed(members):
                            try:
                                member.kill()
                            except (psutil.NoSuchProcess, psutil.AccessDenied):
                                pass
                    break
                if now-last_report >= 60:
                    self.maybe_verify()
                    self.report('running', active=attempt.name)
                    last_report = now
                time.sleep(5)
        try:
            process.wait(timeout=60)
        except subprocess.TimeoutExpired:
            process.kill()
            process.wait()
        log.close()
        job_peak = None
        if job is not None:
            job_peak = job.peak()
            job.close()
        run = read_json(attempt / 'run.json') or {}
        completed = (run.get('counters') or {}).get('completed_iterations', info['completed_iterations_at_start'])
        progressed = completed > info['completed_iterations_at_start']
        info.update(returncode=process.returncode, finished_epoch=time.time(), worker_status=run.get('status'),
                    supervisor_reason=reason, rss_peak_bytes=peak, job_peak_commit_bytes=job_peak,
                    completed_iterations_at_end=completed, status='finished')
        rt.write_json(attempt / 'supervisor.json', info)
        self.save()
        self.log(f"attempt {info['number']} ended code={process.returncode} worker_status={run.get('status')} reason={reason} iterations={completed}")
        if run.get('status') == 'converged' and process.returncode == 0:
            return 'converged'
        if run.get('status') == 'interrupted_by_user_stop_request' or (self.run / 'STOP').exists():
            return 'blocked_disk_space' if reason == 'disk_space' else 'interrupted_by_user_stop_request'
        if reason == 'memory_limit':
            return 'blocked_memory_limit'  # a blind restart would exhaust memory again
        self.state['consecutive_attempts_without_progress'] = 0 if progressed else self.state['consecutive_attempts_without_progress']+1
        self.save()
        if self.state['consecutive_attempts_without_progress'] >= 2:
            return 'blocked_reproducible_failure'
        self.report('restarting_from_checkpoint')
        time.sleep(30)
        return None


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    p = sub.add_parser('prepare')
    p.add_argument('--run-dir', type=Path, required=True)
    p.add_argument('--cache', type=Path, required=True)
    p.add_argument('--init', choices=['legacy-checkpoint', 'baseline-certificate'], required=True)
    p.add_argument('--legacy-checkpoint', type=Path)
    p.add_argument('--legacy-best-dual', type=Path)
    for name in ('launch', 'supervise', 'stop'):
        p = sub.add_parser(name)
        p.add_argument('--run-dir', type=Path, required=True)
        if name == 'stop':
            p.add_argument('--reason', default='user request')
    arguments = parser.parse_args()
    if arguments.action == 'prepare':
        prepare(arguments)
    elif arguments.action == 'launch':
        launch(arguments)
    elif arguments.action == 'stop':
        stop(arguments)
    else:
        Supervisor(arguments.run_dir.resolve()).main()
