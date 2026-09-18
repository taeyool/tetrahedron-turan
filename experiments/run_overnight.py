"""Externally supervise the selected six searches and their exact verification.

This is deliberately a two-model subset, not an implementation of all 14 arms.
"""
from __future__ import annotations
import argparse
import csv
import datetime as dt
import os
from pathlib import Path
import platform
import subprocess
import sys
import time

import runtime as rt
import psutil


class WindowsJob:
    """One kill-on-close job per child tree, with a job-wide commit-memory cap."""
    def __init__(self, process, limit):
        self.handle = None
        if os.name != 'nt':
            return
        import ctypes as c
        from ctypes import wintypes as w
        class Basic(c.Structure):
            _fields_ = [('process_time',c.c_longlong),('job_time',c.c_longlong),('flags',w.DWORD),
                ('min_ws',c.c_size_t),('max_ws',c.c_size_t),('active',w.DWORD),
                ('affinity',c.c_size_t),('priority',w.DWORD),('scheduling',w.DWORD)]
        class IO(c.Structure):
            _fields_ = [(x,c.c_ulonglong) for x in ['read_ops','write_ops','other_ops','read_bytes','write_bytes','other_bytes']]
        class Extended(c.Structure):
            _fields_ = [('basic',Basic),('io',IO),('process_mem',c.c_size_t),('job_mem',c.c_size_t),
                        ('peak_process_mem',c.c_size_t),('peak_job_mem',c.c_size_t)]
        self.c,self.ext = c,Extended
        k = c.WinDLL('kernel32',use_last_error=True)
        k.CreateJobObjectW.argtypes=[c.c_void_p,w.LPCWSTR]; k.CreateJobObjectW.restype=w.HANDLE
        k.SetInformationJobObject.argtypes=[w.HANDLE,c.c_int,c.c_void_p,w.DWORD]
        k.AssignProcessToJobObject.argtypes=[w.HANDLE,w.HANDLE]
        k.TerminateJobObject.argtypes=[w.HANDLE,w.UINT]
        k.CloseHandle.argtypes=[w.HANDLE]
        k.QueryInformationJobObject.argtypes=[w.HANDLE,c.c_int,c.c_void_p,w.DWORD,c.c_void_p]
        self.k=k
        handle=k.CreateJobObjectW(None,None)
        if not handle:
            raise c.WinError(c.get_last_error())
        info=Extended(); info.basic.flags=0x2000|0x200; info.job_mem=limit
        if not k.SetInformationJobObject(handle,9,c.byref(info),c.sizeof(info)):
            k.CloseHandle(handle); raise c.WinError(c.get_last_error())
        if not k.AssignProcessToJobObject(handle,w.HANDLE(int(process._handle))):
            k.CloseHandle(handle); raise c.WinError(c.get_last_error())
        self.handle=handle

    def peak(self):
        if self.handle:
            data=self.ext()
            if self.k.QueryInformationJobObject(self.handle,9,self.c.byref(data),self.c.sizeof(data),None):
                return int(data.peak_job_mem)
        return None

    def kill(self):
        if self.handle:
            self.k.TerminateJobObject(self.handle,1)

    def close(self):
        if self.handle:
            self.k.CloseHandle(self.handle); self.handle=None


def watch(command, output, deadline, memory, search_limit=None, initialization_limit=900):
    output.mkdir(parents=True,exist_ok=True)
    if (output/'supervisor.json').exists():
        raise FileExistsError(f'Attempt already exists: {output}')
    started=time.time()
    log=open(output/'process.log','w',encoding='utf-8')
    process=subprocess.Popen(command,cwd=rt.ROOT,stdout=log,stderr=subprocess.STDOUT,
                             creationflags=subprocess.CREATE_NO_WINDOW if os.name=='nt' else 0)
    job=None
    info=dict(command=list(map(str,command)),pid=process.pid,started_epoch=started,
              memory_cap_bytes=memory,measurement_interval_seconds=1,
              status='running',rss_peak_bytes=0,job_peak_commit_bytes=None)
    try:
        job=WindowsJob(process,memory)
        info['kernel_job_limit_enforced']=bool(job.handle)
    except Exception as exc:
        # Never silently claim a hard kernel cap if attachment fails.
        info['kernel_job_limit_enforced']=False
        info['job_limit_error']=repr(exc)
    rt.write_json(output/'supervisor.json',info)
    reason=None
    with (output/'resources.csv').open('w',newline='',encoding='utf-8') as stream:
        writer=csv.writer(stream); writer.writerow(['elapsed_seconds','tree_rss_bytes','processes'])
        while process.poll() is None:
            now=time.time()
            try:
                parent=psutil.Process(process.pid)
                children=[parent]+parent.children(recursive=True)
                rss=0
                for child in children:
                    try: rss+=child.memory_info().rss
                    except (psutil.NoSuchProcess,psutil.AccessDenied): pass
                info['rss_peak_bytes']=max(info['rss_peak_bytes'],rss)
                writer.writerow([now-started,rss,len(children)]); stream.flush()
            except psutil.NoSuchProcess:
                break
            if now >= deadline:
                reason='campaign_time_limit'
            elif rss > memory:
                reason='memory_limit'
            elif search_limit is not None:
                state_path=output/'run.json'
                try: state=rt.json.loads(state_path.read_text(encoding='utf-8'))
                except (OSError,ValueError): state={}
                began=state.get('search_started_epoch')
                if began is None and now-started > initialization_limit:
                    reason='construction_limit'
                elif began is not None and now-began > search_limit+60:
                    reason='time_limit'
            if reason:
                if job is not None and job.handle:
                    job.kill()
                else:
                    for child in reversed(children):
                        try: child.kill()
                        except (psutil.NoSuchProcess,psutil.AccessDenied): pass
                break
            time.sleep(1)
    process.wait(timeout=20)
    if job:
        info['job_peak_commit_bytes']=job.peak(); job.close()
    log.close()
    info.update(status=reason or ('completed' if process.returncode==0 else 'process_failure'),
                returncode=process.returncode,finished_epoch=time.time(),elapsed_seconds=time.time()-started)
    rt.write_json(output/'supervisor.json',info)
    if search_limit is not None and reason:
        state_path=output/'run.json'
        try: state=rt.json.loads(state_path.read_text(encoding='utf-8'))
        except (OSError,ValueError): state={}
        state.update(status='time_limit' if 'time_limit' in reason else reason,
            supervisor_reason=reason,terminated_epoch=time.time())
        rt.write_json(state_path,state)
    return info


def environment(base):
    folder=base/'environment'; folder.mkdir(parents=True,exist_ok=True)
    report=dict(python=sys.version,executable=sys.executable,platform=platform.platform(),
        physical_cpu_count=psutil.cpu_count(logical=False),logical_cpu_count=psutil.cpu_count(),
        physical_ram_bytes=psutil.virtual_memory().total,available_ram_bytes=psutil.virtual_memory().available,
        disk_free_bytes=rt.shutil.disk_usage(base).free,source_sha256=rt.sources())
    if os.name=='nt':
        import winreg
        with winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE,r'HARDWARE\DESCRIPTION\System\CentralProcessor\0') as key:
            report['cpu_model']=winreg.QueryValueEx(key,'ProcessorNameString')[0]
    for name,cmd in [('revision',['git','rev-parse','HEAD']),('worktree-status',['git','status','--porcelain']),
                     ('worktree.patch',['git','diff','--binary']),('index.patch',['git','diff','--cached','--binary']),
                     ('packages',[sys.executable,'-m','pip','freeze']),('compiler',['c++','--version']),
                     ('power-mode',['powercfg','/getactivescheme'])]:
        value=subprocess.run(cmd,cwd=rt.ROOT,capture_output=True).stdout
        (folder/name).write_bytes(value)
    import contextlib
    import numpy as np
    with (folder/'blas-lapack.txt').open('w',encoding='utf-8') as stream,contextlib.redirect_stdout(stream):
        np.show_config()
    for relative in report['source_sha256']:
        target=folder/'sources'/relative
        target.parent.mkdir(parents=True,exist_ok=True)
        rt.shutil.copy2(rt.ROOT/relative,target)
    rt.write_json(folder/'environment.json',report)
    return report


def main(args):
    base=args.campaign.resolve(); base.mkdir(parents=True,exist_ok=True)
    state_path=base/'status.json'
    if state_path.exists():
        raise FileExistsError('Choose a fresh campaign or inspect the existing supervisor; no automatic reruns')
    deadline=dt.datetime.fromisoformat(args.deadline).timestamp()
    metadata=environment(base)
    memory=min(40*1024**3,int(metadata['physical_ram_bytes']*.70))
    order=[('M7-no5',1),('M7-all5',1),('M7-all5',2),('M7-no5',2),('M7-no5',3),('M7-all5',3)]
    manifest=dict(scope='Two-model subset authorized by user; not the full 14-configuration campaign',
        models=['M7-no5','M7-all5'],method='LP-CUT-CG',repetitions=3,search_seconds=3600,
        order=order,order_policy='Alternating paired order fixed before pilots; repetitions 1/3 control first, 2 expanded first',
        deadline_utc=args.deadline,deadline_epoch=deadline,memory_cap_bytes=memory,
        construction_initialization_limit_seconds=900,shutdown_grace_seconds=60,
        checkpoint_targets=rt.CHECKPOINTS,scale=2000000,compression='svd relative tolerance 1e-7',
        exact_final_uncompressed=True,source_sha256=rt.sources(),
        host_order=7,stationarity=True,fresh=True,types=rt.TYPES,
        deviations=['Only the two selected LP-CUT-CG arms; no M6 or native SDP comparisons',
            'No long continuations or historical optimization reproduction',
            'Native Windows with MinGW DLL loader adaptation, validated against original arithmetic',
            'Initialization cap reduced to 900 seconds; global ten-hour deadline includes preparation',
            'If deadline prevents all checkpoint verification, final candidates take priority and missing checks remain explicit'],
        validation_inputs={str(p.relative_to(base)):rt.digest(p) for p in
            [base/'validation/models/validation.json',base/'exact/reference-verified.summary.json'] if p.exists()})
    rt.write_json(base/'protocol/manifest.json',manifest)
    state=dict(status='pilot',started_epoch=time.time(),deadline_epoch=deadline,pid=os.getpid(),
               completed_searches=[],exact_checks=[],active=None)
    rt.write_json(state_path,state)
    if os.name=='nt':
        import ctypes
        # Thread-scoped: prevents automatic sleep only while this supervisor runs.
        ctypes.windll.kernel32.SetThreadExecutionState(0x80000001)
    try:
        validation=rt.json.loads((base/'validation/models/validation.json').read_text(encoding='utf-8'))
        reference=rt.json.loads((base/'exact/reference-verified.summary.json').read_text(encoding='utf-8'))
        assert validation['status']=='passed'
        assert reference['bound_fraction']=='78151799925597/140000000000000'
        assert reference['integer_square_factors']==629 and reference['raw_count']==13051375
        for name in ['M7-no5','M7-all5']:
            output=base/'pilot'/name
            state['active']=f'pilot/{name}'; rt.write_json(state_path,state)
            command=[sys.executable,'-X','utf8',str(rt.HERE/'run_selected.py'),'--model',name,
                '--cache',str(base/'cache'),'--output',str(output),'--seconds','300','--phase','pilot']
            result=watch(command,output,min(deadline,time.time()+1260),memory,search_limit=300)
            run=rt.json.loads((output/'run.json').read_text(encoding='utf-8'))
            if result['returncode'] != 0 or run['status'] not in ('completed','time_limit') or run.get('best_global_upper') is None:
                raise RuntimeError(f'Pilot failed; production is gated: {name}')
        # A roundtrip/dual consistency gate on the pilots, and predeclared attainable
        # within-model targets; the factor matrices are globally reevaluated below.
        import numpy as np
        targets={}
        for name in ['M7-no5','M7-all5']:
            output=base/'pilot'/name
            oracle,blocks,objective,stat,_=rt.model(base/'cache',name)
            with np.load(output/'best_dual.npz') as z:
                rebuilt=objective+float(z['tau'])*stat
                for i,b in enumerate(blocks):
                    q=z[f'factors{i}'].T@z[f'factors{i}']
                    rebuilt+=np.einsum('hij,ij->h',b,q)
                np.testing.assert_allclose(z['six'],rebuilt,atol=5e-13,rtol=0)
                grams=[]
                for i in range(9,len(z['dimensions'])):
                    q=z[f'factors{i}'].T@z[f'factors{i}']
                    np.testing.assert_allclose(q,z[f'gram{i-9}'],atol=5e-13,rtol=0)
                    grams.append(q)
                v,_=oracle.price(rebuilt,grams,threads=2,top=1)
                np.testing.assert_allclose(v.max(),float(z['global_upper']),atol=1e-11,rtol=0)
                targets[name]=float(np.ceil(float(z['global_upper'])*10000)/10000)
        manifest['predeclared_numerical_targets']=targets
        manifest['frozen_after_pilot_epoch']=time.time()
        rt.write_json(base/'protocol/manifest.json',manifest)
        for name,rep in order:
            if time.time()+3600+120 > deadline:
                state['stopping_reason']='Insufficient time for another full one-hour repetition within deadline'
                break
            output=base/'runs'/name/f'rep-{rep:02d}'
            state.update(status='searching',active=f'{name}/rep-{rep:02d}'); rt.write_json(state_path,state)
            command=[sys.executable,'-X','utf8',str(rt.HERE/'run_selected.py'),'--model',name,
                '--cache',str(base/'cache'),'--output',str(output),'--seconds','3600','--rep',str(rep)]
            result=watch(command,output,deadline,memory,search_limit=3600)
            state['completed_searches'].append(dict(model=name,rep=rep,supervisor_status=result['status']))
            rt.write_json(state_path,state)
            if result['status']=='campaign_time_limit': break
        # Exact verification is sequential and outside timed search. Final SVDs
        # for all repetitions precede uncompressed finals and earlier checkpoints.
        jobs=[]
        for factorization in ['svd','cuts']:
            for name,rep in order:
                run=base/'runs'/name/f'rep-{rep:02d}'
                if (run/'best_dual.npz').exists():
                    jobs.append((run/'best_dual.npz',run/'exact'/f'final-{factorization}',factorization))
        for target in [1800,900,300,60,3600]:
            for name,rep in order:
                run=base/'runs'/name/f'rep-{rep:02d}'
                source=run/'checkpoints'/f'{target:04d}'/'dual.npz'
                if source.exists(): jobs.append((source,run/'exact'/f'{target:04d}-svd','svd'))
        verified={}
        for source,output,factorization in jobs:
            if time.time()+60 > deadline:
                state['stopping_reason']='Campaign deadline; remaining exact checks are not reported as verified'
                break
            key=(rt.digest(source),factorization)
            output.mkdir(parents=True,exist_ok=True)
            if key in verified:
                rt.write_json(output/'reused-verification.json',dict(source_dual_sha256=key[0],
                    verified_artifact=str(verified[key]),factorization=factorization,
                    note='Identical candidate bytes and rounding policy; exact scan reused, not a new timing measurement'))
                continue
            state.update(status='exact_verification',active=str(output.relative_to(base))); rt.write_json(state_path,state)
            command=[sys.executable,'-X','utf8',str(rt.HERE/'runtime.py'),str(rt.RESEARCH/'exactify_five_root.py'),
                str(source),'--factorization',factorization,'--svd-relative-tolerance','1e-7','--scale','2000000',
                '--cross-check-pricing','--threads','2','--cache',str(output/'cache'),'--output',str(output/'certificate.json')]
            result=watch(command,output,deadline-30,memory)
            state['exact_checks'].append(dict(path=str(output.relative_to(base)),status=result['status']))
            if result['returncode']==0 and (output/'certificate.json').exists(): verified[key]=output/'certificate.json'
            rt.write_json(state_path,state)
            if result['status']=='campaign_time_limit': break
        state.update(status='finished',active=None,finished_epoch=time.time())
    except Exception as exc:
        import traceback
        traceback.print_exc()
        state.update(status='failed',error=repr(exc),finished_epoch=time.time())
    finally:
        rt.write_json(state_path,state)
        if os.name=='nt':
            ctypes.windll.kernel32.SetThreadExecutionState(0x80000000)
    from summarize_selected import summarize
    summarize(base)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--campaign',type=Path,required=True)
    parser.add_argument('--deadline',required=True,help='Absolute ISO timestamp with timezone, including preparation time')
    main(parser.parse_args())
