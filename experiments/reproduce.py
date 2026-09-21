"""Prepare and repeat the 43 published trials from a fresh checkout.

Default: print a plan only. Execution requires --run and Windows for the
recorded process-tree memory cap. This is a new campaign, independent of the
historical supervisors' state files. Never overwrites an earlier attempt.
"""
import argparse
import json
import math
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time
import runtime as rt

METHODS = ["SDP-FULL","LP-CUT","SDP-CG","LP-CUT-CG"]
MEMORY = 40*1024**3

def tasks():
    arms = [(m,k) for m in ["M6","M7-no5","M7-all5"] for k in METHODS]
    arms += [("M7-lift6","LP-CUT-CG")]
    result = [dict(id=f"{m}-{k}-rep-{r:02}",model=m,method=k,phase="production",rep=r,seconds=3600)
              for r in [1,2,3] for m,k in arms]
    result += [dict(id=f"{m}-{k}-6h",model=m,method=k,phase="long",rep=1,seconds=21600)
               for m,k in [("M7-no5","LP-CUT-CG"),("M7-all5","LP-CUT-CG"),("M6","SDP-FULL")]]
    result += [dict(id="M6-SDP-FULL-reference-1h",model="M6",method="SDP-FULL",phase="reference",rep=1,seconds=3600)]
    return result

def command(script,*args):
    return [sys.executable,"-X","utf8",str(rt.HERE/"runtime.py"),str(rt.ROOT/script),*map(str,args)]

def run_command(cmd,folder,seconds=14400,search=None):
    from run_overnight import watch
    result = watch(cmd,folder,time.time()+seconds,MEMORY,search_limit=search,initialization_limit=3600)
    if not result["kernel_job_limit_enforced"]:
        raise RuntimeError("The required Windows memory cap was not applied")
    if result["returncode"] != 0:
        raise RuntimeError(f"Command failed; see {folder/'process.log'}")

def prepare(base,selected):
    cache=base/"cache";cache.mkdir(parents=True,exist_ok=True)
    def step(name,cmd):
        folder=base/"preparation"/name
        if (folder/"complete.json").exists(): return
        if folder.exists(): raise FileExistsError(f"Partial preparation retained: {folder}; use a fresh directory")
        run_command(cmd,folder)
        rt.write_json(folder/"complete.json",dict(status="complete",source_sha256=rt.sources()))
    step("components",command("search/analyze_certificate.py","--cache",cache,"--output",cache/"diagnostics.json"))
    models={t["model"] for t in selected}
    if models & {"M6","M7-lift6"}:
        step("remaining-models",command("experiments/remaining_models.py","--cache",cache,"--output",base/"validation/remaining.json"))
    if models & {"M7-no5","M7-all5"}:
        step("seven-models",command("experiments/validate_selected.py","--cache",cache,"--output",base/"validation/seven"))
    full={t["model"] for t in selected if t["model"] in ["M7-no5","M7-all5"] and t["method"] in ["SDP-FULL","LP-CUT"]}
    if full:
        import numpy as np
        legacy=json.loads((rt.ROOT/"certificate/legacy/K4_turan_order7_exact_certificate.json").read_text())
        reps=cache/"representatives.u32"
        np.asarray(legacy["H_representatives"],dtype="<u4").tofile(reps)
        compiler=shutil.which("c++")
        if compiler is None: raise FileNotFoundError("A C++17 compiler named c++ is required")
        exe=cache/"seven_catalog.exe"
        step("catalogue-compile",[compiler,"-O3","-std=c++17","-pthread",str(rt.HERE/"seven_catalog.cpp"),"-o",str(exe)])
        step("catalogue",[str(exe),str(reps),str(cache/"seven_masks.u64"),str(cache/"seven-catalog.json")])
    native={t["model"] for t in selected if t["model"] in full and t["method"]=="SDP-FULL"}
    if native:
        step("native-build",command("experiments/build_native_scs.py","--cache",cache))
        step("native-validation",command("experiments/validate_owned_scs.py","--cache",cache,"--output",base/"validation/native"))
    for model in sorted(full):
        step(f"features-{model}",command("experiments/seven_full.py","--cache",cache,"--model",model))
        step(f"full-validation-{model}",command("experiments/validate_seven_full.py","--cache",cache,"--model",model,"--output",base/f"validation/{model}.json"))
        if model in native:
            step(f"packed-{model}",command("experiments/seven_full_native.py","--cache",cache,"--model",model))
            step(f"adapter-{model}",command("experiments/validate_full_adapters.py","--cache",cache,"--model",model,"--output",base/f"validation/{model}-adapter.json"))
    if any(t["method"].startswith("LP") for t in selected):
        for name in ["lp_memory","no5_lp_memory","recycle_highs"]:
            step(name,command(f"experiments/validate_{name}.py","--output",base/"validation"/name))
    return cache

def search_command(t,cache,out,smoke=None):
    seconds=smoke or t["seconds"]
    common=["--cache",cache,"--output",out,"--seconds",seconds]
    if t["model"]=="M6" and t["phase"] in ["long","reference"]:
        return command("experiments/run_long_reference.py",*common)
    script="run_remaining_method.py" if t["model"] in ["M6","M7-lift6"] else "run_seven_method.py"
    return command("experiments/"+script,"--model",t["model"],"--method",t["method"],
                   "--rep",t["rep"],"--phase","pilot" if smoke else t["phase"],*common)

def exact_command(t,source,cache,out,factorization):
    common=[source,"--cache",cache,"--output",out/"certificate.json","--factorization",factorization]
    if t["model"]=="M6":
        return command("experiments/exactify_order6.py",*common)
    script="exactify_five_root.py" if t["model"]=="M7-all5" else "exactify_reconstructed_dual.py"
    return command("search/"+script,*common,"--scale",2000000,"--threads",2,
                   "--svd-relative-tolerance",1e-7,"--cross-check-pricing")

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output",type=Path,default=Path(".research-repro/reproduction"))
    p.add_argument("--select",action="append",help="Exact task ID; repeat to select several")
    p.add_argument("--run",action="store_true")
    p.add_argument("--prepare-only",action="store_true")
    p.add_argument("--smoke-seconds",type=float,help="Short non-benchmark pilot; requires exactly one task")
    a=p.parse_args()
    selected=[t for t in tasks() if not a.select or t["id"] in a.select]
    if a.select and set(a.select)-{t["id"] for t in selected}: p.error("Unknown task ID")
    if a.smoke_seconds is not None and (not math.isfinite(a.smoke_seconds) or a.smoke_seconds<=0 or len(selected)!=1):
        p.error("--smoke-seconds must be positive and select exactly one task")
    base=a.output.resolve()
    plan=dict(trials=selected,smoke_seconds=a.smoke_seconds,
              total_search_hours=sum(a.smoke_seconds or t["seconds"] for t in selected)/3600,
              note="Preparation and exact verification are additional. --run is required to execute.",
              commands=[search_command(t,base/"cache",base/"runs"/t["id"]/"attempt-01",a.smoke_seconds) for t in selected])
    if not a.run:
        print(json.dumps(plan,indent=2));return
    if os.name!="nt": p.error("This supervised campaign requires Windows; see docs/reproduction.md for portable individual workers")
    base.mkdir(parents=True,exist_ok=True)
    lock=base/"controller.lock"
    with lock.open("x") as f: f.write(str(os.getpid()))
    import ctypes
    ctypes.windll.kernel32.SetThreadExecutionState(0x80000001)
    try:
        if not (base/"environment/environment.json").exists():
            from run_overnight import environment
            environment(base)
        rt.write_json(base/"plan.json",plan)
        cache=prepare(base,selected)
        if a.prepare_only: return
        for t in selected:
            root=base/"runs"/t["id"]
            if (root/"complete.json").exists():
                prior=json.loads((root/"complete.json").read_text())
                if prior.get("smoke_seconds")!=a.smoke_seconds:
                    raise ValueError("A smoke run and a benchmark must use different output directories")
                continue
            root.mkdir(parents=True,exist_ok=True)
            out=root/f"attempt-{len(list(root.glob('attempt-*')))+1:02}"
            run_command(search_command(t,cache,out,a.smoke_seconds),out,(a.smoke_seconds or t["seconds"])+3660,a.smoke_seconds or t["seconds"])
            run=json.loads((out/"run.json").read_text())
            if run["status"] not in ["completed","time_limit"]:
                raise RuntimeError(f"Unresolved search status: {run['status']}; attempt retained at {out}")
            source=out/"best_dual.npz"
            for factorization in ["svd","cuts"]:
                dest=out/"exact"/("final-"+factorization)
                run_command(exact_command(t,source,cache if t["model"]=="M6" else dest/"cache",dest,factorization),dest)
            for snap in sorted((out/"checkpoints").glob("*/dual.npz")):
                dest=out/"exact"/(snap.parent.name+"-svd")
                run_command(exact_command(t,snap,cache if t["model"]=="M6" else dest/"cache",dest,"svd"),dest)
            rt.write_json(root/"complete.json",dict(status="complete",attempt=str(out),smoke_seconds=a.smoke_seconds))
    finally:
        ctypes.windll.kernel32.SetThreadExecutionState(0x80000000)
        lock.unlink()

if __name__=="__main__":main()
