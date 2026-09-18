"""Fresh, instrumented M6 comparisons and M7-lift6 LP-CUT-CG.

Native arms impose PSD cones in every restricted solve (SCS via CVXPY).
Run under run_overnight.watch for hard time and process-tree memory limits.
"""
from __future__ import annotations
import argparse
from pathlib import Path
import time
from types import SimpleNamespace

import runtime as rt
import numpy as np
from scipy import sparse
from scipy.linalg import eigh
import reconstruct_optimization as ro
from remaining_models import model, DIMS

METHODS = ['SDP-FULL', 'LP-CUT', 'SDP-CG', 'LP-CUT-CG']


def native_solve(master, remaining, output):
    import contextlib
    import cvxpy as cp
    start = time.monotonic()
    # An explicit inequality preserves the backend's signed residuals; a
    # nonnegative variable attribute can clip small negative values on unpacking.
    y = cp.Variable(len(master.masks))
    constraints = [cp.sum(y) == 1, (master.deck@master.stationarity)@y == 0, y >= 0]
    for block in master.blocks:
        d = block.shape[1]
        a = master.deck@sparse.csr_matrix(block.reshape(964,-1))
        constraints.append(cp.reshape(a.T@y, (d,d), order='C') >> 0)
    problem = cp.Problem(cp.Maximize((master.deck@master.objective)@y), constraints)
    assembly = time.monotonic()-start
    with (output/'solver.log').open('a',encoding='utf-8') as stream, contextlib.redirect_stdout(stream), contextlib.redirect_stderr(stream):
        problem.solve(solver='SCS', verbose=True, max_iters=1000000,
            eps_abs=1e-8,eps_rel=1e-8,eps_infeas=1e-8,
            use_indirect=False,normalize=True,acceleration_lookback=10,
            time_limit_secs=max(.01,remaining-assembly-5))
    elapsed = time.monotonic()-start
    if problem.status not in [cp.OPTIMAL, cp.OPTIMAL_INACCURATE]:
        return dict(success=False, backend_status=problem.status, solve_seconds=elapsed)
    factors, repairs = [], []
    for constraint in constraints[3:]:
        q = np.asarray(constraint.dual_value)
        ev, vec = eigh((q+q.T)/2)
        positive = ev > 0
        factors.append(np.sqrt(ev[positive])[:,None]*vec[:,positive].T)
        repairs.append(dict(minimum_before=float(ev[0]),
            negative_eigenvalues=int(np.count_nonzero(ev<0)),
            projection_frobenius_norm=float(np.linalg.norm(np.minimum(ev,0)))))
    tau = -float(constraints[1].dual_value)
    six = master.objective+tau*master.stationarity
    for b, f in zip(master.blocks, factors):
        six += np.einsum('hij,ij->h', b, f.T@f)
    return dict(success=True, backend_status=problem.status, y=np.asarray(y.value),
        objective=float(problem.value), factors=factors, six=six, tau=tau,
        solve_seconds=elapsed, assembly_seconds=assembly,
        backend_solve_seconds=problem.solver_stats.solve_time,
        backend_iterations=problem.solver_stats.num_iters,
        native_normalization_dual=float(constraints[0].dual_value), psd_repairs=repairs)


def save_master(master, output, elapsed, method):
    vectors = np.zeros((len(master.cuts),max(DIMS)))
    for i,(b,v) in enumerate(master.cuts):
        vectors[i,:len(v)]=v
    basis=master.h.getBasis()
    data = dict(masks=np.asarray(master.masks,np.uint64),
        blocks=np.asarray([b for b,v in master.cuts],dtype=np.int32), vectors=vectors,
        dimensions=DIMS,stationarity=True,stationarity_face=False,
        elapsed_search_seconds=elapsed,method=method)
    if basis.valid and method.startswith('LP'):
        data.update(basis_columns=np.asarray([int(v) for v in basis.col_status]),
                    basis_rows=np.asarray([int(v) for v in basis.row_status]))
    ro.atomic_savez(output/'master_checkpoint.npz',**data)


def run(args):
    output=args.output.resolve(); output.mkdir(parents=True,exist_ok=True)
    path=output/'run.json'
    if path.exists():
        raise FileExistsError('Refusing to overwrite a prior attempt')
    if args.model != 'M6' and args.method != 'LP-CUT-CG':
        raise ValueError('Only M6 has full/native adapters in this runner')
    constructed=time.monotonic()
    record=dict(model=args.model,method=args.method,repetition=args.rep,phase=args.phase,
        status='initializing',initialization='fresh',stationarity=True,
        search_budget_seconds=args.seconds,checkpoints=rt.CHECKPOINTS,
        source_sha256=rt.sources(),started_epoch=time.time())
    rt.write_json(path,record)
    oracle,blocks,objective,stat,metadata=model(args.cache.resolve(),args.model)
    settings=SimpleNamespace(seed_turan=True,seed_certificate=False,stationarity_face=False,
        warm_dual=None,resume_checkpoint=None,threads=2,price_top=8,max_cuts=80,
        keep_cuts=3000,psd_tolerance=1e-7,price_tolerance=1e-7,
        lp_solver='choose',max_iter=1000000,seconds=args.seconds,output_dir=output)
    master=ro.Master(oracle,blocks,objective,stat,'with',settings)
    full=args.method in ['LP-CUT','SDP-FULL']
    native=args.method.startswith('SDP')
    if full:
        master.add_columns(oracle.reps)
        assert len(master.masks)==964
    extra=dict(dimensions=np.asarray(DIMS),five_root_type_masks=np.array([],dtype=np.uint64),
        model=args.model,method=args.method)
    record.update(ordered_blocks=metadata,dimensions=DIMS,five_root_types=[],
        raw_configuration_count=oracle.raw_count,
        effective_full_universe_count=964 if args.model=='M6' else None,
        initial_columns=len(master.masks),initial_cuts=0,
        initial_columns_sha256=rt.hashlib.sha256(np.asarray(master.masks,'<u8').tobytes()).hexdigest(),
        construction_initialization_seconds=time.monotonic()-constructed,
        settings={k:str(v) if isinstance(v,Path) else v for k,v in vars(settings).items()},
        lp_backend_version=master.h.version(),
        solver_assembly_timing='Included in search time, separately logged for native solves')
    if native:
        import cvxpy, scs
        record.update(native_backend='SCS',native_backend_version=scs.__version__,
            cvxpy_version=cvxpy.__version__,native_settings=dict(eps_abs=1e-8,
            eps_rel=1e-8,eps_infeas=1e-8,max_iters=1000000,use_indirect=False,
            normalize=True,acceleration_lookback=10,threads=1,cone_scale=1,
            reported_psd_tolerance_original_units=1e-7,evaluation_reserve_seconds=5))
    else:
        master.h.setOptionValue('output_flag',True)
        master.h.setOptionValue('log_to_console',False)
        master.h.setOptionValue('log_file',str(output/'solver.log'))
    start=time.monotonic()
    record.update(status='running',search_started_epoch=time.time())
    rt.write_json(path,record)
    saved=set(); status='time_limit'; best_available=None; checkpoint_time=0

    def checkpoint(target, source):
        folder=output/'checkpoints'/f'{target:04d}'
        folder.mkdir(parents=True,exist_ok=True)
        if source and source.exists():
            with np.load(source) as z:
                available=float(z['availability_seconds']); upper=float(z['global_upper'])
            assert available <= target
            rt.shutil.copy2(source,folder/'dual.npz')
            rt.write_json(folder/'checkpoint.json',dict(target_seconds=target,
                candidate_available_seconds=available,global_upper=upper,
                dual_sha256=rt.digest(folder/'dual.npz')))
        else:
            rt.write_json(folder/'checkpoint.json',dict(target_seconds=target,status='no_completed_candidate'))
        saved.add(target)

    for iteration in range(1000000):
        remaining=args.seconds-(time.monotonic()-start)
        if remaining<=0:
            break
        s=time.monotonic()
        diagnostics={}
        if native:
            solved=native_solve(master,remaining,output)
            backend=solved['backend_status']
            if not solved['success']:
                status='time_limit' if time.monotonic()-start>=args.seconds else 'numerical_failure'
                record['backend_status']=backend
                break
            y,objective_value=solved['y'],solved['objective']
            six,tau,factors=solved['six'],solved['tau'],solved['factors']
            solve_seconds=solved['solve_seconds']
            diagnostics={k:solved[k] for k in ['assembly_seconds','backend_solve_seconds',
                'backend_iterations','native_normalization_dual','psd_repairs']}
        else:
            master.h.setOptionValue('time_limit',master.h.getRunTime()+remaining)
            master.h.run()
            solve_seconds=time.monotonic()-s
            backend=master.h.modelStatusToString(master.h.getModelStatus())
            if master.h.getModelStatus()!=master.highspy.HighsModelStatus.kOptimal:
                status='time_limit' if 'time' in backend.lower() else 'numerical_failure'
                record['backend_status']=backend
                break
            sol=master.h.getSolution()
            y=np.asarray(sol.col_value); objective_value=master.h.getObjectiveValue()
            six,grams,tau,weights=master.dual(sol)
            assert not grams
            factors=[np.asarray([np.sqrt(w)*v for w,(bb,v) in zip(weights,master.cuts)
                if bb==b and w>0]).reshape(-1,d) for b,d in enumerate(DIMS)]
        x=master.deck.T@y
        matrices=[np.einsum('h,hij->ij',x,b) for b in blocks]
        s=time.monotonic(); negative=[]; minima=[]
        for b,m in enumerate(matrices):
            ev,vec=eigh((m+m.T)/2,driver='evr')
            minima.append(float(ev[0]))
            negative.extend((float(ev[j]),b,vec[:,j]) for j in np.flatnonzero(ev < -1e-7))
        negative.sort(key=lambda item:item[0])
        eigen_seconds=time.monotonic()-s
        s=time.monotonic()
        values,priced=oracle.price(six,[],threads=2,top=8)
        pricing_seconds=time.monotonic()-s
        evaluated=time.monotonic()-start; upper=float(values.max()); gap=upper-objective_value
        eligible=evaluated<=args.seconds
        # Exported factors must reproduce the evaluated coefficient vector.
        rebuilt=objective+tau*stat
        for b,f in zip(blocks,factors):
            rebuilt += np.einsum('hij,ij->h',b,f.T@f)
        np.testing.assert_allclose(six,rebuilt,atol=5e-12,rtol=0)
        row=dict(iteration=iteration,seconds=evaluated,restricted_objective=objective_value,
            global_dual_upper=upper,pricing_gap=gap,tau=tau,lp_seconds=0 if native else solve_seconds,
            native_seconds=solve_seconds if native else 0,eigen_seconds=eigen_seconds,
            pricing_seconds=pricing_seconds,minimum_eigenvalue=min(minima),
            block_minimum_eigenvalues=minima,stationarity_residual=float(stat@x),
            normalization_residual=float(y.sum()-1),minimum_primal_weight=float(y.min()),
            columns=len(master.masks),cuts=len(master.cuts),primal_support=int(np.count_nonzero(y>1e-9)),
            eligible_for_budget=eligible,backend_status=backend,**diagnostics)
        if eligible and upper<master.best_upper:
            master.best_upper=upper; best_available=evaluated
            master.best_dual=dict(six=six,tau=tau,global_upper=upper,iteration=iteration,
                availability_seconds=evaluated,face_multipliers=np.array([]),**extra,
                **{f'factors{b}':f for b,f in enumerate(factors)})
            if args.model=='M7-lift6':
                # Legacy export layout only: omitted families have no rows.
                for b,d in enumerate([7,236,191],9):
                    master.best_dual[f'factors{b}']=np.zeros((0,d))
                    master.best_dual[f'gram{b-9}']=np.zeros((d,d))
            ro.atomic_savez(output/'best_dual.npz',**master.best_dual)
        for target in rt.CHECKPOINTS:
            if target<=args.seconds and evaluated>=target and target not in saved:
                source=output/('best_dual.npz' if evaluated==target and eligible else 'eligible_previous.npz')
                checkpoint(target,source)
        if (output/'best_dual.npz').exists():
            rt.shutil.copy2(output/'best_dual.npz',output/'eligible_previous.npz')
        row['best_global_upper']=master.best_upper if np.isfinite(master.best_upper) else None
        with (output/'history.jsonl').open('a',encoding='utf-8') as stream:
            stream.write(rt.json.dumps(row,allow_nan=False)+'\n')
        ro.atomic_savez(output/'last_primal.npz',masks=np.asarray(master.masks,np.uint64),
            weights=y,**extra,**{f'moment{b}':m for b,m in enumerate(matrices)})
        record.update(completed_iterations=iteration+1,best_global_upper=row['best_global_upper'],
            best_candidate_available_seconds=best_available,last_iteration=row,
            search_seconds=time.monotonic()-start,backend_status=backend)
        rt.write_json(path,record)
        print(rt.json.dumps({k:row[k] for k in ['iteration','seconds','restricted_objective',
            'global_dual_upper','minimum_eigenvalue','columns','cuts','backend_status']}),flush=True)
        if not negative and gap<=1e-7 and abs(stat@x)<=1e-7 and abs(y.sum()-1)<=1e-7 and y.min()>=-1e-7:
            status='completed'; break
        if not eligible:
            break
        update=time.monotonic()
        added=0 if full else master.add_columns(priced[values>objective_value+1e-7])
        if native:
            if not added:
                status='numerical_failure'; break
        else:
            if iteration%10==0:
                master.prune(sol)
            if gap<=1e-7:
                master.add_cuts([(b,v) for _,b,v in negative[:80]])
        with (output/'updates.jsonl').open('a',encoding='utf-8') as stream:
            stream.write(rt.json.dumps(dict(iteration=iteration,added_columns=added,
                retained_columns=len(master.masks),retained_cuts=len(master.cuts),
                update_seconds=time.monotonic()-update))+'\n')
        if time.monotonic()-start-checkpoint_time>=60:
            save_master(master,output,time.monotonic()-start,args.method)
            checkpoint_time=time.monotonic()-start
    for target in rt.CHECKPOINTS:
        if target<=args.seconds and target not in saved:
            source=output/'best_dual.npz' if best_available is not None and best_available<=target else None
            checkpoint(target,source)
    save_master(master,output,time.monotonic()-start,args.method)
    record.update(status=status,search_seconds=time.monotonic()-start,
        time_limit_overshoot_seconds=max(0,time.monotonic()-start-args.seconds),finished_epoch=time.time())
    rt.write_json(path,record)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--model',choices=['M6','M7-lift6'],required=True)
    p.add_argument('--method',choices=METHODS,required=True)
    p.add_argument('--cache',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--seconds',type=float,default=3600)
    p.add_argument('--rep',type=int,default=1)
    p.add_argument('--phase',choices=['pilot','production','validation'],default='production')
    a=p.parse_args()
    try:
        run(a)
    except Exception as exc:
        import traceback
        traceback.print_exc()
        path=a.output/'run.json'
        record=rt.json.loads(path.read_text(encoding='utf-8')) if path.exists() else {}
        record.update(status='implementation_failure',error=repr(exc))
        rt.write_json(path,record)
        raise
