"""Native SCS PSD adapter for the exact twelve- or thirty-five-block SDP."""
import contextlib
import time
import runtime as rt
import numpy as np
from scipy import sparse
from scipy.linalg import eigh
import reconstruct_optimization as ro


def solve(master,remaining,output,full=False,inner_seconds=300,indirect=True):
    import cvxpy as cp
    start=time.monotonic()
    y=cp.Variable(len(master.masks))
    # Explicit deletion marginals avoid expanding dense six-vertex blocks onto
    # 1.3 million configuration variables during canonicalization.
    x=cp.Variable(964)
    constraints=[cp.sum(y)==1,master.stationarity@x==0,y>=0,x==master.deck.T@y]
    for block in master.blocks:
        d=block.shape[1]
        a=sparse.csr_matrix(block.reshape(964,-1))
        constraints.append(cp.reshape(a.T@x,(d,d),order='C')>>0)
    for a,b,d in zip(ro.OFFSETS[:-1],ro.OFFSETS[1:],ro.DIMS[9:]):
        f=master.feat[:,a:b]
        constraints.append(cp.reshape(f.T@y,(d,d),order='C')>>0)
    problem=cp.Problem(cp.Maximize(master.objective@x),constraints)
    assembly=time.monotonic()-start
    reserve=150 if len(ro.DIMS)>12 else 30
    available=remaining-assembly-reserve
    if available<=0:
        return dict(success=False,backend_status='insufficient_time_for_export_and_pricing',solve_seconds=time.monotonic()-start)
    cap=available if full else min(available,inner_seconds)
    with (output/'solver.log').open('a',encoding='utf-8') as stream,contextlib.redirect_stdout(stream),contextlib.redirect_stderr(stream):
        problem.solve(solver='SCS',verbose=True,max_iters=20000000,eps_abs=1e-8,eps_rel=1e-8,eps_infeas=1e-8,
            use_indirect=indirect,normalize=True,acceleration_lookback=10,time_limit_secs=cap)
    if problem.status not in [cp.OPTIMAL,cp.OPTIMAL_INACCURATE] or y.value is None:
        return dict(success=False,backend_status=problem.status,solve_seconds=time.monotonic()-start)
    factors=[];repairs=[]
    for constraint in constraints[4:]:
        q=np.asarray(constraint.dual_value);ev,vec=eigh((q+q.T)/2,driver='evr');positive=ev>0
        factors.append(np.sqrt(ev[positive])[:,None]*vec[:,positive].T)
        repairs.append(dict(minimum_before=float(ev[0]),negative_eigenvalues=int(np.count_nonzero(ev<0)),projection_frobenius_norm=float(np.linalg.norm(np.minimum(ev,0)))))
    tau=-float(constraints[1].dual_value)
    six=master.objective+tau*master.stationarity
    for b,f in zip(master.blocks,factors[:9]):six+=np.einsum('hij,ij->h',b,f.T@f)
    grams=[f.T@f for f in factors[9:]]
    return dict(success=True,backend_status=problem.status,y=np.asarray(y.value),objective=float(problem.value),
        six=six,grams=grams,tau=tau,factors=factors,psd_repairs=repairs,
        solve_seconds=time.monotonic()-start,assembly_seconds=assembly,
        backend_solve_seconds=problem.solver_stats.solve_time,backend_iterations=problem.solver_stats.num_iters,
        marginal_equality_residual=float(np.max(np.abs(np.asarray(x.value)-master.deck.T@np.asarray(y.value)))))
