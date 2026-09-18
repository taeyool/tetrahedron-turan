"""Sequential numerical equivalence gate for the private full-model SCS build."""
import argparse
from pathlib import Path
import time
import numpy as np
from scipy import sparse
import runtime as rt
import owned_scs
from seven_full_native import pack


def fixture(seed,n=41,dimensions=(2,3,7)):
    rng=np.random.default_rng(seed)
    parts=[np.ones((1,n)),-np.eye(n)]
    for d in dimensions:
        matrices=[]
        for j in range(n):
            matrix=rng.normal(size=(d,d))/np.sqrt(d)
            matrix=(matrix+matrix.T)/2+0.15*np.eye(d)
            if j==0:matrix=np.eye(d)
            matrices.append(-pack(matrix))
        parts.append(np.stack(matrices,axis=1))
    a=sparse.csc_matrix(np.vstack(parts));a.sort_indices()
    b=np.zeros(a.shape[0]);b[0]=1
    c=-rng.uniform(size=n)
    return a,b,c,dict(z=1,l=n,s=list(dimensions))


def serialize(a,cone,path):
    path.mkdir()
    np.asarray(a.data,dtype='<f8').tofile(path/'data.f64')
    np.asarray(a.indices,dtype='<i8').tofile(path/'indices.i64')
    np.asarray(a.indptr,dtype='<i8').tofile(path/'indptr.i64')
    return dict(shape=list(a.shape),nnz=a.nnz,cone=cone)


def validate(cache,output):
    import scs
    started=time.monotonic();output.mkdir(parents=True,exist_ok=True)
    results=[]
    for seed in [612,613]:
        a,b,c,cone=fixture(seed)
        path=output/f'matrix-{seed}';meta=serialize(a,cone,path)
        solved={variant:owned_scs.run(cache,path,meta,b,c,output/f'{variant}-{seed}',
                    budget=10000,reserve=0,max_iters=1000000,variant=variant) for variant in ['stock','owned']}
        assert all(result['success'] for result in solved.values())
        assert all(result['info']['rho_x']==100.0 for result in solved.values())
        assert solved['stock']['info']['iter']==solved['owned']['info']['iter']
        errors={}
        for name in ['x','y','s']:
            np.testing.assert_allclose(solved['owned'][name],solved['stock'][name],atol=1e-13,rtol=1e-13)
            errors[name]=float(np.max(np.abs(solved['owned'][name]-solved['stock'][name])))
        wheel=scs.SCS(dict(A=a,b=b,c=c),cone,verbose=False,use_indirect=True,
            max_iters=1000000,eps_abs=1e-8,eps_rel=1e-8,eps_infeas=1e-8,
            normalize=True,acceleration_lookback=10,rho_x=100.0).solve(warm_start=False)
        assert wheel['info']['status_val'] in [1,2]
        wheel_errors={}
        for name in ['x','y','s']:
            np.testing.assert_allclose(solved['owned'][name],wheel[name],atol=2e-7,rtol=2e-7)
            wheel_errors[name]=float(np.max(np.abs(solved['owned'][name]-wheel[name])))
        results.append(dict(seed=seed,stock_owned_max_errors=errors,wheel_max_errors=wheel_errors,
            stock_owned_iterations=solved['stock']['info']['iter'],wheel_iterations=wheel['info']['iter']))
    # Exercise the deadline path separately; it is not a benchmark repetition.
    a,b,c,cone=fixture(614,n=400,dimensions=(25,30))
    path=output/'matrix-timing';meta=serialize(a,cone,path)
    timed=owned_scs.run(cache,path,meta,b,c,output/'owned-timing',budget=0.5,reserve=0)
    assert timed['success'] and timed['info']['status_val']==2
    assert 'time_limit_secs' in timed['info']['status']
    assert timed['info']['solve_time']/1000<=timed['info']['actual_time_limit_setting_seconds']+0.25
    result=dict(status='passed',stock_owned_fixtures=results,deadline_fixture=timed['info'],
        all_numerical_targets_unchanged=True,rho_x=100.0,fixture_max_iters=1000000,seconds=time.monotonic()-started,
        build_manifest_sha256=rt.digest(cache/'owned-scs-v4/manifest.json'),source_sha256=rt.sources())
    rt.write_json(output/'validation.json',result);print(rt.json.dumps(result))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cache',type=Path,required=True);parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();validate(args.cache.resolve(),args.output.resolve())
