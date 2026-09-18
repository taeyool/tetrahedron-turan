"""Direct packed SCS assembly for the complete seven-vertex SDP.

Graph weights and explicit six-vertex marginals are the same variables as in
the CVXPY adapter. Symmetric cone coordinates use SCS's scaled lower triangle.
"""
import argparse
from pathlib import Path
import time
import numpy as np
from scipy import sparse
from scipy.linalg import eigh
import runtime as rt
import reconstruct_optimization as ro
from seven_full_streamed import FeatureRows, load_deck
import owned_scs


def layout(dimensions):
    sizes=[d*(d+1)//2 for d in dimensions]
    offsets=np.r_[0,np.cumsum(sizes)]
    total=sum(d*d for d in dimensions[9:])
    mapping=np.full(total,-1,dtype=np.int32)
    scales=np.zeros(total)
    transpose=np.empty(total,dtype=np.int32)
    cursor=0
    for b,d in enumerate(dimensions[9:],9):
        index=np.arange(d*d,dtype=np.int32).reshape(d,d)
        transpose[cursor:cursor+d*d]=cursor+index.T.ravel()
        i,j=np.tril_indices(d)
        flat=cursor+i*d+j
        mapping[flat]=(offsets[b]-offsets[9]+j*d-j*(j-1)//2+i-j).astype(np.int32)
        scales[flat]=np.where(i==j,1.0,np.sqrt(2.0))
        cursor+=d*d
    return dict(dimensions=list(dimensions),sizes=sizes,offsets=offsets,
                mapping=mapping,scales=scales,transpose=transpose)


def pack(matrix):
    d=len(matrix);i,j=np.tril_indices(d)
    positions=j*d-j*(j-1)//2+i-j
    result=np.empty(d*(d+1)//2)
    result[positions]=0.5*(matrix[i,j]+matrix[j,i])*np.where(i==j,1,np.sqrt(2))
    return result


def unpack(vector,d):
    i,j=np.tril_indices(d)
    positions=j*d-j*(j-1)//2+i-j
    values=np.asarray(vector)[positions]/np.where(i==j,1,np.sqrt(2))
    result=np.zeros((d,d));result[i,j]=values;result[j,i]=values
    return result


def graph_columns(deck,feat,n,first,info):
    count=deck.shape[0]
    # Match CVXPY's symmetric-part operation, including any roundoff asymmetry.
    feat=0.5*(feat+feat[:,info['transpose']])
    mapped=info['mapping'][feat.indices]
    keep=mapped>=0
    prefix=np.r_[0,np.cumsum(keep,dtype=np.int64)]
    ptr=prefix[feat.indptr]
    packed=sparse.csr_matrix((feat.data[keep]*info['scales'][feat.indices[keep]],
                             mapped[keep],ptr),
                            shape=(count,int(info['offsets'][-1]-info['offsets'][9])))
    packed.sort_indices()
    identity=sparse.csr_matrix((-np.ones(count),np.arange(first,first+count),
                               np.arange(count+1)),shape=(count,n))
    result=sparse.hstack([sparse.csr_matrix(np.ones((count,1))),
        sparse.csr_matrix((count,1)),-deck,identity,
        sparse.csr_matrix((count,int(info['offsets'][9]))),-packed],format='csr')
    result.eliminate_zeros();result.sort_indices()
    return result


def marginal_columns(blocks,stationarity,n,info):
    values=[]
    for block in blocks:
        values.append(np.stack([pack(matrix) for matrix in block]))
    moment=sparse.csr_matrix(np.concatenate(values,axis=1))
    result=sparse.hstack([sparse.csr_matrix((964,1)),
        sparse.csr_matrix(np.asarray(stationarity).reshape(-1,1)),sparse.eye(964),
        sparse.csr_matrix((964,n)),-moment,
        sparse.csr_matrix((964,int(info['offsets'][-1]-info['offsets'][9])))],format='csr')
    result.eliminate_zeros();result.sort_indices()
    return result


def directory(cache,model):
    return Path(cache)/'native-packed-v1'/model


def build(cache,model,chunk=2048):
    target=directory(cache,model)
    if (target/'manifest.json').exists():
        return rt.json.loads((target/'manifest.json').read_text())
    if target.exists():
        raise FileExistsError('Partial packed cache retained; preserve it before a new build attempt')
    target.mkdir(parents=True)
    start=time.monotonic()
    oracle,blocks,objective,stationarity,metadata=rt.model(Path(cache),model)
    reader=FeatureRows(cache,model);deck=load_deck(cache,model)
    info=layout(ro.DIMS);n=reader.rows;m=966+n+int(info['offsets'][-1])
    nnz=0;hashes=[rt.hashlib.sha256() for _ in range(3)]
    with (target/'data.f64').open('wb') as data_file,(target/'indices.i64').open('wb') as index_file,(target/'indptr.i64').open('wb') as pointer_file:
        zero=np.array([0],dtype='<i8');zero.tofile(pointer_file);hashes[2].update(zero.tobytes())

        def emit(rows):
            nonlocal nnz
            assert rows.shape[1]==m and rows.has_sorted_indices
            arrays=[np.asarray(rows.data,dtype='<f8'),np.asarray(rows.indices,dtype='<i8'),
                    np.asarray(rows.indptr[1:],dtype='<i8')+nnz]
            for a,f,h in zip(arrays,[data_file,index_file,pointer_file],hashes):
                a.tofile(f);h.update(a.view(np.uint8))
            nnz+=rows.nnz

        for first in range(0,n,chunk):
            stop=min(n,first+chunk)
            emit(graph_columns(deck[first:stop],reader.read(first,stop),n,first,info))
            if first%(20*chunk)==0:
                rt.write_json(target/'progress.json',dict(rows=stop,total=n,nnz=nnz,
                    seconds=time.monotonic()-start))
                print(f'{model} packed native rows {stop}/{n}; nnz={nnz}',flush=True)
        emit(marginal_columns(blocks,stationarity,n,info))
    result=dict(status='complete',model=model,shape=[m,n+964],graph_columns=n,nnz=nnz,
        dimensions=list(ro.DIMS),cone=dict(z=966,l=n,s=list(ro.DIMS)),
        feature_manifest_sha256=rt.digest(Path(cache)/model/'manifest.json'),
        catalogue_sha256=rt.digest(Path(cache)/'seven_masks.u64'),
        construction_seconds=time.monotonic()-start,
        matrix_bytes=sum(p.stat().st_size for p in target.glob('*.?64')),
        array_sha256={name:h.hexdigest() for name,h in zip(['data.f64','indices.i64','indptr.i64'],hashes)},
        assembly='CSC graph and marginal columns; scaled symmetric lower-triangle PSD coordinates; int64 SCS indices',
        source_sha256=rt.sources())
    rt.write_json(target/'manifest.json',result)
    return result


def load(cache,model):
    target=directory(cache,model)
    meta=rt.json.loads((target/'manifest.json').read_text())
    assert meta['status']=='complete'
    assert meta['feature_manifest_sha256']==rt.digest(Path(cache)/model/'manifest.json')
    assert meta['catalogue_sha256']==rt.digest(Path(cache)/'seven_masks.u64')
    # Assign int64 buffers directly: scipy's tuple constructor otherwise narrows
    # indices to int32, then SCS's int64 wheel copies them back to int64.
    a=sparse.csc_matrix(tuple(meta['shape']))
    a.data=np.memmap(target/'data.f64',dtype='<f8',mode='r')
    a.indices=np.memmap(target/'indices.i64',dtype='<i8',mode='r')
    a.indptr=np.memmap(target/'indptr.i64',dtype='<i8',mode='r')
    assert len(a.data)==len(a.indices)==meta['nnz']
    assert len(a.indptr)==meta['shape'][1]+1 and a.indptr[-1]==meta['nnz']
    a.has_sorted_indices=True;a.has_canonical_format=True
    b=np.zeros(meta['shape'][0]);b[0]=1
    return a,b,meta


def solve(master,remaining,output,full=True):
    import scs
    assert full and scs.__sizeof_int__==8 and scs.__sizeof_float__==8
    started=time.monotonic()
    matrix=directory(master.full_cache,master.full_model)
    meta=rt.json.loads((matrix/'manifest.json').read_text())
    assert meta['status']=='complete'
    assert meta['feature_manifest_sha256']==rt.digest(master.full_cache/master.full_model/'manifest.json')
    n=len(master.masks);c=np.r_[np.zeros(n),-master.objective]
    b=np.zeros(meta['shape'][0]);b[0]=1
    reserve=150 if len(ro.DIMS)>12 else 30
    available=remaining-(time.monotonic()-started)
    if available<=reserve:
        return dict(success=False,backend_status='insufficient_time_for_export_and_pricing',
                    solve_seconds=time.monotonic()-started)
    result=owned_scs.run(master.full_cache,matrix,meta,b,c,output/'native-owned',
                         budget=available,reserve=reserve)
    if not result['success']:
        return dict(success=False,backend_status=result['backend_status'],
                    solve_seconds=time.monotonic()-started)
    diagnostics=result['info'];status=int(diagnostics['status_val'])
    assembled=diagnostics['assembly_seconds']
    cap=diagnostics['actual_time_limit_setting_seconds']
    weights=np.asarray(result['x'][:n]);x=np.asarray(result['x'][n:])
    factors=[];repairs=[];cursor=966+n
    for d in ro.DIMS:
        length=d*(d+1)//2
        q=unpack(result['y'][cursor:cursor+length],d);cursor+=length
        eigenvalues,vectors=eigh(q,driver='evr');positive=eigenvalues>0
        factors.append(np.sqrt(eigenvalues[positive])[:,None]*vectors[:,positive].T)
        repairs.append(dict(minimum_before=float(eigenvalues[0]),
            negative_eigenvalues=int(np.count_nonzero(eigenvalues<0)),
            projection_frobenius_norm=float(np.linalg.norm(np.minimum(eigenvalues,0)))))
    tau=-float(result['y'][1]);six=master.objective+tau*master.stationarity
    for block,f in zip(master.blocks,factors[:9]):
        six+=np.einsum('hij,ij->h',block,f.T@f)
    grams=[f.T@f for f in factors[9:]]
    clean_info={k:(None if isinstance(v,float) and not np.isfinite(v) else v)
                for k,v in diagnostics.items()}
    rt.write_json(output/'native-direct-diagnostics.json',dict(backend_info=clean_info,
        packed_manifest_sha256=rt.digest(directory(master.full_cache,master.full_model)/'manifest.json'),
        packed_matrix_bytes=meta['matrix_bytes'],shared_packed_construction_seconds=meta['construction_seconds'],
        assembly_seconds=assembled,actual_time_limit_setting_seconds=cap,
        same_sdp_as_auxiliary_marginal_cvxpy_formulation=True,
        native_build_manifest_sha256=rt.digest(master.full_cache/'owned-scs-v4/manifest.json'),
        memory_policy='File-loaded malloc-owned A transferred into SCS; only A and its indirect transpose retained',
        timing_policy='Subtract input/setup cost; admit another iteration only with 1.15 times observed iteration cost plus one second remaining'))
    return dict(success=True,backend_status='optimal' if status==1 else 'optimal_inaccurate',
        y=weights,objective=float(master.objective@x),six=six,grams=grams,tau=tau,
        factors=factors,psd_repairs=repairs,solve_seconds=time.monotonic()-started,
        assembly_seconds=assembled,backend_solve_seconds=float(diagnostics['solve_time'])/1000,
        backend_iterations=int(diagnostics['iter']),
        backend_raw_status=diagnostics['status'],
        backend_time_limit_reached='time_limit_secs' in diagnostics['status'],
        marginal_equality_residual=float(np.max(np.abs(x-master.deck.T@weights))))


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cache',type=Path,required=True)
    p.add_argument('--model',choices=['M7-no5','M7-all5'],required=True)
    args=p.parse_args()
    print(rt.json.dumps(build(args.cache.resolve(),args.model)))
