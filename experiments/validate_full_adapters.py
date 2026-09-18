"""Validate streamed full LP coefficients and the serialized direct SCS operator."""
import argparse
from pathlib import Path
from types import SimpleNamespace
import time
import numpy as np
import runtime as rt
import reconstruct_optimization as ro
import seven_full_native as native
import seven_full_streamed as streamed


def validate(cache,model,output):
    started=time.monotonic()
    oracle,blocks,objective,stat,metadata=rt.model(cache,model)
    rng=np.random.default_rng(612)
    import cvxpy as cp
    from cvxpy.reductions.solvers.conic_solvers.scs_conif import SCS
    for d in [2,3,7]:
        matrix=rng.normal(size=(d,d))
        operator=SCS.psd_format_mat(cp.Variable((d,d)) >> 0)
        np.testing.assert_allclose(native.pack(matrix),operator@matrix.ravel(order='F'),atol=1e-14,rtol=1e-14)
        np.testing.assert_allclose(native.unpack(native.pack(matrix),d),(matrix+matrix.T)/2,atol=1e-14,rtol=1e-14)

    a,b,meta=native.load(cache,model)
    for filename,digest in meta['array_sha256'].items():
        assert rt.digest(native.directory(cache,model)/filename)==digest
    masks=np.fromfile(cache/'seven_masks.u64',dtype='<u8');n=len(masks)
    sample=np.sort(np.unique(np.r_[0,n-1,rng.choice(n,30,replace=False)]))
    deck,feat=oracle.features(masks[sample])
    indices=np.r_[sample,np.arange(n,n+964)]
    selected=a[:,indices]
    del a
    weights=rng.normal(size=len(sample));x=rng.normal(size=964)
    actual=selected@np.r_[weights,x]
    expected=np.zeros(meta['shape'][0]);expected[0]=weights.sum();expected[1]=stat@x
    expected[2:966]=x-deck.T@weights;expected[966+sample]=-weights
    moments=[np.einsum('h,hij->ij',x,block) for block in blocks]
    flat=feat.T@weights
    moments += [flat[lo:hi].reshape(d,d) for lo,hi,d in zip(ro.OFFSETS[:-1],ro.OFFSETS[1:],ro.DIMS[9:])]
    cursor=966+n
    for matrix in moments:
        packed=native.pack(matrix);expected[cursor:cursor+len(packed)]=-packed;cursor+=len(packed)
    np.testing.assert_allclose(actual,expected,atol=2e-12,rtol=2e-12)
    forward_error=float(np.max(np.abs(actual-expected)))
    del actual,expected,moments,flat

    # Check the exported tau sign and PSD-dual reconstruction against the
    # serialized operator's transpose, independently of any optimization solve.
    tau=0.13;bound=0.7;six=objective+tau*stat
    dual=np.zeros(meta['shape'][0]);dual[0]=bound;dual[1]=-tau
    cursor=966+n;sample_quadratics=np.zeros(len(sample));directions=[]
    for block_index,d in enumerate(ro.DIMS):
        v=rng.normal(size=d);v/=np.linalg.norm(v);v*=0.1
        q=np.outer(v,v);packed=native.pack(q)
        dual[cursor:cursor+len(packed)]=packed;cursor+=len(packed)
        if block_index<9:
            six+=np.einsum('hij,ij->h',blocks[block_index],q)
        else:
            lo,hi=ro.OFFSETS[block_index-9:block_index-7]
            sample_quadratics+=feat[:,lo:hi]@q.ravel()
        if block_index in [0,9,len(ro.DIMS)-1]:
            directions.append((block_index,v))
    dual[2:966]=six
    transposed=selected.T@dual
    np.testing.assert_allclose(transposed[:len(sample)],bound-deck@six-sample_quadratics,atol=2e-12,rtol=2e-12)
    np.testing.assert_allclose(transposed[len(sample):],objective,atol=2e-12,rtol=2e-12)
    del dual,selected

    full_deck=streamed.load_deck(cache,model)
    reader=streamed.FeatureRows(cache,model)
    master=SimpleNamespace(masks=masks,blocks=blocks,deck=full_deck,feature_rows=reader)
    sixcuts=[np.einsum('i,hij,j->h',v,blocks[k],v,optimize=True) if k<9 else np.zeros(964)
             for k,v in directions]
    values=streamed.streamed_cut_values(master,directions,sixcuts)
    reference=np.empty((len(sample),len(directions)))
    for column,(block_index,v) in enumerate(directions):
        if block_index<9:
            reference[:,column]=deck@np.einsum('hij,ij->h',blocks[block_index],np.outer(v,v))
        else:
            lo,hi=ro.OFFSETS[block_index-9:block_index-7]
            reference[:,column]=feat[:,lo:hi]@np.outer(v,v).ravel()
    np.testing.assert_allclose(values[sample],reference,atol=2e-13,rtol=2e-12)
    result=dict(status='passed',model=model,rows=n,sampled_full_columns=len(sample),
        all_marginal_columns=964,all_psd_blocks=len(ro.DIMS),
        cvxpy_scs_triangle_format_agrees=True,serialized_array_hashes_match=True,
        serialized_forward_operator_max_error=forward_error,
        dual_reconstruction_signs_and_scaling_agree=True,
        streamed_full_cut_directions=len(directions),
        streamed_sample_coefficient_max_error=float(np.max(np.abs(values[sample]-reference))),
        no_optimization_performed=True,seconds=time.monotonic()-started,
        packed_manifest_sha256=rt.digest(native.directory(cache,model)/'manifest.json'),
        source_sha256=rt.sources())
    rt.write_json(output,result);print(rt.json.dumps(result))


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cache',type=Path,required=True)
    p.add_argument('--model',choices=['M7-no5','M7-all5'],required=True)
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args();validate(args.cache.resolve(),args.model,args.output)
