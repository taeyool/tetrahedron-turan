"""Sparse, disk-backed complete seven-vertex coefficient matrices.

The catalogue is a proved relabeling quotient, not a sampled working set.
CSR arrays are streamed to disk before mapping them into full-model arms.
"""
from pathlib import Path
import time
import runtime as rt
import numpy as np
from scipy import sparse
import reconstruct_optimization as ro


def build(cache, name, chunk=2048):
    target=cache/name
    if (target/'manifest.json').exists():
        return rt.json.loads((target/'manifest.json').read_text())
    if target.exists():
        raise FileExistsError('Partial feature cache retained; use a new cache attempt')
    target.mkdir(parents=True)
    start=time.monotonic()
    oracle,blocks,objective,stat,metadata=rt.model(cache,name)
    masks=np.fromfile(cache/'seven_masks.u64',dtype='<u8')
    catalogue=rt.json.loads((cache/'seven-catalog.json').read_text())
    assert len(masks)==catalogue['seven_vertex_classes'] and catalogue['raw_extensions']==13051375
    writers={}; nnz={'deck':0,'feat':0}
    try:
        for kind in nnz:
            writers[kind]=[open(target/f'{kind}.{suffix}','wb') for suffix in ['data.f64','indices.i32','indptr.i64']]
            np.array([0],'<i8').tofile(writers[kind][2])
        for i in range(0,len(masks),chunk):
            deck,feat=oracle.features(masks[i:i+chunk])
            np.testing.assert_allclose(deck@objective,[int(m).bit_count()/35 for m in masks[i:i+chunk]],atol=2e-15,rtol=0)
            for kind,a in [('deck',deck),('feat',feat)]:
                a.data.astype('<f8',copy=False).tofile(writers[kind][0])
                a.indices.astype('<i4',copy=False).tofile(writers[kind][1])
                (a.indptr[1:].astype('<i8')+nnz[kind]).tofile(writers[kind][2])
                nnz[kind]+=a.nnz
            if i%(chunk*20)==0:
                for streams in writers.values():
                    for f in streams:f.flush()
                rt.write_json(target/'progress.json',dict(status='constructing',rows=min(i+chunk,len(masks)),total=len(masks),nnz=nnz,seconds=time.monotonic()-start))
                print(f'{name} full feature rows {min(i+chunk,len(masks))}/{len(masks)} nnz={nnz}',flush=True)
    finally:
        for streams in writers.values():
            for f in streams:f.close()
    result=dict(status='complete',model=name,rows=len(masks),raw_extensions=oracle.raw_count,
        dimensions=list(ro.DIMS),feature_columns=int(ro.OFFSETS[-1]),nnz=nnz,
        construction_seconds=time.monotonic()-start,ordered_blocks=metadata,
        catalogue_sha256=rt.digest(cache/'seven_masks.u64'),source_sha256=rt.sources(),
        coefficient_bytes=sum(p.stat().st_size for p in target.glob('*.f64'))+sum(p.stat().st_size for p in target.glob('*.i32'))+sum(p.stat().st_size for p in target.glob('*.i64')))
    rt.write_json(target/'manifest.json',result)
    return result


def load(cache,name):
    target=cache/name
    meta=rt.json.loads((target/'manifest.json').read_text())
    assert meta['status']=='complete'
    result=[]
    for kind,columns in [('deck',964),('feat',meta['feature_columns'])]:
        arrays=[np.memmap(target/f'{kind}.{suffix}',dtype=dtype,mode='r') for suffix,dtype in [('data.f64','<f8'),('indices.i32','<i4'),('indptr.i64','<i8')]]
        a=sparse.csr_matrix(tuple(arrays),shape=(meta['rows'],columns),copy=False)
        assert a.nnz==meta['nnz'][kind]
        result.append(a)
    return np.memmap(cache/'seven_masks.u64',dtype='<u8',mode='r'),*result,meta


def install(master,cache,name):
    start=time.monotonic()
    masks,deck,feat,meta=load(cache,name)
    assert not master.cuts
    master.h.deleteCols(master.h.getNumCol(),np.arange(master.h.getNumCol(),dtype=np.int32))
    assert master.h.getNumCol()==0 and master.neq==2
    for i in range(0,len(masks),20000):
        d=deck[i:i+20000];n=d.shape[0]
        # s(H) has denominator 60 and deletion averaging denominator 7.
        # Recover exact zeros before HiGHS applies its small-matrix warning.
        values=np.asarray(d@master.stationarity)
        exact_values=np.rint(values*420)/420
        np.testing.assert_allclose(values,exact_values,atol=1e-13,rtol=0)
        eq=sparse.csc_matrix(np.vstack([np.ones(n),exact_values]))
        eq.eliminate_zeros()
        result=master.h.addCols(n,np.asarray(d@master.objective),np.zeros(n),np.full(n,master.highspy.kHighsInf),eq.nnz,eq.indptr.astype(np.int32),eq.indices.astype(np.int32),eq.data)
        assert result==master.highspy.HighsStatus.kOk
    master.masks=masks;master.deck=deck;master.feat=feat
    master.seen=set();master.signatures=set()
    return dict(full_universe_classes=len(masks),full_raw_extensions=meta['raw_extensions'],
        full_feature_cache_sha256=rt.digest(cache/name/'manifest.json'),
        full_install_seconds=time.monotonic()-start,shared_cold_feature_construction_seconds=meta['construction_seconds'],
        full_coefficient_bytes=meta['coefficient_bytes'],stationarity_lp_integer_denominator=420)


if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--cache',type=Path,required=True);p.add_argument('--model',choices=['M7-no5','M7-all5'],required=True)
    a=p.parse_args();print(rt.json.dumps(build(a.cache.resolve(),a.model)),flush=True)
