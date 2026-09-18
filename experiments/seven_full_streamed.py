"""Bounded coefficient reads for complete-model arms, without feature-wide copies."""
from pathlib import Path
from types import MethodType
import time
import numpy as np
from scipy import sparse
import runtime as rt
import reconstruct_optimization as ro


class FeatureRows:
    def __init__(self, cache, model):
        self.path = Path(cache)/model
        self.meta = rt.json.loads((self.path/'manifest.json').read_text())
        assert self.meta['status'] == 'complete'
        self.rows = self.meta['rows']
        self.columns = self.meta['feature_columns']
        self.ptr = np.fromfile(self.path/'feat.indptr.i64', dtype='<i8')
        assert len(self.ptr) == self.rows+1 and self.ptr[-1] == self.meta['nnz']['feat']

    def read(self, start, stop):
        assert 0 <= start <= stop <= self.rows
        lo, hi = map(int, self.ptr[[start, stop]])
        # Ordinary bounded reads release process pages with each chunk, unlike a
        # whole-file mapping whose touched pages accumulate in the working set.
        data = np.fromfile(self.path/'feat.data.f64', dtype='<f8', count=hi-lo, offset=lo*8)
        indices = np.fromfile(self.path/'feat.indices.i32', dtype='<i4', count=hi-lo, offset=lo*4)
        assert len(data) == hi-lo and len(indices) == hi-lo
        return sparse.csr_matrix((data, indices, self.ptr[start:stop+1]-lo),
                                 shape=(stop-start, self.columns), copy=False)


def load_deck(cache, model):
    target = Path(cache)/model
    meta = rt.json.loads((target/'manifest.json').read_text())
    arrays = [np.fromfile(target/f'deck.{suffix}', dtype=dtype) for suffix,dtype in
              [('data.f64','<f8'),('indices.i32','<i4'),('indptr.i64','<i8')]]
    return sparse.csr_matrix(tuple(arrays), shape=(meta['rows'],964), copy=False)


def moments(master, sol):
    y = np.asarray(sol.col_value)
    x = master.deck.T@y
    flat = np.zeros(master.feature_rows.columns)
    for start in range(0,len(y),4096):
        stop = min(start+4096,len(y))
        if np.any(y[start:stop]):
            flat += master.feature_rows.read(start,stop).T@y[start:stop]
    matrices = [np.einsum('h,hij->ij',x,b) for b in master.blocks]
    matrices += [flat[a:b].reshape(d,d) for a,b,d in zip(ro.OFFSETS[:-1],ro.OFFSETS[1:],ro.DIMS[9:])]
    return y,x,matrices


def streamed_cut_values(master, cuts, six):
    values = np.empty((len(master.masks),len(cuts)))
    groups=[]
    for block in sorted({b for b,v in cuts if b>=9}):
        indices=[i for i,(b,v) in enumerate(cuts) if b==block]
        batches=[]
        for first in range(0,len(indices),32):
            selected=indices[first:first+32]
            products=np.array([np.outer(cuts[i][1],cuts[i][1]).ravel() for i in selected])
            batches.append((selected,products))
        groups.append((block,batches))
    six_matrix=np.asarray(six).T
    for start in range(0,len(master.masks),2048):
        stop = min(start+2048,len(master.masks))
        rows=np.asarray(master.deck[start:stop]@six_matrix)
        # Preserve Master.coefficients' formulas and batch size; skip blocks with
        # no requested cut, and construct each outer product only once.
        if groups:
            features=master.feature_rows.read(start,stop)
            for block,batches in groups:
                part=features[:,ro.OFFSETS[block-9]:ro.OFFSETS[block-8]]
                for selected,products in batches:
                    rows[:,selected]=part@products.T
        values[start:stop]=rows
    return values


def add_cuts(master, cuts):
    if not cuts:
        return
    six = []
    for b,v in cuts:
        six.append(np.einsum('i,hij,j->h',v,master.blocks[b],v,optimize=True)
                   if b<9 else np.zeros(964))
    values = streamed_cut_values(master,cuts,six)
    for first in range(0,len(cuts),8):
        last = min(first+8,len(cuts))
        rows = sparse.csr_matrix(values[:,first:last].T)
        before=master.h.getNumRow()
        result = master.h.addRows(last-first,np.zeros(last-first),
            np.full(last-first,master.highspy.kHighsInf),rows.nnz,
            rows.indptr.astype(np.int32),rows.indices.astype(np.int32),rows.data)
        assert result != master.highspy.HighsStatus.kError
        assert master.h.getNumRow()==before+last-first
    master.cuts.extend(cuts)
    master.sixcuts.extend(six)


def install(master, cache, model):
    start = time.monotonic()
    reader = FeatureRows(cache,model)
    deck = load_deck(cache,model)
    masks = np.fromfile(Path(cache)/'seven_masks.u64',dtype='<u8')
    assert len(masks)==reader.rows and not master.cuts and master.neq==2
    master.h.deleteCols(master.h.getNumCol(),np.arange(master.h.getNumCol(),dtype=np.int32))
    for first in range(0,len(masks),20000):
        d=deck[first:first+20000];n=d.shape[0]
        values=np.asarray(d@master.stationarity)
        exact_values=np.rint(values*420)/420
        np.testing.assert_allclose(values,exact_values,atol=1e-13,rtol=0)
        eq=sparse.csc_matrix(np.vstack([np.ones(n),exact_values]));eq.eliminate_zeros()
        result=master.h.addCols(n,np.asarray(d@master.objective),np.zeros(n),
            np.full(n,master.highspy.kHighsInf),eq.nnz,eq.indptr.astype(np.int32),
            eq.indices.astype(np.int32),eq.data)
        assert result==master.highspy.HighsStatus.kOk
    master.masks=masks;master.deck=deck;master.feat=None
    master.feature_rows=reader;master.full_cache=Path(cache);master.full_model=model
    master.seen=set();master.signatures=set()
    master.add_cuts=MethodType(add_cuts,master)
    meta=reader.meta
    return dict(full_universe_classes=len(masks),full_raw_extensions=meta['raw_extensions'],
        full_feature_cache_sha256=rt.digest(Path(cache)/model/'manifest.json'),
        full_install_seconds=time.monotonic()-start,
        shared_cold_feature_construction_seconds=meta['construction_seconds'],
        full_coefficient_bytes=meta['coefficient_bytes'],stationarity_lp_integer_denominator=420,
        full_coefficient_access='bounded ordinary row reads; eight LP rows per insertion; no whole-feature mapping')
