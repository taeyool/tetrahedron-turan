#!/usr/bin/env python3
"""Five-root, six-vertex flag products with complete seven-vertex pricing.

All 23 root types are canonical unlabeled K4-free five-vertex 3-graphs.
Flags retain every labeled root coordinate. Features use the unconditional
ordered-root product normalization (7)_5 * 2 = 5040. A canonical root labeling
followed by the FULL type automorphism action saves redundant work without
restricting the PSD matrices to invariant flag vectors.
"""
from __future__ import annotations
import argparse
import ctypes
import functools
import hashlib
import itertools
import json
from pathlib import Path
import subprocess
import time

import numpy as np
from scipy import sparse
from scipy.linalg import eigh
import reconstruct_optimization as ro

HERE = Path(__file__).resolve().parent
OLD_SIZE = 49 + 236**2 + 191**2


@functools.lru_cache(maxsize=1)
def _tables():
    fs = ro.fs
    permutations = list(itertools.permutations(range(5)))
    pairs = list(itertools.combinations(range(5), 2))
    pix = {p: i for i,p in enumerate(pairs)}
    masks = np.arange(1024, dtype=np.uint16)
    root_perm = np.zeros((120,1024), np.uint16)
    pair_perm = np.zeros((120,1024), np.uint16)
    for k,p in enumerate(permutations):
        for j,dest in enumerate(fs.permutation_edge_map(5,p)):
            root_perm[k] |= ((masks >> j) & 1) << dest
        for j,(a,b) in enumerate(pairs):
            dest = pix[tuple(sorted((p[a],p[b])))];pair_perm[k] |= ((masks >> j) & 1) << dest
    canon_perm = np.argmin(root_perm,axis=0).astype(np.uint8)
    canonical = root_perm[canon_perm,np.arange(1024)]
    sigmas = sorted({int(canonical[m]) for m in range(1024) if fs.is_k4free(m,5)})
    entries = []
    for sigma in sigmas:
        root6 = sum(1 << fs.edge_index(6)[e] for j,e in enumerate(fs.triples(5)) if (sigma >> j) & 1)
        pairs6 = [fs.edge_index(6)[(a,b,5)] for a,b in pairs]
        rawflags = [root6 | sum(1 << pairs6[j] for j in range(10) if (link >> j) & 1) for link in range(1024)]
        flags = sorted(f for f in rawflags if fs.is_k4free(f,6))
        index = {f:i for i,f in enumerate(flags)}
        flag_ids = np.array([index.get(f,-1) for f in rawflags],np.int16)
        automorphism_ids = np.flatnonzero(root_perm[:,sigma] == sigma)
        flag_perms = []
        for k in automorphism_ids:
            # Flags have only one unlabeled vertex, so no rooted canon quotient remains.
            ids = np.empty(len(flags),np.int32)
            for link,old in enumerate(flag_ids):
                if old >= 0:ids[old] = flag_ids[pair_perm[k,link]]
            assert np.array_equal(np.sort(ids),np.arange(len(flags)))
            flag_perms.append(ids)
        entries.append({"sigma":sigma,"roots":5,"flag_vertices":6,"product_vertices":7,
                        "dimension":len(flags),"denominator":5040,"flags":flags,
                        "automorphisms":[permutations[k] for k in automorphism_ids],
                        "flag_permutations":flag_perms,"flag_ids":flag_ids})
    assert len(entries)==23
    return entries,canonical,canon_perm,pair_perm


def catalog():
    """Ordered metadata (sigma increasing); entries include NumPy action tables."""
    return _tables()[0]


def catalog_json():
    return [{k:v for k,v in entry.items() if k not in ("flag_permutations","flag_ids")} for entry in catalog()]


def _valid_masks(masks):
    masks=np.ascontiguousarray(masks,dtype=np.uint64)
    if masks.ndim!=1 or np.any(masks >= (1<<35)):
        raise ValueError("not a vector of seven-vertex masks")
    if any(np.any((masks & k4)==k4) for k4 in ro.fs.k4_masks(7)):
        raise ValueError("five-root oracle requires K4-free masks")
    return masks


class Oracle5:
    order = 7
    global_pricing = True
    deck_denominator = 7
    feature_denominator = 5040

    def __init__(self, base, type_masks, cache=None):
        self.base,self.cert,self.raw_count = base,base.cert,base.raw_count
        self.type_masks = list(map(int,type_masks))
        if len(set(self.type_masks)) != len(self.type_masks):raise ValueError("duplicate five-root types")
        by_sigma = {e["sigma"]:e for e in catalog()}
        self.entries = [by_sigma[s] for s in self.type_masks]
        self.dimensions = [e["dimension"] for e in self.entries]
        self.offsets = np.cumsum([0,49,236**2,191**2]+[d*d for d in self.dimensions])
        cache = Path(cache) if cache is not None else Path(base.lib._name).parent
        cache.mkdir(parents=True,exist_ok=True)
        libpath = cache / "five_root_oracle.dylib"
        sources = [HERE/f for f in ("five_root_oracle.cpp","optimization_oracle.cpp","optimization_oracle_tail.inc","optimization_order8.inc")]
        if not libpath.exists() or max(p.stat().st_mtime for p in sources)>libpath.stat().st_mtime:
            temporary=libpath.with_suffix(".tmp.dylib")
            subprocess.run(["c++","-O3","-std=c++17","-pthread","-shared","-fPIC",str(sources[0]),"-o",str(temporary)],check=True)
            temporary.replace(libpath)
        self.lib = ctypes.CDLL(str(libpath))
        ptr=np.ctypeslib.ndpointer
        self.lib.initialize.argtypes=[ptr(np.uint32),ctypes.c_int];self.lib.initialize.restype=ctypes.c_int
        self.lib.initialize_five.argtypes=[ptr(np.int16),ptr(np.uint8),ptr(np.uint16),ptr(np.int16),ptr(np.int32),ctypes.c_int]
        self.lib.get_five_pairs.argtypes=[ptr(np.uint64),ctypes.c_int,ptr(np.int16),ptr(np.uint32)]
        self.lib.price_five.argtypes=[ptr(np.float64)]*4+[ctypes.c_int,ctypes.c_int,ptr(np.float64),ptr(np.uint64)]
        self.lib.eval_five_exact.argtypes=[ptr(np.uint64),ctypes.c_int]+[ptr(np.int64)]*5
        self.lib.eval_five_exact.restype=ctypes.c_int
        self.lib.price_five_exact.argtypes=[ptr(np.int64)]*4+[ctypes.c_int,ctypes.c_int,ptr(np.int64),ptr(np.uint64)]
        self.lib.price_five_exact.restype=ctypes.c_int
        self._tables_ready=False
        self._activate()

    # The shared C library contains a single current model. Reactivating permits
    # multiple wrappers with different subsets to coexist safely in one process.
    _active=None
    def _activate(self):
        if Oracle5._active is self:return
        n=self.lib.initialize(np.array(self.cert["H_representatives"],np.uint32),964)
        assert n==self.raw_count
        _,canonical,cp,pp=_tables()
        selected={s:i for i,s in enumerate(self.type_masks)}
        typeids=np.array([selected.get(int(c),-1) for c in canonical],np.int16)
        fi=np.stack([e["flag_ids"] for e in self.entries]) if self.entries else np.empty((0,1024),np.int16)
        self.lib.initialize_five(typeids,cp,pp,np.ascontiguousarray(fi),np.array(self.dimensions,np.int32),len(self.entries))
        Oracle5._active=self

    def pairs(self,masks):
        """Canonical pairs per 21 rootsets; columns index the unsymmetrized blocks."""
        self._activate();masks=_valid_masks(masks)
        types=np.empty((len(masks),21),np.int16);pairs=np.empty((len(masks),21),np.uint32)
        self.lib.get_five_pairs(masks,len(masks),types,pairs)
        return types,pairs

    def features(self,masks):
        masks=_valid_masks(masks)
        deck,old=self.base.features(masks)
        types,pairs=self.pairs(masks)
        blocks=[]
        for t,entry in enumerate(self.entries):
            d=entry["dimension"];rows,pos=np.nonzero(types==t);v=pairs[rows,pos]
            aa,bb=v//d,v%d
            rr=[];cc=[]
            for p in entry["flag_permutations"]:
                a,b=p[aa],p[bb]
                rr.extend((rows,rows));cc.extend((a*d+b,b*d+a))
            rows2=np.concatenate(rr) if rr else np.empty(0,np.int64)
            cols2=np.concatenate(cc) if cc else np.empty(0,np.int64)
            block=sparse.csr_matrix((np.ones(len(rows2),np.int16),(rows2,cols2)),shape=(len(masks),d*d))
            block=block.astype(np.float64);block.data/=5040
            blocks.append(block)
        feat=sparse.hstack([old[:,:OLD_SIZE]]+blocks,format="csr")
        feat.eliminate_zeros();feat.sort_indices();deck.sort_indices()
        return deck,feat

    def moment_matrices(self,masks,weights):
        """Full PSD matrices, with all positive/zero/signed supplied weights retained."""
        weights=np.asarray(weights,dtype=float)
        if len(weights)!=len(masks) or not np.all(np.isfinite(weights)):raise ValueError("invalid weights")
        types,pairs=self.pairs(masks);matrices=[]
        for t,e in enumerate(self.entries):
            d=e["dimension"];rows,pos=np.nonzero(types==t)
            raw=np.bincount(pairs[rows,pos],weights=weights[rows],minlength=d*d).reshape(d,d)
            matrix=np.zeros((d,d))
            # Sum over actions; inverse versus forward is immaterial for a group.
            for p in e["flag_permutations"]:matrix+=raw[np.ix_(p,p)]
            matrix=(matrix+matrix.T)/5040;matrices.append(matrix)
        return matrices

    def _symmetrize(self,grams,integer=False):
        if len(grams)!=len(self.entries):raise ValueError("wrong number of five-root Grams")
        out=[]
        for q,e in zip(grams,self.entries):
            q=np.asarray(q);d=e["dimension"]
            if q.shape!=(d,d):raise ValueError("wrong Gram dimensions")
            if integer:
                if not np.issubdtype(q.dtype,np.integer):raise ValueError("integer Grams required")
                bound=max(abs(int(q.min(initial=0))),abs(int(q.max(initial=0))))*2*len(e["automorphisms"])
                if bound>=2**63:raise OverflowError("automorphism sum does not fit signed int64")
                if not np.array_equal(q,q.T):raise ValueError("Gram must be symmetric")
                sym=sum((q[np.ix_(p,p)].astype(np.int64) for p in e["flag_permutations"]),start=np.zeros((d,d),np.int64))*2
            else:
                if not np.all(np.isfinite(q)) or not np.allclose(q,q.T,atol=1e-12,rtol=1e-12):raise ValueError("finite symmetric Gram required")
                sym=sum(q[np.ix_(p,p)] for p in e["flag_permutations"])/2520
            out.append(sym.ravel())
        return np.ascontiguousarray(np.concatenate(out) if out else np.empty(0),dtype=np.int64 if integer else np.float64)

    def price(self,six,grams,threads=4,top=2):
        self._activate()
        if threads<1 or top<1:raise ValueError("positive threads and top required")
        six=np.asarray(six,dtype=float)
        if six.shape!=(964,) or not np.all(np.isfinite(six)):raise ValueError("invalid six coefficients")
        if len(grams)!=3+len(self.entries):raise ValueError("wrong Gram count")
        if not all(np.all(np.isfinite(q)) for q in grams):raise ValueError("nonfinite Gram")
        q1=np.array([grams[0][i,j]/70 for i in range(7) for j in range(i,7)])
        q3=np.concatenate([sum(q[np.ix_(p,p)] for p in perms).ravel()/630 for q,perms in zip(grams[1:3],self.base.perms)])
        q5=self._symmetrize(grams[3:])
        if not all(np.all(np.isfinite(q)) for q in (q1,q3,q5)):
            raise FloatingPointError("symmetrized pricing coefficients overflowed")
        values=np.empty((964,top));masks=np.empty((964,top),np.uint64)
        self.lib.price_five(np.ascontiguousarray(six/7),q1,q3,q5,threads,top,values,masks)
        if np.any(np.isnan(values)) or np.any(np.isposinf(values)):raise FloatingPointError("invalid pricing result")
        return values.ravel(),masks.ravel()

    def _exact_args(self,six,q1,q3,grams5):
        out=[]
        for q,shape in zip((six,q1,q3),((964,),(28,),(236**2+191**2,))):
            q=np.asarray(q)
            if q.shape!=shape or not np.issubdtype(q.dtype,np.signedinteger):raise ValueError("signed integer coefficient table required")
            out.append(np.ascontiguousarray(q,np.int64))
        return out+[self._symmetrize(grams5,integer=True)]

    def eval_exact(self,masks,six,q1,q3,grams5):
        """Integer numerator: seven six-tables +70 q1 +105 q3 +2 sum Aut Q5.

        For denominator5040 M²: six is the usual720 M² coefficient table;
        q1 is72 times the raw Gram's upper triangle; q3 is8 times each raw
        three-root Gram summed over its six root permutations.
        """
        self._activate();masks=_valid_masks(masks);out=np.empty(len(masks),np.int64)
        if self.lib.eval_five_exact(masks,len(masks),*self._exact_args(six,q1,q3,grams5),out):raise OverflowError("exact column exceeds signed int64")
        return out

    def price_exact(self,six,q1,q3,grams5,threads=4,top=1):
        """Complete 13,051,375-column integer scan; format as eval_exact."""
        self._activate()
        if threads<1 or top<1:raise ValueError("positive threads and top required")
        values=np.empty((964,top),np.int64);masks=np.empty((964,top),np.uint64)
        if self.lib.price_five_exact(*self._exact_args(six,q1,q3,grams5),threads,top,values,masks):raise OverflowError("exact column exceeds signed int64")
        return values.ravel(),masks.ravel()


def moment_matrices(masks,weights,type_masks=None,cache=ro.ROOT/'.research-repro/cache'):
    base=ro.Oracle(Path(cache))
    oracle=Oracle5(base,[e['sigma'] for e in catalog()] if type_masks is None else type_masks,cache)
    return oracle.moment_matrices(masks,weights)


def screen(primal,output_dir,cache,eigenvectors=8):
    """Write lowest directions per type; full saved weights enter every matrix."""
    started=time.monotonic();primal=Path(primal);output_dir=Path(output_dir);output_dir.mkdir(parents=True,exist_ok=True)
    raw=primal.read_bytes();saved=np.load(primal,allow_pickle=False)
    mask_key='masks' if 'masks' in saved else 'column_masks'
    weight_key='weights' if 'weights' in saved else 'primal'
    masks=saved[mask_key];weights=saved[weight_key]
    base=ro.Oracle(Path(cache));oracle=Oracle5(base,[e['sigma'] for e in catalog()],cache)
    matrices=oracle.moment_matrices(masks,weights)
    arrays={'types':np.array(oracle.type_masks,np.int32)};rows=[]
    for entry,matrix in zip(oracle.entries,matrices):
        t0=time.monotonic();d=entry['dimension'];k=min(eigenvectors,d)
        eigenvalues,vectors=eigh(matrix,subset_by_index=(0,k-1),driver='evr',check_finite=False)
        mass=float(matrix.sum());norm=float(np.linalg.norm(matrix,ord='fro'))
        sigma=entry['sigma'];arrays[f'vectors_{sigma}']=vectors;arrays[f'eigenvalues_{sigma}']=eigenvalues
        row={'sigma':sigma,'dimension':d,'automorphism_order':len(entry['automorphisms']),
             'lambda_min':float(eigenvalues[0]),'sigma_mass':mass,
             'conditional_lambda_min':float(eigenvalues[0]/mass) if mass>0 else None,
             'relative_lambda_min':float(eigenvalues[0]/norm) if norm>0 else None,
             'unlabeled_type_density':float(mass*120/len(entry['automorphisms'])),
             'frobenius_norm':norm,'eigenvalues':eigenvalues.tolist(),
             'eigen_residual_max':float(np.linalg.norm(matrix@vectors-vectors*eigenvalues,axis=0).max()),
             'seconds':time.monotonic()-t0}
        rows.append(row);print(json.dumps(row),flush=True)
    result={'primal_path':str(primal),'primal_sha256':hashlib.sha256(raw).hexdigest(),
            'mask_count':len(masks),'positive_weights':int(np.count_nonzero(weights>0)),
            'negative_weights':int(np.count_nonzero(weights<0)),'weights_sum':float(weights.sum()),
            'weight_threshold_applied':False,'feature_denominator':5040,'seconds':time.monotonic()-started,
            'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [HERE/'five_root_oracle.py',HERE/'five_root_oracle.cpp']},
            'types':rows,'ranking_by_lambda_min':[r['sigma'] for r in sorted(rows,key=lambda r:r['lambda_min'])]}
    np.savez_compressed(output_dir/'directions.npz',**arrays)
    (output_dir/'screening.json').write_text(json.dumps(result,indent=2)+'\n')
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--catalog',action='store_true')
    parser.add_argument('--primal',type=Path)
    parser.add_argument('--output-dir',type=Path)
    parser.add_argument('--cache',type=Path,default=ro.ROOT/'.research-repro/cache')
    parser.add_argument('--eigenvectors',type=int,default=8)
    args=parser.parse_args()
    if args.catalog:print(json.dumps(catalog_json(),indent=2));return
    if args.primal is None or args.output_dir is None:parser.error('--primal and --output-dir required')
    screen(args.primal,args.output_dir,args.cache,args.eigenvectors)


if __name__=='__main__':main()
