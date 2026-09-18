#!/usr/bin/env python3
"""Reconstruct the selected order-seven edge-density SDP by cuts and columns.

Dependencies: numpy, scipy, highspy; C++17 compiler. Temporary caches are
rebuildable. Every pricing pass visits the complete raw seven-vertex universe.
Numerical output is research evidence, not an exact certificate.
"""
from __future__ import annotations
import argparse
import ctypes
import hashlib
import itertools
import json
import os
from pathlib import Path
import subprocess
import sys
import time

import numpy as np
from scipy import sparse

from analyze_certificate import ROOT, CERT, fs, root_permutations

HERE = Path(__file__).resolve().parent
DIMS = [2, 2, 11, 8, 7, 64, 56, 50, 45, 7, 236, 191]
OFFSETS = np.cumsum([0, 49, 236**2, 191**2])


def turan_blowup_masks(n):
    """Support of the exact, balanced cyclic three-part construction, density 5/9."""
    result={}
    triples=fs.triples(n)
    for colors in itertools.product(range(3),repeat=n):
        mask=0
        for k,(a,b,c) in enumerate(triples):
            z=[colors[a],colors[b],colors[c]]
            if len(set(z))==3 or any(z.count(i)==2 and z.count((i+1)%3)==1 for i in range(3)):
                mask|=1<<k
        result[mask]=result.get(mask,0)+1
    return result


class Oracle:
    def __init__(self, cache):
        self.cert = json.loads((CERT / "legacy/K4_turan_order7_exact_certificate.json").read_text())
        cache.mkdir(parents=True, exist_ok=True)
        libpath = cache / "optimization_oracle.dylib"
        sources = [HERE / "optimization_oracle.cpp", HERE / "optimization_oracle_tail.inc", HERE / "optimization_order8.inc"]
        if not libpath.exists() or max(p.stat().st_mtime for p in sources) > libpath.stat().st_mtime:
            subprocess.run(["c++", "-O3", "-std=c++17", "-pthread", "-shared", "-fPIC",
                            str(sources[0]), "-o", str(libpath)], check=True)
        self.lib = ctypes.CDLL(str(libpath))
        ptr = np.ctypeslib.ndpointer
        self.lib.initialize.argtypes = [ptr(np.uint32, flags="C_CONTIGUOUS"), ctypes.c_int]
        self.lib.initialize.restype = ctypes.c_int
        self.lib.get_features.argtypes = [ptr(np.uint64, flags="C_CONTIGUOUS"), ctypes.c_int,
                                          ptr(np.uint16), ptr(np.uint16), ptr(np.uint32)]
        self.lib.price.argtypes = [ptr(np.float64), ptr(np.float64), ptr(np.float64),
                                  ctypes.c_int, ctypes.c_int, ptr(np.float64), ptr(np.uint64)]
        reps = np.array(self.cert["H_representatives"], dtype=np.uint32)
        self.raw_count = self.lib.initialize(reps, len(reps))
        assert self.raw_count == 13051375
        self.perms = [root_permutations(fs.flags_for_type(3, 5, sig, fs.rooted_canon_table(5, 3))) for sig in (0, 1)]
        # Index maps for Reynolds averaging of the two three-root blocks.
        self.maps = []
        for k in range(6):
            self.maps.append(np.concatenate([(p[:, None]*d+p[None, :]+off).ravel()
                              for p, d, off in [(self.perms[0][k], 236, 0), (self.perms[1][k], 191, 236**2)]]))

    def features(self, masks):
        masks = np.ascontiguousarray(masks, dtype=np.uint64)
        n = len(masks)
        decks, one, three = np.zeros((n, 7), np.uint16), np.zeros((n, 28), np.uint16), np.zeros((n, 105), np.uint32)
        self.lib.get_features(masks, n, decks, one, three)
        assert np.all(decks < 964)
        deck = sparse.csr_matrix((np.full(n*7, 1/7), (np.repeat(np.arange(n), 7), decks.ravel())), shape=(n, 964))
        rows, cols, data = [], [], []
        pos = 0
        for i in range(7):
            for j in range(i, 7):
                rows.extend([np.arange(n), np.arange(n)])
                cols.extend([np.full(n, i*7+j), np.full(n, j*7+i)])
                data.extend([one[:, pos]/140, one[:, pos]/140]); pos += 1
        for mp in self.maps:
            mapped = mp[three]
            trans = np.where(mapped < 236**2, (mapped % 236)*236+mapped//236,
                             ((mapped-236**2) % 191)*191+(mapped-236**2)//191+236**2)
            for values in [mapped, trans]:
                rows.append(np.repeat(np.arange(n), 105)); cols.append(values.ravel()+49)
                data.append(np.full(n*105, 1/1260))
        feat = sparse.csr_matrix((np.concatenate(data), (np.concatenate(rows), np.concatenate(cols))), shape=(n, int(OFFSETS[-1])))
        feat.eliminate_zeros(); feat.sort_indices(); deck.sort_indices()
        return deck, feat

    def price(self, six, grams, threads=4, top=2):
        assert np.all(np.isfinite(six)) and all(np.all(np.isfinite(q)) for q in grams)
        q1 = np.array([grams[0][i,j]/70 for i in range(7) for j in range(i,7)])
        q3 = np.concatenate([sum(q[np.ix_(p,p)] for p in perms).ravel()/630
                             for q, perms in zip(grams[1:], self.perms)])
        values, masks = np.zeros((964, top)), np.zeros((964, top), dtype=np.uint64)
        self.lib.price(np.ascontiguousarray(six/7), q1, q3, threads, top, values, masks)
        assert not np.any(np.isnan(values)) and not np.any(np.isposinf(values))
        return values.ravel(), masks.ravel()


def validate(oracle, cache, blocks, output=None):
    cert = oracle.cert
    masks = [0, cert["example_maximizing_raw_mask"], 27552015, 31837153552, 33554400]
    deck, feat = oracle.features(masks)
    # Independent Python enumeration checks every entry of the new order-seven moments.
    direct = fs.build_blocks(7, masks, include_s=[1,3], verbose=False)
    for j,b in enumerate(direct):
        assert b.flags == fs.flags_for_type(b.s,b.l,b.sigma,fs.rooted_canon_table(b.l,b.s))
        np.testing.assert_allclose(feat[:,OFFSETS[j]:OFFSETS[j+1]].toarray(), b.A.reshape(len(masks),-1), atol=2e-16)
    scale = cert["scale"]
    fields = cert["order6_factors_by_block"] + [cert[k] for k in ["order7_s1_factors", "order7_s3_nonedge_factors", "order7_s3_edge_factors"]]
    grams = [np.asarray(f).reshape(-1,d).T @ np.asarray(f).reshape(-1,d) / scale**2 for f,d in zip(fields,DIMS)]
    data = np.load(cache / "components.npz")
    six = data["edge"]/(720*scale**2)+data["stat"]/(720*scale**2)+data["squares"]/(720*scale**2)
    actual = deck @ six + feat @ np.concatenate([q.ravel() for q in grams[9:]])
    target = cert["bound_numerator_unreduced"] / cert["common_denominator_unreduced"]
    np.testing.assert_allclose(actual[1:3], target, atol=3e-13, rtol=0)
    start=time.monotonic()
    values, priced = oracle.price(six, grams[9:])
    np.testing.assert_allclose(values.max(), target, atol=3e-13, rtol=0)
    pd,pf=oracle.features(priced)
    np.testing.assert_allclose(values, pd@six+pf@np.concatenate([q.ravel() for q in grams[9:]]),atol=5e-13,rtol=0)
    result={"raw_count":oracle.raw_count,"stored_bound":target,"reconstructed_max":float(values.max()),
            "direct_moment_matrices_checked":len(masks)*3,"pricing_seconds":time.monotonic()-start,
            "all_returned_prices_independently_recomputed":len(values)}
    output=output or HERE/"optimization_validation.json"
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(result,indent=2)+"\n")
    print(result,flush=True)


class Master:
    def __init__(self, oracle, blocks, objective, stationarity, mode, args):
        import highspy
        self.highspy=highspy
        self.oracle,self.blocks,self.objective,self.stationarity=oracle,blocks,objective,stationarity
        self.mode,self.args=mode,args
        self.h=highspy.Highs()
        for key,value in {"output_flag":False,"primal_feasibility_tolerance":1e-9,
                          "dual_feasibility_tolerance":1e-9,"threads":1}.items():
            self.h.setOptionValue(key,value)
        self.h.setOptionValue("solver",getattr(args,"lp_solver","choose"))
        self.h.changeObjectiveSense(highspy.ObjSense.kMaximize)
        self.h.addRow(1,1,0,np.array([],np.int32),np.array([],float))
        self.neq=1
        if mode=="with":
            self.h.addRow(0,0,0,np.array([],np.int32),np.array([],float)); self.neq=2
        self.face=[]
        if mode=="with" and getattr(args,"stationarity_face",False):
            v=np.array([0,-1,-2,-3,3,2,1],float)/3
            for e in np.eye(7):
                self.face.append((np.outer(e,v)+np.outer(v,e))/2)
                self.h.addRow(0,0,0,np.array([],np.int32),np.array([],float));self.neq+=1
        self.masks=[];self.seen=set();self.signatures=set()
        self.deck=sparse.csr_matrix((0,964));self.feat=sparse.csr_matrix((0,int(OFFSETS[-1])))
        self.cuts=[];self.sixcuts=[]
        self.history=[];self.best_upper=float("inf");self.best_dual=None
        self.provenance={"arguments":{k:str(v) if isinstance(v,Path) else v for k,v in vars(args).items()},
                         "driver_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
        self.add_columns([0])
        if getattr(args,"seed_turan",False):self.add_columns(turan_blowup_masks(getattr(oracle,"order",7)))
        if args.seed_certificate:
            cert=oracle.cert
            factors=cert["order6_factors_by_block"]+[cert[k] for k in ["order7_s1_factors","order7_s3_nonedge_factors","order7_s3_edge_factors"]]
            self.add_cuts([(b,np.array(v,dtype=float)/np.linalg.norm(v)) for b,ff in enumerate(factors) for v in ff])
        warm=getattr(args,"warm_dual",None)
        if warm:
            data=np.load(warm)
            self.add_cuts([(b,v/np.linalg.norm(v)) for b in range(len(DIMS)) if f"factors{b}" in data for v in data[f"factors{b}"] if np.linalg.norm(v)>0])
            values,masks=oracle.price(data["six"],[data[f"gram{i}"] for i in range(3)],args.threads,args.price_top)
            self.add_columns(masks)
        checkpoint=getattr(args,"resume_checkpoint",None)
        if checkpoint:
            data=np.load(checkpoint)
            self.provenance["resume_checkpoint_sha256"]=hashlib.sha256(checkpoint.read_bytes()).hexdigest()
            if "stationarity" in data:assert bool(data["stationarity"])==(mode=="with")
            if "stationarity_face" in data:assert bool(data["stationarity_face"])==bool(self.face)
            np.testing.assert_array_equal(data["dimensions"],DIMS)
            self.add_columns(data["masks"],preserve_order=True)
            self.add_cuts([(int(b),v[:DIMS[b]]) for b,v in zip(data["blocks"],data["vectors"])])
            # A saved basis is meaningful only for precisely the same row/column order.
            if ("basis_columns" in data and np.array_equal(data["masks"],self.masks)
                    and len(data["basis_rows"])==self.h.getNumRow()
                    and len(data["blocks"])==len(self.cuts)):
                basis=highspy.HighsBasis()
                basis.col_status=[highspy.HighsBasisStatus(int(v)) for v in data["basis_columns"]]
                basis.row_status=[highspy.HighsBasisStatus(int(v)) for v in data["basis_rows"]]
                restored=self.h.setBasis(basis)
                self.provenance["restored_basis"]=restored==highspy.HighsStatus.kOk
            previous=(checkpoint.with_name(checkpoint.name.removesuffix("_checkpoint.npz")+"_best_dual.npz")
                      if checkpoint.name.endswith("_checkpoint.npz") else None)
            if previous is not None and previous.exists():
                with np.load(previous) as prior:self.best_dual={k:prior[k].copy() for k in prior.files}
                values,_=oracle.price(self.best_dual["six"],[self.best_dual[f"gram{i}"] for i in range(3)],args.threads,args.price_top)
                self.best_upper=float(values.max())
                self.provenance["inherited_best_dual_sha256"]=hashlib.sha256(previous.read_bytes()).hexdigest()
        warm_columns=getattr(args,"warm_columns",None)
        if warm_columns:self.add_columns(np.load(warm_columns)["masks"])

    def add_columns(self,masks,preserve_order=False):
        fresh=([m for m in dict.fromkeys(map(int,masks)) if m not in self.seen]
               if preserve_order else sorted(set(map(int,masks))-self.seen))
        self.seen.update(fresh)
        if not fresh:return 0
        deck,feat=self.oracle.features(fresh)
        keep=[]
        for i in range(len(fresh)):
            d,f=deck.getrow(i),feat.getrow(i)
            # Equal full moment features and deletion marginals are identical model columns.
            deck_den=getattr(self.oracle,"deck_denominator",7)
            feature_den=getattr(self.oracle,"feature_denominator",1260)
            key=hashlib.sha256(d.indices.tobytes()+np.round(d.data*deck_den).astype(np.int16).tobytes()+f.indices.tobytes()+np.round(f.data*feature_den).astype(np.int16).tobytes()).digest()
            if key not in self.signatures:self.signatures.add(key);keep.append(i)
        deck,feat=deck[keep],feat[keep]
        if not keep:return 0
        cost=np.asarray(deck@self.objective)
        eq=[np.ones(len(keep))]
        if self.mode=="with":eq.append(np.asarray(deck@self.stationarity))
        eq.extend(np.asarray(feat[:,:49]@m.ravel()) for m in self.face)
        coeff=np.array(eq)
        if self.cuts:
            cutvalues=self.coefficients(deck,feat,self.cuts,self.sixcuts)
            coeff=np.vstack([coeff,cutvalues.T])
        matrix=sparse.csc_matrix(coeff)
        self.h.addCols(len(keep),cost,np.zeros(len(keep)),np.full(len(keep),self.highspy.kHighsInf),
                       matrix.nnz,matrix.indptr.astype(np.int32),matrix.indices.astype(np.int32),matrix.data)
        self.deck=sparse.vstack([self.deck,deck],format="csr");self.feat=sparse.vstack([self.feat,feat],format="csr")
        self.masks.extend(fresh[i] for i in keep)
        return len(keep)

    def coefficients(self,deck,feat,cuts,six):
        result=np.asarray(deck@np.array(six).T)
        for b in range(9,len(DIMS)):
            indices=[i for i,(bb,v) in enumerate(cuts) if bb==b]
            features=feat[:,OFFSETS[b-9]:OFFSETS[b-8]]
            for start in range(0,len(indices),32):
                selected=indices[start:start+32]
                products=np.array([np.outer(cuts[i][1],cuts[i][1]).ravel() for i in selected])
                result[:,selected]=features@products.T
        return result

    def add_cuts(self,cuts):
        if not cuts:return
        six=[]
        for b,v in cuts:
            s=np.zeros(964)
            if b<9:s=np.einsum("i,hij,j->h",v,self.blocks[b],v,optimize=True)
            six.append(s)
        values=self.coefficients(self.deck,self.feat,cuts,six)
        mat=sparse.csr_matrix(values.T)
        self.h.addRows(len(cuts),np.zeros(len(cuts)),np.full(len(cuts),self.highspy.kHighsInf),
                       mat.nnz,mat.indptr.astype(np.int32),mat.indices.astype(np.int32),mat.data)
        self.cuts.extend(cuts);self.sixcuts.extend(six)

    def dual(self,sol):
        multipliers=-np.asarray(sol.row_dual[self.neq:])
        assert multipliers.min(initial=0)>-1e-7
        multipliers=np.maximum(multipliers,0)
        tau=-sol.row_dual[1] if self.mode=="with" else 0.
        six=self.objective+tau*self.stationarity
        if len(multipliers):six=six+np.einsum("r,rh->h",multipliers,np.array(self.sixcuts),optimize=False)
        grams=[np.zeros((d,d)) for d in DIMS[9:]]
        for multiplier,m in zip(sol.row_dual[2:self.neq],self.face):grams[0]-=multiplier*m
        for w,(b,v) in zip(multipliers,self.cuts):
            if b>=9 and w:grams[b-9]+=w*np.outer(v,v)
        return six,grams,tau,multipliers

    def prune(self,sol):
        limit=getattr(self.args,"keep_cuts",1800)
        if limit<=0 or len(self.cuts)<=limit:return
        dual=np.asarray(sol.row_dual[self.neq:])
        recent=limit//2
        keep=[i for i in range(len(self.cuts)) if abs(dual[i])>1e-10 or i>=len(self.cuts)-recent]
        if len(keep)>=len(self.cuts)*.85:return
        keep_set=set(keep)
        remove=np.array([self.neq+i for i in range(len(self.cuts)) if i not in keep_set],np.int32)
        self.h.deleteRows(len(remove),remove)
        self.cuts=[self.cuts[i] for i in keep];self.sixcuts=[self.sixcuts[i] for i in keep]

    def save(self,status):
        order=getattr(self.oracle,"order",7)
        global_pricing=getattr(self.oracle,"global_pricing",True)
        path=self.args.output_dir/f"order{order}_{self.mode}_stationarity.json"
        result={"status":status,"stationarity":self.mode=="with","blocks":DIMS,
                "raw_pricing_universe":self.oracle.raw_count if global_pricing else None,"seed_certificate_directions":self.args.seed_certificate,
                "lp_solver":getattr(self.args,"lp_solver","choose"),
                "provenance":self.provenance,
                "stationarity_face_equalities":bool(self.face),
                ("best_globally_priced_numerical_upper" if global_pricing else "best_sampled_dual_maximum"):self.best_upper if np.isfinite(self.best_upper) else None,
                "interpretation":("Restricted-master objectives are not full SDP optima. Globally priced duals give numerical upper estimates; exact rational verification is separate. If facial reduction is enabled, gram0 includes the explicitly recorded zero-valued face terms and need not itself be PSD." if global_pricing else "Exploratory eight-vertex run with heuristic pricing. Neither the restricted objective nor the sampled dual maximum is a bound for the full SDP or Turan density."),
                "history":self.history}
        temporary=path.with_suffix(".json.tmp")
        temporary.write_text(json.dumps(result,indent=2)+"\n");temporary.replace(path)
        if self.best_dual is not None:
            atomic_savez(self.args.output_dir/f"order{order}_{self.mode}_best_dual.npz",**self.best_dual)
        if getattr(self.args,"checkpoint",False):
            vectors=np.zeros((len(self.cuts),max(DIMS)))
            for i,(b,v) in enumerate(self.cuts):vectors[i,:len(v)]=v
            basis=self.h.getBasis()
            basis_data=({"basis_columns":np.array([int(v) for v in basis.col_status]),
                         "basis_rows":np.array([int(v) for v in basis.row_status])} if basis.valid else {})
            atomic_savez(self.args.output_dir/f"order{order}_{self.mode}_checkpoint.npz",masks=np.array(self.masks,np.uint64),
                     blocks=np.array([b for b,v in self.cuts]),vectors=vectors,dimensions=DIMS,stationarity=self.mode=="with",
                     stationarity_face=bool(self.face),**basis_data)

    def run(self):
        start=time.monotonic();since_price=0;y=None;moments=None
        status="running"
        for it in range(self.args.max_iter):
            solve_start=time.monotonic();self.h.run();solve_seconds=time.monotonic()-solve_start
            if self.h.getModelStatus()!=self.highspy.HighsModelStatus.kOptimal:
                status=self.h.modelStatusToString(self.h.getModelStatus());break
            sol=self.h.getSolution();y=np.array(sol.col_value);x=self.deck.T@y
            flat=self.feat.T@y
            moments=[np.einsum("h,hij->ij",x,b) for b in self.blocks]+[flat[a:b].reshape(d,d) for a,b,d in zip(OFFSETS[:-1],OFFSETS[1:],DIMS[9:])]
            minima=[];negative=[]
            for b,m in enumerate(moments):
                vals,vec=np.linalg.eigh((m+m.T)/2);minima.append(float(vals[0]))
                negative.extend((float(vals[j]),b,vec[:,j]) for j in np.flatnonzero(vals < -self.args.psd_tolerance))
            negative.sort(key=lambda t:t[0])
            row={"iteration":it,"seconds":time.monotonic()-start,"restricted_objective":self.h.getObjectiveValue(),
                 "lp_seconds":solve_seconds,
                 "minimum_eigenvalue":min(minima),"block_minimum_eigenvalues":minima,
                 "columns":len(self.masks),"cuts":len(self.cuts),"primal_support":int(np.count_nonzero(y>1e-9)),
                 "stationarity_residual":float(np.einsum("h,h->",self.stationarity,x,optimize=False))}
            should_price=getattr(self.args,"price_first",False) or it==0 or since_price>=self.args.cut_rounds or not negative
            added=0
            if should_price:
                pstart=time.monotonic();six,grams,tau,weights=self.dual(sol)
                if getattr(self.args,"save_dual_history",False):
                    np.savez(self.args.output_dir/f"dual_{self.mode}_{it:04d}.npz",six=six,tau=tau,
                             **{f"gram{i}":q for i,q in enumerate(grams)})
                values,masks=self.oracle.price(six,grams,self.args.threads,self.args.price_top)
                global_pricing=getattr(self.oracle,"global_pricing",True)
                upper=float(values.max());row.update({("global_dual_upper" if global_pricing else "sampled_dual_maximum"):upper,("pricing_gap" if global_pricing else "sampled_gap"):upper-row["restricted_objective"],
                                                       "tau":tau,"pricing_seconds":time.monotonic()-pstart})
                if upper<self.best_upper:
                    self.best_upper=upper
                    self.best_dual={"six":six,"tau":tau,"global_upper":upper,"iteration":it,
                                    **{f"gram{i}":q for i,q in enumerate(grams)}}
                    self.best_dual["face_multipliers"]=-np.array(sol.row_dual[2:self.neq]) if self.face else np.array([])
                    # Save PSD factors for all blocks, with nonnegative LP weights.
                    for b,d in enumerate(DIMS):
                        self.best_dual[f"factors{b}"]=np.array([np.sqrt(w)*v for w,(bb,v) in zip(weights,self.cuts) if bb==b and w>0]).reshape(-1,d)
                good=values>row["restricted_objective"]+self.args.price_tolerance
                added=self.add_columns(masks[good]);row["added_columns"]=added;since_price=0
                if not negative and upper-row["restricted_objective"]<=self.args.price_tolerance:
                    status="numerical_tolerances_met" if global_pricing else "heuristic_pricing_stalled"
            newcuts=[(b,v) for _,b,v in negative[:self.args.max_cuts]]
            if getattr(self.args,"price_first",False) and upper-row["restricted_objective"]>self.args.price_tolerance:
                newcuts=[]
            self.history.append(row)
            print(self.mode,{k:v for k,v in row.items() if k!="block_minimum_eigenvalues"},flush=True)
            self.save(status)
            if status in ("numerical_tolerances_met","heuristic_pricing_stalled"):break
            if it%10==0:self.prune(sol)
            self.add_cuts(newcuts);since_price+=1
            if time.monotonic()-start>=self.args.seconds:
                status="time_limit";break
        else:
            status="iteration_limit"
        # Save the current state so all feasible-moment diagnostics can be recomputed.
        order=getattr(self.oracle,"order",7)
        if y is not None:
            atomic_savez(self.args.output_dir/f"order{order}_{self.mode}_primal.npz",masks=np.array(self.masks[:len(y)],np.uint64),weights=y,
                         **{f"moment{i}":m for i,m in enumerate(moments)})
        self.save(status)


def atomic_savez(path,**arrays):
    """Allow exactifiers/monitors to read the previous complete snapshot while saving."""
    temporary=path.with_suffix(".npz.tmp")
    with temporary.open("wb") as stream:np.savez(stream,**arrays)
    temporary.replace(path)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--cache",type=Path,default=ROOT/".research-repro/cache")
    p.add_argument("--deps",type=Path,default=ROOT/".research-repro/empty-deps")
    p.add_argument("--output-dir",type=Path,default=ROOT/".research-repro/optimization_runs")
    p.add_argument("--validate",action="store_true")
    p.add_argument("--validation-output",type=Path)
    p.add_argument("--mode",choices=["with","without","both"],default="both")
    p.add_argument("--max-iter",type=int,default=300)
    p.add_argument("--seconds",type=float,default=1800)
    p.add_argument("--threads",type=int,default=4)
    p.add_argument("--cut-rounds",type=int,default=5)
    p.add_argument("--max-cuts",type=int,default=80)
    p.add_argument("--price-top",type=int,default=2)
    p.add_argument("--psd-tolerance",type=float,default=1e-7)
    p.add_argument("--price-tolerance",type=float,default=1e-7)
    p.add_argument("--seed-certificate",action="store_true")
    p.add_argument("--warm-dual",type=Path)
    p.add_argument("--keep-cuts",type=int,default=1800)
    p.add_argument("--lp-solver",choices=["choose","simplex","ipm"],default="choose")
    p.add_argument("--checkpoint",action="store_true")
    p.add_argument("--resume-checkpoint",type=Path)
    p.add_argument("--save-dual-history",action="store_true")
    p.add_argument("--seed-turan",action="store_true")
    p.add_argument("--stationarity-face",action="store_true")
    p.add_argument("--price-first",action="store_true")
    p.add_argument("--warm-columns",type=Path)
    args=p.parse_args();sys.path.insert(0,str(args.deps));args.output_dir.mkdir(parents=True,exist_ok=True)
    oracle=Oracle(args.cache)
    data=np.load(args.cache/"components.npz");blocks=[data[f"block{i}"] for i in range(9)]
    if args.validate:validate(oracle,args.cache,blocks,args.validation_output);return
    objective=data["edge"]/(720*oracle.cert["scale"]**2);stat=data["stat_unscaled"]/60
    for mode in (["without","with"] if args.mode=="both" else [args.mode]):
        Master(oracle,blocks,objective,stat,mode,args).run()


if __name__=="__main__":main()
