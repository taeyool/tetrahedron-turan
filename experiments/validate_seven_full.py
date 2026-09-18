"""Independent relabeling checks and exhaustive raw-vs-catalogue pricing."""
from pathlib import Path
import argparse
import time
import runtime as rt
import numpy as np
import reconstruct_optimization as ro
from seven_full import load


def main(cache,name,output):
    start=time.monotonic();oracle,blocks,objective,stat,metadata=rt.model(cache,name)
    masks,deck,feat,meta=load(cache,name)
    rng=np.random.default_rng(611)
    ids=np.sort(rng.choice(len(masks),32,replace=False));sample=np.asarray(masks[ids])
    perm=tuple(rng.permutation(7));edge_map=ro.fs.permutation_edge_map(7,perm)
    relabeled=np.zeros(len(sample),np.uint64)
    for old,new in enumerate(edge_map):relabeled|=((sample>>old)&1)<<new
    direct_d,direct_f=oracle.features(sample);moved_d,moved_f=oracle.features(relabeled)
    for left,right,den in [(deck[ids],direct_d,7),(feat[ids],direct_f,5040),(direct_d,moved_d,7),(direct_f,moved_f,5040)]:
        delta=(left-right).tocsr();assert np.max(np.abs(delta.data),initial=0)<1e-13
        assert np.max(np.abs(np.rint(left.data*den)-left.data*den),initial=0)<1e-10
    factors=[rng.normal(0,.001,(2,m['dimension'])) for m in metadata]
    grams=[f.T@f for f in factors];tau=-.123
    six=objective+tau*stat
    for b,q in zip(blocks,grams[:9]):six+=np.einsum('hij,ij->h',b,q)
    catalog_values=deck@six+feat@np.concatenate([q.ravel() for q in grams[9:]])
    raw,_=oracle.price(six,grams[9:],threads=2,top=1)
    error=abs(float(catalog_values.max()-raw.max()));assert error<5e-12
    result=dict(status='passed',model=name,canonical_classes=len(masks),raw_extensions=oracle.raw_count,
        cached_sparse_rows_checked=len(sample),permuted_feature_rows_checked=len(sample),
        exhaustive_global_price_error=error,ordered_blocks=metadata,
        catalogue_sha256=rt.digest(cache/'seven_masks.u64'),feature_manifest_sha256=rt.digest(cache/name/'manifest.json'),
        seconds=time.monotonic()-start,source_sha256=rt.sources())
    rt.write_json(output,result);print(rt.json.dumps({k:v for k,v in result.items() if k not in ['ordered_blocks','source_sha256']}),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--cache',type=Path,required=True);p.add_argument('--model',required=True);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();main(a.cache.resolve(),a.model,a.output.resolve())
