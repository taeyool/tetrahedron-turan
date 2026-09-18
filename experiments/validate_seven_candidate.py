"""Roundtrip validation for full/native seven-vertex factor exports."""
import argparse
from pathlib import Path
import runtime as rt
import numpy as np


def main(cache,name,source,output):
    oracle,blocks,obj,stat,meta=rt.model(cache,name)
    with np.load(source,allow_pickle=False) as z:
        assert list(z['dimensions'])==[m['dimension'] for m in meta]
        assert list(z['five_root_type_masks'])==oracle.type_masks
        six=obj+float(z['tau'])*stat
        grams=[]
        for b,m in enumerate(meta):
            f=z[f'factors{b}'];assert f.shape[1]==m['dimension'] and np.isfinite(f).all()
            q=f.T@f
            if b<9:six+=np.einsum('hij,ij->h',blocks[b],q)
            else:
                np.testing.assert_allclose(q,z[f'gram{b-9}'],atol=5e-11,rtol=1e-12);grams.append(q)
        np.testing.assert_allclose(six,z['six'],atol=5e-11,rtol=1e-12)
        v,_=oracle.price(six,grams,threads=2,top=1)
        error=abs(float(v.max()-z['global_upper']));assert error<1e-9
    rt.write_json(output,dict(status='passed',model=name,source_dual_sha256=rt.digest(source),raw_extensions=oracle.raw_count,global_price_error=error))


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--cache',type=Path,required=True);p.add_argument('--model',required=True);p.add_argument('--source',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();main(a.cache.resolve(),a.model,a.source.resolve(),a.output.resolve())
