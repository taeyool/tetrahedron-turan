"""Round M6 factors and verify all 964 classes with two counting paths."""
from __future__ import annotations
import argparse
import copy
from fractions import Fraction
from pathlib import Path
import time

import runtime as rt
import numpy as np
from remaining_models import source_data, DIMS
from analyze_certificate import stat_numerators


def evaluate(cert, cache):
    reference,reps,blocks,objective,stat,metadata=source_data(cache)
    assert cert['model']=='M6' and cert['host_order']==6
    assert cert['ordered_blocks']==metadata and cert['representatives']==reps.tolist()
    scale=cert['scale']; tau=cert['tau_numerator']
    assert type(scale) is int and scale>0 and type(tau) is int
    assert cert['tau_denominator']==scale*scale
    families=cert['factors_by_block']
    assert len(families)==9
    bounds=[]; grams=[]
    for d,ff in zip(DIMS,families):
        assert all(len(row)==d and all(type(v) is int for v in row) for row in ff)
        bound=sum(max(map(abs,row),default=0)**2 for row in ff)
        assert bound<2**63
        bounds.append(bound)
        f=np.asarray(ff,dtype=np.int64).reshape(-1,d)
        grams.append(f.T@f)
    # Bounds cover every product, sum and signed accumulation in both paths.
    assert 720*(scale*scale+sum(bounds))+abs(tau)*720*12 < 2**63
    first=np.asarray([int(h).bit_count()*36*scale*scale for h in reps],dtype=np.int64)
    first += 12*tau*stat_numerators(reps.tolist())
    with np.load(cache/'order6-independent.npz') as independent:
        second=independent['edge720']*scale*scale+independent['stat720']*tau
        for b,(a,meta,q) in enumerate(zip(blocks,metadata,grams)):
            den=meta['denominator']; assert 720%den==0
            counts=np.rint(a*den).astype(np.int64)
            first += (720//den)*np.einsum('hij,ij->h',counts,q)
            second += np.einsum('hij,ij->h',independent[f'count{b}'].astype(np.int64),q)
    np.testing.assert_array_equal(first,second)
    numerator=int(first.max()); denominator=720*scale*scale
    return dict(bound_fraction=str(Fraction(numerator,denominator)),
        bound_numerator_unreduced=numerator,common_denominator_unreduced=denominator,
        decimal=float(Fraction(numerator,denominator)),
        maximizing_representative=int(reps[int(first.argmax())]),
        coefficient_numerators_sha256=rt.hashlib.sha256(first.astype('<i8').tobytes()).hexdigest(),
        integer_square_factors=sum(map(len,families)),integer_entries=sum(len(f)*d for f,d in zip(families,DIMS)),
        raw_count=964,independent_full_scan_agrees=True,formalized_in_Lean=False)


def verify(cert,cache):
    actual=evaluate(cert,cache)
    for key in ['bound_fraction','bound_numerator_unreduced','common_denominator_unreduced',
                'coefficient_numerators_sha256','integer_square_factors','integer_entries']:
        assert cert[key]==actual[key],f'Certificate mismatch: {key}'
    return actual


def exactify(source,cache,output,factorization='svd',corruption_test=False):
    started=time.monotonic()
    reference,reps,blocks,objective,stat,metadata=source_data(cache)
    with np.load(source) as z:
        assert str(z['model'])=='M6'
        np.testing.assert_array_equal(z['dimensions'],DIMS)
        floating=[]; counts=[]
        rebuilt=objective+float(z['tau'])*stat
        for i,(d,b) in enumerate(zip(DIMS,blocks)):
            f=np.asarray(z[f'factors{i}']).reshape(-1,d)
            assert np.isfinite(f).all()
            rebuilt += np.einsum('hij,ij->h',b,f.T@f)
            counts.append(len(f))
            if factorization=='svd' and len(f):
                _,s,v=np.linalg.svd(f,full_matrices=False)
                keep=s>1e-7*s[0]
                f=s[keep,None]*v[keep]
            floating.append(f)
        np.testing.assert_allclose(rebuilt,z['six'],atol=5e-12,rtol=0)
        assert abs(float(rebuilt.max())-float(z['global_upper'])) < 5e-12
        scale=2000000
        assert all(np.max(np.abs(f),initial=0)*scale<2**63 for f in floating)
        families=[np.rint(f*scale).astype(np.int64).tolist() for f in floating]
        tau=int(round(float(z['tau'])*scale*scale))
    cert=dict(model='M6',host_order=6,stationarity=True,scale=scale,
        tau_numerator=tau,tau_denominator=scale*scale,factors_by_block=families,
        ordered_blocks=metadata,representatives=reps.tolist(),
        reconstruction=dict(source_dual_sha256=rt.digest(source),source_dual=str(source),
            factorization=factorization,svd_relative_tolerance=1e-7 if factorization=='svd' else None,
            original_factor_counts=counts,formalized_in_Lean=False),
        counting_paths=['Original cached uniform disjoint-flag counts with block-specific denominators',
            'Independently enumerated 720 vertex permutations per class; fixed disjoint flags'],
        input_hashes=dict(components=rt.digest(cache/'components.npz'),
            independent_counts=rt.digest(cache/'order6-independent.npz')))
    cert.update(evaluate(cert,cache))
    rt.write_json(output,cert)
    reloaded=rt.json.loads(output.read_text(encoding='utf-8'))
    result=verify(reloaded,cache)
    if corruption_test:
        bad=copy.deepcopy(reloaded)
        bad['bound_numerator_unreduced']+=1
        try: verify(bad,cache)
        except AssertionError: pass
        else: raise AssertionError('Corrupted numerator was accepted')
        bad=copy.deepcopy(reloaded)
        # Add a nonzero square to the constant empty flag: every coefficient changes.
        bad['factors_by_block'][0].append([scale,scale])
        try: verify(bad,cache)
        except AssertionError: pass
        else: raise AssertionError('Corrupted factors were accepted')
        result['corrupted_coefficient_and_factor_rejected']=True
    result.update(status='verified',source_dual_sha256=rt.digest(source),
        certificate_sha256=rt.digest(output),factorization=factorization,
        exactification_verification_seconds=time.monotonic()-started)
    rt.write_json(output.with_suffix('.summary.json'),result)
    print(rt.json.dumps(result),flush=True)
    return result


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('dual',type=Path)
    p.add_argument('--cache',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--factorization',choices=['svd','cuts'],default='svd')
    p.add_argument('--corruption-test',action='store_true')
    a=p.parse_args()
    exactify(a.dual.resolve(),a.cache.resolve(),a.output.resolve(),a.factorization,a.corruption_test)
