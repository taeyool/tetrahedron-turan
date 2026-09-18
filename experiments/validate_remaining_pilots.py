"""Roundtrip and full-universe gates for the new nine-block pilot candidates."""
import argparse
from pathlib import Path
import time
import itertools
import runtime as rt
import numpy as np
from remaining_models import model, DIMS, SixOracle
import reconstruct_optimization as ro
from pilot_remaining import ARMS


def validate(base,label,output):
    started=time.monotonic()
    state=rt.json.loads((base/f'{label}-status.json').read_text(encoding='utf-8'))
    assert state['status']=='finished'
    reports=[]; runs={}
    for name,method in ARMS:
        folder=base/label/name/method
        run=rt.json.loads((folder/'run.json').read_text(encoding='utf-8'))
        oracle,blocks,objective,stat,metadata=model(base/'cache',name)
        assert run['ordered_blocks']==metadata and run['dimensions']==DIMS
        assert run['stationarity'] and run['initial_cuts']==0
        with np.load(folder/'best_dual.npz') as z:
            np.testing.assert_array_equal(z['dimensions'],DIMS)
            rebuilt=objective+float(z['tau'])*stat
            for b,a in enumerate(blocks):
                f=z[f'factors{b}']
                rebuilt += np.einsum('hij,ij->h',a,f.T@f)
            if name=='M7-lift6':
                for b,d in enumerate([7,236,191],9):
                    assert z[f'factors{b}'].shape==(0,d)
                    assert not np.any(z[f'gram{b-9}'])
            np.testing.assert_allclose(rebuilt,z['six'],atol=5e-12,rtol=0)
            values,priced=oracle.price(rebuilt,[],threads=2,top=8)
            deck,_=oracle.features(priced)
            np.testing.assert_allclose(values,deck@rebuilt,atol=5e-12,rtol=0)
            np.testing.assert_allclose(values.max(),float(z['global_upper']),atol=5e-12,rtol=0)
            upper=float(values.max())
            if name=='M7-lift6':
                check_masks=list(dict.fromkeys([0,int(priced[int(values.argmax())]),
                    oracle.cert['example_maximizing_raw_mask']]+list(map(int,priced[:8]))))
                actual,_=oracle.features(check_masks)
                canonical=SixOracle(base/'cache',oracle.cert).canonical
                direct=np.zeros((len(check_masks),964))
                for i,mask in enumerate(check_masks):
                    for vertices in itertools.combinations(range(7),6):
                        six_mask=ro.fs.induced_mask(mask,7,vertices)
                        index=int(canonical[six_mask]); assert index>=0
                        direct[i,index]+=1/7
                np.testing.assert_allclose(actual.toarray(),direct,atol=2e-16,rtol=0)
        runs[name,method]=run
        reports.append(dict(model=name,method=method,pilot_status=run['status'],
            upper=upper,full_universe_count=oracle.raw_count,roundtrip_verified=True,
            zero_padding_verified=name=='M7-lift6',source_dual_sha256=rt.digest(folder/'best_dual.npz'),
            final_diagnostics=run['last_iteration']))
    assert runs['M6','SDP-CG']['initial_columns_sha256']==runs['M6','LP-CUT-CG']['initial_columns_sha256']
    full=runs['M6','SDP-FULL']['last_iteration']
    cg=runs['M6','SDP-CG']['last_iteration']
    def approximately_feasible(row):
        return (row['minimum_eigenvalue']>=-1e-7 and row['minimum_primal_weight']>=-1e-7
            and abs(row['normalization_residual'])<=1e-7 and abs(row['stationarity_residual'])<=1e-7)
    # Do not turn an infeasible native iterate into an alleged primal lower
    # bound. Use the independently validated construction when inconclusive.
    for report in reports:
        assert report['upper']>=5/9-1e-12
    if approximately_feasible(full):
        for method in ['LP-CUT','LP-CUT-CG']:
            assert runs['M6',method]['best_global_upper']>=full['restricted_objective']-1e-7,method
    if approximately_feasible(cg):
        assert cg['restricted_objective']<=runs['M6','SDP-FULL']['best_global_upper']+1e-7
    result=dict(status='passed',seconds=time.monotonic()-started,
        all_algorithms_same_nine_block_coefficients=True,full_methods_all_964_columns=True,
        initial_generated_columns_identical=True,numerical_interval_consistency_passed=True,
        native_reference_interval=[full['restricted_objective'],full['global_dual_upper']],
        reference_interpretation='Approximate moment objective and globally repriced dual; residuals retained, no exact lower-bound or optimality claim.',
        native_reference_primal_passes_reported_tolerance=approximately_feasible(full),
        certified_feasible_construction_objective=5/9,
        rigorous_reference_interval_note='Only the 5/9 construction supplies the unconditional primal endpoint when native residuals are unresolved.',
        unresolved_native_tolerance=[r['method'] for r in reports if r['model']=='M6'
            and r['method'].startswith('SDP') and r['pilot_status']!='completed'],
        reports=reports)
    rt.write_json(output,result)
    print(rt.json.dumps({k:v for k,v in result.items() if k!='reports'}),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--campaign',type=Path,required=True)
    p.add_argument('--label',required=True)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    validate(a.campaign.resolve(),a.label,a.output.resolve())
