"""Serialize a native 32-block numerical dual in the legacy 35-slot exactifier layout.

The legacy slots 1, 3 and 4 (the three 2*l-s=5 blocks) receive EMPTY factor
arrays only. This is serialization padding for exactify_five_root.py, not
three active optimization blocks. Every dependent field (dimensions, type
order, aggregate six-vertex contribution, gram0..25) is recomputed from the
native factors; nothing is copied from a pre-migration aggregate. Renumbered
factors0..31 are never handed to the old exactifier directly.
"""
from __future__ import annotations

import argparse
from pathlib import Path

import runtime as rt
import numpy as np
import reconstruct_optimization as ro
import model32

LABEL = 'legacy-35-slot serialization of a native M7-all5-32 dual; slots 1,3,4 are empty padding'


def export(native_path, output_path, model, threads=2, reprice=True):
    native_path, output_path = Path(native_path), Path(output_path)
    with np.load(native_path, allow_pickle=False) as data:
        model.check_identity(data)  # rejects legacy, renumbered-without-identity or foreign files
        assert bool(data['stationarity']) and not bool(data['stationarity_face'])
        names = {k for k in data.files if k.startswith('factors')}
        assert names == {f'factors{b}' for b in range(32)}, 'native file must carry exactly factors0..31'
        tau = float(data['tau'])
        factors = []
        for b, d in enumerate(model.dims):
            rows = np.asarray(data[f'factors{b}'], float)
            assert rows.ndim == 2 and rows.shape[1] == d and np.isfinite(rows).all(), f'invalid native factors{b}'
            factors.append(rows)
        claimed = float(data['global_upper']) if 'global_upper' in data else None
    assert np.isfinite(tau)
    legacy_dims = model32.LEGACY_DIMS + model32.FIVE_DIMS
    legacy = {old: np.empty((0, legacy_dims[old])) for old in model32.EXCLUDED_LEGACY}
    for m, rows in zip(model.meta, factors):
        assert legacy_dims[m['legacy_index']] == m['dimension']
        legacy[m['legacy_index']] = rows
    assert sorted(legacy) == list(range(35))
    for old in model32.EXCLUDED_LEGACY:
        assert legacy[old].shape == (0, legacy_dims[old]), 'padding slots must be empty'
    six = model.six_coefficients(tau, factors)
    grams = model.grams(factors)  # oracle order == legacy gram0..25
    result = dict(native_sha256=rt.digest(native_path), claimed_native_upper=claimed)
    if reprice:
        values, masks = model.oracle.price(six, grams, threads=threads, top=1)
        upper = float(values.max())
        result.update(repriced_upper=upper, repriced_maximizer=int(masks[int(np.argmax(values))]))
        if claimed is not None:
            assert abs(upper-claimed) <= 1e-10, f'native claimed upper {claimed} disagrees with recomputation {upper}'
    ro.atomic_savez(output_path, six=six, tau=tau, global_upper=result.get('repriced_upper', np.nan),
                    face_multipliers=np.array([]), dimensions=np.asarray(legacy_dims, np.int32),
                    five_root_type_masks=np.asarray(model.oracle.type_masks, np.int32),
                    serialization_label=np.asarray(LABEL), native_model_id=np.asarray(model32.MODEL_ID),
                    native_sha256=np.asarray(result['native_sha256']),
                    **{f'gram{j}': q for j, q in enumerate(grams)},
                    **{f'factors{old}': legacy[old] for old in range(35)})
    result.update(output=str(output_path), output_sha256=rt.digest(output_path),
                  legacy_factor_counts=[len(legacy[old]) for old in range(35)], empty_padding_slots=list(model32.EXCLUDED_LEGACY))
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('native', type=Path)
    parser.add_argument('--cache', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--threads', type=int, default=2)
    args = parser.parse_args()
    info = export(args.native, args.output, model32.Model32(args.cache.resolve()), args.threads)
    rt.write_json(args.output.with_suffix('.export.json'), info)
    print(rt.json.dumps(info, indent=2))
