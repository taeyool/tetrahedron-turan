"""Shared support for the bounded two-model campaign (no archive mutations)."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
RESEARCH = ROOT / 'search'
for name in ('OPENBLAS_NUM_THREADS', 'VECLIB_MAXIMUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[name] = '1'
os.environ['PYTHONUTF8'] = '1'
sys.path.insert(0, str(RESEARCH))
# Python 3.8+ no longer searches PATH for dependent DLLs in ctypes loads.
# This is a loader adaptation only; the audited C++ sources remain unchanged.
DLL_HANDLES = []
if os.name == 'nt':
    compiler = shutil.which('c++')
    if compiler:
        DLL_HANDLES.append(os.add_dll_directory(str(Path(compiler).parent)))

TYPES = [0, 1, 3, 7, 11, 12, 13, 15, 30, 31, 63, 76, 77, 86, 87, 94,
         116, 117, 119, 222, 236, 237, 254]
CHECKPOINTS = [60, 300, 900, 1800, 3600]


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def write_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(value, indent=2, allow_nan=False) + '\n'
    fd, name = tempfile.mkstemp(prefix=path.name + '.', suffix='.tmp', dir=path.parent)
    tmp = Path(name)
    with os.fdopen(fd, 'w', encoding='utf-8') as stream:
        stream.write(payload)
    # Readers/scanners can briefly deny delete sharing on Windows. Keep the old
    # complete JSON visible while retrying the atomic replacement, never truncate it.
    deadline = time.monotonic() + 5
    attempts = 0
    while True:
        try:
            tmp.replace(path)
            if attempts:
                print(f'JSON replacement recovered after {attempts} retries: {path}',
                      file=sys.stderr, flush=True)
            return
        except PermissionError as exc:
            if os.name != 'nt' or exc.winerror not in (5, 32, 33) or time.monotonic() >= deadline:
                # Retain the completed temporary file for recovery on a lasting error.
                raise
            attempts += 1
            time.sleep(0.05)


def sources():
    paths = sorted(set(RESEARCH.glob('*.py')) | set(RESEARCH.glob('*.cpp')) |
                   set(RESEARCH.glob('*.inc')) | set(RESEARCH.glob('*.hpp')) |
                   set(HERE.glob('*.py')) | set(HERE.glob('*.cpp')) |
                   set((HERE / 'native_scs').glob('*.c')) |
                   set((HERE / 'native_scs').glob('*.json')) |
                   set((ROOT / 'certificate').glob('*.py')) |
                   set((ROOT / 'certificate').glob('*.cpp')))
    return {str(p.relative_to(ROOT)): digest(p) for p in paths}


def model(cache, name):
    import numpy as np
    import reconstruct_optimization as ro
    from five_root_oracle import Oracle5
    from expand_seven_optimization import OLD_DIMS
    base = ro.Oracle(cache)
    types = [] if name == 'M7-no5' else TYPES
    if name not in ('M7-no5', 'M7-all5'):
        raise ValueError('This bounded runner supports only the two selected models')
    oracle = Oracle5(base, types, cache)
    ro.DIMS = OLD_DIMS + oracle.dimensions
    ro.OFFSETS = np.cumsum([0] + [d*d for d in ro.DIMS[9:]])
    with np.load(cache / 'components.npz', allow_pickle=False) as data:
        blocks = [data[f'block{i}'].copy() for i in range(9)]
        objective = data['edge'] / (720 * base.cert['scale']**2)
        stat = data['stat_unscaled'] / 60
    np.testing.assert_allclose(objective, [int(h).bit_count()/20 for h in base.cert['H_representatives']], atol=1e-15, rtol=0)
    metadata = []
    for b in base.cert['order6_blocks']:
        metadata.append(dict(b))
    fs = ro.fs
    for s, l, sigma in [(1, 4, 0), (3, 5, 0), (3, 5, 1)]:
        flags = fs.flags_for_type(s, l, sigma, fs.rooted_canon_table(l, s))
        metadata.append(dict(s=s, l=l, sigma=sigma, flags=flags, dimension=len(flags)))
    for entry in oracle.entries:
        metadata.append(dict(s=5, l=6, sigma=entry['sigma'], flags=entry['flags'], dimension=entry['dimension']))
    for i, item in enumerate(metadata):
        item['block_index'] = i
        item['ordered_basis_sha256'] = hashlib.sha256(json.dumps(item['flags'], separators=(',', ':')).encode()).hexdigest()
    return oracle, blocks, objective, stat, metadata


def moments(master, sol):
    import numpy as np
    import reconstruct_optimization as ro
    y = np.asarray(sol.col_value)
    x = master.deck.T @ y
    flat = master.feat.T @ y
    matrices = [np.einsum('h,hij->ij', x, b) for b in master.blocks]
    matrices += [flat[a:b].reshape(d, d) for a, b, d in zip(ro.OFFSETS[:-1], ro.OFFSETS[1:], ro.DIMS[9:])]
    return y, x, matrices


if __name__ == '__main__':
    # Run original tools with the Windows DLL search path and pinned threading.
    import runpy
    script = Path(sys.argv[1]).resolve()
    sys.argv = sys.argv[1:]
    runpy.run_path(str(script), run_name='__main__')
