"""Release retained HiGHS allocations via bounded, checked model serialization."""
import gc
import hashlib
import json
from pathlib import Path
import time
import weakref
import numpy as np
from scipy import sparse
import highspy


def checked(status):
    assert status != highspy.HighsStatus.kError, status


def columns(h, first, stop):
    indices = np.arange(first, stop, dtype=np.int32)
    status, count, cost, lower, upper, nonzeros = h.getCols(len(indices), indices)
    checked(status)
    status, starts, rows, values = h.getColsEntries(len(indices), indices)
    checked(status)
    assert count == len(indices) and len(values) == len(rows) == nonzeros
    matrix = sparse.csc_matrix((values, rows, np.r_[starts, nonzeros]),
                              shape=(h.getNumRow(), count))
    # Canonical ordering avoids depending on the backend's internal entry order.
    matrix.sort_indices()
    return dict(cost=np.asarray(cost, dtype='<f8'), lower=np.asarray(lower, dtype='<f8'),
        upper=np.asarray(upper, dtype='<f8'), starts=np.asarray(matrix.indptr, dtype='<i4'),
        rows=np.asarray(matrix.indices, dtype='<i4'), values=np.asarray(matrix.data, dtype='<f8'))


def bundle_digest(bundle):
    digest = hashlib.sha256()
    for name in sorted(bundle):
        values = np.ascontiguousarray(bundle[name])
        digest.update(name.encode('ascii'))
        digest.update(values.dtype.str.encode('ascii'))
        digest.update(np.asarray(values.shape, dtype='<i8').tobytes())
        digest.update(values.tobytes())
    return digest.hexdigest()


def snapshot(h, directory, chunk_columns):
    n, m = h.getNumCol(), h.getNumRow()
    status, count, lower, upper, nnz = h.getRows(m, np.arange(m, dtype=np.int32))
    checked(status)
    assert count == m and nnz == h.getNumNz()
    status, sense = h.getObjectiveSense()
    checked(status)
    status, offset = h.getObjectiveOffset()
    checked(status)
    options = h.getOptions()
    settings = {name: getattr(options, name) for name in dir(options)
                if not name.startswith('_') and isinstance(getattr(options, name), (bool, int, float, str))}
    basis = h.getBasis()
    metadata = dict(n=n, m=m, nonzeros=nnz, sense=int(sense), offset=float(offset),
        settings=settings, basis_was_valid=bool(basis.valid), chunks=[])
    # Return only independent Python/NumPy data; no object retaining the old solver.
    basis_columns = np.asarray([int(value) for value in basis.col_status], dtype='<i4')
    basis_rows = np.asarray([int(value) for value in basis.row_status], dtype='<i4')
    np.savez(directory / 'rows-and-basis.npz', lower=np.array(lower, copy=True),
             upper=np.array(upper, copy=True), basis_columns=basis_columns, basis_rows=basis_rows)
    for first in range(0, n, chunk_columns):
        stop = min(first + chunk_columns, n)
        bundle = columns(h, first, stop)
        filename = f'columns-{first:07d}.npz'
        np.savez(directory / filename, **bundle)
        metadata['chunks'].append(dict(first=first, stop=stop, filename=filename,
                                       sha256=bundle_digest(bundle), nonzeros=len(bundle['values'])))
    assert sum(chunk['nonzeros'] for chunk in metadata['chunks']) == nnz
    return metadata


def cleanup_scratch(directory, metadata):
    # Delete only the exact temporary files created by this invocation.
    for filename in [chunk['filename'] for chunk in metadata['chunks']] + ['rows-and-basis.npz']:
        path = directory / filename
        assert path.parent == directory and path.is_file()
        path.unlink()


def recycle(master, directory, search_deadline, chunk_columns=2048):
    started = time.monotonic()
    directory = Path(directory).resolve()
    directory.mkdir(parents=True, exist_ok=False)
    metadata = snapshot(master.h, directory, chunk_columns)
    exported = time.monotonic()
    metadata.update(snapshot_seconds=exported - started, status='snapshotted',
                    entry_roundtrip='Canonical CSC coefficients, costs and bounds checked per bounded column chunk.')
    (directory / 'manifest.json').write_text(json.dumps(metadata, indent=2) + '\n')
    # Keep the old solver intact if time is too short for import and verification.
    reserve = 4 * metadata['snapshot_seconds'] + 60
    if search_deadline - exported <= reserve:
        metadata.update(status='skipped_for_time', required_import_reserve_seconds=reserve,
                        seconds=time.monotonic() - started, old_solver_released=False)
        cleanup_scratch(directory, metadata)
        (directory / 'manifest.json').write_text(json.dumps(metadata, indent=2) + '\n')
        return dict(applied=False, status=metadata['status'], seconds=metadata['seconds'], reserve_seconds=reserve)
    old_reference = weakref.ref(master.h)
    master.h = None
    gc.collect()
    if old_reference() is not None:
        master.h = old_reference()
        raise RuntimeError('Old HiGHS instance remains referenced; refusing a second full matrix allocation.')
    released = time.monotonic()
    fresh = highspy.Highs()
    for name, value in metadata['settings'].items():
        if name == 'log_file':
            value = str(directory / 'solver.log')
        checked(fresh.setOptionValue(name, value))
    checked(fresh.changeObjectiveSense(highspy.ObjSense(metadata['sense'])))
    checked(fresh.changeObjectiveOffset(metadata['offset']))
    with np.load(directory / 'rows-and-basis.npz') as stored:
        row_lower = stored['lower']; row_upper = stored['upper']
        basis_columns = stored['basis_columns']; basis_rows = stored['basis_rows']
    checked(fresh.addRows(metadata['m'], row_lower, row_upper, 0,
        np.zeros(metadata['m'] + 1, dtype=np.int32), np.array([], dtype=np.int32), np.array([], dtype=float)))
    for chunk in metadata['chunks']:
        with np.load(directory / chunk['filename']) as stored:
            bundle = {name: stored[name] for name in stored.files}
        assert bundle_digest(bundle) == chunk['sha256']
        count = chunk['stop'] - chunk['first']
        checked(fresh.addCols(count, bundle['cost'], bundle['lower'], bundle['upper'],
            len(bundle['values']), bundle['starts'], bundle['rows'], bundle['values']))
    assert fresh.getNumCol() == metadata['n'] and fresh.getNumRow() == metadata['m']
    assert fresh.getNumNz() == metadata['nonzeros']
    # Check the restored backend, not merely that the temporary files were read.
    for chunk in metadata['chunks']:
        assert bundle_digest(columns(fresh, chunk['first'], chunk['stop'])) == chunk['sha256']
    status, count, actual_lower, actual_upper, actual_nnz = fresh.getRows(metadata['m'], np.arange(metadata['m'], dtype=np.int32))
    checked(status)
    assert count == metadata['m'] and actual_nnz == metadata['nonzeros']
    np.testing.assert_array_equal(actual_lower, row_lower)
    np.testing.assert_array_equal(actual_upper, row_upper)
    basis_restored = len(basis_columns) == metadata['n'] and len(basis_rows) == metadata['m']
    if basis_restored:
        basis = highspy.HighsBasis()
        basis.col_status = [highspy.HighsBasisStatus(int(value)) for value in basis_columns]
        basis.row_status = [highspy.HighsBasisStatus(int(value)) for value in basis_rows]
        checked(fresh.setBasis(basis))
    master.h = fresh
    metadata.update(status='restored_and_verified', old_solver_released=True,
        release_seconds=released - exported, restore_and_verify_seconds=time.monotonic() - released,
        seconds=time.monotonic() - started, basis_restored=basis_restored,
        all_coefficients_costs_and_bounds_identical=True,
        restored_log_file=str(directory / 'solver.log'),
        note='Simplex basis statuses restored when available; internal scaling, factorization and edge weights are rebuilt. This overhead is included in search wall time.')
    cleanup_scratch(directory, metadata)
    (directory / 'manifest.json').write_text(json.dumps(metadata, indent=2) + '\n')
    return dict(applied=True, status=metadata['status'], seconds=metadata['seconds'],
        snapshot_seconds=metadata['snapshot_seconds'], basis_restored=basis_restored,
        old_solver_released=True, all_coefficients_costs_and_bounds_identical=True,
        nonzeros=metadata['nonzeros'], n=metadata['n'], m=metadata['m'])
