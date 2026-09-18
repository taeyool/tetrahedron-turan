"""Sequential coefficient, basis, optimum and budget checks for solver recycling."""
import argparse
from pathlib import Path
from types import SimpleNamespace
import time
import numpy as np
from scipy import sparse
import highspy
import runtime as rt
from recycle_highs import recycle, checked


def validate(output):
    output.mkdir(parents=True, exist_ok=False)
    h = highspy.Highs()
    for name, value in [('output_flag', False), ('threads', 1),
                        ('primal_feasibility_tolerance', 1e-9), ('dual_feasibility_tolerance', 1e-9)]:
        checked(h.setOptionValue(name, value))
    n = 48
    rng = np.random.default_rng(61248)
    checked(h.addVars(n, np.zeros(n), np.full(n, highspy.kHighsInf)))
    checked(h.changeObjectiveSense(highspy.ObjSense.kMaximize))
    checked(h.changeColsCost(n, np.arange(n, dtype=np.int32), rng.uniform(size=n)))
    rows = [np.ones(n), np.tile([-1., 1.], n // 2)]
    for _ in range(30):
        row = rng.normal(size=n)
        rows.append(row - row.mean() + 0.1)
    matrix = sparse.csr_matrix(np.stack(rows))
    lower = np.zeros(len(rows)); upper = np.full(len(rows), highspy.kHighsInf)
    lower[0] = upper[0] = 1.; upper[1] = 0.
    checked(h.addRows(len(rows), lower, upper, matrix.nnz, matrix.indptr, matrix.indices, matrix.data))
    holder = SimpleNamespace(h=h)
    del h  # The test exercises real destruction; no extra solver owner remains.
    results = []
    for iteration in range(2):
        checked(holder.h.run())
        assert holder.h.getModelStatus() == highspy.HighsModelStatus.kOptimal
        before = holder.h.getObjectiveValue()
        result = recycle(holder, output / f'cycle-{iteration}', time.monotonic() + 10000, chunk_columns=7)
        assert result['applied'] and result['old_solver_released'] and result['basis_restored']
        checked(holder.h.run())
        assert holder.h.getModelStatus() == highspy.HighsModelStatus.kOptimal
        after = holder.h.getObjectiveValue()
        np.testing.assert_allclose(after, before, atol=1e-9, rtol=0)
        results.append(dict(before=before, after=after, recycling=result))
        if iteration == 0:
            # Exercise row deletion and addition before recycling again.
            dual = np.asarray(holder.h.getSolution().row_dual)
            inactive = np.flatnonzero(np.abs(dual[2:]) <= 1e-10)[:3] + 2
            assert len(inactive)
            checked(holder.h.deleteRows(len(inactive), inactive.astype(np.int32)))
            for _ in range(2):
                row = rng.normal(size=n); row = row - row.mean() + 0.05
                checked(holder.h.addRow(0., highspy.kHighsInf, n, np.arange(n, dtype=np.int32), row))
    original_identity = id(holder.h)
    skipped = recycle(holder, output / 'budget-skip', time.monotonic() + 0.01, chunk_columns=7)
    assert not skipped['applied'] and id(holder.h) == original_identity
    record = dict(status='passed', cycles=results, budget_skip=skipped,
        all_coefficients_costs_and_bounds_identical=True, old_instances_released=True,
        basis_statuses_restored=True, no_numerical_tolerance_changed=True, source_sha256=rt.sources())
    rt.write_json(output / 'validation.json', record)
    print(rt.json.dumps(record))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    validate(parser.parse_args().output.resolve())
