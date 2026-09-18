"""Numerical check of tighter admission while retaining the optimal dual support."""
import argparse
from pathlib import Path
from types import SimpleNamespace
import highspy
import numpy as np
import runtime as rt
from lp_memory import prune_for_memory
from no5_lp_memory import admit_cuts, NO5_ENTRY_LIMIT


def validate(output):
    output.mkdir(parents=True, exist_ok=False)
    h = highspy.Highs()
    for name, value in [('output_flag', False), ('threads', 1),
                        ('primal_feasibility_tolerance', 1e-9), ('dual_feasibility_tolerance', 1e-9)]:
        assert h.setOptionValue(name, value) == highspy.HighsStatus.kOk
    h.changeObjectiveSense(highspy.ObjSense.kMaximize)
    h.addVars(2, np.zeros(2), np.full(2, highspy.kHighsInf))
    h.changeColsCost(2, np.array([0, 1], np.int32), np.array([1., 0.]))
    h.addRow(1., 1., 2, np.array([0, 1], np.int32), np.ones(2))
    caps = [0.4] + [0.5 + .01 * i for i in range(20)]
    for cap in caps:
        h.addRow(-highspy.kHighsInf, cap, 1, np.array([0], np.int32), np.ones(1))
    h.run()
    assert h.getModelStatus() == highspy.HighsModelStatus.kOptimal
    before = h.getObjectiveValue()
    master = SimpleNamespace(h=h, highspy=highspy, neq=1, masks=[0, 1],
                             cuts=list(enumerate(caps)), sixcuts=list(caps))
    solution = h.getSolution()
    policy = admit_cuts(master, solution, requested=80, entry_limit=16)
    assert policy['admitted'] == 6 and policy['admitted'] < policy['requested']
    pruning = prune_for_memory(master, solution, policy['admitted'], entry_limit=16)
    assert pruning['configuration_columns_removed'] == 0
    assert master.cuts[0][0] == 0
    # Add the admitted prefix of known redundant inequalities; x <= .4 remains active.
    for i in range(policy['admitted']):
        cap = .7 + .01 * i
        h.addRow(-highspy.kHighsInf, cap, 1, np.array([0], np.int32), np.ones(1))
        master.cuts.append((100 + i, cap)); master.sixcuts.append(cap)
    assert h.getNumCol() * h.getNumRow() <= 16
    h.run()
    assert h.getModelStatus() == highspy.HighsModelStatus.kOptimal
    after = h.getObjectiveValue()
    np.testing.assert_allclose(before, after, atol=1e-10, rtol=0)
    # At the real column count, a large existing dual support admits fewer new cuts.
    full = SimpleNamespace(masks=range(1_295_600), neq=2, cuts=list(range(220)))
    dual = SimpleNamespace(row_dual=[0., 0.] + [1.] * 200 + [0.] * 20)
    large = admit_cuts(full, dual, 80)
    assert large['admitted'] == 29
    assert (full.neq + 200 + large['admitted']) * len(full.masks) <= NO5_ENTRY_LIMIT
    result = dict(status='passed', objective_before=before, objective_after=after,
                  fixture_admission=policy, fixture_pruning=pruning,
                  full_column_admission=large, every_active_cut_retained=True,
                  configuration_columns_unchanged=True, source_sha256=rt.sources())
    rt.write_json(output / 'validation.json', result)
    print(rt.json.dumps(result))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    validate(parser.parse_args().output.resolve())
