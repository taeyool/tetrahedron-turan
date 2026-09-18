"""Sequential checks of common inactive-cut memory housekeeping."""
import argparse
from pathlib import Path
from types import SimpleNamespace
import numpy as np
import highspy
import runtime as rt
from lp_memory import prune_for_memory, select_retained


def validate(output):
    output.mkdir(parents=True, exist_ok=False)
    # Active cuts are kept even if they alone exceed the admission target.
    assert select_retained(np.array([1., 0., -2., 0.]), 4, 1) == ([0, 2], [0, 2])
    assert select_retained(np.array([1., 0., 0., 0.]), 4, 3) == ([0, 2, 3], [0])
    h = highspy.Highs()
    for name, value in [('output_flag', False), ('threads', 1),
                        ('primal_feasibility_tolerance', 1e-9), ('dual_feasibility_tolerance', 1e-9)]:
        h.setOptionValue(name, value)
    h.changeObjectiveSense(highspy.ObjSense.kMaximize)
    h.addVars(2, np.zeros(2), np.full(2, highspy.kHighsInf))
    h.changeColsCost(2, np.array([0, 1], np.int32), np.array([1., 0.]))
    indices = np.array([0, 1], np.int32)
    h.addRow(1., 1., 2, indices, np.ones(2))
    # x <= 0.4 is active; all later x <= larger values are redundant.
    caps = [0.4] + [0.5 + 0.01 * i for i in range(20)]
    for cap in caps:
        h.addRow(-highspy.kHighsInf, cap, 1, np.array([0], np.int32), np.ones(1))
    h.run()
    assert h.getModelStatus() == highspy.HighsModelStatus.kOptimal
    before = h.getObjectiveValue()
    master = SimpleNamespace(h=h, highspy=highspy, neq=1, masks=[0, 1],
        cuts=list(enumerate(caps)), sixcuts=list(caps))
    noop = prune_for_memory(master, h.getSolution(), 80)
    assert not noop['triggered'] and h.getNumRow() == 22
    changed = prune_for_memory(master, h.getSolution(), 2, entry_limit=16)
    assert changed['triggered'] and changed['cuts_removed'] > 0
    assert master.cuts[0][0] == 0 and changed['configuration_columns_removed'] == 0
    h.run()
    assert h.getModelStatus() == highspy.HighsModelStatus.kOptimal
    after = h.getObjectiveValue()
    np.testing.assert_allclose(after, before, atol=1e-10, rtol=0)
    assert h.getNumCol() == 2
    record = dict(status='passed', active_cuts_preserved=True,
        small_models_noop=True, before_objective=before, after_objective=after,
        fixture_pruning=changed, source_sha256=rt.sources())
    rt.write_json(output / 'validation.json', record)
    print(rt.json.dumps(record))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    validate(parser.parse_args().output.resolve())
