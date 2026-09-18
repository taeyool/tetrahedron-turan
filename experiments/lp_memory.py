"""Common LP inactive-cut housekeeping when dense coefficient storage is large."""
import numpy as np

ENTRY_LIMIT = 500_000_000
DUAL_ACTIVE_TOLERANCE = 1e-10


def select_retained(duals, count, capacity):
    """Keep every dual-active cut, then fill remaining capacity newest first."""
    assert len(duals) == count and capacity >= 0
    active = np.flatnonzero(np.abs(duals) > DUAL_ACTIVE_TOLERANCE).tolist()
    retained = set(active)
    for index in range(count - 1, -1, -1):
        if len(retained) >= capacity:
            break
        retained.add(index)
    return sorted(retained), active


def prune_for_memory(master, solution, incoming_cuts, entry_limit=ENTRY_LIMIT):
    """Apply to both LP methods; ordinary keep_cuts pruning remains the fallback.

    The threshold estimates storage using rows times columns, conservatively
    including zeros. It is an admission target, not permission to remove active
    rows. The external process-tree memory limit still applies if active rows
    alone exceed the target. No configuration column is removed.
    """
    columns = len(master.masks)
    count = len(master.cuts)
    projected = columns * (master.neq + count + incoming_cuts)
    if not columns or projected <= entry_limit:
        return dict(triggered=False, projected_dense_entries=projected)
    duals = np.asarray(solution.row_dual[master.neq:], dtype=float)
    assert len(duals) == count and np.all(np.isfinite(duals))
    capacity = max(0, entry_limit // columns - master.neq - incoming_cuts)
    keep, active = select_retained(duals, count, capacity)
    keep_set = set(keep)
    remove = np.asarray([master.neq + i for i in range(count) if i not in keep_set], dtype=np.int32)
    before = master.h.getNumRow()
    assert before == master.neq + count
    if len(remove):
        status = master.h.deleteRows(len(remove), remove)
        assert status != master.highspy.HighsStatus.kError
        assert master.h.getNumRow() == before - len(remove)
        master.cuts = [master.cuts[i] for i in keep]
        master.sixcuts = [master.sixcuts[i] for i in keep]
    return dict(triggered=True, entry_limit=entry_limit, columns=columns,
        projected_dense_entries=projected, dual_active_tolerance=DUAL_ACTIVE_TOLERANCE,
        cuts_before=count, cuts_removed=len(remove), cuts_retained=len(keep),
        dual_active_cuts=len(active), target_retained_capacity=capacity,
        target_exceeded_by_active_cuts=len(active) > capacity,
        incoming_cuts=incoming_cuts, configuration_columns_removed=0)
