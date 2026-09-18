"""Conservative coefficient admission for the measured no5 full-LP backend."""
import numpy as np
from lp_memory import DUAL_ACTIVE_TOLERANCE

NO5_ENTRY_LIMIT = 300_000_000


def admit_cuts(master, solution, requested, entry_limit=NO5_ENTRY_LIMIT):
    """Leave room for every active cut, taking a prefix of ranked new cuts."""
    columns = len(master.masks)
    assert columns > 0 and requested >= 0
    duals = np.asarray(solution.row_dual[master.neq:], dtype=float)
    assert len(duals) == len(master.cuts) and np.all(np.isfinite(duals))
    active = int(np.count_nonzero(np.abs(duals) > DUAL_ACTIVE_TOLERANCE))
    capacity = max(0, entry_limit // columns - master.neq)
    available = max(0, capacity - active)
    admitted = min(requested, available)
    if requested and not admitted:
        raise RuntimeError('Active cuts exhaust the no5 coefficient-storage target; retain candidate and diagnose before retrying.')
    return dict(requested=requested, admitted=admitted, dual_active_cuts=active,
                total_cut_capacity=capacity, entry_limit=entry_limit,
                ranked_prefix_preserved=True, active_cuts_preserved=True)
