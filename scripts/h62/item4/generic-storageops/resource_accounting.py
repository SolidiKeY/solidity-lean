#!/usr/bin/env python3
"""H113 cache-adjusted accounting only; cap/swap/reserve/thread checks stay external."""


def non_reclaimable(current, stats):
    values = [current, stats['inactive_file'], stats['active_file']]
    if any(type(v) is not int or v < 0 for v in values):
        raise ValueError('invalid cgroup memory sample')
    cache = stats['inactive_file'] + stats['active_file']
    return max(0, current - cache), cache


def account(parent_current, runtime_current, parent_stats, runtime_stats):
    parent_noncache, parent_cache = non_reclaimable(parent_current, parent_stats)
    runtime_noncache, runtime_cache = non_reclaimable(runtime_current, runtime_stats)
    return dict(parent_current=parent_current, runtime_current=runtime_current,
                parent_other_raw=max(0, parent_current-runtime_current),
                parent_reclaimable_file=parent_cache,
                runtime_reclaimable_file=runtime_cache,
                parent_non_reclaimable=parent_noncache,
                runtime_non_reclaimable=runtime_noncache,
                parent_other=max(0, parent_noncache-runtime_noncache),
                accounting_authority='H113',
                accounting_formula='max(0, (parent.current-parent.active_file-parent.inactive_file) - max(0, runtime.current-runtime.active_file-runtime.inactive_file)); each non-reclaimable term clamped at zero')
