"""Verify existing kernel-enforced scope limits; never infer a waiver."""
from pathlib import Path, PurePosixPath

CAP = 12*1024**3
HOST_RESERVE = 12*1024**3


class ScopeError(RuntimeError):
    pass


def require_scope(proc_root=Path('/proc'), cgroup_root=Path('/sys/fs/cgroup'), check_reserve=True):
    try:
        memberships = [line[3:] for line in (proc_root/'self/cgroup').read_text().splitlines()
                       if line.startswith('0::')]
        if len(memberships) != 1:
            raise ScopeError('one observable unified cgroup membership is required')
        member = PurePosixPath(memberships[0])
        if not member.is_absolute() or '..' in member.parts:
            raise ScopeError('invalid cgroup membership')
        scope = cgroup_root.joinpath(*member.parts[1:])
        maximum = (scope/'memory.max').read_text().strip()
        swap_maximum = (scope/'memory.swap.max').read_text().strip()
        if maximum == 'max' or int(maximum) != CAP:
            raise ScopeError('verified MemoryMax=12GiB is required; observed '+maximum)
        if swap_maximum != '0':
            raise ScopeError('verified MemorySwapMax=0 is required; observed '+swap_maximum)
        current = int((scope/'memory.current').read_text())
        swap_current = int((scope/'memory.swap.current').read_text())
        if current < 0 or swap_current != 0:
            raise ScopeError('scope observations invalid or swap usage is nonzero')
        memory = dict(line.split(':', 1) for line in (proc_root/'meminfo').read_text().splitlines())
        available = int(memory['MemAvailable'].split()[0])*1024
        if check_reserve and available < HOST_RESERVE:
            raise ScopeError('12GiB host reserve unavailable')
        return dict(membership=str(member), scope_path=str(scope), memory_max_bytes=int(maximum),
                    memory_swap_max_bytes=0, memory_current_bytes=current, memory_swap_current_bytes=0,
                    host_available_bytes=available, host_reserve_bytes=HOST_RESERVE)
    except ScopeError:
        raise
    except (OSError, KeyError, ValueError) as error:
        raise ScopeError('hard scope observation unavailable: '+str(error)) from error
