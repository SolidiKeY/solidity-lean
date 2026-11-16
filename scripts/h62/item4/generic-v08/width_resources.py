"""Fail-closed Linux measurements of a known owned process tree."""
import os
from pathlib import Path


class MeasurementError(RuntimeError):
    pass


def process_alive(pid):
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except OSError as error:
        raise MeasurementError(f'cannot establish liveness of owned pid {pid}') from error
    return True


def process_usage(pid, proc_root=Path('/proc'), alive=process_alive):
    """Discover kernel parent IDs, then require status data for live owned PIDs.

    A failed discovery read cannot silently hide an owned descendant. ENOENT is
    benign only when liveness confirms exit. Process RSS already includes threads.
    The optional root/liveness parameters support isolated filesystem regressions.
    """
    def read(path, current):
        try:
            return path.read_text()
        except FileNotFoundError:
            if not alive(current):
                return None
            raise MeasurementError(f'missing data for live pid {current}')
    try:
        parents = {}
        for root in proc_root.iterdir():
            if not root.name.isdigit():
                continue
            current = int(root.name)
            text = read(root/'stat', current)
            if text is None:
                continue
            # comm may contain spaces and parentheses; following fields do not.
            close = text.rfind(')')
            if close < 0 or text[:text.find(' ')].strip() != root.name:
                raise MeasurementError(f'invalid discovery data for pid {current}')
            tail = text[close+1:].split()
            parents[current] = int(tail[1])
        selected = {pid}
        while True:
            children = {i for i, parent in parents.items() if parent in selected} - selected
            if not children:
                break
            selected.update(children)
        rss, lean = 0, 0
        for current in selected:
            text = read(proc_root/str(current)/'status', current)
            if text is None:
                continue
            fields = dict(line.split(':', 1) for line in text.splitlines() if ':' in line)
            name = fields['Name'].strip()
            if fields.get('State', '').strip().startswith('Z'):
                continue
            memory = int(fields['VmRSS'].split()[0])*1024
            if memory < 0 or not name:
                raise MeasurementError(f'invalid status for owned pid {current}')
            rss += memory
            lean += name == 'lean'
        return rss, lean
    except MeasurementError:
        raise
    except (OSError, KeyError, ValueError, IndexError) as error:
        raise MeasurementError(f'process measurement unavailable: {type(error).__name__}') from error
