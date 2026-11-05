"""Sample actual Lean argv0 names; command text in other processes is not a worker."""
from pathlib import PurePosixPath

def lean_workers(ps: str) -> list[str]:
    workers = []
    for line in ps.splitlines():
        parts = line.split(None, 2)
        if len(parts) >= 2 and PurePosixPath(parts[1]).name == 'lean':
            workers.append(line)
    return workers
