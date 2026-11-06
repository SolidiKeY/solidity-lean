"""Compare committed guarded controls; never derive expectations from execution.

Caller holds writer.lock and uses a bounded runner with 4GiB VM reserve.
The reviewed #guard_msgs expectations are already committed in the Lean files.
"""
import hashlib
from gate_runtime import ROOT, Runner, arguments

CONTROLS = ['Trust', 'AdvancedControls', 'GraphControls', 'DefensiveControls']


def main():
    paths = [ROOT / f'tests/sol-override-validation/{name}.lean' for name in CONTROLS]
    before = {p: hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    runner = Runner(arguments(__doc__), 'control-gates')
    if runner.preflight():
        return 1
    if runner.run('no-live-lean', ['sh', '-c',
            "! ps -eo stat=,comm= | awk '$1 !~ /^Z/ && ($2 == \"lean\" || $2 == \"lake\") {found=1} END {exit !found}'"]):
        return 1
    for name in CONTROLS:
        if runner.run('control-proof-' + name,
                      ['lake', 'env', 'lean', '-j1', '--tstack=131072', f'tests/sol-override-validation/{name}.lean']):
            return 1
    if any(hashlib.sha256(p.read_bytes()).hexdigest() != digest for p, digest in before.items()):
        raise RuntimeError('control sources changed during comparison')
    print('PASS committed guarded control expectations; sources unchanged', flush=True)
    return runner.status()


if __name__ == '__main__':
    raise SystemExit(main())
