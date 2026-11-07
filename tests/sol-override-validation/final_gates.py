"""Run required serial gates; any failed gate makes the process fail.

Caller holds writer.lock, prepares PATH/SOLKEY_RULES and retains 4GiB VM reserve.
Logs are local outputs, never updated proof expectations or committed evidence.
"""
from gate_runtime import ROOT, Runner, arguments

CONTROLS = ['Trust', 'GraphControls', 'AdvancedControls', 'DefensiveControls']


def main():
    runner = Runner(arguments(__doc__), 'final-gates')
    if runner.preflight():
        return 1
    if runner.run('no-live-lean-before-mcp', ['sh', '-c',
            "! ps -eo stat=,comm= | awk '$1 !~ /^Z/ && ($2 == \"lean\" || $2 == \"lake\") {found=1} END {exit !found}'"]):
        return 1
    runner.run('lean-version', ['lean', '--version'])
    runner.run('lake-version', ['lake', '--version'])
    for source in sorted((ROOT / 'Solidity/Frontend/OverrideValidation').glob('*.lean')):
        runner.run('final-diag-' + source.stem,
                   ['scripts/coord-tools/lean-mcp', 'diag', str(source.relative_to(ROOT))])
    for name in CONTROLS:
        runner.run('final-diag-' + name,
                   ['scripts/coord-tools/lean-mcp', 'diag', f'tests/sol-override-validation/{name}.lean'])
    # Stop before shell Lean; a failed diagnostic is retained by status().
    if runner.run('mcp-stop', ['scripts/coord-tools/lean-mcp', 'stop']):
        return 1
    if runner.run('no-live-lean', ['sh', '-c',
            "! ps -eo stat=,comm= | awk '$1 !~ /^Z/ && ($2 == \"lean\" || $2 == \"lake\") {found=1} END {exit !found}'"]):
        return 1
    for name in CONTROLS:
        runner.run('final-proof-' + name,
                   ['lake', 'env', 'lean', '-j1', '--tstack=131072', f'tests/sol-override-validation/{name}.lean'])
    for name, command, seconds in [
        ('final-keysort', ['bash', 'scripts/check-solkey.sh'], 600),
        ('final-run-lean', ['bash', './run-lean.sh'], 1800),
        ('final-axiom-inventory', ['node', 'scripts/check-axiom-pins.mjs'], 180),
        ('final-doc-paths', ['bash', 'scripts/check-doc-paths.sh'], 180),
        ('final-core-checkpoint', ['lake', 'build', 'Solidity'], 1800),
        ('final-resources', ['sh', '-c', 'cat /sys/fs/cgroup/memory.max /sys/fs/cgroup/memory.swap.max /sys/fs/cgroup/memory.peak /sys/fs/cgroup/memory.events'], 180),
    ]:
        runner.run(name, command, seconds)
    return runner.status()


if __name__ == '__main__':
    raise SystemExit(main())
