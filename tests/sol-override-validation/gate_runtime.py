"""Serial gate runner. Caller supplies a bounded runner and holds writer.lock."""
import argparse
import json
import os
from pathlib import Path
import shlex
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]


def arguments(description):
    parser = argparse.ArgumentParser(description=description)
    parser.add_argument('--runner', default=os.environ.get('SOL_OV_RUNNER'),
                        help='command prefix in a prepared bounded environment, e.g. docker exec CONTAINER')
    parser.add_argument('--local', action='store_true', help='use the current bounded environment and PATH')
    parser.add_argument('--output', type=Path, default=ROOT / 'tests/sol-override-validation/runtime/gates')
    args = parser.parse_args()
    if bool(args.runner) == args.local:
        parser.error('choose exactly one of --runner or --local; no container/PATH is assumed')
    return args


class Runner:
    def __init__(self, args, label):
        self.prefix = shlex.split(args.runner) if args.runner else []
        self.output = args.output.resolve()
        self.output.mkdir(parents=True, exist_ok=True)
        self.label = label
        self.results = []

    def run(self, name, args, seconds=180):
        command = self.prefix + ['env', 'LEAN_NUM_THREADS=1', 'timeout', '--kill-after=10', str(seconds)] + args
        started = time.monotonic()
        path = self.output / (name + '.log')
        with path.open('w') as output:
            try:
                code = subprocess.run(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT).returncode
            except OSError as error:
                output.write(str(error) + '\n')
                code = 127
        self.results.append(dict(name=name, command=command, exitCode=code,
                                 status='pass' if code == 0 else 'fail',
                                 seconds=round(time.monotonic()-started, 2), evidence=str(path)))
        (self.output / (self.label + '.json')).write_text(json.dumps(self.results, indent=2) + '\n')
        print(f'{name}: exit {code}', flush=True)
        return code

    def status(self):
        return 1 if any(result['exitCode'] != 0 for result in self.results) else 0

    def preflight(self):
        # Explicit -j1 must apply to Lake-built dependencies too. Neither this
        # checker nor the runner rewrites the effective package configuration.
        code = """import pathlib,tomllib
p=pathlib.Path('/sys/fs/cgroup')
m=int((p/'memory.max').read_text()); s=int((p/'memory.swap.max').read_text())
assert 0<m<=12*1024**3 and s==0, 'requires <=12GiB hard cap and zero swap'
c=tomllib.loads(pathlib.Path('lakefile.toml').read_text())
assert '-j1' in c.get('weakLeanArgs',[]), 'package lacks -j1'
assert c.get('lean_lib') and all('-j1' in x.get('weakLeanArgs',[]) for x in c['lean_lib']), 'library lacks -j1'
print('bounded serial configuration verified; caller must retain 4GiB VM reserve')
"""
        return self.run('serial-resource-preflight', ['python3', '-c', code])
