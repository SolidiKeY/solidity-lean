#!/usr/bin/env python3
"""Guard H97 compatibility from hidden warm or cold report-validation regressions.

Run under the repository writer lock. Uses an explicit synthetic report, records
warm7x25 and freshCLIwarmup+7, and never deploys host tooling or reruns size gates.
The before/after input and source hashes bind evidence to actual measured files.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import resource
import statistics
import subprocess
import time

ROOT = Path(__file__).resolve().parents[3]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(args):
    output, report, source = args.output.resolve(), args.report.resolve(), args.validator.resolve()
    if output.is_relative_to(ROOT) or output.exists():
        raise ValueError('choose a new off-checkout evidence path')
    ancestor = output.parent
    while not ancestor.exists():
        ancestor = ancestor.parent
    if subprocess.run(['git', '-C', str(ancestor), 'rev-parse', '--show-toplevel'],
                      stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0:
        raise ValueError('evidence must be outside Git checkouts')
    output.parent.mkdir(parents=True, exist_ok=True)
    text = report.read_text()
    spec = importlib.util.spec_from_file_location('measured_validator', source)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    inputs = {str(path): sha(path) for path in (report, source, module.SCHEMA)}
    expected = module.validate(text)
    warm = []
    for _ in range(7):
        started = time.monotonic()
        for _ in range(25):
            if module.validate(text) != expected:
                raise RuntimeError('validator result changed')
        warm.append((time.monotonic() - started) / 25)
    relative_source = source.relative_to(ROOT) if source.is_relative_to(ROOT) else source
    command = ['python3', '-B', str(relative_source), str(report)]
    cli = []
    for index in range(8):
        log = output.with_name(output.stem + f'-cli-{index}.log')
        started = time.monotonic()
        with log.open('xb') as stream:
            process = subprocess.Popen(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
            _, status, usage = os.wait4(process.pid, 0)
            process.returncode = os.waitstatus_to_exitcode(status)
        if process.returncode:
            raise RuntimeError(f'CLI validation failed: {log}')
        cli.append(dict(seconds=time.monotonic() - started, maxRssKiB=usage.ru_maxrss,
                        outputSha256=sha(log), log=log.name))
    if inputs != {path: sha(Path(path)) for path in inputs}:
        raise RuntimeError('measured inputs changed')
    if len({row['outputSha256'] for row in cli}) != 1:
        raise RuntimeError('CLI output changed')
    result = dict(command=command, inputs=inputs, warmSecondsPerCall=warm,
                  warmMedian=statistics.median(warm),
                  warmMaxRssKiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                  cliWarmup=cli[0], cli=cli[1:],
                  cliMedian=statistics.median(row['seconds'] for row in cli[1:]),
                  boundary='Synthetic report only; no host/API/Lean proof. WarmRSS is process high-water; CLIRSS is per-invocation wait4.')
    if args.before:
        before = json.loads(args.before.read_text())
        comparison = dict(warmDeltaPercent=(result['warmMedian']/before['warmMedian']-1)*100,
                          cliDeltaPercent=(result['cliMedian']/before['cliMedian']-1)*100,
                          sameCliOutput=result['cli'][0]['outputSha256']==before['cli'][0]['outputSha256'],
                          thresholdPercent=10)
        comparison['stop'] = max(comparison['warmDeltaPercent'], comparison['cliDeltaPercent']) > 10
        result['comparison'] = comparison
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: result[key] for key in ('warmMedian', 'cliMedian', 'comparison') if key in result}))
    if result.get('comparison', {}).get('stop') or not result.get('comparison', {}).get('sameCliOutput', True):
        raise RuntimeError('STOP: report-validation budget or output identity failed')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--before', type=Path)
    parser.add_argument('--validator', type=Path, default=Path(__file__).with_name('validate_result.py'))
    run(parser.parse_args())
