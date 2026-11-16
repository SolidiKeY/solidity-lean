#!/usr/bin/env python3
"""Partial certified CLI totals; unknown phases/RSS remain unknown.

Build the existing frontend first, then hold the repository writer lock.
Each admitted function runs in a fresh process. Existing CLI supervisors retain
the unchanged <=300s bound per compiler/Lean tool job, not per whole function. This never establishes a complete U01 baseline.
"""
import argparse
import hashlib
import json
import os
import pathlib
import resource
import platform
import shutil
import subprocess
import sys
import time


def digest(path):
    return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()


def load_admission(path):
    raw = path.read_bytes()
    return json.loads(raw), hashlib.sha256(raw).hexdigest()


def runtime_identity():
    tools = {}
    for name in ['node', 'lean', 'lake']:
        executable = shutil.which(name)
        try:
            version = subprocess.check_output([name, '--version'], text=True, stderr=subprocess.STDOUT).strip()
        except (OSError, subprocess.CalledProcessError) as error:
            version = 'unavailable: ' + str(error)
        tools[name] = {'executable': executable, 'version': version}
    quota = pathlib.Path('/sys/fs/cgroup/cpu.max')
    cpu = pathlib.Path('/proc/cpuinfo')
    model = next((line.split(':', 1)[1].strip() for line in cpu.read_text().splitlines()
                  if line.startswith('model name')), None) if cpu.exists() else None
    return {'python': sys.version, 'platform': platform.platform(), 'machine': platform.machine(),
            'cpuModel': model, 'cpuMax': quota.read_text().strip() if quota.exists() else None,
            'tools': tools, 'LEAN_NUM_THREADS': '1'}


def save(path, value):
    temporary = path.with_suffix('.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def result_errors(expected, payload, exit_code, unchanged):
    errors = list(payload.get('errors', []))
    rows = payload.get('results', [])
    if exit_code != 0:
        errors.append({'stage': 'process', 'reason': f'CLI exited {exit_code}'})
    if not unchanged:
        errors.append({'stage': 'source-identity', 'reason': 'source changed during verification'})
    if len(rows) != 1:
        errors.append({'stage': 'selection', 'reason': 'expected exactly one selected declaration'})
    else:
        row = rows[0]
        for key in ['sourceId', 'contract', 'sourceHash']:
            if row.get(key) != expected.get(key):
                errors.append({'stage': 'identity', 'reason': f'{key} mismatch'})
        if row.get('verification') not in [None, 'certified']:
            errors.append({'stage': 'verification', 'reason': 'not a certified result marker'})
        if row.get('status') != 'proved':
            errors.append({'stage': 'verification', 'reason': row.get('status', 'missing status')})
        if row.get('preconditions') not in [None, 'possible', 'notApplicable']:
            errors.append({'stage': 'preconditions', 'reason': row['preconditions']})
    return errors


def worker(config):
    cfg = json.loads(pathlib.Path(config).read_text())
    folder = pathlib.Path(cfg['folder'])
    row, repo = cfg['row'], pathlib.Path(cfg['repo'])
    command = ['node', 'scripts/test-solidity.mjs', '--json', '--no-build',
               '--contract', row['contract'], '--function', row['signature'],
               '--timeout-ms', str(cfg['timeoutMs']), '--solkey', cfg['solkey'],
               '--soljson', cfg['soljson'], row['source']]
    record = {'command': command, 'attemptFinished': False, 'errors': [], 'results': [],
              'wallMs': None, 'maxIndividualProcessRssKiB': None,
              'aggregateTreePeakRss': None, 'phases': None, 'walkSteps': None}
    try:
        if digest(row['source']) != row['sourceHash']:
            raise ValueError('input source no longer matches admission')
        start = time.perf_counter()
        with (folder/'stdout.json').open('w') as stdout, (folder/'stderr.log').open('w') as stderr:
            run = subprocess.run(command, cwd=repo, stdout=stdout, stderr=stderr,
                                 env=dict(os.environ, LEAN_NUM_THREADS='1'))
        record.update(wallMs=(time.perf_counter()-start)*1000, exit=run.returncode,
                      maxIndividualProcessRssKiB=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
        try:
            payload = json.loads((folder/'stdout.json').read_text())
        except (ValueError, OSError) as error:
            payload = {'results': [], 'errors': [{'stage': 'report', 'reason': str(error)}]}
        record['results'] = payload.get('results', [])
        record['errors'] = result_errors(row, payload, run.returncode,
                                         digest(row['source']) == row['sourceHash'])
        record['retry135'] = run.returncode == 135 or any(
            e.get('tool', {}).get('exitCode') == 135 for e in payload.get('errors', []))
        record['attemptFinished'] = True
    except Exception as error:
        record['errors'].append({'stage': 'setup', 'reason': str(error)})
    save(folder/'measurement.json', record)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--admission', type=pathlib.Path, required=True)
    parser.add_argument('--work', type=pathlib.Path, required=True, help='new, nonexisting evidence directory')
    parser.add_argument('--repo', type=pathlib.Path, default=pathlib.Path(__file__).resolve().parents[2])
    parser.add_argument('--soljson', type=pathlib.Path, required=True)
    parser.add_argument('--timeout-ms', type=int, default=300000)
    args = parser.parse_args()
    if not 1 <= args.timeout_ms <= 300000:
        parser.error('timeout must be 1..300000; original proof budgets unchanged')
    work, repo = args.work.resolve(), args.repo.resolve()
    work.mkdir(parents=True, exist_ok=False)
    report = {'kind': 'u01-partial-certified-process-totals', 'sourceToVerdictBaseline': False,
              'suiteComplete': False, 'attemptFinished': False, 'allScheduledPassed': False,
              'cacheState': 'warm imported artifacts; fresh CLI process per function; no build',
              'rssMetric': 'Linux RUSAGE_CHILDREN ru_maxrss: maximum individual-process RSS, not simultaneous aggregate tree peak',
              'limitations': 'Disjoint phases, aggregate tree peak RSS and walk steps unavailable. no systemd scope on the cloud VM (H232)',
              'rows': [], 'errors': [], 'perToolTimeoutMs': args.timeout_ms}
    save(work/'report.json', report)
    try:
        data, admission_sha = load_admission(args.admission)
        if data.get('kind') != 'u01-admission-only' or data.get('attemptFinished') is not True:
            raise ValueError('requires a finished admission-only report, not a verdict baseline')
        report['rows'] = [{'input': row, 'state': 'pending' if row.get('status') == 'ready' else 'not-scheduled', 'attempts': []} for row in data['results']]
        save(work/'report.json', report)
        report.update(repo=str(repo), toolHead=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip(),
                      driverSha256=digest(__file__), admissionSha256=admission_sha,
                      cliSha256=digest(repo/'scripts/test-solidity.mjs'), runtime=runtime_identity(),
                      toolWorktreeStatus=subprocess.check_output(['git', 'status', '--porcelain'], cwd=repo, text=True).splitlines(),
                      compilerFiles={str(p): digest(p) for p in sorted(args.soljson.resolve().glob('*.js'))})
        report['errors'].extend(data.get('errors', []))
        expected = {str(pathlib.Path(i['path']).resolve()): i['sha256'] for i in data['inputs']}
        for source, sha in expected.items():
            if digest(source) != sha:
                raise ValueError('admission source snapshot has changed: '+source)
        scheduled = 0
        for index, entry in enumerate(report['rows']):
            row = entry['input']
            if row.get('status') != 'ready':
                entry['reason'] = 'admission status retained; not a verification success'
                continue
            if expected.get(str(pathlib.Path(row['source']).resolve())) != row.get('sourceHash'):
                raise ValueError('admission row source hash mismatch')
            if not row.get('signature') or row.get('sourceId') is None:
                raise ValueError('ready row lacks exact signature/declaration ID')
            scheduled += 1
            entry['state'] = 'pending'
            save(work/'report.json', report)
            for attempt in range(2):
                folder = work/f'{index:04d}-{attempt}'
                folder.mkdir()
                cfg = {'folder': str(folder), 'row': row, 'repo': str(repo), 'timeoutMs': args.timeout_ms,
                       'solkey': str(repo/'tests/migration/solkey'), 'soljson': str(args.soljson.resolve())}
                save(folder/'config.json', cfg)
                run = subprocess.run([sys.executable, str(pathlib.Path(__file__).resolve()), '_one', str(folder/'config.json')])
                if run.returncode != 0:
                    raise RuntimeError('measurement worker failed; partial report retained')
                measurement = json.loads((folder/'measurement.json').read_text())
                entry['attempts'].append(measurement)
                save(work/'report.json', report)
                if not measurement.get('retry135') or attempt == 1:
                    break
            entry['state'] = 'passed' if measurement['attemptFinished'] and not measurement['errors'] else 'failed'
            save(work/'report.json', report)
            print(f"{index+1}/{len(data['results'])} {row['contract']}.{row['signature']}: {entry['state']}", flush=True)
        if subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip() != report['toolHead']:
            raise ValueError('tool checkout HEAD changed during measurement')
        for source, sha in expected.items():
            if digest(source) != sha:
                raise ValueError('source snapshot changed during suite: '+source)
        if digest(__file__) != report['driverSha256']:
            raise ValueError('measurement driver bytes changed during suite')
        if digest(args.admission) != admission_sha:
            raise ValueError('admission snapshot changed during measurement')
        if digest(repo/'scripts/test-solidity.mjs') != report['cliSha256']:
            raise ValueError('CLI bytes changed during measurement')
        if {str(p): digest(p) for p in sorted(args.soljson.resolve().glob('*.js'))} != report['compilerFiles']:
            raise ValueError('compiler bytes changed during measurement')
        report['attemptFinished'] = True
        report['allScheduledPassed'] = scheduled > 0 and not report['errors'] and all(
            r['state'] in ['passed', 'not-scheduled'] for r in report['rows'])
    except Exception as error:
        report['errors'].append({'stage': 'runner', 'reason': str(error)})
    save(work/'report.json', report)
    return 0 if report['allScheduledPassed'] else 1


if __name__ == '__main__':
    if len(sys.argv) == 3 and sys.argv[1] == '_one':
        worker(sys.argv[2])
    else:
        sys.exit(main())
