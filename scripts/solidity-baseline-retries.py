#!/usr/bin/env python3
"""Select uncheckpointed followers for one isolated replay; never retry in a loop."""
import argparse
import hashlib
import json
import re
from pathlib import Path
import subprocess
import time


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def observations_preserved(before, after):
    variants = {v['pipeline']: v for v in after.get('variants', [])}
    for old in before.get('variants', []):
        prefix = old.get('observed', [])
        current = variants.get(old['pipeline'], {}).get('observed', [])
        if current[:len(prefix)] != prefix:
            return False
    return True


def select(report, snapshot):
    rows = {row['path']: row for row in report['results']}
    if len(rows) != len(report['results']):
        raise ValueError('duplicate fixture paths')
    for row in rows.values():
        modes = [v['pipeline'] for v in row.get('variants', [])]
        if len(modes) != len(set(modes)):
            raise ValueError('duplicate pipeline modes')
        if any(p not in modes for p in row.get('requiredPipelines', [])):
            raise ValueError('missing completed/blocked required pipeline')
    jobs = [(row, pipeline) for entry in snapshot['files']
            if (row := rows.get(entry['path']))
            for pipeline in row.get('requiredPipelines', [])]
    batches = []
    selected = set()
    size = report['metadata']['batchSize']
    for start in range(0, len(jobs), size):
        failed = []
        for row, pipeline in jobs[start:start + size]:
            variant = next(v for v in row['variants'] if v['pipeline'] == pipeline)
            if variant.get('tool'):
                failed.append((row['path'], pipeline, variant['tool']))
        if not failed:
            continue
        first = failed[0][0]
        followers = sorted({path for path, _, _ in failed if path != first})
        selected.update(followers)
        batches.append({'firstJobIndex': start, 'firstUncheckpointedFixture': first,
                        'failedModes': failed, 'followerCandidates': followers})
    selected.difference_update(batch['firstUncheckpointedFixture'] for batch in batches)
    return {'metadata': report['metadata'], 'queuedModeJobs': len(jobs), 'batches': batches,
            'fixtures': sorted(selected),
            'policy': 'One replay per uncheckpointed follower candidate, both required modes; the first fixture is not retried and its unfinished modes retain blocked verdicts. First is not a proven root cause. No limit is raised and no resource retry loop is used.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='mode', required=True)
    pick = sub.add_parser('select')
    pick.add_argument('results', type=Path)
    pick.add_argument('--fresh-run',action='store_true',required=True,help='Source bulk command did not use --resume')
    pick.add_argument('--out', type=Path, required=True)
    pick.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    replay = sub.add_parser('run')
    replay.add_argument('selection', type=Path)
    replay.add_argument('--compiler', required=True)
    replay.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    if args.mode == 'select':
        summary_path = args.results/'summary.json'
        report_path = args.results/'results.json'
        snapshot_path = args.root/'tests/upstream/snapshot.json'
        summary = json.loads(summary_path.read_text())
        if not summary['complete']:
            raise ValueError('bulk report is incomplete; preserve it rather than selecting retries')
        report = json.loads(report_path.read_text())
        snapshot = json.loads(snapshot_path.read_text())
        if report['metadata'].get('filter') is not None:
            raise ValueError('requires fresh unfiltered bulk run, never --resume')
        if any(summary.get(k) != v for k,v in report['metadata'].items()):
            raise ValueError('bulk metadata disagreement')
        if report['metadata']['archiveSha256'] != snapshot['archiveSha256']:
            raise ValueError('archive identity differs')
        expected = {f['path'] for f in snapshot['files'] if re.search(r'\.(sol|yul|json|stack|ssa|asm|asmjson)$',f['path'])}
        if {r['path'] for r in report['results']} != expected or summary['totalFixtureFiles'] != len(expected):
            raise ValueError('not a whole-snapshot bulk report')
        result = select(report, snapshot)
        result['freshRunRequired'] = True
        result['freshRunAttested'] = args.fresh_run
        result['provenance'] = {name: {'path': str(path.resolve()), 'sha256': digest(path)}
                                for name,path in [('report',report_path),('summary',summary_path),('snapshot',snapshot_path),('selector',Path(__file__))]}
        if args.out.exists():
            raise ValueError('refusing to overwrite selection evidence')
        args.out.write_text(json.dumps(result, indent=2)+'\n')
        print(len(result['fixtures']), 'isolated follower candidates')
        return
    selection = json.loads(args.selection.read_text())
    for source in selection['provenance'].values():
        if digest(source['path']) != source['sha256']:
            raise ValueError('selection source changed: '+source['path'])
    bulk = json.loads(Path(selection['provenance']['report']['path']).read_text())
    before = {row['path']:row for row in bulk['results']}
    args.out.mkdir(parents=True, exist_ok=False)
    records = []
    for fixture in selection['fixtures']:
        destination = args.out/hashlib.sha256(fixture.encode()).hexdigest()[:20]
        command = ['node', 'scripts/solidity-upstream.mjs', 'run', '--compiler', args.compiler,
                   '--filter', fixture, '--batch-size', '1', '--timeout-ms',
                   str(selection['metadata']['timeoutMs']), '--out', str(destination)]
        start = time.monotonic()
        with destination.with_suffix('.log').open('w') as log:
            completed = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT)
        report_file = destination/'results.json'
        retry = json.loads(report_file.read_text()) if report_file.exists() else {}
        after = retry.get('results', [])
        failures = []
        retry_summary = destination/'summary.json'
        if completed.returncode not in (0,1) or not retry_summary.exists() or not json.loads(retry_summary.read_text()).get('complete'):
            failures.append('retry invocation did not complete')
        if len(after)==1:
            modes = [v['pipeline'] for v in after[0].get('variants', [])]
            if len(modes)!=len(set(modes)) or set(modes)!=set(before[fixture]['requiredPipelines']):
                failures.append('retry modes incomplete or duplicated')
        if any(retry.get('metadata',{}).get(k) != v for k,v in selection['metadata'].items() if k not in ('filter','batchSize')):
            failures.append('retry provenance differs')
        if len(after)!=1 or after[0]['path']!=fixture:
            failures.append('retry fixture identity differs')
        elif after[0].get('stage')!='lean-runtime' or after[0].get('requiredPipelines')!=before[fixture]['requiredPipelines']:
            failures.append('retry execution stage or required modes differ')
        elif not observations_preserved(before[fixture],after[0]):
            failures.append('original observation prefix would change or shrink')
        eligible = not failures
        records.append({'mergeEligible':eligible,'mergeGuardFailures':failures,'reportSha256':digest(report_file) if report_file.exists() else None,'fixture': fixture, 'command': command, 'exitCode': completed.returncode,
                        'elapsedSeconds': time.monotonic()-start})
        (args.out/'runs.json').write_text(json.dumps(records, indent=2)+'\n')
        print(f"Isolated {len(records)}/{len(selection['fixtures'])}: {fixture}: exit {completed.returncode}", flush=True)
        if completed.returncode not in (0, 1):
            raise SystemExit(completed.returncode)


if __name__ == '__main__':
    main()
