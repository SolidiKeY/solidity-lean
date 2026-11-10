#!/usr/bin/env python3
"""Summarize partial benchmark receipts; never certify a complete U01 baseline.

Read-only inputs; JSON is written only to stdout. Timer scopes stay separate.
"""
import argparse
import collections
import hashlib
import json
import math
import pathlib

ATTEMPTED = {'proved', 'refuted', 'pending', 'error'}

def read(path):
    data = pathlib.Path(path).read_bytes()
    return json.loads(data), hashlib.sha256(data).hexdigest()

def identity(row):
    return (str(pathlib.Path(row['source']).resolve()), row['sourceHash'],
            row['contract'], row.get('sourceId', row.get('signature')))

def number(value):
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(value) and value >= 0

def stats(values):
    values = sorted(values)
    return None if not values else {'count': len(values),
        'p50': values[math.ceil(.5*len(values))-1],
        'p95': values[math.ceil(.95*len(values))-1], 'max': values[-1]}

def correlation(points):
    pairs = [(p['statements'], p['wallMs']) for p in points
             if number(p.get('statements')) and number(p.get('wallMs'))]
    if len(pairs) < 3:
        return {'count': len(pairs), 'pearsonR': None}
    xs, ys = zip(*pairs)
    mx, my = sum(xs)/len(xs), sum(ys)/len(ys)
    xx = sum((x-mx)**2 for x in xs)
    yy = sum((y-my)**2 for y in ys)
    xy = sum((x-mx)*(y-my) for x,y in pairs)
    return {'count': len(pairs), 'pearsonR': xy/math.sqrt(xx*yy) if xx and yy else None}

def unique_map(rows):
    result = {}
    for row in rows:
        key = identity(row)
        if key in result:
            raise ValueError('ambiguous static-size identity: '+str(key))
        result[key] = row.get('staticSize')
    return result

def provenance(report):
    errors = report.get('errors', [])
    invalid = [e for e in errors if e.get('stage') != 'lean']
    return {'errors': errors, 'statisticsAllowed': not invalid,
        'status': 'unavailable: report provenance/setup errors' if invalid else
            ('provisional: incomplete run; end checks not complete' if not report['attemptFinished'] else
             'runner completed; execution failures retained')}

def summarize(processes, batch=None, batch_sizes=None):
    summary = {'kind': 'u01-partial-observations', 'sourceToVerdictBaseline': False,
        'suiteComplete': False, 'percentiles': 'nearest rank ceil(p*n); failures retained; groups overlap and are not pooled',
        'groups': [], 'top10IsolatedFunctions': [], 'batchChecks': None,
        'unknown': ['disjoint phases', 'dynamic walk steps', 'aggregate per-function tree peak RSS'],
        'budgets': 'unapproved proposals; no complete-U01 or full-gate acceptance credit'}
    unique = {}
    for group, report_path, sizes_path in processes:
        report, report_sha = read(report_path)
        sizes, sizes_sha = read(sizes_path)
        size_map = unique_map(sizes['results'])
        size_provenance = {'errors': sizes.get('errors', []), 'statisticsAllowed': not sizes.get('errors', []), 'attemptFinished': sizes.get('attemptFinished')}
        if not size_provenance['statisticsAllowed']:
            size_map = {}
        validity = provenance(report)
        keys = [identity(r['input']) for r in report['rows']]
        if len(set(keys)) != len(keys):
            raise ValueError('duplicate process inventory identity')
        points = []
        for row in report['rows']:
            if not validity['statisticsAllowed'] or row['state'] not in ['passed', 'failed']:
                continue
            attempts = row['attempts']
            wall = sum(a['wallMs'] for a in attempts) if attempts and all(number(a.get('wallMs')) for a in attempts) else None
            rss = max(a['maxIndividualProcessRssKiB'] for a in attempts) if attempts and all(number(a.get('maxIndividualProcessRssKiB')) for a in attempts) else None
            size = size_map.get(identity(row['input'])) or {}
            point = {'source': row['input']['source'], 'contract': row['input']['contract'],
                'function': row['input'].get('signature'), 'state': row['state'],
                'wallMs': wall, 'maxIndividualProcessRssKiB': rss,
                'statements': size.get('statements'), 'phases': None, 'walkSteps': None}
            points.append(point)
            previous = unique.get(identity(row['input']))
            if wall is not None and (previous is None or wall > previous['wallMs']):
                unique[identity(row['input'])] = dict(point, group=group)
        summary['groups'].append({'group': group, 'toolHead': report.get('toolHead'),
            'driverSha256': report.get('driverSha256'), 'attemptFinished': report['attemptFinished'],
            'states': dict(collections.Counter(r['state'] for r in report['rows'])),
            'provenance': validity, 'metric': 'per-function CLI wall total including retries; one point per completed inventory row',
            'wallMsAllCompletedFunctionTotals': stats([p['wallMs'] for p in points if p['wallMs'] is not None]),
            'wallMsPassedFunctionTotals': stats([p['wallMs'] for p in points if p['wallMs'] is not None and p['state']=='passed']),
            'wallMsFailedFunctionTotals': stats([p['wallMs'] for p in points if p['wallMs'] is not None and p['state']=='failed']),
            'maxIndividualProcessRssKiB': stats([p['maxIndividualProcessRssKiB'] for p in points if p['maxIndividualProcessRssKiB'] is not None]),
            'costVsStaticStatements': dict(correlation(points), interpretation='descriptive only; no linear-scaling claim; failed attempts included', points=points),
            'report': report_path, 'reportSha256': report_sha, 'sizesSha256': sizes_sha, 'sizesProvenance': size_provenance})
    summary['top10IsolatedFunctions'] = sorted(unique.values(), key=lambda r:r['wallMs'], reverse=True)[:10]
    summary['worstFunctionPolicy'] = 'maximum observed total CLI-attempt wall per exact identity across overlapping groups; inclusive of retries/failures'
    if batch:
        report, sha = read(batch)
        sizes, size_sha = read(batch_sizes) if batch_sizes else ({'results': []}, None)
        size_map = unique_map(sizes['results'])
        size_provenance = {'errors': sizes.get('errors', []), 'statisticsAllowed': not sizes.get('errors', []), 'attemptFinished': sizes.get('attemptFinished')}
        if not size_provenance['statisticsAllowed']:
            size_map = {}
        validity = provenance(report)
        counts = collections.Counter(identity(r['input']) for r in report['rows'])
        timed = []
        for row in report['rows']:
            observations = row['observations']
            value = row.get('functionReportedElapsedMs')
            if (
                not validity['statisticsAllowed']
                or counts[identity(row['input'])] != 1
                or len(observations) != 1
                or identity(observations[0]) != identity(row['input'])
                or type(observations[0].get('elapsedMs')) is not int
                or value != observations[0].get('elapsedMs')
                or observations[0].get('status') not in ATTEMPTED
                or observations[0].get('verification') not in [None, 'certified']
                or not isinstance(value, int)
                or isinstance(value, bool)
                or not 0 <= value <= 9007199254740991
            ):
                continue
            timed.append({'source': row['input']['source'], 'contract': row['input']['contract'],
                'function': row['input'].get('signature'), 'checkElapsedMs': value,
                'status': observations[0]['status'], 'staticSize': size_map.get(identity(row['input'])), 'phases': None})
        summary['batchChecks'] = {'toolHead': report.get('toolHead'), 'attemptFinished': report['attemptFinished'],
            'provenance': validity, 'duplicateInventoryKeys': sum(v>1 for v in counts.values()),
            'inventory': len(report['rows']), 'observed': sum(bool(r['observations']) for r in report['rows']),
            'rawStatuses': dict(collections.Counter(o['status'] for r in report['rows'] for o in r['observations'])),
            'missingReadyRows': report.get('missingReadyRows'), 'timerScope': report['timerScope'],
            'reportedCheckElapsedMs': stats([r['checkElapsedMs'] for r in timed]),
            'apiWallMs': report['apiWallMs'], 'perFunctionSourceToVerdictWallMs': None,
            'perFunctionRss': None, 'top10ReportedChecks': sorted(timed,key=lambda r:r['checkElapsedMs'],reverse=True)[:10],
            'report': batch, 'reportSha256': sha, 'sizesSha256': size_sha, 'sizesProvenance': size_provenance,
            'projection': report.get('projection')}
    return summary

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--process', nargs=3, action='append', default=[], metavar=('GROUP','REPORT','SIZES'))
    parser.add_argument('--batch')
    parser.add_argument('--batch-sizes')
    args = parser.parse_args()
    if not args.process and not args.batch:
        parser.error('at least one partial report is required')
    print(json.dumps(summarize(args.process,args.batch,args.batch_sizes),indent=2,allow_nan=False))
