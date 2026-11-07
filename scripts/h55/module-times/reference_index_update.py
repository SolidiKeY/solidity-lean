#!/usr/bin/env python3
"""Guard regression: old references silently cover changed standalone source bytes."""
import hashlib
import copy
import json
from pathlib import Path
import re
import sys
import rebase_reference_index


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


MAPPING_FIELDS = ('category', 'context', 'module', 'resolution', 'collision')


def update(drift, artifacts):
    if not isinstance(drift, dict) or not isinstance(drift.get('rows'), list):
        raise ValueError('invalid drift snapshot')
    if drift.get('removed_from_candidate_set') or any('historical_references_require_review' in entry for entry in drift['rows']):
        raise ValueError('extended drift requires version-preserving mode')
    rows = {}
    for entry in drift['rows']:
        candidate = entry['candidate']
        path, sha, state = candidate['path'], candidate['sha256'], entry['state']
        refs = entry['prior_reference_artifacts']
        if (not isinstance(path, str) or not path or path in rows or not isinstance(sha, str)
                or not re.fullmatch(r'[0-9a-f]{64}', sha) or any(f not in candidate for f in MAPPING_FIELDS)
                or not isinstance(candidate['collision'], bool) or not isinstance(refs, list)
                or any(not isinstance(x, str) or not x for x in refs) or len(set(refs)) != len(refs)):
            raise ValueError('invalid drift row')
        if state not in ('new-candidate','changed-candidate-review','referenced-static-only','no-supplied-per-path-reference'):
            raise ValueError('invalid drift state')
        if state in ('new-candidate','no-supplied-per-path-reference') and refs:
            raise ValueError('unexpected prior reference')
        if state == 'referenced-static-only' and not refs:
            raise ValueError('missing prior reference')
        rows[path] = {'candidate': candidate, 'prior_state': state,
                      'current_static_references': list(refs) if state == 'referenced-static-only' else [],
                      'historical_references_require_review': list(refs) if state == 'changed-candidate-review' else []}
    for label, doc in artifacts:
        if not isinstance(doc, dict) or not isinstance(doc.get('rows'), list):
            raise ValueError('invalid classification artifact')
        seen = set()
        for entry in doc['rows']:
            row = entry['candidate']
            path = row['path']
            if (path in seen or path not in rows or row.get('sha256') != rows[path]['candidate']['sha256']
                    or any(f not in row or row[f] != rows[path]['candidate'][f] for f in MAPPING_FIELDS)):
                raise ValueError('duplicate, unknown or stale classification')
            seen.add(path)
            if label in rows[path]['current_static_references']:
                raise ValueError('duplicate classification label')
            rows[path]['current_static_references'].append(label)
    return [{'candidate': r['candidate'], 'prior_state': r['prior_state'],
             'current_static_references': sorted(r['current_static_references']),
             'historical_references_require_review': sorted(r['historical_references_require_review']),
             'status': 'referenced-static-only' if r['current_static_references'] else 'no-supplied-current-reference'}
            for _, r in sorted(rows.items())]


def update_extended(index, drift, artifacts, versions, lineage):
    rows, removed = rebase_reference_index.rebase(index, drift)
    rows, removed = copy.deepcopy(rows), copy.deepcopy(removed)
    lookup = {r['candidate']['path']: r for r in rows}
    for row in rows + removed:
        for record in row.get('historical_reference_records', []):
            existing = record.get('artifact_versions')
            if existing is not None:
                if (not isinstance(existing, list) or len(existing) != len(record['artifact_paths'])
                        or any(not isinstance(v, dict) or v.get('path') != path
                               or not isinstance(v.get('sha256'), str)
                               or not re.fullmatch(r'[0-9a-f]{64}', v['sha256'])
                               for v, path in zip(existing, record['artifact_paths']))):
                    raise ValueError('invalid preserved artifact versions')
            else:
                try:
                    record['artifact_versions'] = [{'path':path, 'sha256':versions[path]} for path in record['artifact_paths']]
                    if any(lineage.get(v['path']) != v['sha256'] for v in record['artifact_versions']):
                        raise ValueError('historical artifact version is not bound by index lineage')
                except KeyError as exc:
                    raise ValueError('missing version for historical artifact') from exc
    for row in rows + removed:
        bound = {path for record in row.get('historical_reference_records', []) for path in record['artifact_paths']}
        row['unbound_historical_reference_artifacts'] = sorted(set(row['historical_references_require_review']) - bound)
    for tombstone in removed:
        old_versions = tombstone.get('tombstone_reference_versions')
        if old_versions is None:
            try:
                old_versions = [{'path':path, 'sha256':versions[path]} for path in tombstone['current_static_references']]
            except KeyError as exc:
                raise ValueError('missing version for removed artifact') from exc
            if any(lineage.get(v['path']) != v['sha256'] for v in old_versions):
                raise ValueError('removed artifact version is not bound by index lineage')
            tombstone['tombstone_reference_versions'] = old_versions
        elif (not isinstance(old_versions, list) or len(old_versions) != len(tombstone['current_static_references'])
                or any(not isinstance(v, dict) or v.get('path') != path or not isinstance(v.get('sha256'), str)
                       or not re.fullmatch(r'[0-9a-f]{64}', v['sha256'])
                       for v, path in zip(old_versions, tombstone['current_static_references']))):
            raise ValueError('invalid preserved tombstone versions')
    for label, doc in artifacts:
        if not isinstance(doc, dict) or not isinstance(doc.get('rows'), list):
            raise ValueError('invalid classification artifact')
        seen = set()
        for entry in doc['rows']:
            row = entry['candidate']; path = row['path']
            if (path in seen or path not in lookup or row.get('sha256') != lookup[path]['candidate']['sha256']
                    or any(f not in row or row[f] != lookup[path]['candidate'][f] for f in MAPPING_FIELDS)):
                raise ValueError('duplicate, unknown or stale classification')
            seen.add(path)
            if label in lookup[path]['current_static_references']:
                raise ValueError('duplicate classification label')
            lookup[path]['current_static_references'].append(label)
    for row in rows:
        row['current_static_references'].sort()
        row['status'] = 'referenced-static-only' if row['current_static_references'] else 'no-supplied-current-reference'
    return rows, removed


def lineage_versions(index):
    result, visited = {}, set()
    def visit(doc):
        inputs = doc.get('inputs', [])
        if not isinstance(inputs, list):
            raise ValueError('invalid index lineage')
        for item in inputs:
            path, sha = item['path'], item['sha256']
            if (not isinstance(path, str) or not Path(path).is_absolute() or str(Path(path)) != path
                    or '..' in Path(path).parts or not isinstance(sha, str) or not re.fullmatch(r'[0-9a-f]{64}', sha)):
                raise ValueError('invalid lineage entry')
            if path in result and result[path] != sha:
                raise ValueError('conflicting artifact versions in lineage')
            result[path] = sha
            if (path, sha) in visited:
                continue
            visited.add((path, sha))
            artifact = Path(path)
            if artifact.is_symlink() or not artifact.is_file():
                raise ValueError('missing lineage artifact')
            raw = artifact.read_bytes()
            if digest(raw) != sha:
                raise ValueError('lineage artifact hash mismatch')
            try:
                child = json.loads(raw)
            except (ValueError, UnicodeError):
                continue
            if isinstance(child, dict) and 'inputs' in child:
                visit(child)
    visit(index)
    return result


def parse_versions(raw):
    versions = {}
    for line in raw.decode('utf-8').splitlines():
        match = re.fullmatch(r'([0-9a-f]{64})  (/.+)', line)
        if not match or match[2] in versions:
            raise ValueError('invalid or duplicate version manifest entry')
        path = Path(match[2])
        if str(path) != match[2] or '..' in path.parts or path.is_symlink() or not path.is_file():
            raise ValueError('invalid version artifact path')
        if digest(path.read_bytes()) != match[1]:
            raise ValueError('version artifact hash mismatch')
        versions[match[2]] = match[1]
    return versions


def main():
    if len(sys.argv) < 4:
        print('usage: reference_index_update.py DRIFT.json INDEX.json DELTA_OR_VERSIONS [CLASSIFICATION.json...]', file=sys.stderr)
        return 2
    try:
        files = [Path(x) for x in sys.argv[1:]]
        if len({str(p.resolve()) for p in files}) != len(files):
            raise ValueError('duplicate input artifact')
        raws = [p.read_bytes() for p in files]
        docs = [json.loads(raws[0]), json.loads(raws[1]), None] + [json.loads(raw) for raw in raws[3:]]
        if docs[0]['input_sha256'] != digest(raws[1]):
            raise ValueError('drift coverage digest mismatch')
        baseline_rows = docs[1].get('rows')
        if not isinstance(baseline_rows, list) or not baseline_rows:
            raise ValueError('cannot infer schema from empty baseline')
        extended = 'current_static_references' in baseline_rows[0]
        if extended:
            versions = parse_versions(raws[2])
            for artifact in docs[3:]:
                if artifact.get('input_sha256') not in {digest(raws[0]), digest(raws[1])}:
                    raise ValueError('classification input digest is not supplied')
            lineage = lineage_versions(docs[1])
            rows, removed = update_extended(docs[1], docs[0], [(str(p.resolve()), d) for p, d in zip(files[3:], docs[3:])], versions, lineage)
        else:
            if digest(raws[2]) not in {item['sha256'] for item in docs[1]['inputs']}:
                raise ValueError('coverage delta digest mismatch')
            for artifact in docs[3:]:
                if artifact.get('input_sha256') not in {digest(raws[0]), digest(raws[1]), digest(raws[2])}:
                    raise ValueError('classification input digest is not supplied')
            rows = update(docs[0], [(str(p.resolve()), d) for p, d in zip(files[3:], docs[3:])])
            removed = []
        referenced = sum(bool(r['current_static_references']) for r in rows)
        print(json.dumps({'status':'static-reference-index-not-execution-acceptance', 'snapshot_head':docs[0]['head'],
            'limitations':'supplied snapshot and artifacts only; references do not resolve execution; ignored/generated inputs, later changes and runtime are not covered',
            'inputs':[{'path':str(p.resolve()), 'sha256':digest(raw)} for p, raw in zip(files, raws)],
            'total':len(rows), 'referenced':referenced, 'unreferenced':len(rows)-referenced,
            'historical_reference_review':sum(bool(r['historical_references_require_review']) for r in rows),
            'overlap':sum(len(r['current_static_references'])>1 for r in rows), 'removed_from_candidate_set':removed, 'rows':rows}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        print(f'reference index update unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
