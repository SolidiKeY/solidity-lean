#!/usr/bin/env python3
"""Guard false missing-.sol evidence caused by the frozen corpus suffix filter.

This separate, read-only check uses the entire pinned Git tree. It does not change
item2.py or its frozen contract, infer feature support, or follow evidence links.
"""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
PINNED_BASE = '6f3eedf0788ee1f8a3bcf230558c712ecdca04d5'
PINNED_TREE = '114f3a4e901fc282cec56d9e210fcffb2776e0cd'
MANIFEST = 'docs/solidity-features.json'
FROZEN_ACCEPTANCE = ROOT / 'tests/h28-terra/drift-reports/accept.py'
FROZEN_SHA256 = '01a6a0a842966fa758441e3e70af53799a8d657a181540341a7bcbe759071e64'
FROZEN_SUFFIXES = ('.lean', '.md', '.json', '.sh', '.py', '.mjs')
SELECTED = ('partial', 'missing', 'unsupported')
MODES = {'100644': ('blob', 'regular'), '100755': ('blob', 'regular'),
         '120000': ('blob', 'symlink'), '160000': ('commit', 'gitlink')}


def path_name(value):
    if (not isinstance(value, str) or not value or value.startswith('/')
            or '\0' in value or any(p in ('', '.', '..') for p in value.split('/'))):
        raise ValueError('evidence must name a canonical repository-relative Git path')
    return value


def inventory(raw):
    entries = {}
    if raw and not raw.endswith(b'\0'):
        raise ValueError('truncated Git path inventory')
    for record in raw.split(b'\0')[:-1]:
        header, name = record.split(b'\t', 1)
        mode, kind, oid = header.decode('ascii').split()
        path = path_name(name.decode('utf-8', errors='surrogateescape'))
        if (mode not in MODES or kind != MODES[mode][0]
                or not re.fullmatch(r'[0-9a-f]{40}', oid)):
            raise ValueError('unsupported Git inventory entry')
        if path in entries:
            raise ValueError('duplicate path in Git inventory')
        entries[path] = {'mode': mode, 'kind': MODES[mode][1], 'object': oid}
    return entries


def unique_keys(pairs):
    obj = {}
    for key, value in pairs:
        if key in obj:
            raise ValueError('duplicate manifest JSON key')
        obj[key] = value
    return obj


def reject_constant(value):
    raise ValueError('nonfinite JSON constant is not supported')


def finite_float(value):
    number = float(value)
    if not math.isfinite(number):
        raise ValueError('nonfinite JSON number is not supported')
    return number


def analyze(manifest, entries):
    if not isinstance(manifest, dict) or not isinstance(manifest.get('features'), list):
        raise ValueError('manifest must contain a features array')
    rows = []; seen = set()
    counts = dict(features=len(manifest['features']), qualifyingFeatures=0,
                  evidenceOccurrences=0, existingOccurrences=0, missingOccurrences=0,
                  nonRegularOccurrences=0, frozenOmittedExistingOccurrences=0,
                  frozenAffectedFeatures=0)
    for feature in manifest['features']:
        if (not isinstance(feature, dict) or not isinstance(feature.get('id'), str)
                or not feature['id'] or feature['id'] in seen
                or not isinstance(feature.get('current'), str)):
            raise ValueError('malformed or duplicate feature identity/status')
        seen.add(feature['id'])
        refs = feature.get('localEvidence', [])
        if not isinstance(refs, list):
            raise ValueError('localEvidence must be an array')
        for path in refs:
            path_name(path)
        if feature['current'] not in SELECTED:
            continue
        evidence = []
        missing = []; nonregular = []; omitted = []
        for index, path in enumerate(refs):
            entry = entries.get(path)
            excluded = entry is not None and not path.endswith(FROZEN_SUFFIXES)
            evidence.append(dict(index=index, path=path, tracked=entry is not None,
                                 entry=entry, omittedByFrozenSelection=excluded))
            if entry is None:
                missing.append(path)
            elif entry['kind'] != 'regular':
                nonregular.append(path)
            if excluded:
                omitted.append(path)
        counts['qualifyingFeatures'] += 1
        counts['evidenceOccurrences'] += len(refs)
        counts['existingOccurrences'] += len(refs) - len(missing)
        counts['missingOccurrences'] += len(missing)
        counts['nonRegularOccurrences'] += len(nonregular)
        counts['frozenOmittedExistingOccurrences'] += len(omitted)
        counts['frozenAffectedFeatures'] += bool(omitted)
        rows.append(dict(id=feature['id'], status=feature['current'], scope=feature.get('scope'),
                         evidence=evidence, missingEvidence=sorted(missing),
                         nonRegularEvidence=sorted(nonregular),
                         frozenOmittedExistingEvidence=sorted(omitted),
                         verdict='owner-review-required-no-status-rewrite'))
    return dict(counts=counts, features=rows)


def collect(repo, base):
    if not re.fullmatch(r'[0-9a-f]{40}', base):
        raise ValueError('--base must be a full commit SHA, not a movable reference')
    frozen = FROZEN_ACCEPTANCE.read_bytes()
    if hashlib.sha256(frozen).hexdigest() != FROZEN_SHA256:
        raise ValueError('frozen acceptance changed; explicit selection-policy review required')
    env = {k: v for k, v in os.environ.items() if not k.startswith('GIT_')}
    env.update(GIT_NO_REPLACE_OBJECTS='1', GIT_OPTIONAL_LOCKS='0',
               GIT_NO_LAZY_FETCH='1', GIT_TERMINAL_PROMPT='0')
    def git(*args):
        return subprocess.check_output(['git', '--no-replace-objects', '-C', str(repo), *args],
                                       env=env, stderr=subprocess.PIPE)
    if git('cat-file', '-t', base).strip() != b'commit':
        raise ValueError('--base must identify a commit object')
    tree = git('rev-parse', base + '^{tree}').decode().strip()
    if base == PINNED_BASE and tree != PINNED_TREE:
        raise ValueError('original pinned tree mismatch')
    raw = git('ls-tree', '-rz', '--full-tree', base)
    entries = inventory(raw)
    manifest_entry = entries.get(MANIFEST)
    if not manifest_entry or manifest_entry['kind'] != 'regular':
        raise ValueError('feature manifest must be a regular tracked blob')
    manifest_bytes = git('cat-file', 'blob', manifest_entry['object'])
    manifest = json.loads(manifest_bytes, object_pairs_hook=unique_keys,
                          parse_constant=reject_constant, parse_float=finite_float)
    report = analyze(manifest, entries)
    report.update(schema=1, check='full-pinned-path-evidence-completeness',
                  source=dict(commit=base, tree=tree, originalPinnedBase=base == PINNED_BASE,
                              trackedEntries=len(entries), inventorySha256=hashlib.sha256(raw).hexdigest(),
                              manifestPath=MANIFEST, manifestObject=manifest_entry['object'],
                              manifestSha256=hashlib.sha256(manifest_bytes).hexdigest(),
                              frozenAcceptanceSha256=FROZEN_SHA256,
                              frozenSuffixSelection=list(FROZEN_SUFFIXES)),
                  boundary='Pinned Git entry membership only; no declaration, feature-support, routing or runtime acceptance.')
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=ROOT)
    parser.add_argument('--base', default=PINNED_BASE)
    args = parser.parse_args()
    try:
        report = collect(args.repo, args.base)
        output = json.dumps(report, sort_keys=True, ensure_ascii=True, indent=2, allow_nan=False)
    except (OSError, ValueError, UnicodeError, RecursionError, subprocess.CalledProcessError) as exc:
        print(json.dumps({'error': str(exc), 'check': 'full-pinned-path-evidence-completeness'}),
              file=sys.stderr)
        return 2
    print(output)
    return int(bool(report['counts']['missingOccurrences'] or report['counts']['nonRegularOccurrences']))


if __name__ == '__main__':
    sys.exit(main())
