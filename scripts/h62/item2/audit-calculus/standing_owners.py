#!/usr/bin/env python3
"""Regression guard: migration scopes and missing live scope inputs cannot transfer semantic ownership.

Apply only Q-SEM-OWNER-02's Calculus standing rule to the authenticated H82b
snapshot. Matching a scope leaves ownership unresolved; it does not identify a
semantic producer. Roles, joint witnesses and proof acceptance are independent.
"""
import fnmatch
import hashlib
import json
from pathlib import Path
from census import expand

SUMS_SHA = "ce406a8143f535f3ad79f501072f685a3a23dd5b21447eefe0e03f480931f5d3"
MANIFEST_SHA = "39fb14a45e1e34042b75922e8d60da77f4b6a3555bcae718a8f95e4c37d3055b"
FIELDS = ('exclusive_files', 'new_file_scope', 'write_scope_candidates', 'production_scopes')

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def parse_scope(value):
    namespace = value.get('write_namespace')
    if namespace not in ('live', 'migration-overlay/v4.35'):
        raise ValueError('unknown scope namespace')
    if set(value) - set(FIELDS) - {'write_namespace', 'scope_rule'}:
        raise ValueError('unknown scope field could conceal ownership')
    entries = []
    for field in FIELDS:
        paths = value.get(field, [])
        if not isinstance(paths, list) or any(not isinstance(p, str) for p in paths):
            raise ValueError('invalid scope path list')
        for path in paths:
            if not path or path.startswith('/') or '..' in Path(path).parts:
                raise ValueError('unsafe scope path')
            entries.extend(expand(path))
    return {'namespace': namespace, 'entries': entries}

def load_scopes(root):
    if sha(root/'SHA256SUMS') != SUMS_SHA or sha(root/'manifest.json') != MANIFEST_SHA:
        raise ValueError('unauthenticated H82b index')
    expected = {}
    for line in (root/'SHA256SUMS').read_text().splitlines():
        digest, rel = line.split('  ', 1)
        if rel.startswith('assignments/') and rel.endswith('/scope.json'):
            if rel in expected:
                raise ValueError('duplicate scope index')
            expected[rel] = digest
    actual = {str(p.relative_to(root)) for p in (root/'assignments').glob('*/scope.json')}
    if len(expected) != 25 or set(expected) != actual:
        raise ValueError('incomplete H82b scope roster')
    result = []
    for rel, digest in sorted(expected.items()):
        path = root/rel
        if sha(path) != digest:
            raise ValueError('changed scope manifest')
        result.append(dict(parse_scope(json.loads(path.read_text())), path=rel, sha256=digest))
    return result

def matches(file, pattern):
    # Conservatively include candidate/new-file patterns too. Overlap does not
    # justify master ownership, even if that entry alone grants no live write.
    return fnmatch.fnmatchcase(file, pattern) or (
        not pattern.endswith('.lean') and file.startswith(pattern.rstrip('/')+'/'))

def match_live_scopes(file, scopes):
    """Pure overlap query; an empty result alone does NOT authenticate ownership."""
    if not scopes or any(s.get('namespace') not in ('live', 'migration-overlay/v4.35') for s in scopes):
        raise ValueError('missing or unknown scope namespace')
    if not file.startswith('Solidity/Calculus/') or not file.endswith('.lean') or '..' in Path(file).parts:
        raise ValueError('standing rule applies only to Calculus Lean files')
    return [s['path'] for s in scopes if s['namespace']=='live' and any(matches(file,p) for p in s['entries'])]

def classify_files(files, root):
    # Ownership decisions always authenticate the COMPLETE snapshot themselves;
    # callers cannot supply a nonempty but truncated scope list.
    if not isinstance(root, Path):
        raise ValueError('authenticated package path required')
    scopes = load_scopes(root)
    decisions = []
    for file in sorted(set(files)):
        hits = match_live_scopes(file, scopes)
        decisions.append({'file':file, 'matching_live_scopes':hits,
                          'status':'unresolved' if hits else 'master (coordinator), no live producer'})
    return decisions
