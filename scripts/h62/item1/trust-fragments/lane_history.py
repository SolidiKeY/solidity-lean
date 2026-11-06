#!/usr/bin/env python3
"""Compare current lane inputs with an explicitly selected committed snapshot.

This protects supplied prior entries from deletion or reassignment. The caller
must select the coordinator-approved prior commit; this script cannot decide
which commit or owner claims are authoritative.
"""
import json
import pathlib
import re
import subprocess

import collect

PREFIX = 'tests/h62/item1/trust-fragments/lanes/'
OWNER = r'[a-z0-9]+(?:-[a-z0-9]+)*'
FILE = OWNER + r'\.json'


def add(inventory, owner, data):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f'duplicate JSON key: {key}')
            result[key] = value
        return result
    payload = json.loads(data, object_pairs_hook=unique)
    if not isinstance(payload, dict) or set(payload) != {'imports', 'headlines'}:
        raise ValueError('invalid committed lane schema')
    if any(not isinstance(payload[key], list) or any(not isinstance(x, str) for x in payload[key])
           for key in ('imports', 'headlines')) or not payload['headlines']:
        raise ValueError('invalid committed lane entries')
    atom = r"[A-Za-z_][A-Za-z0-9_']*[?!]?"
    name_pattern = re.compile(r'Solidity(?:\.' + atom + r')+')
    if any(not name_pattern.fullmatch(name) for key in ('imports', 'headlines') for name in payload[key]):
        raise ValueError('invalid committed lane name')
    row = inventory.setdefault(owner, {'imports': set(), 'headlines': set()})
    row['imports'].update(payload['imports'])
    for name in payload['headlines']:
        if any(name in item['headlines'] for item in inventory.values()):
            raise ValueError(f'duplicate committed headline: {name}')
        row['headlines'].add(name)


def read_commit(commit):
    if not re.fullmatch(r'[0-9a-f]{40}', commit):
        raise ValueError('prior commit must be a full lowercase 40-character SHA')
    if subprocess.check_output(['git', 'cat-file', '-t', commit], cwd=collect.ROOT).strip() != b'commit':
        raise ValueError('prior object must be a commit')
    ancestry = subprocess.run(['git', 'merge-base', '--is-ancestor', commit, 'HEAD'],
                              cwd=collect.ROOT, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    if ancestry.returncode != 0:
        raise ValueError('prior commit must be an ancestor of HEAD')
    data = subprocess.check_output(['git', 'ls-tree', '-r', '-z', commit, '--', PREFIX], cwd=collect.ROOT)
    inventory = {}
    for entry in filter(None, data.split(b'\0')):
        metadata, raw_path = entry.split(b'\t', 1)
        mode, kind, oid = metadata.split(b' ')
        path = raw_path.decode('utf-8')
        match = re.fullmatch(re.escape(PREFIX) + f'({OWNER})/({FILE})', path)
        if mode not in (b'100644', b'100755') or kind != b'blob' or not match:
            raise ValueError(f'invalid committed lane entry: {path}')
        content = subprocess.check_output(['git', 'cat-file', 'blob', oid.decode('ascii')], cwd=collect.ROOT)
        add(inventory, match.group(1), content.decode('utf-8'))
    return inventory


def read_current(lane_root):
    inventory = {}
    if lane_root.exists():
        for lane in sorted(lane_root.iterdir(), key=lambda p: p.name):
            for path in sorted(lane.iterdir(), key=lambda p: p.name):
                add(inventory, lane.name, path.read_text(encoding='utf-8'))
    return inventory


def preserve(prior, current):
    for owner, fields in prior.items():
        for key in ('imports', 'headlines'):
            missing = fields[key] - current.get(owner, {}).get(key, set())
            if missing:
                raise ValueError(f'previously committed {key} removed or reassigned from {owner}: {sorted(missing)}')
