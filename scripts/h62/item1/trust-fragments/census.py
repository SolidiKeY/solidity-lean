#!/usr/bin/env python3
"""Inventory the existing frozen TrustAudit; no whole-project axiom audit."""
import hashlib
import json
import re

import accept_baseline
import collect


def census(data):
    if hashlib.sha256(data).hexdigest() != accept_baseline.SHA256:
        raise ValueError('census only supports the pinned original audit')
    text = data.decode('utf-8')
    blocks = re.split(r'(?m)^run_cmd do\n', text)[1:]
    records = []
    for number, block in enumerate(blocks):
        headlines = re.search(r'  let headlines : List Name := \[(.*?)\]', block, re.S)
        if headlines is None:
            raise ValueError(f'unrecognized audit block {number}')
        names = re.findall(r'``([^,\s\]]+)', headlines.group(1))
        records.append({'index': number, 'headlines': names})
    return {
        'base': accept_baseline.BASE,
        'source_sha256': accept_baseline.SHA256,
        'imports': re.findall(r'(?m)^import (\S+)', text),
        'audit_blocks': records,
        'print_axioms': re.findall(r'(?m)^#print axioms (\S+)', text),
    }


def main():
    print(json.dumps(census(collect.AUDIT.read_bytes()), indent=2, ensure_ascii=False))


if __name__ == '__main__':
    main()
