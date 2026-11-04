#!/usr/bin/env python3
"""Verify pinned compaction attachments as data, never as proof evidence."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import resource
import sys

SPEC = importlib.util.spec_from_file_location('v17_compact', Path(__file__).with_name('roadmap-v17-compact-json.py'))
C = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(C)
FLAGS = dict(C.FLAGS, toolExecutionAuthenticated=False)


def read_pinned(path, pin, limit):
    C.pinned_hash(pin)
    with C.regular(path) as stream:
        before = C.identity(os.fstat(stream.fileno()))
        C.require(before[2] <= limit, 'attachment byte limit exceeded')
        raw = stream.read(limit + 1)
        C.require(len(raw) <= limit and hashlib.sha256(raw).hexdigest() == pin, 'attachment SHA256 mismatch')
        C.require(C.identity(os.fstat(stream.fileno())) == before, 'attachment changed')
        C.require(C.identity(os.stat(path, follow_symlinks=False)) == before, 'attachment path changed')
        return raw


def parse(raw):
    return json.loads(raw.decode('utf-8'), object_pairs_hook=C.unique_object, parse_constant=C.forbidden_constant)


def verify(receipt, receipt_sha256, compact, syntax):
    paths = [Path(p).absolute() for p in (receipt, compact, syntax)]
    C.require([p.name for p in paths] == ['receipt.json', 'compact.json', 'syntax.unverified.json']
              and len({p.parent for p in paths}) == 1, 'unpublished or unlinked attachment paths')
    report = parse(read_pinned(receipt, receipt_sha256, 65536))
    C.require(type(report.get('schema')) is int and report['schema'] == 1, 'unsupported receipt schema')
    C.require(report.get('status') == 'data-only' and report.get('accountingOnly') is True
              and report.get('jsonSyntaxValidated') is True, 'incomplete compaction receipt')
    C.require(all(report.get(k) is False for k in FLAGS), 'receipt promotes unverified evidence')
    expected = dict(addressSpaceBytes=536870912, cpuSeconds=60, inputBytes=C.MAX_INPUT, compactBytes=C.MAX_COMPACT)
    C.require(report.get('ceilings') == expected and all(type(v) is int for v in report['ceilings'].values()),
              'changed ceilings')
    for key, ceiling in [('addressSpace', 536870912), ('cpu', 60)]:
        limits = report['observedProcessLimits'][key]
        C.require(type(limits) is list and len(limits) == 2 and all(type(n) is int and 0 < n <= ceiling for n in limits)
                  and limits[0] <= limits[1], 'unsupported reported limits')
    meta = report['bytes']
    for key, bound in [('inputBytes', C.MAX_INPUT), ('compactBytes', C.MAX_COMPACT), ('syntaxBytes', 2*C.MAX_COMPACT+1)]:
        C.require(type(meta[key]) is int and 0 <= meta[key] <= bound, 'invalid byte count')
    C.require(0 < meta['compactBytes'] <= meta['syntaxBytes'] <= meta['inputBytes']
              and meta['syntaxBytes'] <= 2*meta['compactBytes']+1, 'impossible compaction byte counts')
    C.require(meta['inputSha256'] == report['input']['expectedSha256'], 'contradictory original input pin')
    C.pinned_hash(meta['inputSha256'])
    raw = read_pinned(compact, meta['compactSha256'], C.MAX_COMPACT)
    separated = read_pinned(syntax, meta['syntaxSha256'], 2*C.MAX_COMPACT+1)
    C.require(len(raw) == meta['compactBytes'] and len(separated) == meta['syntaxBytes'], 'attachment size mismatch')
    # Validate original-token separators before comparing exact compact bytes.
    parse(separated)
    parse(raw)
    import io
    out = io.BytesIO()
    C.compact(io.BytesIO(separated), out, meta['syntaxSha256'])
    C.require(out.getvalue() == raw, 'syntax/compact byte disagreement')
    return dict(schema=1, status='data-only', accountingOnly=True, attachmentsConsistent=True,
                receiptSha256=receipt_sha256, compactSha256=meta['compactSha256'],
                originalInputSha256=meta['inputSha256'], originalInputRechecked=False,
                boundary='Pinned attachments only; original execution, revision, imports and proof claims remain unauthenticated.',
                **FLAGS)


def main():
    for key, cap in [(resource.RLIMIT_AS, 536870912), (resource.RLIMIT_CPU, 60)]:
        limits = [n for n in (*resource.getrlimit(key), cap) if n != resource.RLIM_INFINITY]
        resource.setrlimit(key, (min(limits), min(limits)))
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('receipt', 'receipt-sha256', 'compact', 'syntax'):
        parser.add_argument('--' + name, required=True)
    args = parser.parse_args()
    try:
        print(json.dumps(verify(args.receipt, args.receipt_sha256, args.compact, args.syntax), sort_keys=True))
        return 0
    except Exception as error:
        print(json.dumps(dict(status='error', error=type(error).__name__ + ': ' + str(error), **FLAGS)))
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
