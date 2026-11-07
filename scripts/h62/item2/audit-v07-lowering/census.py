#!/usr/bin/env python3
"""Conservative source census, not an elaborated Lean statement certificate.

Records every theorem/lemma token outside comments/strings in the mapped files.
All candidates remain pending: source extraction cannot infer elaborator-added
parameters or certify simultaneous feasibility. Full source hashes freeze context.
"""
import argparse
import hashlib
import json
import pathlib
import re


def masked(source):
    """Erase nested comments and strings while preserving offsets/newlines."""
    out = list(source)
    i = 0
    depth = 0
    string = False
    while i < len(source):
        c = source[i]
        if depth:
            if source.startswith('/-', i):
                out[i:i+2] = '  '
                depth += 1
                i += 2
                continue
            if source.startswith('-/', i):
                out[i:i+2] = '  '
                depth -= 1
                i += 2
                continue
            if c != '\n':
                out[i] = ' '
        elif string:
            if c == '\\' and i+1 < len(source):
                out[i] = ' '
                if source[i+1] != '\n':
                    out[i+1] = ' '
                i += 2
                continue
            if c == '"':
                string = False
            if c != '\n':
                out[i] = ' '
        elif source.startswith('--', i):
            end = source.find('\n', i)
            end = len(source) if end < 0 else end
            out[i:end] = ' ' * (end-i)
            i = end
            continue
        elif source.startswith('/-', i):
            depth = 1
            out[i:i+2] = '  '
            i += 2
            continue
        elif c == '"':
            string = True
            out[i] = ' '
        i += 1
    if depth or string:
        raise ValueError('unterminated comment/string')
    return ''.join(out)


def census(repo):
    map_path = repo / 'docs/module-map/v07-lowering.md'
    map_text = map_path.read_text()
    names = sorted(set(re.findall(r'`(Lowering/V07/[A-Za-z0-9_/]+)(?:\.lean)?`', map_text)))
    # Extension-less map rows name Lean modules too.
    records = []
    modules = []
    for name in names:
        path = pathlib.Path('Solidity') / (name + '.lean')
        raw = (repo / path).read_bytes()
        source = raw.decode()
        code = masked(source)
        found = []
        for match in re.finditer(r'\b(theorem|lemma)\s+([^\s({\[:]+)', code):
            # Retain the full original declaration tail rather than guess where
            # a dependent binder's := or a tactic quotation ends a signature.
            # A future elaborated census must certify statement boundaries.
            start = match.start()
            found.append({'local_name': match[2], 'kind': match[1],
                          'line': source.count('\n', 0, start)+1,
                          'offset': start,
                          'source_tail_sha256': hashlib.sha256(source[start:].encode()).hexdigest(),
                          'statement_fidelity': 'pending-elaboration',
                          'simultaneous_witness': 'pending',
                          'premise_classification': 'pending',
                          'owner': 'V07 (v07-v11/v07-lowering)'})
        modules.append({'path': str(path), 'sha256': hashlib.sha256(raw).hexdigest(),
                        'candidate_count': len(found)})
        records.extend(dict(item, path=str(path)) for item in found)
    keys = [(x['path'], x['offset']) for x in records]
    assert len(keys) == len(set(keys))
    return {'schema': 1, 'scope': 'docs/module-map/v07-lowering.md',
            'map_sha256': hashlib.sha256(map_text.encode()).hexdigest(),
            'boundary': 'Lexical candidates only; no witness or statement-fidelity claim.',
            'module_count': len(modules), 'candidate_count': len(records),
            'modules': modules, 'candidates': records}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=pathlib.Path, default=pathlib.Path.cwd())
    parser.add_argument('--output', required=True, type=pathlib.Path)
    args = parser.parse_args()
    result = census(args.repo)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(f"{result['module_count']} modules; {result['candidate_count']} lexical candidates; all pending")
