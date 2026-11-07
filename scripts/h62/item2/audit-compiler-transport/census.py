#!/usr/bin/env python3
"""Frozen source census. Lexical evidence only; never reports a witness as proved.

Generated bulk stays outside Git. Source spans plus file hashes preserve exact
signatures and their implicit-variable context. Lean reflection is a separate gate.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

BASE = 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
MAP = 'docs/module-map/compiler-transport.md'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def mask(text):
    """Preserve offsets/newlines while masking nested comments and string bodies."""
    out = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            n = 2 if text[i:i+2] in ('/-', '-/') else 1
            if text[i:i+2] == '/-': depth += 1
            elif text[i:i+2] == '-/': depth -= 1
        elif string:
            n = 2 if text[i] == '\\' else 1
            if text[i] == '"': string = False
        elif text[i:i+2] == '/-':
            depth, n = 1, 2
        elif text[i:i+2] == '--':
            end = text.find('\n', i)
            n = (end if end >= 0 else len(text)) - i
        elif text[i] == '"':
            string, n = True, 1
        else:
            i += 1
            continue
        for j in range(i, min(i+n, len(text))):
            if out[j] != '\n': out[j] = ' '
        i += n
    if depth or string:
        raise ValueError('unterminated comment or string')
    return ''.join(out)


def signature_end(clean, start):
    depth = 0
    type_matches = []
    i = start
    while i < len(clean):
        c = clean[i]
        if c in '({[': depth += 1
        elif c in ')}]': depth -= 1
        if depth == 0 and clean[i:i+2] == ':=': return i
        # At depth zero, offside match arms can still belong to the result
        # type. An equation body starts only after leaving those matches.
        line_start = clean.rfind('\n', 0, i) + 1
        if depth == 0 and clean[i:i+5] == 'match' and (i == 0 or not (clean[i-1].isalnum() or clean[i-1] in "_.'")) and (i+5 == len(clean) or not (clean[i+5].isalnum() or clean[i+5] == '_')):
            line = clean[line_start:i]
            type_matches.append(len(line)-len(line.lstrip()))
        if depth == 0 and c == '|' and not clean[line_start:i].strip():
            indent = i-line_start
            while type_matches and indent < type_matches[-1]:
                type_matches.pop()
            if not type_matches: return i
        i += 1
    raise ValueError('missing top-level :=')


def declarations(source, module):
    clean = mask(source)
    command = re.compile(r'(?m)^\s*(?:@\[[^\n]*?\]\s*)*(?:(private|protected)\s+)?(namespace|section|mutual|end|theorem)\b(?:[ \t]+([^\s(:{]+))?')
    scopes, rows = [], []
    for match in command.finditer(clean):
        visibility, kind, name = match.groups()
        if kind in ('namespace', 'section', 'mutual'):
            scopes.append((kind, name or ''))
        elif kind == 'end':
            if not scopes: raise ValueError(f'{module}: unpaired end at {match.start()}')
            scopes.pop()
        else:
            if not name: raise ValueError('unnamed theorem')
            begin = clean.index('theorem', match.start(), match.end())
            end = signature_end(clean, match.end())
            namespace = '.'.join(n for k, n in scopes if k == 'namespace')
            fq = (name[len('_root_.'):] if name.startswith('_root_.') else
                  f'{namespace}.{name}' if namespace else name)
            raw = source[begin:end].rstrip()
            conclusion_false = bool(re.search(r':\s*False\s*$', clean[begin:end]))
            owner_key = ('V12' if '/InternalFlow/' in module else
                         'VO1' if module.startswith('Solidity/Optimizer/') else 'V09')
            rows.append({
                'id': f'{module}::{fq}', 'source_name': fq,
                'visibility': visibility or 'public',
                'kernel_name': None,  # Private names require Lean's private-name mapping.
                'module': module, 'line': source[:begin].count('\n') + 1,
                'signature_span': [begin, end], 'signature': raw,
                'signature_sha256': digest(raw.encode()),
                'context_span': [0, begin],
                'context_note': 'Exact source prefix preserves open/variable/include/omit/section context; elaborated type pending.',
                'owner_key': owner_key,
                'owner': {'V09': 'v07-v11/v09-compiler-passes', 'V12': 'v12-v17/v12-flow-calls', 'VO1': 'solidity-fullscope-20261104/vo1-optimizer'}[owner_key],
                'owner_basis': ('compiler-transport module-map V12 rows' if owner_key == 'V12' else
                                'ownership snapshot item VO1, writeScope Solidity/Optimizer/**' if owner_key == 'VO1' else
                                'G24-G31 ownership snapshot; P12 dependencies additionally V07'),
                'global_premises': 'unclassified; structure inhabitation does not prove this input feasible',
                'input_feasibility': 'joint hypotheses not yet witnessed',
                'witness_status': 'impossible-as-requested' if conclusion_false else 'uncovered',
                'false_conclusion': conclusion_false,
                'elaborated_census_status': 'pending',
            })
    if scopes: raise ValueError(f'{module}: unclosed scopes {scopes}')
    return rows


def generate(root):
    map_bytes = (root / MAP).read_bytes()
    frozen_map = subprocess.check_output(['git', 'show', f'{BASE}:{MAP}'], cwd=root)
    if frozen_map != map_bytes: raise ValueError('frozen module-map modified')
    modules = re.findall(r'(?m)^\| `([^`]+\.lean)` \|', map_bytes.decode())
    if len(modules) != len(set(modules)): raise ValueError('duplicate module-map row')
    records, files = [], []
    for relative in modules:
        path = 'Solidity/' + relative
        content = (root / path).read_bytes()
        frozen = subprocess.check_output(['git', 'show', f'{BASE}:{path}'], cwd=root)
        if frozen != content: raise ValueError(f'frozen interface modified: {path}')
        rows = declarations(content.decode(), path)
        files.append({'module': path, 'sha256': digest(content), 'theorems': len(rows)})
        records.extend(rows)
    ids = [x['id'] for x in records]
    if len(ids) != len(set(ids)): raise ValueError('duplicate theorem identity')
    return {'schema': 1, 'base': BASE, 'module_map': MAP,
            'map_sha256': digest(map_bytes), 'modules': files, 'statements': records,
            'summary': {'modules': len(files), 'theorems': len(records),
                        'public': sum(r['visibility'] != 'private' for r in records),
                        'private': sum(r['visibility'] == 'private' for r in records),
                        'joint_witnesses_verified': 0,
                        'false_conclusions': sum(r['false_conclusion'] for r in records)},
            'limitation': 'Source census, not elaborated Lean census. No premise, global structure, or per-input witness is certified by scanning.'}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', type=Path, default=Path.cwd())
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    result = generate(args.root.resolve())
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps(result['summary'], sort_keys=True))

if __name__ == '__main__': main()
