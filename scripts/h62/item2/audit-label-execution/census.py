#!/usr/bin/env python3
"""Frozen source census, not a substitute for elaborated premise/witness checking.

Output is off git. Every named theorem/lemma is retained, including controls,
private helpers and statements that may have no Prop premises. Classification
requires a Lean environment; this scanner deliberately does not guess it.
"""
import argparse
import fnmatch
import hashlib
import json
from pathlib import Path
import re
import subprocess

BASE = 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
MAP = 'docs/module-map/label-execution.md'

def digest(data):
    return hashlib.sha256(data).hexdigest()

def mask(text):
    """Blank nested comments and string literals without changing offsets."""
    out = list(text)
    i = 0
    depth = 0
    string = False
    line = False
    while i < len(text):
        pair = text[i:i+2]
        if line:
            if text[i] == '\n': line = False
            else: out[i] = ' '
        elif depth:
            if pair == '/-':
                out[i:i+2] = '  '; depth += 1; i += 1
            elif pair == '-/':
                out[i:i+2] = '  '; depth -= 1; i += 1
            elif text[i] != '\n': out[i] = ' '
        elif string:
            if text[i] == '\\' and i+1 < len(text):
                out[i:i+2] = '  '; i += 1
            elif text[i] == '"': out[i] = ' '; string = False
            elif text[i] != '\n': out[i] = ' '
        elif pair in ('/-', '--'):
            out[i:i+2] = '  '
            depth = int(pair == '/-'); line = pair == '--'; i += 1
        elif text[i] == '"': out[i] = ' '; string = True
        i += 1
    if depth or string: raise ValueError('unterminated comment/string')
    return ''.join(out)

def expand_braces(s):
    m = re.search(r'\{([^{}]*)\}', s)
    if not m: return [s]
    return [v for choice in m[1].split(',')
            for v in expand_braces(s[:m.start()] + choice + s[m.end():])]

def frozen_bytes(root, path):
    data = subprocess.check_output(['git','show',f'{BASE}:{path}'],cwd=root)
    if (root/path).read_bytes() != data:
        raise ValueError(f'frozen source differs from worktree: {path}')
    return data

def modules(root):
    text = frozen_bytes(root, MAP).decode()
    pattern = r'(?:Bridge/SolidityBridge|Frontend/Yul|Backend|Lowering|Yul|HashBridge|ExternalEvm)/[A-Za-z0-9_/{},.]*[A-Za-z0-9_}]'
    paths = set()
    for m in re.finditer(pattern, text):
        for name in expand_braces(m[0]):
            if not name.endswith('.lean'): name += '.lean'
            if name.startswith(('HashBridge/', 'ExternalEvm/')):
                name = 'Bridge/SolidityBridge/' + name
            elif not name.startswith('Bridge/'):
                name = 'Solidity/' + name
            paths.add(name)
    missing = [p for p in sorted(paths) if not (root / p).is_file()]
    if missing: raise ValueError('unresolved map paths: ' + ', '.join(missing))
    return sorted(paths)

DECL = re.compile(r'(?m)^[ \t]*(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma)\s+([^\s({\[:]+)')
SCOPE = re.compile(r'(?m)^(namespace|section|end)\b[^\n]*')

def declarations(text, path):
    clean = mask(text)
    scopes = []
    events = sorted([(m.start(), 'scope', m) for m in SCOPE.finditer(clean)] +
                    [(m.start(), 'decl', m) for m in DECL.finditer(clean)])
    rows = []
    for pos, kind, m in events:
        if kind == 'scope':
            words = m[0].split()
            if words[0] == 'end':
                if scopes: scopes.pop()
            else: scopes.append((words[0], words[1] if len(words)>1 else ''))
            continue
        start = m.start()
        # Defaults inside binders contain :=; only depth-zero := ends a signature.
        depth = 0
        pending_lets = 0
        end = None
        for i in range(m.end(), len(clean)):
            c = clean[i]
            if c in '({[': depth += 1
            elif c in ')}]': depth -= 1
            if depth == 0 and clean[i:i+3] == 'let' and (i == 0 or not (clean[i-1].isalnum() or clean[i-1] == '_')) and (i+3 == len(clean) or not (clean[i+3].isalnum() or clean[i+3] == '_')):
                pending_lets += 1
            if depth == 0 and clean[i:i+2] == ':=':
                if pending_lets: pending_lets -= 1
                else:
                    end = i; break
        if end is None: raise ValueError(f'{path}:{m[2]}: unsupported theorem syntax')
        ns = '.'.join(n for k,n in scopes if k == 'namespace')
        name = m[2]
        full = name[len('_root_.'):] if name.startswith('_root_.') else '.'.join(filter(None,[ns,name]))
        raw = text[start:end].strip()
        rows.append(dict(name=full, source_name=name, path=path,
                         line=text.count('\n',0,start)+1,
                         signature=raw, signature_sha256=digest(raw.encode()),
                         visibility='private' if re.search(r'\bprivate\b', clean[start:m.end()]) else 'public',
                         context_sha256=digest(text[:start].encode()),
                         preceding_variable_commands=[v[0] for v in re.finditer(r'(?m)^variable\b[^\n]*(?:\n[ \t]+[^\n]*)*', text[:start])],
                         premise_classification='pending-elaborated-type',
                         simultaneous_witness='pending', statement_fidelity='pending'))
    return rows

def owners(path, registry):
    matches = []
    for item in registry['items']:
        if item.get('group') != 'h30-file-ownership': continue
        for glob in item.get('writeScope','').split(';'):
            if fnmatch.fnmatchcase(path, glob.strip()):
                matches.append(dict(owner=item.get('owner'), reservation=item['id'], pattern=glob.strip()))
    return matches

def run(root, registry):
    files = []
    rows = []
    for path in modules(root):
        data = frozen_bytes(root,path)
        ds = declarations(data.decode(),path)
        own = owners(path,registry)
        for row in ds: row['owner_evidence'] = own
        files.append(dict(path=path, sha256=digest(data), declarations=len(ds), owner_evidence=own))
        rows.extend(ds)
    keys = [(r['path'],r['name']) for r in rows]
    if len(keys) != len(set(keys)): raise ValueError('duplicate declaration identity')
    return dict(schema=1, base=BASE, map=MAP, map_sha256=digest(frozen_bytes(root,MAP)),
                source_fidelity='all mapped worktree bytes equal pinned git blobs',
                limitations=['Source signatures retain defaults and full-prefix hashes; elaboration must recover section/implicit binders.',
                             'All named source theorems are candidates; no theorem is excluded by a textual hypothesis heuristic.',
                             'Owner reservations are evidence from the supplied snapshot; absent/overlapping claims require coordinator resolution.'],
                files=files, declarations=rows,
                counts=dict(files=len(files), declarations=len(rows), witnessed=0,
                            uncovered=len(rows), owner_unresolved=sum(len(r['owner_evidence']) != 1 for r in rows)))

if __name__ == '__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[4])
    p.add_argument('--ownership',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args()
    result=run(args.root,json.loads(args.ownership.read_text()))
    args.output.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps(result['counts'],sort_keys=True))
