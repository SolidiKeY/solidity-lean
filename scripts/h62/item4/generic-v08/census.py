#!/usr/bin/env python3
"""Deterministic lexical inventory; never edits or imports the owned family.

Headers are exact UTF-8 source slices through (excluding) the body delimiter.
This is a source-integrity census, not Lean elaboration or a semantic audit.
Anonymous examples are indexed by source order. All declarations, including
helpers outside *Controls files, are retained to make exclusions inspectable.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

BASE = 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
FAMILY = 'Solidity/Lowering/V08'
ROOT = Path(__file__).resolve().parents[4]


def digest(s):
    return hashlib.sha256(s.encode()).hexdigest()


def mask(s):
    """Mask nested comments and string contents, preserving offsets/newlines."""
    out = list(s)
    i, depth, string = 0, 0, False
    while i < len(s):
        if depth:
            if s.startswith('/-', i):
                out[i:i+2] = '  '; depth += 1; i += 2
            elif s.startswith('-/', i):
                out[i:i+2] = '  '; depth -= 1; i += 2
            else:
                if s[i] != '\n': out[i] = ' '
                i += 1
        elif string:
            if s[i] == '\\':
                out[i:i+2] = ' ' * min(2, len(s)-i); i += 2
            elif s[i] == '"':
                string = False; i += 1
            else:
                if s[i] != '\n': out[i] = ' '
                i += 1
        elif s.startswith('/-', i):
            out[i:i+2] = '  '; depth = 1; i += 2
        elif s.startswith('--', i):
            j = s.find('\n', i)
            if j < 0: j = len(s)
            out[i:j] = ' ' * (j-i); i = j
        elif s[i] == '"':
            string = True; i += 1
        else: i += 1
    if depth or string: raise ValueError('unterminated comment/string')
    return ''.join(out)


COMMAND = re.compile(r'^(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(?P<kind>theorem|lemma|def|abbrev|opaque|axiom|constant|structure|inductive|instance|example)\b', re.M)


def declarations(path, source):
    clean = mask(source)
    matches = list(COMMAND.finditer(clean))
    rows = []
    for ordinal, m in enumerate(matches, 1):
        limit = matches[ordinal].start() if ordinal < len(matches) else len(source)
        # Track nesting: ':=' inside a binder is not the declaration's body.
        depth, end, lets = 0, limit, {}
        for token in re.finditer(r':=|\blet\b|\bwhere\b|\||[(){}\[\]]', clean[m.end():limit], re.M):
            text = token.group()
            if text in ('(', '{', '['): depth += 1
            elif text in (')', '}', ']'): depth -= 1
            elif text == 'let': lets[depth] = lets.get(depth, 0) + 1
            elif text == ':=' and lets.get(depth, 0): lets[depth] -= 1
            elif text == '|' and m['kind'] not in ('def', 'abbrev', 'opaque', 'instance', 'inductive'): continue
            elif depth == 0:
                end = m.end() + token.start(); break
        if end == limit and m['kind'] not in ('axiom', 'constant'):
            raise ValueError(f'{path}:{source.count(chr(10), 0, m.start())+1}: no body delimiter')
        name = re.match(r'\s+([^\s(:{\[]+)', clean[m.end():end])
        label = name[1] if name and m['kind'] != 'example' else f'@{m["kind"]}:{ordinal}'
        header = source[m.start():end]
        rows.append(dict(path=path, line=source.count('\n',0,m.start())+1,
                         ordinal=ordinal, kind=m['kind'], name=label,
                         header=header, statement_sha256=digest(header),
                         control_file=path.endswith('Controls.lean')))
    return rows


def inventory(root, revision=None):
    if revision:
        files = subprocess.check_output(['git','ls-tree','-r','--name-only',revision,'--',FAMILY],cwd=root,text=True).splitlines()
        read = lambda p: subprocess.check_output(['git','show',f'{revision}:{p}'],cwd=root).decode()
    else:
        files = [p.relative_to(root).as_posix() for p in (root/FAMILY).rglob('*.lean')]
        read = lambda p: (root/p).read_text()
    files = sorted(p for p in files if p.endswith('.lean'))
    result = dict(schema=1, base=BASE, family=FAMILY, files=[], declarations=[])
    for p in files:
        source = read(p)
        result['files'].append(dict(path=p, sha256=digest(source)))
        result['declarations'].extend(declarations(p,source))
    return result


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument('--write',type=Path)
    parser.add_argument('--check',type=Path)
    parser.add_argument('--revision')
    args = parser.parse_args()
    data = inventory(ROOT,args.revision)
    if args.check:
        frozen = json.loads(args.check.read_text())
        if data != frozen: raise SystemExit('FAIL: family inventory or exact source hashes changed')
    if args.write:
        args.write.write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n')
    print(f'PASS: {len(data["files"])} family files; {len(data["declarations"])} declarations; '
          f'{sum(d["kind"] in ("theorem","lemma","example") for d in data["declarations"])} proof declarations; '
          f'{sum(d["control_file"] for d in data["declarations"])} declarations in Controls files')

if __name__ == '__main__': main()
