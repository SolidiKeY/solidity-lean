#!/usr/bin/env python3
"""Deterministic source census, not a Lean parser or semantic proof.

All family files are frozen by byte hashes. Declaration signature hashes are
source hashes (comments/whitespace retained), not elaborated theorem hashes.
Anonymous examples have stable file/line identities. No vector generator here.
"""
import argparse
import collections
import hashlib
import json
from pathlib import Path
import re
import subprocess

BASE = 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
ROOT = Path(__file__).resolve().parents[4]
FAMILY = 'Solidity/Backend/PrimitivePackets'
COMMAND = re.compile(r'^[ \t]*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(theorem|lemma|example|def|abbrev|opaque|structure|inductive|class|namespace|section|end)\b(?:[ \t]+([^\s:({\[]+))?', re.M)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def masked(source):
    """Preserve offsets/newlines while hiding nested comments and strings."""
    out = list(source)
    i, depth = 0, 0
    while i < len(source):
        if source.startswith('/-', i):
            depth += 1
            out[i:i+2] = '  '
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            out[i:i+2] = '  '
            i += 2
        elif depth:
            if source[i] != '\n':
                out[i] = ' '
            i += 1
        elif source.startswith('--', i):
            end = source.find('\n', i)
            end = len(source) if end < 0 else end
            out[i:end] = ' ' * (end-i)
            i = end
        elif source[i] == '"':
            out[i] = ' '
            i += 1
            while i < len(source):
                ch = source[i]
                if ch != '\n':
                    out[i] = ' '
                i += 1
                if ch == '\\' and i < len(source):
                    out[i] = ' '
                    i += 1
                elif ch == '"':
                    break
        else:
            i += 1
    if depth:
        raise ValueError('unclosed block comment')
    return ''.join(out)


def signature_end(text, start, stop):
    # Body assignments inside binder types do not end a declaration signature.
    depth = 0
    pending_let = 0
    i = start
    while i < stop:
        ch = text[i]
        if ch in '([{⟨':
            depth += 1
        elif ch in ')]}⟩':
            depth -= 1
        elif depth == 0 and re.match(r'let\b', text[i:]):
            pending_let += 1
        elif depth == 0 and text.startswith(':=', i):
            if pending_let:
                pending_let -= 1
            else:
                return i
        i += 1
    return stop


def collect(root):
    files, declarations = [], []
    for path in sorted((root/FAMILY).rglob('*.lean')):
        raw = path.read_bytes()
        source = raw.decode()
        code = masked(source)
        rel = path.relative_to(root).as_posix()
        control = path.name.endswith('Controls.lean')
        files.append(dict(path=rel, sha256=digest(raw), control=control))
        commands = list(COMMAND.finditer(code))
        scope = []
        for index, match in enumerate(commands):
            kind, name = match.group(1, 2)
            if kind in ('namespace', 'section'):
                scope.append((kind, name))
                continue
            if kind == 'end':
                if not scope:
                    raise ValueError(f'{rel}: unmatched end')
                scope.pop()
                continue
            stop = commands[index+1].start() if index+1 < len(commands) else len(source)
            line = source.count('\n', 0, match.start()) + 1
            end = signature_end(code, match.start(), stop)
            qualified = '.'.join([n for k,n in scope if k == 'namespace' and n] +
                                 [f'example@{line}' if kind == 'example' else name])
            declarations.append(dict(path=rel, line=line, name=qualified, kind=kind,
                control=control, audit_items=([9] if path.parent.name in ('CheckedAdd','CheckedSub','CheckedMul','SignedCheckedAdd','SignedCheckedSub','SignedCheckedMul') and path.stem in ('Agreement','Target','Controls') else []) + ([16] if control and kind in ('theorem','example') else []), source_signature_sha256=digest(source[match.start():end].encode()),
                source_region_sha256=digest(source[match.start():stop].encode()),
                signature=source[match.start():end].strip()))
    counts = collections.Counter(d['kind'] for d in declarations if d['control'])
    return dict(schema=1, base=BASE, hash_boundary='source bytes, not elaborated Lean expressions',
        files=files, declarations=declarations,
        summary=dict(files=len(files), control_files=sum(f['control'] for f in files),
            declarations=len(declarations), control_declarations=sum(counts.values()),
            control_kinds=dict(sorted(counts.items()))),
        audit=dict(item9='Checked{Add,Sub,Mul} and SignedChecked{Add,Sub,Mul}: Agreement/Target/Controls twins',
            item11=dict(status='candidates only; no semantic equivalence claimed', sites=[
                dict(path=FAMILY+'/UnsignedCast/Controls.lean', line=66, helper='absent: empty HRef'),
                dict(path=FAMILY+'/Comparisons/Controls.lean', line=37, helper='noRef: empty HRef'),
                dict(path=FAMILY+'/UnsignedDiv/Witness.lean', line=34, helper='hn: empty HRef'),
                dict(path=FAMILY+'/CheckedMul/Populated.lean', line=61, helper='ref_cases: populated heap, separate semantics'),
                dict(path=FAMILY+'/CheckedMul/Populated.lean', line=71, helper='heap_repr: populated heap, separate semantics')]),
            item16='Per-case Controls candidates; Yul Raw/vector generation belongs to H55 and is excluded'))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--check', type=Path)
    args = parser.parse_args()
    data = collect(ROOT)
    # Fail closed on any changed original, added original, or missing original.
    published = subprocess.check_output(['git','ls-tree','-r','--name-only',BASE,'--',FAMILY], cwd=ROOT).decode().splitlines()
    actual = [f['path'] for f in data['files']]
    if actual != sorted(p for p in published if p.endswith('.lean')):
        raise ValueError('original file inventory changed')
    for row in data['files']:
        old = subprocess.check_output(['git','show',f"{BASE}:{row['path']}"], cwd=ROOT)
        if digest(old) != row['sha256']:
            raise ValueError(f"frozen original changed: {row['path']}")
    encoded = json.dumps(data, ensure_ascii=False, sort_keys=True, indent=2) + '\n'
    if args.check:
        if args.check.read_text() != encoded:
            raise ValueError('census differs from acceptance fixture')
    if args.output:
        args.output.write_text(encoded)
    print(json.dumps(data['summary'],sort_keys=True))
    print('FROZEN_SOURCE_INVENTORY_PASS')


if __name__ == '__main__':
    main()
