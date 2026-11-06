#!/usr/bin/env python3
"""Conservative source census: all theorem/lemma declarations, including private helpers.

Exact source signatures and file hashes are authoritative; lexical detection is
not a Lean elaboration or a proof of satisfiable premises. Keep every candidate
until a kernel-checked witness and review have classified it.
"""
import argparse
import hashlib
import json
import pathlib
import re
import subprocess

BASE = 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
ROOT = pathlib.Path(__file__).resolve().parents[4]
MAP = ROOT / 'docs/module-map/precompiles.md'


def mask(source):
    """Keep positions/newlines; hide nested comments and string contents."""
    out = list(source)
    i = depth = 0
    string = False
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                out[i:i+2] = '  '; depth += 1; i += 2; continue
            if source.startswith('-/', i):
                out[i:i+2] = '  '; depth -= 1; i += 2; continue
            if source[i] != '\n': out[i] = ' '
            i += 1; continue
        if string:
            if source[i] == '\\' and i + 1 < len(source):
                out[i:i+2] = '  '; i += 2; continue
            if source[i] == '"': string = False
            if source[i] != '\n': out[i] = ' '
            i += 1; continue
        if source.startswith('--', i):
            j = source.find('\n', i)
            if j < 0: j = len(source)
            out[i:j] = ' ' * (j-i); i = j; continue
        if source.startswith('/-', i):
            depth = 1; out[i:i+2] = '  '; i += 2; continue
        if source[i] == '"': string = True; out[i] = ' '
        i += 1
    if depth or string: raise ValueError('unclosed comment/string')
    return ''.join(out)


def declarations(source):
    clean = mask(source)
    frames = []
    events = re.compile(r'(?m)^[ \t]*(?:(private|protected)[ \t]+)?(namespace|section|mutual|end|theorem|lemma)\b[ \t]*([^\s(:{\[]*)')
    for event in events.finditer(clean):
        visibility, kind, name = event.groups()
        if kind in ('namespace', 'section', 'mutual'):
            frames.append((kind, name)); continue
        if kind == 'end':
            if frames: frames.pop()
            continue
        start = event.start()
        while start < len(clean) and clean[start].isspace(): start += 1
        cursor = event.end()
        depth = 0
        let_assignments = 0
        while cursor < len(clean):
            if depth == 0 and re.match(r'let\b', clean[cursor:]) and (cursor == 0 or not (clean[cursor-1].isalnum() or clean[cursor-1] == '_')):
                let_assignments += 1
            if depth == 0 and clean.startswith(':=', cursor):
                if let_assignments:
                    let_assignments -= 1
                    cursor += 2
                    continue
                break
            if depth == 0 and re.match(r'where\b', clean[cursor:]) and (cursor == 0 or not (clean[cursor-1].isalnum() or clean[cursor-1] == '_')):
                break
            if clean[cursor] in '([{': depth += 1
            if clean[cursor] in ')]}': depth -= 1
            cursor += 1
        if cursor == len(clean): raise ValueError('missing proof delimiter: ' + name)
        signature = source[start:cursor].rstrip()
        namespace = '.'.join(n for k,n in frames if k == 'namespace')
        yield dict(name=(namespace + '.' if namespace else '') + name,
                   visibility=visibility or 'public', constant_name_status=('private-mangled-name-pending' if visibility == 'private' else 'source-qualified-name'), line=source.count('\n',0,start)+1,
                   signature=signature,
                   preceding_variable_commands=re.findall(r'(?m)^[ \t]*variable[^\n]*', clean[:start]),
                   context_prefix_sha256=hashlib.sha256(source[:start].encode()).hexdigest(),
                   signature_sha256=hashlib.sha256(signature.encode()).hexdigest(),
                   # Explicit proof binders and implicit/section parameters must be
                   # distinguished by Lean elaboration, never guessed away here.
                   status='pending-elaboration-and-simultaneous-witness')


def census():
    map_raw = MAP.read_bytes()
    frozen_map = subprocess.run(['git', 'show', BASE + ':docs/module-map/precompiles.md'], cwd=ROOT, check=True, capture_output=True).stdout
    if map_raw != frozen_map: raise ValueError('frozen module map changed')
    paths = re.findall(r'^\| `([^`]+\.lean)`', map_raw.decode(), re.M)
    result = []
    for short in paths:
        path = short if short.startswith('Bridge/') else 'Solidity/' + short
        raw = (ROOT/path).read_bytes()
        frozen = subprocess.run(['git', 'show', BASE + ':' + path], cwd=ROOT, check=True, capture_output=True).stdout
        if raw != frozen: raise ValueError('frozen source changed: ' + path)
        source = raw.decode()
        owner = ('solidity-sol-20261103/precompile-agreement' if path.startswith('Bridge/')
                 else 'master (area producer lane-precompiles; Stipend adequacy G43: V14)')
        result.append(dict(path=path, owner=owner,
                           source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                           declarations=list(declarations(source))))
    names = [d['name'] for f in result for d in f['declarations']]
    if len(names) != len(set(names)): raise ValueError('duplicate declaration name')
    return dict(base=BASE, module_map_sha256=hashlib.sha256(MAP.read_bytes()).hexdigest(),
                scope_files=len(paths), declarations=len(names),
                boundary='Source census only. Every candidate retained; no witness or fidelity gate claimed.',
                files=result)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output', type=pathlib.Path)
    parser.add_argument('--check', type=pathlib.Path)
    args=parser.parse_args()
    value=census()
    rendered=json.dumps(value,indent=2,ensure_ascii=False)+'\n'
    if args.check and args.check.read_text()!=rendered:
        raise SystemExit('FAIL: frozen source census differs')
    if args.output: args.output.write_text(rendered)
    print(f"SOURCE_CENSUS files={value['scope_files']} declarations={value['declarations']} (witnesses pending)")

if __name__=='__main__': main()
