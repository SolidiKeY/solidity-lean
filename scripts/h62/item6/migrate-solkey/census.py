#!/usr/bin/env python3
"""Deterministic source census; source hashes are stricter than interface hashes.

This is a lexical audit, not Lean elaboration or an axiom audit. Full-source
hashes freeze command-generated declarations and guards without guessing names.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path


def sha(data):
    return hashlib.sha256(data).hexdigest()


def uncomment(text):
    # Preserve newlines/strings and nested Lean comments for command locations.
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        pair = text[i:i+2]
        if depth:
            if pair == '/-':
                depth += 1; out.extend('  '); i += 2; continue
            if pair == '-/':
                depth -= 1; out.extend('  '); i += 2; continue
            out.append('\n' if text[i] == '\n' else ' '); i += 1; continue
        if not string and pair == '--':
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            out.extend(' ' * (end-i)); i = end; continue
        if not string and pair == '/-':
            depth = 1; out.extend('  '); i += 2; continue
        if string and text[i] == '\\' and i+1 < len(text):
            out.extend(text[i:i+2]); i += 2; continue
        if text[i] == '"': string = not string
        out.append(text[i]); i += 1
    if depth or string: raise ValueError('unterminated comment/string')
    return ''.join(out)


def census(root):
    files = sorted((root/'Solidity/Solkey').glob('*.lean'))
    result, closure = [], {}
    def imports(path):
        return [name for m in re.finditer(r'^(?:(?:public|private|meta)[ \t]+)*import[ \t]+([^\n]+)', uncomment(path.read_text()), re.M) for name in m[1].split() if name != 'all']
    def visit(mod):
        if mod in closure: return
        path = root / (mod.replace('.', '/') + '.lean')
        closure[mod] = None
        if path.exists():
            deps = imports(path)
            closure[mod] = {'source': str(path.relative_to(root)), 'sha256': sha(path.read_bytes()), 'imports': deps}
            for dep in deps: visit(dep)
    for path in files:
        text = uncomment(path.read_text())
        deps = imports(path)
        commands = [{'line': text[:m.start()].count('\n')+1, 'text': m.group(0).strip()}
                    for m in re.finditer(r'^(?:(?:private|protected|noncomputable)\s+)*(?:def|abbrev|theorem|instance|structure|inductive|opaque|axiom)\b[^\n]*|^[ \t]*(?:#[\w?]+|solc_import|solc_scoped_problems|set_option)\b[^\n]*', text, re.M)]
        fixtures = []
        for match in re.finditer(r'solc_import\s+"([^"]+)"\s+hash\s+(0x[0-9a-f]+)\s+as\s+([\w.]+)', text):
            target = (path.parent / match[1]).resolve()
            fixtures.append({'source': str(target.relative_to(root)), 'namespace': match[3], 'literal': match[2], 'sha256': sha(target.read_bytes())})
        result.append({'source': str(path.relative_to(root)), 'source_sha256': sha(path.read_bytes()), 'imports': deps, 'commands': commands, 'fixtures': fixtures})
        for dep in deps: visit(dep)
    return {'format': 1, 'boundary': 'lexical source/fixture audit; not elaborated declaration/type hashes', 'modules': result, 'external_dependency_closure': dict(sorted(closure.items()))}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[4])
    parser.add_argument('--compare', type=Path)
    args = parser.parse_args()
    data = census(args.root.resolve())
    if args.compare:
        if json.loads(args.compare.read_text()) != data: raise SystemExit('CENSUS_CHANGED')
        print('CENSUS_UNCHANGED: all source, fixture, command and dependency hashes match')
    else: print(json.dumps(data, indent=2, sort_keys=True))

if __name__ == '__main__': main()
