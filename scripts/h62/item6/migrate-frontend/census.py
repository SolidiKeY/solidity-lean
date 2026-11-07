#!/usr/bin/env python3
"""Deterministic source census, not an elaborated Lean API/axiom checker."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

BASE = 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
OWNER = 'H62-6-MIGRATE-FRONTEND'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def mask(text):
    """Blank comments and strings; preserve offsets/newlines, nested comments."""
    out = list(text)
    i = 0
    depth = 0
    string = False
    while i < len(text):
        if depth:
            n = 2 if text[i:i+2] in ('/-', '-/') else 1
            if text[i:i+2] == '/-': depth += 1
            elif text[i:i+2] == '-/': depth -= 1
        elif string:
            n = 2 if text[i] == '\\' and i + 1 < len(text) else 1
            if text[i] == '"': string = False
        elif text[i] == "'" and (i == 0 or not (text[i-1].isalnum() or text[i-1] in "_'")) and (char := re.match(r"'(?:[^'\\\n]|\\.)'", text[i:])):
            n = len(char[0])
        elif text[i:i+2] == '--':
            end = text.find('\n', i)
            n = (len(text) if end < 0 else end) - i
        elif text[i:i+2] == '/-':
            depth = 1
            n = 2
        elif text[i] == '"':
            string = True
            n = 1
        else:
            i += 1
            continue
        for j in range(i, min(i+n, len(text))):
            if text[j] != '\n': out[j] = ' '
        i += n
    return ''.join(out)

def imports(text):
    code = mask(text)
    # Lean import commands precede declarations. Reject unrecognized header text.
    result = []
    for line in code.splitlines():
        line = line.strip()
        if not line or line == 'prelude': continue
        if not re.match(r'import\s+', line): break
        names = line.split()[1:]
        if names and names[0] == 'all': names = names[1:]
        if not names or any(not re.fullmatch(r'[\w\u0080-\uffff]+(?:\.[\w\u0080-\uffff]+)*', n) for n in names):
            raise ValueError('Unsupported import syntax: ' + line)
        result.extend(names)
    return result

def module(path):
    return str(path.with_suffix('')).replace('/', '.')

def census(root, ownership):
    source_files = sorted(p for p in root.glob('Solidity/Frontend/**/*') if p.is_file())
    owned = next(v for v in ownership['items'] if v['id'] == OWNER)
    assigned = sorted(p.strip() for p in owned['writeScope'].split(';') if p.strip().startswith('Solidity/Frontend/'))
    actual = sorted(str(p.relative_to(root)) for p in source_files)
    if actual != assigned:
        raise ValueError({'unassigned': sorted(set(actual)-set(assigned)), 'missing': sorted(set(assigned)-set(actual))})
    allpaths = sorted(root.glob('Solidity/**/*.lean')) + sorted(root.glob('*.lean'))
    modules = {module(p.relative_to(root)): p for p in allpaths}
    deps = {m: imports(p.read_text()) for m, p in modules.items()}
    ordered = []
    visiting, seen = set(), set()
    def visit(m):
        if m in seen or m not in modules: return
        if m in visiting: raise ValueError('Import cycle: '+m)
        visiting.add(m)
        for d in deps[m]: visit(d)
        visiting.remove(m)
        seen.add(m)
        ordered.append(m)
    frontend = sorted(module(Path(p)) for p in assigned if p.endswith('.lean'))
    for m in frontend: visit(m)
    rows = []
    candidates = []
    options = []
    decl = re.compile(r'^\s*(?:(?:private|protected|noncomputable|unsafe|partial|opaque|nonrec)\s+)*(def|theorem|lemma|structure|inductive|abbrev|class|instance|example|axiom)\b\s*([^\s(:{\[]*)')
    for rel in assigned:
        p = root / rel
        raw = p.read_bytes()
        row = {'path': rel, 'sha256': sha(raw), 'bytes': len(raw)}
        if p.suffix == '.lean':
            code = mask(raw.decode())
            row['module'] = module(Path(rel))
            row['imports'] = deps[row['module']]
            for n, line in enumerate(code.splitlines(), 1):
                match = decl.match(line)
                if match:
                    candidates.append({'path': rel, 'line': n, 'kind': match[1], 'unqualified_candidate': match[2]})
                if re.search(r'\bset_option\s+', line):
                    options.append({'path': rel, 'line': n, 'text': line.strip()})
        rows.append(row)
    boundary = [{'from': m, 'to': d, 'local': d in modules} for m in frontend for d in deps[m] if not d.startswith('Solidity.Frontend.')]
    return {'schema': 1, 'base': BASE, 'scope_files': rows, 'frontend_modules': frontend,
            'topological_closure': ordered, 'closure_imports': {m: deps[m] for m in ordered},
            'closure_sources': [{'path': str(modules[m].relative_to(root)), 'sha256': sha(modules[m].read_bytes())} for m in ordered],
            'external_local_modules': sorted(seen-set(frontend)),
            'cross_directory_imports': boundary, 'declaration_candidates': candidates, 'proof_options': options,
            'limits': 'Whole-source SHA256 pins are exact. Declaration rows are lexical candidates only; not qualified/elaborated API, complete command inventory, axiom audit, or proof of compatibility.'}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', type=Path, default=Path.cwd())
    ap.add_argument('--inputs', type=Path, default=Path('/workspace/h62-coordinator-inputs'))
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    root = args.root.resolve()
    subprocess.run(['git', 'merge-base', '--is-ancestor', BASE, 'HEAD'], cwd=root, check=True)
    checks = json.loads((args.inputs/'sha256.json').read_text())
    for name, digest in checks.items():
        if sha((args.inputs/name).read_bytes()) != digest: raise ValueError('Input checksum mismatch: '+name)
    result = census(root, json.loads((args.inputs/'ownership.json').read_text()))
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out/'census.json').write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    (args.out/'frozen-source.sha256').write_text(''.join(f"{r['sha256']}  {r['path']}\n" for r in result['scope_files']))
    (args.out/'targets.txt').write_text('\n'.join(result['frontend_modules'])+'\n')
    (args.out/'closure.txt').write_text('\n'.join(result['topological_closure'])+'\n')
    print(json.dumps({k: len(result[k]) for k in ('scope_files','frontend_modules','topological_closure','external_local_modules','cross_directory_imports','declaration_candidates','proof_options')},sort_keys=True))

if __name__ == '__main__': main()
