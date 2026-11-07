#!/usr/bin/env python3
"""Reproducible source census, not an elaborated Lean API/type audit."""
import argparse, hashlib, json, pathlib, re

def scrub(s):
    # Retain offsets/newlines while removing nested comments and strings.
    out = list(s); i = 0; depth = 0; string = False
    while i < len(s):
        n = 1
        if depth:
            if s.startswith('/-', i): depth += 1; n = 2
            elif s.startswith('-/', i): depth -= 1; n = 2
        elif string:
            if s[i] == '\\': n = min(2, len(s)-i)
            elif s[i] == '"': string = False
        elif s.startswith('/-', i): depth = 1; n = 2
        elif s.startswith('--', i):
            j = s.find('\n', i); n = (len(s) if j < 0 else j)-i
        elif s[i] == "'" and (m := re.match(r"'(?:[^'\\\n]|\\.)'", s[i:])):
            n = len(m[0])
        elif s[i] == '"': string = True
        else: i += 1; continue
        for k in range(i, i+n):
            if s[k] != '\n': out[k] = ' '
        i += n
    return ''.join(out)

def census(root):
    files = sorted(root.glob('Solidity/**/*.lean')) + sorted(root.glob('Bridge/**/*.lean')) + sorted(root.glob('*.lean'))
    sources = {str(p.relative_to(root))[:-5].replace('/', '.'): p for p in files}
    rows = {}; order = []; visiting = set(); visited = set()
    for name, p in sorted(sources.items()):
        raw = p.read_bytes(); code = scrub(raw.decode())
        imports = re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([\w.]+)', code, re.M)
        decls = []
        pattern = r'^['+r' \t'+r']*(?:@\[[^\]\n]*\][ \t]*)*(?:(?:private|protected|noncomputable|unsafe|partial|local|scoped)\s+)*(def|abbrev|theorem|lemma|structure|inductive|class|instance|axiom|opaque|example)\b[ \t]*([^\s:({]+)?'
        for m in re.finditer(pattern, code, re.M):
            decls.append({'kind': m[1], 'name': None if m[1]=='example' else m[2], 'line': code.count('\n', 0, m.start(1))+1})
        rows[name] = dict(path=str(p.relative_to(root)), sha256=hashlib.sha256(raw).hexdigest(), imports=imports, lexical_declarations=decls, acceptance_commands=[{'kind':m[1],'line':code.count('\n',0,m.start())+1} for m in re.finditer(r'#(guard_msgs|guard|eval|check|print|assert)\b',code)])
    yul = sorted(n for n in rows if n.startswith('Solidity.Yul.'))
    def visit(n):
        if n in visited or n not in rows: return
        if n in visiting: raise ValueError('import cycle: '+n)
        visiting.add(n)
        for imp in rows[n]['imports']: visit(imp)
        visiting.remove(n); visited.add(n); order.append(n)
    visit('SolkeyCheck')
    keysort_order = order.copy(); order.clear(); visited.clear()
    for n in yul: visit(n)
    boundary = [{'importer': n, 'dependency': i} for n in yul for i in rows[n]['imports'] if not i.startswith('Solidity.Yul.')]
    consumers = [{'importer': n.removeprefix('Bridge.'), 'importer_path': rows[n]['path'], 'package': 'Bridge' if n.startswith('Bridge.') else 'core', 'dependency': i} for n in sorted(rows) if n not in yul for i in rows[n]['imports'] if i in yul]
    return dict(schema=1, limitation='Lexical declarations are discovery only; whole-file hashes freeze source, not elaborated types. Standard library imports use the pinned toolchain.', keysort_order=keysort_order, yul_count=len(yul), closure_count=len(order), yul_modules=yul, build_order=order, boundary_imports=boundary, external_consumers=consumers, modules={n:rows[n] for n in sorted(set(order + keysort_order))})

if __name__ == '__main__':
    p = argparse.ArgumentParser(); p.add_argument('root', type=pathlib.Path); p.add_argument('output', type=pathlib.Path); a = p.parse_args()
    result = census(a.root.resolve()); a.output.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps({k:result[k] for k in ('yul_count', 'closure_count')}))
