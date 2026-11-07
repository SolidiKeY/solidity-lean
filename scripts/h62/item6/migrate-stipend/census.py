#!/usr/bin/env python3
"""Deterministic source census; hashes are source guards, not Lean type hashes."""
import hashlib, json, pathlib, re, subprocess
ROOT = pathlib.Path(__file__).resolve().parents[4]
BASE = 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
def digest(data): return hashlib.sha256(data).hexdigest()
def census():
    modules = sorted(ROOT.glob('Solidity/Stipend/*.lean'))
    order, visiting, seen, imports = [], set(), set(), {}
    def visit(name):
        if name in seen: return
        if name in visiting: raise ValueError('import cycle: ' + name)
        path = ROOT / (name.replace('.', '/') + '.lean')
        if not path.exists(): return
        visiting.add(name)
        deps = re.findall(r'^import\s+(\S+)', path.read_text(), re.M)
        imports[name] = deps
        for dep in deps: visit(dep)
        visiting.remove(name); seen.add(name); order.append(name)
    for path in modules: visit('.'.join(path.relative_to(ROOT).with_suffix('').parts))
    files = {}
    for path in modules:
        rel = str(path.relative_to(ROOT)); data = path.read_bytes(); src = data.decode()
        original = subprocess.check_output(['git', 'show', BASE + ':' + rel], cwd=ROOT)
        # Exact source including bodies is stronger than a signature-only text guard.
        declarations = []
        for m in re.finditer(r'^(structure|def|theorem|instance)\s+([^\n]+)', src, re.M):
            declarations.append({'kind':m[1], 'header':m[2], 'line':src[:m.start()].count('\n')+1})
        files[rel] = {'sha256':digest(data), 'base_sha256':digest(original),
                      'unchanged':data == original, 'declarations':declarations,
                      'pattern_rows':[{'line':i,'source':line.strip()} for i,line in enumerate(src.splitlines(),1) if line.lstrip().startswith('|')],
                      'budget_options':re.findall(r'^set_option[^\n]*',src,re.M),
                      'forbidden_tokens':re.findall(r'\b(?:sorry|axiom|native_decide)\b',src)}
    reverse = []
    for path in sorted(ROOT.glob('Solidity/**/*.lean')):
        if 'import Solidity.Stipend.Rule' in path.read_text(): reverse.append(str(path.relative_to(ROOT)))
    return {'base':BASE, 'files':files, 'topological_closure':order,
            'closure_source_hashes':{n:digest((ROOT/(n.replace('.', '/')+'.lean')).read_bytes()) for n in order},
            'closure_matches_base':{n:(ROOT/(n.replace('.', '/')+'.lean')).read_bytes()==subprocess.check_output(['git','show',BASE+':'+n.replace('.', '/')+'.lean'],cwd=ROOT) for n in order},
            'imports':dict(sorted(imports.items())), 'direct_consumers':reverse,
            'hash_boundary':'Exact UTF-8 source guards; no elaborated type equality claim.'}
if __name__ == '__main__': print(json.dumps(census(), indent=2, sort_keys=True))
