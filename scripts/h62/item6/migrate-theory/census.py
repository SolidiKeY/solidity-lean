#!/usr/bin/env python3
"""Deterministic source census; whole-source pins conservatively freeze interfaces.
This is a lexical inventory, not an elaborated interface/axiom audit.
"""
import argparse, hashlib, json, pathlib, re, subprocess
ROOT = pathlib.Path(__file__).resolve().parents[4]
BASE = 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
FILES = '''Bridge/Denote CallerModel/Static Mutability/Assignable Mutability/Closer Mutability/Payable Mutability/Pure Mutability/View Progress/Calls Progress/Controls Progress/Fragment Progress/Leaves Progress/Outcome Progress/Program Progress/Tuple Reachable/CallerModel Reachable/CleanTail Reachable/Mode Segs Typed/Leaves Typed/Mem Typed/MemMirror Typed/Obs Typed/Obs/Ops Typed/Obs/Paths Typed/Obs/Values'''.split()
OWNED = ['Solidity/Theory/' + p + '.lean' for p in FILES]
def strip_comments(s):
    # Preserve newlines and positions; handle nested Lean comments and strings.
    out, i, depth, string = [], 0, 0, False
    while i < len(s):
        if depth:
            if s.startswith('/-', i): depth += 1; out.extend('  '); i += 2
            elif s.startswith('-/', i): depth -= 1; out.extend('  '); i += 2
            else: out.append('\n' if s[i] == '\n' else ' '); i += 1
        elif string:
            if s[i] == '\\' and i + 1 < len(s): out.extend('  '); i += 2
            elif s[i] == '"': string = False; out.append(' '); i += 1
            else: out.append('\n' if s[i] == '\n' else ' '); i += 1
        elif s.startswith('/-', i): depth = 1; out.extend('  '); i += 2
        elif s.startswith('--', i):
            end = s.find('\n', i)
            if end < 0: end = len(s)
            out.extend(' ' * (end-i)); i = end
        elif s[i] == '"': string = True; out.append(' '); i += 1
        else: out.append(s[i]); i += 1
    return ''.join(out)
def imports(s):
    return [m for line in re.findall(r'^[ \t]*(?:(?:public|private)[ \t]+)?import[ \t]+([^\n]+)', strip_comments(s), re.M) for m in line.split()]
def source_path(mod):
    path = ROOT / (mod.replace('.', '/') + '.lean')
    if path.exists(): return path
    vendor = ROOT/'vendor/LeanTeX'/ (mod.replace('.', '/') + '.lean')
    if vendor.exists(): return vendor
    if mod.split('.')[0] in {'Init', 'Lean', 'Lake', 'Std'}: return None
    raise FileNotFoundError('unresolved non-toolchain import: ' + mod)
def declaration_candidates(source):
    clean = strip_comments(source)
    rows = []
    for m in re.finditer(r'\b(theorem|lemma|def|abbrev|opaque|structure|inductive|class|instance|axiom)\b', clean):
        following = clean[m.end():].lstrip()
        name = re.match(r'[^\s:({\[]+', following)
        rows.append({'line': clean.count('\n', 0, m.start())+1,
          'kind':m[1], 'name':name[0] if name else None,
          'source_line_sha256':hashlib.sha256(source.splitlines()[clean.count('\n',0,m.start())].encode()).hexdigest()})
    return rows
def census():
    actual = sorted(str(p.relative_to(ROOT)) for p in (ROOT/'Solidity/Theory').rglob('*.lean'))
    assert actual == sorted(OWNED), (actual, OWNED)
    order, visiting, seen, edges = [], set(), set(), {}
    def visit(mod):
        if mod in seen: return
        assert mod not in visiting, 'import cycle: ' + mod
        path = source_path(mod)
        if path is None: return  # explicitly allowlisted toolchain namespace
        visiting.add(mod)
        edges[mod] = imports(path.read_text())
        for dep in edges[mod]: visit(dep)
        visiting.remove(mod); seen.add(mod); order.append(mod)
    rows = []
    for p in sorted(OWNED):
        data = (ROOT/p).read_bytes(); source = data.decode()
        pinned = subprocess.check_output(['git','show',BASE+':'+p], cwd=ROOT)
        clean = strip_comments(source)
        rows.append({'path':p,'sha256':hashlib.sha256(data).hexdigest(),
          'base_sha256':hashlib.sha256(pinned).hexdigest(),'unchanged':data == pinned,
          'imports':imports(source),
          'declaration_candidates':declaration_candidates(source),
          'branch_lines':[{'line':i,'text':line.strip()} for i,line in enumerate(clean.splitlines(),1) if re.match(r'\s*\|',line)],
          'budgets':re.findall(r'set_option\s+(?:maxHeartbeats|maxRecDepth)\s+\S+',clean),
          'trust_tokens':{t:len(re.findall(r'\b'+t+r'\b',clean)) for t in ['sorry','axiom','native_decide']}})
        visit(p[:-5].replace('/','.'))
    return {'base':BASE,'assigned_count':len(rows),'files':rows,'topological_closure':order,
      'external_dependencies':[m for m in order if not m.startswith('Solidity.Theory.')],
      'edges':edges,'closure_source_sha256':{str(source_path(m).relative_to(ROOT)):hashlib.sha256(source_path(m).read_bytes()).hexdigest() for m in order},'interface_boundary':'whole-source pins; lexical declaration candidates only; no elaborated API equivalence claim'}
if __name__ == '__main__':
    a=argparse.ArgumentParser(); a.add_argument('--output',type=pathlib.Path,required=True); args=a.parse_args()
    result=census(); args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(f"assigned={result['assigned_count']} closure={len(result['topological_closure'])} external={len(result['external_dependencies'])}")
