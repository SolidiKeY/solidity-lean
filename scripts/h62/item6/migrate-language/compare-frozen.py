#!/usr/bin/env python3
"""Compare structural Lean snapshots, source-declared interfaces and generated API.
Usage: compare-frozen.py OLD_LOG NEW_LOG OUTPUT_JSON
Source names are indexed from the pinned source's explicit namespaces and commands;
all eight files and all named declarations must be represented. Anonymous cases
remain covered by source review, unchanged statement text and module builds.
"""
import hashlib,json,pathlib,re,subprocess,sys
root=pathlib.Path(__file__).resolve().parents[4]
base='c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
def read(p):
    return {r['name']:r for l in pathlib.Path(p).read_text().splitlines() if l.startswith('FROZEN_JSON ') for r in [json.loads(l[12:]) ]}
def digest(s): return hashlib.sha256(s.encode()).hexdigest()
a,b=read(sys.argv[1]),read(sys.argv[2]); names=[]; example_headers=[]; members=[]
for p in sorted(root.glob('Solidity/Language/**/*.lean')):
    text=subprocess.check_output(['git','show',base+':'+str(p.relative_to(root))],cwd=root).decode()
    current=p.read_text()
    def examples(src):
        return [src[m.start():].split(':=',1)[0] for m in re.finditer(r'^example\b',src,re.M)]
    assert examples(text)==examples(current), 'anonymous example statement prefix changed'
    example_headers.extend(examples(text))
    stack=[]; data_kind=None; data_name=None
    for line in text.splitlines():
        if m:=re.match(r'^(namespace|section)\s+(\S+)',line): stack.append((m[1],m[2]));data_name=None;continue
        if re.match('^end(?: |$)',line):
            assert stack;stack.pop();data_name=None;continue
        if m:=re.match(r'^(?:private |protected )*(def|abbrev|theorem|lemma|structure|inductive|class)\s+([^\s:(]+)',line):
            n='.'.join([v for k,v in stack if k=='namespace']+[m[2]]); names.append(n)
            data_kind=m[1];data_name=n if data_kind in ['structure','inductive','class'] else None
            if data_kind in ['structure','class']:members.append(n+'.mk')
        elif data_name and data_kind=='inductive' and line.startswith('  |'):
            members.extend(data_name+'.'+n for n in re.findall(r'\|\s+([A-Za-z][A-Za-z0-9_]*)',line))
        elif data_name and data_kind in ['structure','class']:
            if m:=re.match(r'^  ([A-Za-z][A-Za-z0-9_]*)\s*:',line):members.append(data_name+'.'+m[1])
    assert not stack
assert len(names)==len(set(names))==344
assert len(example_headers)==44
# The sole anonymous source instance has a stable generated public name.
names.append('Solidity.Language.FixedPoint.instDecidableEqFx')
missing=[n for n in names if n not in a or n not in b]
changed=[n for n in names if n in a and n in b and (a[n]['type']!=b[n]['type'] or a[n]['levels']!=b[n]['levels'])]
member_missing=[n for n in members if n not in a or n not in b]
member_changed=[n for n in members if n in a and n in b and (a[n]['type']!=b[n]['type'] or a[n]['levels']!=b[n]['levels'])]
member_rows=[dict(name=n,type_sha256=digest(a[n]['type']),levels=a[n]['levels']) for n in sorted(set(members)) if n in a and n in b]
shared=sorted(a.keys()&b.keys());allowed={'propext','Classical.choice','Quot.sound'}
assert all(set(r['axioms'])<=allowed for r in b.values()), 'nonstandard axiom dependency'
rows=[dict(name=n,type_sha256=digest(a[n]['type']),levels=a[n]['levels'],old_axioms=a[n]['axioms'],new_axioms=b[n]['axioms']) for n in sorted(names) if n in a and n in b]
result=dict(base=base,source_member_count=len(member_rows),missing_source_members=member_missing,changed_source_member_types=member_changed,source_members=member_rows,source_members_sha256=digest(json.dumps(member_rows,separators=(',',':'))),source_declared_count=len(names),anonymous_example_count=len(example_headers),anonymous_example_prefixes_sha256=digest(json.dumps(example_headers)),missing_source_declarations=missing,changed_source_types=changed,
 frozen_source_types_sha256=digest(json.dumps([(r['name'],r['levels'],r['type_sha256']) for r in rows],separators=(',',':'))),source_interfaces=rows,
 old_all_constant_count=len(a),new_all_constant_count=len(b),generated_removed=sorted(a.keys()-b.keys()),generated_added=sorted(b.keys()-a.keys()),
 generated_type_changes=[dict(name=n,old_type_sha256=digest(a[n]['type']),new_type_sha256=digest(b[n]['type'])) for n in shared if a[n]['type']!=b[n]['type'] or a[n]['levels']!=b[n]['levels']],
 standard_axiom_changes=[dict(name=n,old=a[n]['axioms'],new=b[n]['axioms']) for n in shared if a[n]['axioms']!=b[n]['axioms']])
pathlib.Path(sys.argv[3]).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:v for k,v in result.items() if not isinstance(v,list)}))
assert not missing and not changed and not member_missing and not member_changed, 'frozen source-declared interface changed'
