#!/usr/bin/env python3
"""Exact source pins and complete type-constructor inventory (external check)."""
import hashlib,json,pathlib,re
root=pathlib.Path(__file__).resolve().parents[3]
m=json.loads((root/'tests/h28-sol/type-grammar/inventory.json').read_text())
for name,want in m['inputs'].items():
    assert hashlib.sha256((root/name).read_bytes()).hexdigest()==want,name
s=(root/'Solidity/Source/Syntax.lean').read_text()
section=s.split('  -- Type names.\n',1)[1].split('  | varDecl',1)[0]
actual=re.findall(r'^  \| (\w+)',section,re.M)
assert actual==m['type_constructors'],actual
for name in actual:
    assert re.search(r'\| _, \.'+name+r'\b',(root/'Solidity/Frontend/Checked/Print.lean').read_text()),name
assert m['elementary']==['address','addressPayable','bool','string','bytes','int','fixedBytes','fixed']
assert m['function_layouts']==['attrs []','attrs [vis]','attrs [mutab]','attrs [vis, mutab]','attrs [mutab, vis]']
assert len(set(m['function_layouts']))==5
print('PASS: 8 source pins; all 5 Syn typeName constructors; 8 elementary constructor families; 5 attribute layout shapes')
local=root/'Solidity/Frontend/TypeGrammarH28'
registration=json.loads((local/'registration.json').read_text())
registered=[entry['module'] for entry in registration['modules']]
actual_modules=sorted(str(p.relative_to(root)).removesuffix('.lean').replace('/','.') for p in local.glob('*.lean'))
assert sorted(registered)==actual_modules and len(set(registered))==len(registered)
print('PASS: local registration covers all '+str(len(actual_modules))+' task modules')
print('External inventory check only: no uniqueness/completeness theorem is implied')
