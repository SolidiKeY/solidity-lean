#!/usr/bin/env python3
"""Owned traversal and exhaustive intrinsic specimens; structural coverage only."""
import json
from pathlib import Path
import re
import runpy
import sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
api=runpy.run_path(str(ROOT/'scripts/source-ctors.py'))
ctors=api['constructors']()
marker='marker'
leaf='⟨"leaf", []⟩'
def strip(t):
    t=t.strip()
    if t.startswith('(') and t.endswith(')'):
        depth=0
        for i,c in enumerate(t):
            depth+=(c=='(')-(c==')')
            if depth==0 and i<len(t)-1:return t
        return t[1:-1].strip()
    return t
def child(cat):
    cat=strip(cat)
    if cat=='c':cat='.expr'
    if cat.startswith('.list '):
        item,refs=child(cat[6:]);return f'(.cons {item} .nil)',refs
    if cat.startswith('.opt '):
        item,refs=child(cat[5:]);return f'(.some {item})',refs
    table={
      '.unit':('(.unit (.cons (.topPart (.constant (.userType marker) "v" (.lit (.bool true)))) .nil))',[marker]),
      '.top':('(.topPart (.constant (.userType marker) "v" (.lit (.bool true))))',[marker]),
      '.importAlias':('(.importAlias "a" (some "b"))',[]),
      '.inherit':('(.inherit marker .none)',[marker]),
      '.callArgs':('(.positional (.cons (.ident "leaf") .nil))',[leaf]),
      '.namedArg':('(.namedArg "v" (.ident "leaf"))',[leaf]),
      '.modInv':('(.modInv marker .none)',[marker]),
      '.param':('(.param (.userType marker) none none)',[marker]),
      '.structMember':('(.structMember (.userType marker) "v")',[marker]),
      '.eventParam':('(.eventParam (.userType marker) false none)',[marker]),
      '.errorParam':('(.errorParam (.userType marker) none)',[marker]),
      '.usingAlias':('(.usingAlias marker none)',[marker]),
      '.using':('(.usingPath marker .none false)',[marker]),
      '.fallbackSig':('(.fbParams (.param (.userType marker) none none) .nil .nil)',[marker]),
      '.typeName':('(.userType marker)',[marker]),
      '.varDecl':('(.varDecl (.userType marker) none "v")',[marker]),
      '.expr':('(.ident "leaf")',[leaf]),
      '.simple':('(.exprStmt (.ident "leaf"))',[leaf]),
      '.yulStmt':('(.yulExprStmt (.yulPath "y" ["z"]))',[]),
      '.yulExpr':('(.yulPath "y" ["z"])',[]),
      '.yulCase':('(.yulCase (.bool true) .nil)',[])}
    if cat in table:return table[cat]
    if cat.startswith('.part '):return '(.struct "S" (.structMember (.userType marker) "v") .nil)',[marker]
    statement='(.simpleStmt (.exprStmt (.ident "leaf")))'
    block=f'(.block (.cons (.stmtItem {statement}) .nil))'
    if cat.startswith('.stmt '):return statement,[leaf]
    if cat.startswith('.item '):return f'(.stmtItem {statement})',[leaf]
    if cat.startswith('.block '):return block,[leaf]
    if cat.startswith('.catchClause '):return f'(.catchPlain {block})',[leaf]
    raise ValueError(('category',cat))
def arg(t):
    if t.startswith('Syn '):return child(t[4:])
    table={'Bool':'false','String':'"token"','List String':'[]','List (List String)':'[]',
      'Nat':'0','Elem':'.bool','Lit':'(.bool true)','NumLit':'(.dec 1 0 0)',
      'YulLit':'(.bool true)','FnName':'(.ident "f")','IdPath':'marker',
      'MapKey':'(.path marker)','Option (List IdPath)':'(some [marker])',
      'PrefixOp':'.not','SuffixOp':'.inc','MulOp':'.mul','AddOp':'.add',
      'ShiftOp':'.shl','OrderOp':'.lt','EqOp':'.eq','AssignOp':'.assign',
      'Denom':'.wei','e ≠ .addressPayable':'(by decide)'}
    if t.startswith('Option ') and t not in table:return 'none',[]
    return table[t],([marker] if t in ['IdPath','MapKey','Option (List IdPath)'] else [])
syntax=(ROOT/'Solidity/Source/Syntax.lean').read_text()
body=syntax[syntax.index('inductive Syn : Cat → Type where'):syntax.index('end Solidity.Source')]
raw=[];cur=None
for line in body.splitlines()[1:]:
    if line.startswith('  | '):
        if cur:raw.append(cur)
        cur=line[4:]
    elif line.startswith('      ') and cur is not None:cur+=' '+line.strip()
    else:
        if cur:raw.append(cur)
        cur=None
if cur:raw.append(cur)
results={s.split()[0]:s.rsplit('→',1)[-1].strip() if '→' in s else s.rsplit(':',1)[-1].strip() for s in raw}
for name in results:
    for old,new in [('c','.expr'),('t','false'),('k','.body'),('l','false'),('u','false')]:
        results[name]=re.sub(r'\b'+old+r'\b',new,results[name])
header='import Solidity.Frontend.QualifiedUnits.Checked\n\n/-! Structural reference coverage over existing intrinsic syntax. -/\nnamespace Solidity.Frontend.QualifiedUnits\nopen Solidity.Source\n\n'
code=header+'''/-- Identifier/member expression syntax as an existing path. -/
def expressionPath : Syn .expr → Option IdPath
  | .ident name => some ⟨name, []⟩
  | .member receiver name => (expressionPath receiver).map fun p => ⟨p.head, p.tail ++ [name]⟩
  | _ => none

/-- Explicit paths, identifiers and member prefixes. Runtime fields of
non-path receivers remain with G13; their ordinary subterms are traversed. -/
def references : {c : Cat} → Syn c → List IdPath
'''
for name,args in ctors:
    patterns=[];own=[];children=[]
    for i,(n,t) in enumerate(args):
        v=f'a{i}'
        if t.startswith('Syn'):patterns.append(v);children.append(f'(references {v})')
        elif t=='IdPath':patterns.append(v);own.append(f'[{v}]')
        elif t=='Option (List IdPath)':patterns.append(v);own.append(f'{v}.getD []')
        elif t=='MapKey':patterns.append(v);own.append(f'MapKey.paths {v}')
        elif name=='ident':patterns.append(v);own.append(f'[⟨{v}, []⟩]')
        elif name=='member':patterns.append(v)
        else:patterns.append('_')
    if name=='member':own=['(expressionPath (.member a0 a1)).toList']
    pattern='.'+name+(' '+' '.join(patterns) if patterns else '')
    code+='  | _, '+pattern+' => '+(' ++ '.join(own+children) or '[]')+'\n'
code+='\nend Solidity.Frontend.QualifiedUnits\n'
(ROOT/'Solidity/Frontend/QualifiedUnits/References.lean').write_text(code)
code='import Solidity.Frontend.QualifiedUnits.References\n\n/-! One typed specimen and literal expected traversal per existing constructor. -/\nnamespace Solidity.Frontend.QualifiedUnits.ConstructorFixtures\nopen Solidity.Source\n\ndef marker : IdPath := ⟨"N", ["M", "T"]⟩\n\n'
matrix=json.loads((ROOT/'tests/sol-qualified-units/constructors.json').read_text())
for (name,args),row in zip(ctors,matrix['rows']):
    values=[];own=[];kids=[]
    for n,t in args:
        expr,refs=arg(t);values.append(expr)
        if t.startswith('Syn'):kids+=refs
        else:own+=refs
    if name=='ident':own=['⟨"token", []⟩']
    if name=='member':own=['⟨"leaf", ["token"]⟩']
    expr='.'+name+(' '+' '.join(values) if values else '')
    code+=f'def specimen_{name} : {results[name]} := {expr}\n\n'
    expected='['+', '.join(own+kids)+']'
    proof = '  constructor\n  · rfl\n  · simp only [specimen_member, references, expressionPath, Option.map, Option.toList, List.nil_append, List.cons_append]' if name == 'member' else '  exact ⟨rfl, rfl⟩'
    code+=f'theorem fixture_{name} : specimen_{name}.ctor = .{name} ∧ references specimen_{name} = {expected} := by\n{proof}\n\n'
    row['kernel_fixture']='ConstructorFixtures.fixture_'+name
    row['status']='kernel-fixture-ready'
code+='end Solidity.Frontend.QualifiedUnits.ConstructorFixtures\n'
(ROOT/'Solidity/Frontend/QualifiedUnits/ConstructorFixtures.lean').write_text(code)
(ROOT/'tests/sol-qualified-units/constructors.json').write_text(json.dumps(matrix,indent=2)+'\n')
