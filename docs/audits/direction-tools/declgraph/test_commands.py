#!/usr/bin/env python3
"""Exercise Lean-native syntax parsing, including quotations and UTF-16 positions.
Run with pinned lean on PATH and LEAN_NUM_THREADS=1. The census parses syntax; imported grammar fixtures are separately compiled.
the intentionally invalid proof and throwing #eval must not be executed.
"""
import json,os,pathlib,subprocess,tempfile
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parents[3]
def main():
 cases=json.loads((HERE/'root_fixtures.json').read_text())
 cache=ROOT/'.lake/refactor-cache';cache.mkdir(parents=True,exist_ok=True)
 with tempfile.TemporaryDirectory(prefix='declgraph-parser-test-',dir=cache) as d:
  d=pathlib.Path(d);paths=[];items=[]
  keyword='import Lean\nsyntax "memory" : term\nmacro_rules | `(memory) => `(0)\ndef reserved := memory\n'
  (d/'DeclgraphKeyword.lean').write_text(keyword)
  c=subprocess.run(['lean','-j1','-o','DeclgraphKeyword.olean','-i','DeclgraphKeyword.ilean','DeclgraphKeyword.lean'],cwd=d,text=True,capture_output=True)
  assert c.returncode==0,c.stdout+c.stderr
  local_source='import Lean\nsection\nlocal macro "memory" : term => `(0)\nlocal macro (priority := 1000000) "#eval " _x:term : command => `(command| example : True := by trivial)\n#eval memory\nend\n#eval 1\n'
  delayed_source='import Lean\ndef lateMemory : Lean.ParserDescr := Lean.ParserDescr.symbol "memory"\ndef beforeRegistration (memory : Nat) := memory\nattribute [term_parser] lateMemory\n'
  for name,source in [('DeclgraphLocal',local_source),('DeclgraphDelayed',delayed_source)]:
   (d/(name+'.lean')).write_text(source)
   c=subprocess.run(['lean','-j1','-o',name+'.olean','-i',name+'.ilean',name+'.lean'],cwd=d,text=True,capture_output=True)
   assert c.returncode==0,c.stdout+c.stderr
   if name=='DeclgraphLocal':assert c.stdout.strip()=='1',c.stdout+c.stderr
  discard_source='import Lean\nsyntax "discard " command : command\nmacro_rules | `(command| discard $_c:command) => `(command| #check Nat)\n'
  (d/'DeclgraphDiscard.lean').write_text(discard_source)
  c=subprocess.run(['lean','-j1','-o','DeclgraphDiscard.olean','-i','DeclgraphDiscard.ilean','DeclgraphDiscard.lean'],cwd=d,text=True,capture_output=True)
  assert c.returncode==0,c.stdout+c.stderr
  cases=cases+[
   dict(name='discarded_nested_eval',source='import DeclgraphDiscard\ndiscard #eval (throw (IO.userError "MUST_NOT_RUN") : IO Unit)\n',kinds=[],incomplete=True),
   dict(name='eval_prefix_not_executed',source='import Lean\n#eval (throw (IO.userError "MUST_NOT_RUN") : IO Unit) in variable (x : Nat)\n',kinds=[],incomplete=True),
   dict(name='example_prefix_not_elaborated',source='import Lean\nexample : False := by exact True.intro in variable (x : Nat)\n',kinds=[],incomplete=True),
   dict(name='keyword_owner',source=keyword,module='DeclgraphKeyword',probes=['memory'],kinds=[],start=False,end=True),
   dict(name='keyword_import',source='import DeclgraphKeyword\n#eval memory\n',probes=['memory'],kinds=['eval'],start=True,end=True),
   dict(name='keyword_unrelated',source='import Lean\ndef useMemory (memory : Nat) := memory\n',probes=['memory'],kinds=[],start=False,end=False),
   dict(name='local_cached',source=local_source,module='DeclgraphLocal',kinds=['eval']),
   dict(name='local_uncached',source=local_source,kinds=['eval']),
   dict(name='delayed_registration',source=delayed_source,module='DeclgraphDelayed',kinds=[],incomplete=True),
   dict(name='wrapped_local_shadow',source='import Lean\nsection\nset_option hygiene false in\nlocal macro (priority := 1000000) "#eval " _x:term : command => `(command| example : True := by trivial)\n#eval 1\nend\n#eval 2\n',kinds=['eval']),
   dict(name='local_notation_variables',source='import Lean\nsection\nvariable (f : Nat)\nlocal notation "natLocal" => f\nexample : natLocal = f := rfl\nend\n',kinds=['example']),
   dict(name='uncached_global_shadow',source='import Lean\nmacro (priority := 1000000) "#eval " _x:term : command => `(command| example : True := by trivial)\n#eval 1\n',kinds=[],incomplete=True)]
  # Deliberately documents a semantic-context gap: skipped custom elaboration
  # installs local grammar; the syntax census still sees the builtin eval.
  activation='local macro (priority := 1000000) "#eval " _x:term : command => `(command| #check Nat)'
  activator='import Lean\nopen Lean Elab Command\nelab "activate_shadow" : command => do\n  let stx ← ofExcept (Parser.runParserCategory (← getEnv) `command '+json.dumps(activation)+')\n  elabCommand stx\n'
  (d/'DeclgraphActivator.lean').write_text(activator)
  c=subprocess.run(['lean','-j1','-o','DeclgraphActivator.olean','-i','DeclgraphActivator.ilean','DeclgraphActivator.lean'],cwd=d,text=True,capture_output=True)
  assert c.returncode==0,c.stdout+c.stderr
  activated='import DeclgraphActivator\nactivate_shadow\n#eval 1\n'
  (d/'Activated.lean').write_text(activated)
  c=subprocess.run(['lean','-j1','Activated.lean'],cwd=d,text=True,capture_output=True,env=dict(os.environ,LEAN_PATH=str(d)))
  assert c.returncode==0 and 'Nat : Type' in c.stdout and c.stdout.strip()!='1',c.stdout+c.stderr
  cases.append(dict(name='generated_grammar_semantics_unverified',source=activated,kinds=['eval']))
  for c in cases:
   p=d/(c['name']+'.lean');p.write_text(c['source']);paths.append(str(p));items.append(dict(path=str(p),module=c.get('module'),probes=c.get('probes',[])))
  (d/'modules.txt').write_text('Lean\nDeclgraphKeyword\nDeclgraphLocal\nDeclgraphDelayed\nDeclgraphDiscard\nDeclgraphActivator\n');(d/'paths.txt').write_text(''.join(json.dumps(x)+'\n' for x in items))
  out=d/'commands.jsonl'
  env=dict(os.environ,LEAN_PATH=str(d)+(os.pathsep+os.environ['LEAN_PATH'] if os.environ.get('LEAN_PATH') else ''))
  r=subprocess.run(['lean','-j1','--run',str(HERE/'Commands.lean'),str(d/'modules.txt'),str(d/'paths.txt'),str(out)],text=True,capture_output=True,env=env)
  assert r.returncode==0,r.stdout+r.stderr
  assert r.stdout.strip()=='COMMAND_INDEX_WRITTEN',r.stdout
  rows=[json.loads(s) for s in out.read_text().splitlines()];assert len(rows)==len(cases)
  for c,row in zip(cases,rows):
   if c.get('incomplete'):
    assert not row['complete'] and row['unsupported_registrations'] and not row['parse_errors'] and row['checks']==[],(c['name'],row)
    continue
   assert row['complete'],(c['name'],row)
   assert not row['parse_errors'] and not row['scope_errors'] and not row['missing_imports'] and not row['unlocated_parser_groups'],(c['name'],row)
   assert [r['kind'] for r in row['checks']]==c['kinds'],(c['name'],row)
   if 'start' in c:
    assert row['probe_start']['memory']==c['start'] and row['probe_end']['memory']==c['end'],(c['name'],row)
   if 'ranges' in c:assert [r['range'] for r in row['checks']]==c['ranges'],(c['name'],row)
 print('COMMAND_PARSER_FIXTURES_PASS',len(cases))
if __name__=='__main__':main()
