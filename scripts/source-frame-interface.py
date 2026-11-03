#!/usr/bin/env python3
"""Generate exact H16 frame-operation signatures; no assumed theorem bodies."""
import argparse,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('output',type=Path);p.add_argument('--controls',action='store_true');p.add_argument('--pin-axioms',type=Path);a=p.parse_args()
names=['Solidity.Source.St','Solidity.Source.FailureExecution.RuntimePlan','Solidity.Source.FailureExecution.check','Solidity.Source.FailureExecution.pending','Solidity.Source.FailureExecution.frame','Solidity.Source.FailureExecution.emit']
imports='import Solidity.Source.FailureMachine\n'
if a.controls:
 imports+='import Solidity.Source.FailureMachineControls\n'
 names += ['Solidity.Source.FailureExecution.Controls.'+n for n in re.findall(r'^theorem ([A-Za-z0-9_]+)',Path('Solidity/Source/FailureMachineControls.lean').read_text(),re.M)]
a.output.write_text(imports+'\n'.join('#print '+n for n in names)+'\n'+'\n'.join('#print axioms '+n for n in names[2:])+'\n')

if a.pin_axioms:
 text=a.pin_axioms.read_text()
 reports={}
 for name,tail in re.findall(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[[^\]]*\])",text,re.S):
  reports[name]=' '.join(tail.split())
 for file,ns,selected in [
  ('Solidity/Source/FailureMachine.lean','Solidity.Source.FailureExecution',names[2:6]),
  ('Solidity/Source/FailureMachineControls.lean','Solidity.Source.FailureExecution.Controls',names[6:])]:
  assert selected and all(n in reports for n in selected)
  p=Path(file);source=p.read_text();marker='/- BEGIN GENERATED H16 AXIOM PINS -/'
  if marker in source:source=source[:source.index(marker)]+source[source.index('/- END GENERATED H16 AXIOM PINS -/')+len('/- END GENERATED H16 AXIOM PINS -/'):]
  pins=marker+'\n'
  for n in selected:
   tail=reports[n]
   assert tail in ['does not depend on any axioms','depends on axioms: [propext, Classical.choice, Quot.sound]'],(n,tail)
   pins+="/-- info: '"+n+"' "+tail+' -/\n#guard_msgs (whitespace := lax) in #print axioms '+n+'\n'
  pins+='/- END GENERATED H16 AXIOM PINS -/\n\n'
  end='end '+ns
  assert source.count(end)==1
  source=source.replace(end,pins+end)
  p.write_text(source)
