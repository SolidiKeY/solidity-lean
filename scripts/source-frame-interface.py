#!/usr/bin/env python3
"""Generate exact frame-operation signatures; no assumed theorem bodies."""
import argparse,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('output',type=Path);p.add_argument('--controls',action='store_true');p.add_argument('--pin-axioms',type=Path);p.add_argument('--clean-process-comments',action='store_true');a=p.parse_args()
if a.clean_process_comments and a.pin_axioms:p.error('cleanup and pin generation are mutually exclusive')
names=['Solidity.Source.St','Solidity.Source.FailureExecution.RuntimePlan','Solidity.Source.FailureExecution.check','Solidity.Source.FailureExecution.pending','Solidity.Source.FailureExecution.frame','Solidity.Source.FailureExecution.emit']
imports='import Solidity.Source.FailureMachine\n'
if a.controls:
 imports+='import Solidity.Source.FailureMachineControls\n'
 names += ['Solidity.Source.FailureExecution.Controls.'+n for n in re.findall(r'^theorem ([A-Za-z0-9_]+)',Path('Solidity/Source/FailureMachineControls.lean').read_text(),re.M)]
a.output.write_text(imports+'\n'.join('#print '+n for n in names)+'\n'+'\n'.join('#print axioms '+n for n in names[2:])+'\n')

if a.clean_process_comments:
 for file in ['FailureMachine', 'FailureMachineControls']:
  target=Path('Solidity/Source')/(file+'.lean')
  source=target.read_text()
  source=source.replace('(H16 execution leaf)', '(execution leaf)')
  source=source.replace('GENERATED H16 AXIOM PINS', 'GENERATED AXIOM PINS')
  target.write_text(source)

if a.pin_axioms:
 text=a.pin_axioms.read_text()
 reports={}
 for name,tail in re.findall(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[[^\]]*\])",text,re.S):
  reports[name]=' '.join(tail.split())
 for file,ns,selected in [
  ('Solidity/Source/FailureMachine.lean','Solidity.Source.FailureExecution',names[2:6]),
  ('Solidity/Source/FailureMachineControls.lean','Solidity.Source.FailureExecution.Controls',names[6:])]:
  assert selected and all(n in reports for n in selected)
  p=Path(file);source=p.read_text();marker='/- BEGIN GENERATED AXIOM PINS -/'
  for label in ['H16 AXIOM', 'AXIOM']:
   begin='/- BEGIN GENERATED '+label+' PINS -/'
   end='/- END GENERATED '+label+' PINS -/'
   if begin in source:source=source[:source.index(begin)]+source[source.index(end)+len(end):]
  pins=marker+'\n'
  for n in selected:
   tail=reports[n]
   assert tail in ['does not depend on any axioms','depends on axioms: [propext, Classical.choice, Quot.sound]'],(n,tail)
   pins+="/-- info: '"+n+"' "+tail+' -/\n#guard_msgs (whitespace := lax) in #print axioms '+n+'\n'
  pins+='/- END GENERATED AXIOM PINS -/\n\n'
  end='end '+ns
  assert source.count(end)==1
  source=source.replace(end,pins+end)
  p.write_text(source)
