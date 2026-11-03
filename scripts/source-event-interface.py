#!/usr/bin/env python3
"""Generate exact actual-emitter signatures and checked standard-axiom pins."""
import argparse,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('output',type=Path);p.add_argument('--pin',type=Path);a=p.parse_args()
groups=[('Solidity/Source/FailureEventLaws.lean','Solidity.Source.FailureExecution',['Solidity.Source.emitEvent','Solidity.Source.FailureExecution.emit_stopped_run']),('Solidity/Source/FailureEventControls.lean','Solidity.Source.FailureExecution.EventControls',[])]
groups[1][2].extend(groups[1][1]+'.'+n for n in re.findall(r'^theorem ([A-Za-z0-9_]+)',Path(groups[1][0]).read_text(),re.M))
names=[n for _,_,ns in groups for n in ns]
a.output.write_text('import Solidity.Source.FailureEventControls\n'+'\n'.join('#print '+n+'\n#print axioms '+n for n in names)+'\n')
if a.pin:
 reports={n:' '.join(t.split()) for n,t in re.findall(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[[^\]]*\])",a.pin.read_text(),re.S)}
 for file,namespace,ns in groups:
  text=Path(file).read_text();assert 'BEGIN GENERATED EVENT PINS' not in text
  block='/- BEGIN GENERATED EVENT PINS -/\n'
  for n in ns:
   t=reports[n];assert t in ['does not depend on any axioms','depends on axioms: [propext, Classical.choice, Quot.sound]'],(n,t)
   block+="/-- info: '"+n+"' "+t+' -/\n#guard_msgs (whitespace := lax) in #print axioms '+n+'\n'
  block+='/- END GENERATED EVENT PINS -/\n\n';end='end '+namespace;assert text.count(end)==1;Path(file).write_text(text.replace(end,block+end))
