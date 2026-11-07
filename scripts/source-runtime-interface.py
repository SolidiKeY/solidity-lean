#!/usr/bin/env python3
"""Generate actual runtime signatures and standard-axiom pins from checked reports."""
import argparse,re
from pathlib import Path
ops=['evalE','evalPair','evalArgs','evalConvArgs','evalLoc','evalBuiltin','evalArgsRev','pay','execS','forIter','execItems','runMods','callInternal','callAddr','enterInstance','envLoop','dispatch']

def code_mask(source):
 """Preserve offsets, masking nested comments and strings (not an AST)."""
 out=list(source);i=0
 while i<len(source):
  if source.startswith('/-',i):
   j=i+2;depth=1
   while j<len(source) and depth:
    if source.startswith('/-',j):depth+=1;j+=2
    elif source.startswith('-/',j):depth-=1;j+=2
    else:j+=1
   if depth:raise ValueError('unterminated block comment')
  elif source.startswith('--',i):
   j=source.find('\n',i);j=len(source) if j<0 else j
  elif source[i]=='"':
   j=i+1
   while j<len(source):
    if source[j]=='\\':j+=2
    elif source[j]=='"':j+=1;break
    else:j+=1
   else:raise ValueError('unterminated string')
  else:i+=1;continue
  for k in range(i,j):
   if out[k]!='\n':out[k]=' '
  i=j
 return ''.join(out)

def audit_forwarding(source):
 masked=code_mask(source);a=masked.index('\nmutual\n');b=masked.index('\nend\n',a);body=masked[a:b]
 decls=list(re.finditer(r'(?m)^def (\w+)',body))
 if [m.group(1) for m in decls]!=ops:raise ValueError('unexpected evaluator definition inventory')
 positions={m.start(1) for m in decls}
 for i,m in enumerate(decls):
  end=decls[i+1].start() if i+1<len(decls) else len(body)
  marker=body.index(':=',m.end(),end)
  # The first := belongs to the required optional parameter.
  if not re.search(r'\(plan\s*:\s*FailureExecution\.RuntimePlan\s*$',body[m.end():marker]):
   raise ValueError('missing typed plan parameter: '+m.group(1))
  if not re.match(r':=\s*none\)',body[marker:]):raise ValueError('changed default plan: '+m.group(1))
 counts={n:0 for n in ops+['emitEvent']}
 if '«' in body or '»' in body:raise ValueError('quoted identifiers require explicit forwarding-audit review')
 for m in re.finditer(r'(?<![\w.])(?:\w+\.)*('+ '|'.join(counts)+r')\b',body):
  if m.start() in positions:continue
  qualifier=m.group(0)[:-len(m.group(1))]
  if qualifier not in ['', 'Source.', 'Solidity.Source.', '_root_.Source.', '_root_.Solidity.Source.']:
   raise ValueError('unsupported evaluator qualification: '+qualifier)
  if not re.match(r'\s+\(plan\s*:=\s*plan\)',body[m.end():]):
   raise ValueError('missing or changed same-plan forwarding: '+m.group(1))
  counts[m.group(1)]+=1
 if counts['emitEvent']!=5:raise ValueError('event-call inventory changed')
 return counts

def main():
 audit_forwarding(Path('Solidity/Source/Eval.lean').read_text())
 p=argparse.ArgumentParser();p.add_argument('output',type=Path);p.add_argument('--pin',type=Path);a=p.parse_args()
 file=Path('Solidity/Source/FailureRuntimeControls.lean');ns='Solidity.Source.FailureExecution.RuntimeControls'
 laws=[ns+'.'+n for n in re.findall(r'^theorem ([A-Za-z0-9_]+)',file.read_text(),re.M)]
 assert len(laws)==23,len(laws)
 names=['Solidity.Source.'+n for n in ops]+['Solidity.Source.FailureExecution.preflight']+laws
 a.output.write_text('import Solidity.Source.FailureRuntimeControls\n'+'\n'.join('#check @'+n+'\n#print axioms '+n for n in names)+'\n')
 if a.pin:
  reports={n:' '.join(t.split()) for n,t in re.findall(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[[^\]]*\])",a.pin.read_text(),re.S)}
  text=file.read_text();assert 'BEGIN GENERATED RUNTIME PINS' not in text
  block='/- BEGIN GENERATED RUNTIME PINS -/\n'
  for n in ['Solidity.Source.FailureExecution.preflight']+laws:
   t=reports[n];assert t in ['does not depend on any axioms','depends on axioms: [propext, Classical.choice, Quot.sound]'],(n,t)
   block+="/-- info: '"+n+"' "+t+' -/\n#guard_msgs (whitespace := lax) in #print axioms '+n+'\n'
  block+='/- END GENERATED RUNTIME PINS -/\n\n';end='end '+ns;assert text.count(end)==1;file.write_text(text.replace(end,block+end))

if __name__=='__main__':main()
