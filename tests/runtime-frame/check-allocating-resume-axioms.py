#!/usr/bin/env python3
"""Exact ordered builtin reports; independent actual outer hard-cap receipt."""
import re,sys
from pathlib import Path
STANDARD=['propext','Classical.choice','Quot.sound']
PINS=[('Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingResume.reexport', ['propext']), ('Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingResume.Continuation', ['propext', 'Classical.choice', 'Quot.sound']), ('Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingResume.successful_env', ['propext', 'Classical.choice', 'Quot.sound']), ('Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingResume.reexport_self', ['propext']), ('Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingResume.coupled', ['propext', 'Classical.choice', 'Quot.sound']), ('Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingResume.finish', ['propext', 'Classical.choice', 'Quot.sound']), ('Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingResume.complete', ['propext', 'Classical.choice', 'Quot.sound']), ('Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingResume.Checks.available', ['propext', 'Classical.choice', 'Quot.sound']), ('Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingResume.Checks.source', ['propext', 'Classical.choice', 'Quot.sound']), ('Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingResume.Checks.extension', ['propext', 'Classical.choice', 'Quot.sound']), ('Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingResume.Checks.machine', ['propext', 'Classical.choice', 'Quot.sound']), ('Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingResume.Checks.addresses', ['propext', 'Classical.choice', 'Quot.sound']), ('Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingResume.Checks.specification', ['propext', 'Classical.choice', 'Quot.sound']), ('Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingResume.Checks.same_machine', ['propext', 'Classical.choice', 'Quot.sound']), ('Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingResume.Checks.observations', ['propext', 'Classical.choice', 'Quot.sound']), ('Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingResume.Checks.returned', ['propext', 'Classical.choice', 'Quot.sound']), ('Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingResume.Checks.source_result', ['propext', 'Classical.choice', 'Quot.sound']), ('Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingResume.Checks.source_all', ['propext', 'Classical.choice', 'Quot.sound']), ('Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingResume.Checks.outerReturned', ['propext', 'Classical.choice', 'Quot.sound']), ('Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingResume.Checks.caller_result', ['propext', 'Classical.choice', 'Quot.sound']), ('Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingResume.Checks.caller_identity', ['propext', 'Classical.choice', 'Quot.sound']), ('Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingResume.Checks.shallow', ['propext', 'Classical.choice', 'Quot.sound']), ('Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingResume.Checks.shallow_not_revert', ['propext', 'Classical.choice', 'Quot.sound']), ('Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingResume.Checks.still_needs_unwind', ['propext', 'Classical.choice', 'Quot.sound'])]
PATTERN=re.compile(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)")
def check(text,receipt):
 actual=[(n,[x.strip() for x in a.split(',')] if a else []) for n,a in PATTERN.findall(text)]
 if actual!=PINS: raise ValueError('missing/duplicate/order/changed axiom report')
 if PATTERN.sub('',text).strip(): raise ValueError('unexpected diagnostic/output')
 if not re.fullmatch(r'CAP_EVIDENCE\n12884901888\n0\n[0-9]+\n?',receipt): raise ValueError('incomplete/invalid actual cap receipt')
def render(pins):
 return '\n'.join("'%s' depends on axioms: [%s]"%(n,', '.join(a)) if a else "'%s' does not depend on any axioms"%n for n,a in pins)
def controls():
 receipt='CAP_EVIDENCE\n12884901888\n0\n1';good=render(PINS);check(good,receipt)
 ordered=PINS.copy();ordered[0],ordered[1]=ordered[1],ordered[0]
 changed=PINS.copy();changed[0]=(changed[0][0],['sorryAx'])
 for text,cap in [(render(PINS[1:]),receipt),(render(PINS+[PINS[0]]),receipt),(render(ordered),receipt),(render(changed),receipt),(good+'\nerror: failed',receipt),(good,receipt.replace('12884901888','1')),(good,receipt.replace('\n0\n1','\n1\n1')),(good,''),(good,receipt+'\n'+receipt),(good,'CAP_EVIDENCE\n1\n1\n1\n'+receipt),(good,'unexpected\n'+receipt)]:
  try:check(text,cap)
  except ValueError:pass
  else:raise AssertionError('accepted corruption')
 print('PASS:24 exact ordered reports; missing/duplicate/order/axiom/diagnostic/cap corruption controls')
if __name__=='__main__':
 if sys.argv[1:]==['--self-test']:controls()
 elif len(sys.argv)==3:
  check(Path(sys.argv[1]).read_text(),Path(sys.argv[2]).read_text());print('PASS:24 actual exact ordered reports and actual outer cap receipt')
 else:raise SystemExit('usage: --self-test | REPORT_LOG ACTUAL_OUTER_RECEIPT')
