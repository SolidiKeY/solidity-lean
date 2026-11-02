#!/usr/bin/env python3
"""Reached-state Source emit extension; all prior guards SHA-bound, no build/write/start."""
import hashlib,json,sys,importlib.util
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
PRIOR_MIXED_CHECKER_SHA='b04a833b258d424479a289aac832acc772220d7b3f4156f97d03394c8a0f59c1'
PRIOR_MIXED_PINS_SHA='a8d5d93c2c5d67fc042c7d9a93344e2885c9341831ed22e236c8447b270a6e37'
def validate_prior_mixed(checker,pins):
 assert hashlib.sha256(checker).hexdigest()==PRIOR_MIXED_CHECKER_SHA,'963 checker changed'
 assert hashlib.sha256(pins).hexdigest()==PRIOR_MIXED_PINS_SHA,'14 prior pins changed'
 assert len(json.loads(pins))==14

def validate_transient_emit_inputs(extra,prior):
 assert len(extra)==26 and not set(extra)&set(prior),'emit pins missing/overlap'
 assert all(k.startswith('Solidity.Lowering.V08.SourceTransientEmitControls.') for k in extra),'foreign emit pin'
 for name,axes in extra.items():
  assert axes==sorted(set(axes)) and set(axes)<={'propext','Classical.choice','Quot.sound'},('nonstandard emit pin',name)
 return dict(prior)|extra
prior_path=ROOT/'scripts/v08-check-transient-mixed.py'
validate_prior_mixed(prior_path.read_bytes(),(ROOT/'scripts/v08-transient-mixed-axiom-pins.json').read_bytes())
spec=importlib.util.spec_from_file_location('checked_prior_mixed',prior_path)
prior_module=importlib.util.module_from_spec(spec)
previous_bytecode=sys.dont_write_bytecode
sys.dont_write_bytecode=True
try:spec.loader.exec_module(prior_module)
finally:sys.dont_write_bytecode=previous_bytecode
for name in ['validate_base_inputs','validate_extra_inputs','validate_prior_rethrow','validate_standard_inputs','validate_prior_standard','validate_prefixed_inputs','validate_prior_prefixed','validate_transient_rethrow_inputs','validate_prior_transient','validate_transient_mixed_inputs']:
 globals()[name]=getattr(prior_module,name)
native=ROOT/'scripts/v08-check-public099.py'
program=prior_module.program
a=" expected=validate_transient_mixed_inputs(json.loads((ROOT/'scripts/v08-transient-mixed-axiom-pins.json').read_bytes()),expected)"
b=a+"\n expected=validate_transient_emit_inputs(json.loads((ROOT/'scripts/v08-transient-emit-axiom-pins.json').read_bytes()),expected)"
assert program.count(a)==1;program=program.replace(a,b)
exec(compile(program,str(native),'exec'),globals())
if __name__=='__main__':print('PASS:989 exact sets; all963 prior sets/guards unchanged;26 new reached emit clauses')
