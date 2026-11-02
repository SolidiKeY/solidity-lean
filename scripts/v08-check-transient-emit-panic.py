#!/usr/bin/env python3
"""Reached argument panic extension; exact old guards, no build/write/start."""
import hashlib,json,sys,importlib.util
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
PRIOR_EMIT_CHECKER_SHA='9bd45067d3f21f3585a254f7f80cf24e62f9596789c5d49fbdd85fc4fa233562'
PRIOR_EMIT_PINS_SHA='e1b160d2579533adc66a463de9d52e5ea3fba9afcabdb7bd9548458c9f016a22'
def validate_prior_emit(checker,pins):
 assert hashlib.sha256(checker).hexdigest()==PRIOR_EMIT_CHECKER_SHA,'989 checker changed'
 assert hashlib.sha256(pins).hexdigest()==PRIOR_EMIT_PINS_SHA,'26 prior pins changed'
 assert len(json.loads(pins))==26

def validate_transient_emit_panic_inputs(extra,prior):
 assert len(extra)==15 and not set(extra)&set(prior),'panic pins missing/overlap'
 assert all(k.startswith('Solidity.Lowering.V08.SourceTransientEmitPanicControls.') for k in extra),'foreign panic pin'
 for name,axes in extra.items():
  assert axes==sorted(set(axes)) and set(axes)<={'propext','Classical.choice','Quot.sound'},('nonstandard panic pin',name)
 return dict(prior)|extra
prior_path=ROOT/'scripts/v08-check-transient-emit.py'
validate_prior_emit(prior_path.read_bytes(),(ROOT/'scripts/v08-transient-emit-axiom-pins.json').read_bytes())
spec=importlib.util.spec_from_file_location('checked_prior_emit',prior_path)
prior_module=importlib.util.module_from_spec(spec)
previous_bytecode=sys.dont_write_bytecode
sys.dont_write_bytecode=True
try:spec.loader.exec_module(prior_module)
finally:sys.dont_write_bytecode=previous_bytecode
for name in ['validate_base_inputs','validate_extra_inputs','validate_prior_rethrow','validate_standard_inputs','validate_prior_standard','validate_prefixed_inputs','validate_prior_prefixed','validate_transient_rethrow_inputs','validate_prior_transient','validate_transient_mixed_inputs','validate_prior_mixed','validate_transient_emit_inputs']:
 globals()[name]=getattr(prior_module,name)
native=ROOT/'scripts/v08-check-public099.py'
program=prior_module.program
a=" expected=validate_transient_emit_inputs(json.loads((ROOT/'scripts/v08-transient-emit-axiom-pins.json').read_bytes()),expected)"
b=a+"\n expected=validate_transient_emit_panic_inputs(json.loads((ROOT/'scripts/v08-transient-emit-panic-axiom-pins.json').read_bytes()),expected)"
assert program.count(a)==1;program=program.replace(a,b)
exec(compile(program,str(native),'exec'),globals())
if __name__=='__main__':print('PASS:1004 exact sets; all989 prior sets/guards unchanged;15 new actual reached panic clauses')
