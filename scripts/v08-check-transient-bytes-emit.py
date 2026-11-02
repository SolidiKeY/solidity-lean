#!/usr/bin/env python3
"""Valid memory-bytes event evidence extension; prior guards SHA-bound, no build/write/start."""
import hashlib,json,sys,importlib.util
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
PRIOR_PANIC_CHECKER_SHA='ae45bef2d61bdb9d9523e1e91abd09c46bb81d1adcbdc1f81f2be1d9e52228df'
PRIOR_PANIC_PINS_SHA='7272b5aee0f185561b6773fe6cf74c4a675cdd2b0bb828e0fe82309915945209'
def validate_prior_emit_panic(checker,pins):
 assert hashlib.sha256(checker).hexdigest()==PRIOR_PANIC_CHECKER_SHA,'1004 checker changed'
 assert hashlib.sha256(pins).hexdigest()==PRIOR_PANIC_PINS_SHA,'15 prior pins changed'
 assert len(json.loads(pins))==15

def validate_transient_bytes_inputs(extra,prior):
 assert len(extra)==28 and not set(extra)&set(prior),'bytes pins missing/overlap'
 assert all(k.startswith('Solidity.Lowering.V08.SourceTransientBytesEmitControls.') for k in extra),'foreign bytes pin'
 for name,axes in extra.items():
  assert axes==sorted(set(axes)) and set(axes)<={'propext','Classical.choice','Quot.sound'},('nonstandard bytes pin',name)
 return dict(prior)|extra
prior_path=ROOT/'scripts/v08-check-transient-emit-panic.py'
validate_prior_emit_panic(prior_path.read_bytes(),(ROOT/'scripts/v08-transient-emit-panic-axiom-pins.json').read_bytes())
spec=importlib.util.spec_from_file_location('checked_prior_emit_panic',prior_path)
prior_module=importlib.util.module_from_spec(spec)
previous_bytecode=sys.dont_write_bytecode
sys.dont_write_bytecode=True
try:spec.loader.exec_module(prior_module)
finally:sys.dont_write_bytecode=previous_bytecode
for name in ['validate_base_inputs','validate_extra_inputs','validate_prior_rethrow','validate_standard_inputs','validate_prior_standard','validate_prefixed_inputs','validate_prior_prefixed','validate_transient_rethrow_inputs','validate_prior_transient','validate_transient_mixed_inputs','validate_prior_mixed','validate_transient_emit_inputs','validate_prior_emit','validate_transient_emit_panic_inputs']:
 globals()[name]=getattr(prior_module,name)
native=ROOT/'scripts/v08-check-public099.py'
program=prior_module.program
a=" expected=validate_transient_emit_panic_inputs(json.loads((ROOT/'scripts/v08-transient-emit-panic-axiom-pins.json').read_bytes()),expected)"
b=a+"\n expected=validate_transient_bytes_inputs(json.loads((ROOT/'scripts/v08-transient-bytes-emit-axiom-pins.json').read_bytes()),expected)"
assert program.count(a)==1;program=program.replace(a,b)
exec(compile(program,str(native),'exec'),globals())
if __name__=='__main__':print('PASS:1032 exact sets; all1004 prior sets/guards unchanged;28 new valid memory-bytes event clauses')
