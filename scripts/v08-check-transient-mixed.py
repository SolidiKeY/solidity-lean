#!/usr/bin/env python3
"""Mixed effecting ABI after actual transient prefix; all old guards byte-bound."""
import hashlib,json,sys,importlib.util
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
PRIOR_TRANSIENT_CHECKER_SHA='c4eb258899ec70e0c8bc7a0558516c0624f6591223bbd5a81367a0b22e9cdcdd'
PRIOR_TRANSIENT_PINS_SHA='ee6041d02cfa1ed58b3c31242c205922abb2c81b7139e81268ada539876539e5'
def validate_prior_transient(checker,pins):
 assert hashlib.sha256(checker).hexdigest()==PRIOR_TRANSIENT_CHECKER_SHA,'949 checker changed'
 assert hashlib.sha256(pins).hexdigest()==PRIOR_TRANSIENT_PINS_SHA,'19 prior pins changed'
 assert len(json.loads(pins))==19

def validate_transient_mixed_inputs(extra,prior):
 assert len(extra)==14 and not set(extra)&set(prior),'mixed pins missing/overlap'
 assert all(k.startswith('Solidity.Lowering.V08.SourceTransientMixedRethrowControls.') for k in extra),'foreign mixed pin'
 for name,axes in extra.items():
  assert axes==sorted(set(axes)) and set(axes)<={'propext','Classical.choice','Quot.sound'},('nonstandard mixed pin',name)
 return dict(prior)|extra
prior_path=ROOT/'scripts/v08-check-transient-rethrow.py'
validate_prior_transient(prior_path.read_bytes(),(ROOT/'scripts/v08-transient-rethrow-axiom-pins.json').read_bytes())
spec=importlib.util.spec_from_file_location('checked_prior_transient',prior_path)
prior_module=importlib.util.module_from_spec(spec)
previous_bytecode=sys.dont_write_bytecode
sys.dont_write_bytecode=True
try:spec.loader.exec_module(prior_module)
finally:sys.dont_write_bytecode=previous_bytecode
for name in ['validate_base_inputs','validate_extra_inputs','validate_prior_rethrow','validate_standard_inputs','validate_prior_standard','validate_prefixed_inputs','validate_prior_prefixed','validate_transient_rethrow_inputs']:
 globals()[name]=getattr(prior_module,name)
native=ROOT/'scripts/v08-check-public099.py'
program=prior_module.program
a=" expected=validate_transient_rethrow_inputs(json.loads((ROOT/'scripts/v08-transient-rethrow-axiom-pins.json').read_bytes()),expected)"
b=a+"\n expected=validate_transient_mixed_inputs(json.loads((ROOT/'scripts/v08-transient-mixed-axiom-pins.json').read_bytes()),expected)"
assert program.count(a)==1;program=program.replace(a,b)
exec(compile(program,str(native),'exec'),globals())
if __name__=='__main__':print('PASS:963 exact sets; all949 prior sets/guards unchanged;14 new reached mixed-argument sets')
