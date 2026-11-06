#!/usr/bin/env python3
"""Transient statement/rethrow extension; all prior guards SHA-bound, no build/write/start."""
import hashlib,json,sys,importlib.util
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
PRIOR_PREFIX_CHECKER_SHA='b599179906a7a68cc638c1daeebd5e5823d699a2dd1d38245e76ebc34364edad'
PRIOR_PREFIX_PINS_SHA='26194dfe21dc1be940738c4ea939d2fff968f4e1bc627a0f08416fed880397c2'
def validate_prior_prefixed(checker,pins):
 assert hashlib.sha256(checker).hexdigest()==PRIOR_PREFIX_CHECKER_SHA,'930 checker changed'
 assert hashlib.sha256(pins).hexdigest()==PRIOR_PREFIX_PINS_SHA,'17 prior pins changed'
 assert len(json.loads(pins))==17

def validate_transient_rethrow_inputs(extra,prior):
 assert len(extra)==19 and not set(extra)&set(prior),'transient pins missing/overlap'
 assert all(k.startswith('Solidity.Lowering.V08.SourceTransientRethrowControls.') for k in extra),'foreign transient pin'
 for name,axes in extra.items():
  assert axes==sorted(set(axes)) and set(axes)<={'propext','Classical.choice','Quot.sound'},('nonstandard transient pin',name)
 return dict(prior)|extra
prior_path=ROOT/'scripts/v08-check-prefixed-rethrow.py'
validate_prior_prefixed(prior_path.read_bytes(),(ROOT/'scripts/v08-prefixed-rethrow-axiom-pins.json').read_bytes())
spec=importlib.util.spec_from_file_location('checked_prior_prefixed',prior_path)
prior_module=importlib.util.module_from_spec(spec)
previous_bytecode=sys.dont_write_bytecode
sys.dont_write_bytecode=True
try:spec.loader.exec_module(prior_module)
finally:sys.dont_write_bytecode=previous_bytecode
for name in ['validate_base_inputs','validate_extra_inputs','validate_prior_rethrow','validate_standard_inputs','validate_prior_standard','validate_prefixed_inputs']:
 globals()[name]=getattr(prior_module,name)
native=ROOT/'scripts/v08-check-public099.py'
program=prior_module.program
a=" expected=validate_prefixed_inputs(json.loads((ROOT/'scripts/v08-prefixed-rethrow-axiom-pins.json').read_bytes()),expected)"
b=a+"\n expected=validate_transient_rethrow_inputs(json.loads((ROOT/'scripts/v08-transient-rethrow-axiom-pins.json').read_bytes()),expected)"
assert program.count(a)==1;program=program.replace(a,b)
exec(compile(program,str(native),'exec'),globals())
if __name__=='__main__':print('PASS:949 exact sets; all930 prior sets/guards unchanged;19 new actual transient/ABI/rethrow sets')
