#!/usr/bin/env python3
"""Reference-signature extension over byte-exact913-set guards. No build/write/start."""
import hashlib,json,sys,importlib.util
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
PRIOR_CHECKER_SHA='a4d5fb186754157dfe37bb1daf28a63664e87ecaf1e7cd412e2fe89aa7bffeea'
PRIOR_PINS_SHA='33f19ede9d742e6447d10e0bb763491173b16d03d9acbd51349d909948422966'
def validate_prior_standard(checker,pins):
 assert hashlib.sha256(checker).hexdigest()==PRIOR_CHECKER_SHA,'913 checker changed'
 assert hashlib.sha256(pins).hexdigest()==PRIOR_PINS_SHA,'26 pins changed'
 assert len(json.loads(pins))==26

def validate_prefixed_inputs(extra,prior):
 assert len(extra)==17 and not set(extra)&set(prior),'prefixed pins missing/overlap'
 assert all(k.startswith('Solidity.Lowering.V08.SourcePrefixedRethrowControls.') for k in extra),'foreign prefixed pin'
 for name,axes in extra.items():
  assert axes==sorted(set(axes)) and set(axes)<={'propext','Classical.choice','Quot.sound'},('nonstandard prefixed pin',name)
 return dict(prior)|extra
prior_path=ROOT/'scripts/v08-check-standard-rethrow.py'
validate_prior_standard(prior_path.read_bytes(),(ROOT/'scripts/v08-standard-rethrow-axiom-pins.json').read_bytes())
spec=importlib.util.spec_from_file_location('checked_prior_standard',prior_path)
prior_module=importlib.util.module_from_spec(spec)
previous_bytecode=sys.dont_write_bytecode
sys.dont_write_bytecode=True
try:spec.loader.exec_module(prior_module)
finally:sys.dont_write_bytecode=previous_bytecode
validate_base_inputs=prior_module.validate_base_inputs
validate_extra_inputs=prior_module.validate_extra_inputs
validate_prior_rethrow=prior_module.validate_prior_rethrow
validate_standard_inputs=prior_module.validate_standard_inputs
native=ROOT/'scripts/v08-check-public099.py'
program=prior_module.source
a=" expected=validate_standard_inputs(json.loads((ROOT/'scripts/v08-standard-rethrow-axiom-pins.json').read_bytes()),expected)"
b=a+"\n expected=validate_prefixed_inputs(json.loads((ROOT/'scripts/v08-prefixed-rethrow-axiom-pins.json').read_bytes()),expected)"
assert program.count(a)==1;program=program.replace(a,b)
compile(program,str(native),'exec')
exec(compile(program,str(native),'exec'),globals())
if __name__=='__main__':print('PASS:930 sets; all913 prior sets/checker/pin bytes unchanged;17 new reference-signature sets; all guards retained')
