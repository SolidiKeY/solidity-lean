#!/usr/bin/env python3
"""Additive standard-rethrow checker; retains all SHA-bound887-set guards.
No start/build/write occurs here.
"""
import hashlib,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
OLD_CHECKER_SHA='0862f1a6d0aec444d922839726e627e254144b34fe94ef4c104ca40334ba1662'
OLD_EXTRA_SHA='97bf4efb235d56181a79a684e31deb81ed7352f84c3d917a627376ce2e3d7954'
def validate_prior_rethrow(checker,pins):
 assert hashlib.sha256(checker).hexdigest()==OLD_CHECKER_SHA,'prior887 checker changed'
 assert hashlib.sha256(pins).hexdigest()==OLD_EXTRA_SHA,'prior29 pin bytes changed'
 assert len(json.loads(pins))==29

def validate_standard_inputs(extra,prior):
 assert len(extra)==26 and not set(extra)&set(prior),'standard pins missing/overlap'
 assert all(k.startswith(('Solidity.Lowering.V08.SourceStandardRethrow.','Solidity.Lowering.V08.SourceStandardRethrowControls.')) for k in extra),'foreign standard pin'
 for name,axes in extra.items():
  assert axes==sorted(set(axes)) and set(axes)<={'propext','Classical.choice','Quot.sound'},('nonstandard pin',name)
 return dict(prior)|extra

prior_program=ROOT/'scripts/v08-check-rethrow.py'
validate_prior_rethrow(prior_program.read_bytes(),(ROOT/'scripts/v08-rethrow-axiom-pins.json').read_bytes())
program=prior_program.read_text()
a=' expected=validate_extra_inputs(extra,expected)'
b=a+"\n expected=validate_standard_inputs(json.loads((ROOT/'scripts/v08-standard-rethrow-axiom-pins.json').read_bytes()),expected)"
assert program.count(a)==1;program=program.replace(a,b)
a='"core = [\'SourceRethrow\',"'
b='"core = [\'SourceStandardRethrow\',\'SourceRethrow\',"'
assert program.count(a)==1;program=program.replace(a,b)
compile(program,str(prior_program),'exec')
exec(compile(program,str(prior_program),'exec'),globals())
if __name__=='__main__':print('PASS:913 exact sets; all887 prior sets/checker/pin bytes unchanged;26 disjoint standard-rethrow sets; all native guards retained')
