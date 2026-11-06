#!/usr/bin/env python3
"""Additive rethrow evidence extension over the byte-exact native099 checker.
All historical source/config/runtime/log/resource guards execute unchanged.
No Docker start/build/write occurs in this checker.
"""
import hashlib,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
PIN_SHA='bbf9497b64531610b2d778c27d288559d32198a9c49e84e4847513166670fb49'
NATIVE_SHA='fce0e4c877930ad58f0e842dc95b9d38d1558d28f800d916474f03a7e8af4a77'
def validate_base_inputs(pins,checker):
 assert hashlib.sha256(pins).hexdigest()==PIN_SHA,'prior858 pin bytes changed'
 assert hashlib.sha256(checker).hexdigest()==NATIVE_SHA,'native checker bytes changed'
 prior=json.loads(pins);assert len(prior)==858
 return prior
def validate_extra_inputs(extra,prior):
 assert len(extra)==29 and not set(extra)&set(prior),'extra pins overlap/missing'
 assert all(k.startswith(('Solidity.Lowering.V08.SourceRethrow.','Solidity.Lowering.V08.SourceRethrowControls.')) for k in extra),'foreign pin namespace'
 for name,axes in extra.items():
  assert axes==sorted(set(axes)) and set(axes)<={'propext','Classical.choice','Quot.sound'},('nonstandard extra pin',name)
 return dict(prior)|extra
native=ROOT/'scripts/v08-check-public099.py'
base=validate_base_inputs((ROOT/'scripts/v08-axiom-pins.json').read_bytes(),native.read_bytes())
source=native.read_text()
a="expected=json.loads((ROOT/'scripts/v08-axiom-pins.json').read_bytes())"
b="""expected=validate_base_inputs((ROOT/'scripts/v08-axiom-pins.json').read_bytes(),native.read_bytes())
 extra=json.loads((ROOT/'scripts/v08-rethrow-axiom-pins.json').read_bytes())
 expected=validate_extra_inputs(extra,expected)"""
assert source.count(a)==1;source=source.replace(a,b)
a='core = ['
assert source.count(a)==1;source=source.replace(a,"core = ['SourceRethrow',",1)
compile(source,str(native),'exec')
exec(compile(source,str(native),'exec'),globals())
if __name__=='__main__':print('PASS: all858 prior pin/checker bytes unchanged;29 new rethrow sets; unchanged native guards and new core boundary')
