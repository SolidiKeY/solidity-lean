#!/usr/bin/env python3
"""The exact reviewable proof/accounting inputs, excluding gate outputs/caches."""
import hashlib,json,pathlib
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[2]
DATA=['inventory.json','registration.json','premise-expansions.json','public-contracts.json','open-premises.json','resource-findings.json','statement-analysis.json','signature-names.json','axiom-pins.json']
RUNTIME=['runtime/bin/lake','runtime/bin/node','runtime/keysort','runtime/accounting','runtime/measure.py','runtime/workers.py','runtime/check-layout.py','runtime/lakefile.toml']
def inputs():
 files=list((HERE/'lean/Solidity/Assurance/NonVacuityH28').glob('*.lean'))+list(HERE.glob('*.py'))
 files += [HERE/x for x in DATA+RUNTIME]
 return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(set(files))}
if __name__=='__main__':print(json.dumps({'sha256':inputs()},indent=2))
