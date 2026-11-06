#!/usr/bin/env python3
"""Validate C3 proof receipts, full new theorem axiom census and vector provenance.
No proof credit is inferred from the external EVM results.
"""
import json,re
from pathlib import Path
import bounded_lean, verify_census

def main():
 repo=Path.cwd(); root=Path('/workspace/h62-audit-g25-artifacts'); cache=root/'audit-v424'
 tests=repo/'tests/h62/item2/audit-g25-scalar-lowering'; prefix='tests.h62.item2.audit-g25-scalar-lowering.'
 modules=['ScalarTotality','ClosedTotality','EnvironmentTotality','SuccessControls','BoundaryVectors']
 expected=[]
 for module in modules:
  source=(tests/(module+'.lean')).read_text()
  ns=re.search(r'^namespace (\S+)',source,re.M)[1]
  expected += [ns+'.'+name for name in re.findall(r'^theorem (\S+)',source,re.M)]
 commands=re.findall(r'^#print axioms (\S+)',(tests/'SuccessAxioms.lean').read_text(),re.M)
 if commands!=expected: raise ValueError('new theorem axiom census does not reproduce')
 log=cache/'logs'/(prefix+'SuccessAxioms.log')
 required={prefix+'BoundaryVectors':[root/'evidence/boundary-vectors.json'],prefix+'SuccessAxioms':[log]}
 receipts=verify_census.validate_receipts(repo,cache,Path('/workspace/.setup/tools/lean-4.24.0-linux'),required,[prefix+'SuccessAxioms'])
 rows=re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^]]*)\])",log.read_text(),re.S)
 if len(rows)!=len(expected) or {n for n,_ in rows}!=set(expected): raise ValueError('axiom output census differs')
 axioms={n:[x.strip() for x in xs.split(',') if x.strip()] for n,xs in rows}
 if any(set(xs)-{'propext','Classical.choice','Quot.sound'} for xs in axioms.values()): raise ValueError('unexpected trust dependency')
 reference=json.loads((root/'evidence/reference-boundaries.json').read_text())
 vector_sha=bounded_lean.digest_file(root/'evidence/boundary-vectors.json')
 if reference['vectorSha256']!=vector_sha or reference['status']!='pass' or len(reference['cases'])!=6 or any(x['status']!='pass' for x in reference['cases']):
  raise ValueError('finite reference acceptance/provenance differs')
 report={'status':'pass','public_theorems':len(expected),'validated_compilation_receipts':receipts,
  'axiom_output_sha256':bounded_lean.digest_file(log),'axioms':axioms,
  'vector_sha256':vector_sha,'external_reference_cases':6,'negative_harness_controls':reference['negativeHarnessControls'],
  'proof_boundary':'Kernel proofs concern unchanged intrinsic source and gasless component contracts. Six finite EVM runs are external tests, not compiler correctness or gas/fork proofs.'}
 (root/'evidence/success-evidence.json').write_text(json.dumps(report,indent=2)+'\n')
 print(f"PASS: {len(expected)} new public theorem axiom reports; {receipts} valid proof receipts; 6 external cases separately labeled")

if __name__=='__main__': main()
