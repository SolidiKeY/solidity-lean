#!/usr/bin/env python3
"""Exact-head receipt using repository gates and the frozen local-root policy."""
import json,os,pathlib,shlex,subprocess,sys
root=pathlib.Path(__file__).resolve().parents[3];os.chdir(root)
out=pathlib.Path(sys.argv[1]).resolve();out.mkdir(parents=True,exist_ok=True)
env=dict(os.environ,GATE_LOGS=str(out),GATE_BASE='6f3eedf0788ee1f8a3bcf230558c712ecdca04d5',
 H28_EVIDENCE_DIR=str(out),SOLKEY_RULES=str(root/'tests/migration/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key'),
 SOLKEY_EXAMPLES=str(root/'tests/migration/solkey/keyext.solidity.examples'))
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],text=True)
files=['Solidity/Calculus/SolkeyAgreementH28/Freshness.lean','tests/h28-sol/solkey-ports/Controls.lean','tests/h28-sol/solkey-ports/Ledger.lean','tests/h28-sol/solkey-ports/Runtime.lean']
for f in files:
 assert pathlib.Path(f).read_bytes()==subprocess.check_output(['git','show','96780494a943f45035d3d8164321bff6c30d3be7:'+f])
subprocess.run(['bash','scripts/coord-tools/gate.sh','per-file',*files],env=env,check=True)
checks=[
 ('full-build-exact-head',['lake','build','Solidity','SolidityExamples','solkeycheck','solidity-lean','SolkeyTestSuite','Solidity.Calculus.SolkeyAgreementH28.Freshness']),
 ('trust-exact-head',['bash','scripts/check-trust.sh']),
 ('orphans-exact-head',['node','scripts/check-orphans.mjs','--allow','tests/h28-sol/solkey-ports/registration.allow']),
 ('layers-exact-head',['node','scripts/check-layers.mjs']),
 ('docs-exact-head',['bash','scripts/check-doc-paths.sh']),
 ('axiom-pins-exact-head',['node','scripts/check-axiom-pins.mjs']),
 ('testsuite-exact-head',['bash','scripts/check-testsuite.sh']),
 ('automatic-exact-head',['node','scripts/check-automatic.mjs','--strict']),
 ('corpus-exact-head',['bash','scripts/check-corpus.sh']),
 ('sort-exact-head',['lake','exe','solkeycheck','--key',env['SOLKEY_RULES']]),
 ('selected-exact-head',[sys.executable,'tests/h28-sol/solkey-ports/accept.py'])]
for name,cmd in checks:
 print('START',name,flush=True)
 result=subprocess.run([sys.executable,'tests/h28-sol/solkey-ports/run.py',name,*cmd],env=env)
 data=json.loads((out/(name+'.json')).read_text())
 assert data['head']==head
 with (out/'gates.tsv').open('a') as f:
  f.write(('PASS' if result.returncode==0 else 'FAIL')+'\t'+name+'\t'+str(data['seconds'])+'\t'+str(out/(name+'.log'))+'\t'+shlex.join(cmd)+'\n')
 if result.returncode: sys.exit(result.returncode)
assert (out/'HEAD').read_text().strip()==head
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],text=True)
print('EXACT_HEAD_ACCEPTANCE_PASS '+head)
