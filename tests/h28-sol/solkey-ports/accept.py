#!/usr/bin/env python3
"""Exhaustive acceptance of the two selected clauses, without other rule inventory."""
import hashlib,json,pathlib,re,subprocess,sys
root=pathlib.Path(__file__).resolve().parents[3]
base='6f3eedf0788ee1f8a3bcf230558c712ecdca04d5'
p=root/'tests/h28-sol/solkey-ports'
def sha(b): return hashlib.sha256(b).hexdigest()
def git(*a): return subprocess.check_output(['git',*a],cwd=root,text=True).strip()
pin=json.loads((p/'pin.json').read_text())
assert pin['commit']==json.loads((root/'tests/migration/solkey.pin.json').read_text())['commit']
snapshot=json.loads((root/'tests/migration/solkey/snapshot.json').read_text())
assert snapshot['commit']==pin['commit']
assert len(pin['rules'])==2
assert [r['clause'] for r in pin['rules']]==['newFromWrite','newFromCopySt']
for r in pin['rules']:
 b=(root/r['file']).read_bytes();body=(p/(r['clause']+'.key')).read_bytes()
 assert sha(b)==r['source_sha256'] and sha(body)==r['body_sha256']
 assert body.decode()==r['body'] and b.count(body)==1
 assert b[:b.index(body)].count(b'\n')+1==r['start_line']
 rel=r['file'].removeprefix('tests/migration/solkey/')
 assert next(f['sha256'] for f in snapshot['files'] if f['path']==rel)==sha(b)
assert pin['map_rows']==(root/'docs/lean-key-rule-map.md').read_text().splitlines()[647:650]
assert git('branch','--show-current')=='codex/solidity-h28-sol-20261104/solkey-ports'
subprocess.run(['git','merge-base','--is-ancestor',base,'HEAD'],cwd=root,check=True)
# Adopt only the coordinator's explicitly published integration, preserving
# the original frozen source provenance and the lane's exclusive delta.
approved_publications=('70845978ab616a63b13d0dee8b31b28893ccf591',
                       'e6849d3bdf516099d20c33d3581d523449764018',
                       '9584f9e7df09f638d9e0cb8930501d1660aa4b2f',
                       'f77cf60d3cea8f7f1db8db29cc027532b0cd3fce',
                       '8495f1deb0a95dd6b9301822d8649ab76b217681')
scope_base=next((published for published in approved_publications
 if subprocess.run(['git','merge-base','--is-ancestor',published,'HEAD'],cwd=root,
                   stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode==0),base)
adopted=scope_base!=base
changed=set(git('diff','--name-only',scope_base).splitlines())|set(git('ls-files','--others','--exclude-standard').splitlines())
assert all(f.startswith(('Solidity/Calculus/SolkeyAgreementH28/','tests/h28-sol/solkey-ports/')) or f=='docs/feature-work/h28-solkey-ports.md' for f in changed)
source=root/'Solidity/Calculus/SolkeyAgreementH28/Freshness.lean'
controls=p/'Controls.lean'
names=re.findall(r'^theorem ([\w.]+)',controls.read_text(),re.M)
cov=json.loads((p/'coverage.json').read_text())
assert set(names)=={n for group in cov.values() for n in group} and len(names)==46
for row in json.loads((p/'declarations.json').read_text()):
 assert row['source'] in (root/row['file']).read_text() and sha(row['source'].encode())==row['sha256']
assert len(re.findall(r'^theorem ',source.read_text(),re.M))==15
reg=json.loads((p/'registration.json').read_text())
assert [r['module'] for r in reg['modules']]==(p/'registration.allow').read_text().splitlines()
# Assignment explicitly freezes generated roots; audit the exact integration delta.
r=subprocess.run(['bash','scripts/coord-tools/register.sh','--check'],cwd=root,text=True,capture_output=True)
registered='import '+reg['modules'][0]['module'] in (root/'Solidity.lean').read_text().splitlines()
if adopted:
 assert registered and r.returncode==0 and not r.stdout,(r.stdout,r.stderr)
else:
 assert not registered and r.returncode==1 and r.stdout.splitlines()==['Solidity.lean: missing import '+reg['modules'][0]['module']],(r.stdout,r.stderr)
if '--static' not in sys.argv:
 for name in ['controls-kernel-final','ledger-kernel-final','keysort-runtime-final','full-build','trust','orphans','layers','doc-paths-final','axiom-pins','testsuite','corpus','automatic-strict','sort-conformance']:
  d=json.loads((p/'evidence'/(name+'.json')).read_text());assert d['exit']==0,(name,d['exit'])
  assert d['memory.max']=='12884901888' and d['memory.swap.max']=='0'
  for f,h in d['source_sha256'].items(): assert sha((root/f).read_bytes())==h,(name,f)
 for path,log,namespace in [(source,'ledger-kernel-final','Solidity.SolkeyAgreementH28.'),(controls,'controls-kernel-final','Solidity.SolkeyAgreementH28.Controls.')]:
  out=(p/'evidence'/(log+'.log')).read_text()
  for n in re.findall(r'^theorem ([\w.]+)',path.read_text(),re.M):
   full=namespace+n
   assert full+' :' in out or '@'+full+' :' in out,full
   m=re.search("'"+re.escape(full)+r"' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",out)
   assert m,full
   assert not m[2] or set(m[2].split(', '))<={'propext','Quot.sound','Classical.choice'}
 ledger=json.loads((p/'trust-ledger.json').read_text())
 assert len(ledger)==61
 for row in ledger:
  assert sha(row['compiler_statement'].encode())==row['statement_sha256']
  assert sha((root/row['compiler_log']).read_bytes())==row['compiler_log_sha256']
  assert row['compiler_statement'] in (root/row['compiler_log']).read_text()
  assert set(row['axioms'])<={'propext','Quot.sound'}
 for f,h in json.loads((p/'evidence/frozen-inputs.json').read_text()).items():
  assert sha((root/f).read_bytes())==h
 assert 'parsed 377 taclets, 131 read-bearing, table covers 131' in (p/'evidence/sort-conformance.log').read_text()
 assert 'KeySort runtime: PASS'  in (p/'evidence/keysort-runtime-final.log').read_text()
print('SELECTED_ACCEPTANCE_PASS' if '--static' not in sys.argv else 'SELECTED_STATIC_PASS')
print('2 exact pinned clauses; 15 universal/consequence theorems; 46 complete kernel controls; scope and local registration verified')
