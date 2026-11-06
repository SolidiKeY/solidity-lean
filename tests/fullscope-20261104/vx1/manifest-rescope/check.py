from pathlib import Path
import json, hashlib
r=Path(__file__).resolve().parents[4]
p=json.loads((Path(__file__).parent/'all30-proposal.json').read_text())
m=json.loads((r/'docs/solidity-features.json').read_text())
l=json.loads((r/'docs/solidity-upstream-inventory.json').read_text())
old={x['id']:x for x in m['features'] if x['scope']=='exclude'}
assert len(old)==30
assert hashlib.sha256((r/'docs/solidity-features.json').read_bytes()).hexdigest()==p['manifestSha256']
assert hashlib.sha256((r/'docs/solidity-upstream-inventory.json').read_bytes()).hexdigest()==p['ledgerSha256']
assert len(p['rows'])==30 and {x['id'] for x in p['rows']}==set(old)
for x in p['rows']:
 assert x['before']==old[x['id']]
 y=x['proposed']
 assert y['category']==x['before']['category'] and y['syntax']==x['before']['syntax']
 assert y['id']==x['id'] and y['scope']=='model' and y['current']=='missing'
 assert 'decision' not in y and y['requirement']
 assert y['localEvidence']==x['before']['localEvidence'] and y['upstream']==x['before']['upstream']
 assert x['obligationStatus']=='open'
 expected=[{'family':f,'symbol':s} for f,syms in l['symbols'].items() for s,ids in syms.items() if x['id'] in ids]
 assert p['upstreamReferences'][x['id']]==expected
assert set(p['upstreamReferences'])==set(old)
print('PASS:30 exact transitions; original evidence/provenance preserved; all ledger references covered; zero production admission claims')
