"""Compare source-anchored observations from two actual Reader configurations."""
from pathlib import Path
from collections import Counter
import hashlib,json
owned=Path(__file__).resolve().parent;root=owned.parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
suites=[]
for prefix in ['', 'fresh-']:
 paths=[owned/(prefix+'construct-reader-matrix.json'),owned/('composed-'+prefix+'construct-reader-matrix.json'),owned/(prefix+'construct-reader-cases.json')]
 old,new,cases=[json.loads(p.read_text()) for p in paths];cases=cases['cases']
 assert len(old)==len(new)==len(cases)==57
 before={r['nodeType']:r for r in old};after={r['nodeType']:r for r in new};anchors={r['nodeType']:r for r in cases}
 assert len(before)==len(after)==len(anchors)==57 and before.keys()==after.keys()==anchors.keys()
 changes=[]
 for kind,row in after.items():
  prior=before[kind];case=anchors[kind];assert row['route']==prior['route']==case['route']
  assert row['producerExpression']==prior['producerExpression']
  assert sha(root/case['fixture'])==case['fixtureSha256']
  if row['route']=='none':assert row['natural']==prior['natural']=={'status':'not-standalone'} and row['unknownRoot'] is None
  else:assert row['unknownRoot']['status']==prior['unknownRoot']['status']=='refused'
  if row['natural']!=prior['natural']:
   changes.append({'nodeType':kind,'route':row['route'],'before':prior['natural'],'composed':row['natural'],'sourceIdentity':{k:case.get(k) for k in ['fixture','fixtureSha256','pointer','nodeId','src','compilerVersion','compilerSha256']}})
 suites.append({'suite':prefix or 'existing','inputs':[{'path':str(p.relative_to(root)),'sha256':sha(p)} for p in paths],'defaultCounts':dict(Counter(r['natural']['status'] for r in old)),'composedCounts':dict(Counter(r['natural']['status'] for r in new)),'unknownRootRefusals':sum(r['route']!='none' for r in new),'changes':changes})
result={'boundary':'Whole selected witness decoding, followed by existing metadata checks for expressions/statements and public function/contract checks. Child failures can dominate. Reader configurations use the actual Shared.reader and Shared.executableReader; neither decoding success nor reason differences establish intrinsic closure, identity adequacy, source preservation or backend support.','suites':suites}
(owned/'reader-comparison.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps([{'suite':s['suite'],'default':s['defaultCounts'],'composed':s['composedCounts'],'changedWitnesses':len(s['changes'])} for s in suites]))
