"""Select one frozen witness per inventoried field subvariant; no AST translation."""
from pathlib import Path
import collections,hashlib,json
owned=Path(__file__).resolve().parent;root=owned.parents[2]
bulk=owned/'artifacts/h68-bulk'
inventory=json.loads((bulk/'fixture-variants.json').read_text())
routes={r['nodeType']:r['route'] for r in json.loads((owned/'construct-reader-cases.json').read_text())['cases']}
cases=[]
for row in inventory['variants']:
 variant=row['variant'];witness=row['witnesses'][0]
 digest=hashlib.sha256(json.dumps(variant,sort_keys=True,separators=(',',':')).encode()).hexdigest()
 path=root/witness['fixture'];assert hashlib.sha256(path.read_bytes()).hexdigest()==witness['fixtureSha256']
 cases.append({'caseId':digest,'nodeType':variant['nodeType'],'route':routes[variant['nodeType']],'variant':variant,**witness})
assert len(cases)==inventory['variantCount']==806 and len({r['caseId'] for r in cases})==806
(bulk/'variant-reader-cases.json').write_text(json.dumps({'basis':inventory['basis'],'boundary':'One existing-corpus witness for each selected-field subvariant, including intentional mutations and unauthenticated compiler-header claims. Standalone reader observations only; not exhaustive syntax forms, source preservation or backend support.','cases':cases},indent=2)+'\n')
print(json.dumps({'cases':len(cases),'routes':dict(collections.Counter(r['route'] for r in cases))}))
