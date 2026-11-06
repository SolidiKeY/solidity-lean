"""One standalone reader witness per frozen observed structural form.
No AST translation or inherited source/semantic support verdict is introduced.
"""
from pathlib import Path
from collections import Counter
import json,sys
sys.dont_write_bytecode=True
from corpus_packet import verified_corpus,sha
ROOT=Path(__file__).resolve().parents[3];OWNED=Path(__file__).resolve().parent
source,packet=verified_corpus();out=OWNED/'artifacts/corpus-readers';out.mkdir(exist_ok=True)
forms=json.loads((source/'forms.json').read_text());routes={r['nodeType']:r['route'] for r in json.loads((OWNED/'construct-reader-cases.json').read_text())['cases']}
knownYul={r['nodeType'] for r in json.loads((OWNED/'coverage-inventory.json').read_text())['yulConstructs']}
cache={};cases=[]
for row in forms:
 witness=row['witness'];fixture=ROOT/witness['fixture']
 if fixture not in cache:cache[fixture]=(sha(fixture),json.loads(fixture.read_text()))
 digest,node=cache[fixture];assert digest==witness['fixtureSha256']
 for part in witness['pointer'].split('/')[1:]:
  key=part.replace('~1','/').replace('~0','~');node=node[int(key)] if isinstance(node,list) else node[key]
 kind=row['form']['nodeType'];assert node['nodeType']==kind
 assert kind in routes or kind in knownYul
 cases.append({'caseId':row['formId'],'nodeType':kind,'route':routes.get(kind,'none'),**witness})
assert len(cases)==len({r['caseId'] for r in cases})==1926
(out/'cases.json').write_text(json.dumps({'basis':packet['basis'],'censusArchiveSha256':packet['archiveSha256'],'boundary':'One exact witness per observed immediate-field form. Input corpus includes intentional mutations and retained raw/normalized ASTs. Outcomes are standalone decoder observations,not complete semantics or source/backend preservation.','cases':cases},indent=2)+'\n')
print(json.dumps({'cases':len(cases),'routes':dict(Counter(r['route'] for r in cases)),'censusArchiveSha256':packet['archiveSha256']}))
