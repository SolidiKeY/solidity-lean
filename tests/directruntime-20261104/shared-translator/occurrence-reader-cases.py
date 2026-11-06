"""All frozen AST occurrences, using existing standalone reader routes only."""
from pathlib import Path
from collections import Counter
import hashlib,json,sys
sys.dont_write_bytecode=True
from corpus_packet import verified_corpus
ROOT=Path(__file__).resolve().parents[3];OWNED=Path(__file__).resolve().parent
source,packet=verified_corpus();out=OWNED/'artifacts/occurrence-readers';out.mkdir(exist_ok=True)
routes={r['nodeType']:r['route'] for r in json.loads((OWNED/'construct-reader-cases.json').read_text())['cases']}
yul={r['nodeType'] for r in json.loads((OWNED/'coverage-inventory.json').read_text())['yulConstructs']}
cases=[];seen=set()
for line in (source/'nodes.jsonl').open():
 node=json.loads(line);kind=node['nodeType'];assert kind in routes or kind in yul
 ident=hashlib.sha256(json.dumps([node['fixture'],node['fixtureSha256'],node['pointer']],separators=(',',':')).encode()).hexdigest()
 assert ident not in seen;seen.add(ident)
 cases.append({'caseId':ident,'nodeType':kind,'route':routes.get(kind,'none'),'fixture':node['fixture'],'fixtureSha256':node['fixtureSha256'],'pointer':node['pointer'],'nodeSha256':node['nodeSha256'],'formId':node['formId']})
assert len(cases)==packet['counts']['nodes']==55218
(out/'cases.json').write_text(json.dumps({'basis':packet['basis'],'censusArchiveSha256':packet['archiveSha256'],'cases':cases,'boundary':'Every occurrence in a fixed finite corpus;standalone decoding/printing only,not full-context elaboration,proof closure or source/backend preservation.'},indent=2)+'\n')
print(json.dumps({'cases':len(cases),'routes':dict(Counter(r['route'] for r in cases))}))
