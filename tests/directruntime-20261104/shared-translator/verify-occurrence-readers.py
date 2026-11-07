"""Verify all occurrence witnesses and their optional frozen reader outcomes.
Full occurrence accounting is not a source/type/lexical correctness proof.
"""
from pathlib import Path
from collections import Counter
import argparse,hashlib,json,sys
sys.dont_write_bytecode=True
from corpus_packet import verified_corpus,sha
parser=argparse.ArgumentParser();parser.add_argument('--cases-only',action='store_true');parser.add_argument('--capture-summary',action='store_true');args=parser.parse_args()
ROOT=Path(__file__).resolve().parents[3];OWNED=Path(__file__).resolve().parent
source,packet=verified_corpus();out=OWNED/'artifacts/occurrence-readers'
casePacket=json.loads((out/'cases.json').read_text());cases=casePacket['cases']
assert casePacket['basis']==packet['basis'] and casePacket['censusArchiveSha256']==packet['archiveSha256']
assert len(cases)==packet['counts']['nodes']==55218, 'occurrence count mismatch'
routes={r['nodeType']:r['route'] for r in json.loads((OWNED/'construct-reader-cases.json').read_text())['cases']}
cache={};seen=set();kinds=Counter();documents=Counter();formIds=set()
for case,line in zip(cases,(source/'nodes.jsonl').open(),strict=True):
 row=json.loads(line)
 for field in ['nodeType','fixture','fixtureSha256','pointer','nodeSha256','formId']:assert case[field]==row[field], 'occurrence witness field mismatch: '+field
 ident=hashlib.sha256(json.dumps([row['fixture'],row['fixtureSha256'],row['pointer']],separators=(',',':')).encode()).hexdigest()
 assert case['caseId']==ident and ident not in seen, 'occurrence identity mismatch';seen.add(ident)
 assert case['route']==routes.get(case['nodeType'],'none'), 'occurrence route mismatch'
 path=ROOT/case['fixture']
 if path not in cache:cache[path]=(sha(path),json.loads(path.read_text()))
 digest,node=cache[path];assert digest==case['fixtureSha256']
 for part in case['pointer'].split('/')[1:]:
  key=part.replace('~1','/').replace('~0','~');node=node[int(key)] if isinstance(node,list) else node[key]
 assert node['nodeType']==case['nodeType']
 assert hashlib.sha256(json.dumps(node,sort_keys=True,separators=(',',':'),ensure_ascii=True).encode()).hexdigest()==case['nodeSha256']
 kinds[case['nodeType']]+=1;documents[case['fixture']]+=1;formIds.add(case['formId'])
census=json.loads((source/'summary.json').read_text())
assert dict(kinds)==census['nodesByKind'] and len(documents)==packet['counts']['documents'] and len(formIds)==packet['counts']['forms']
result={'cases':len(cases),'documents':len(documents),'kinds':len(kinds),'forms':len(formIds),'routes':dict(Counter(c['route'] for c in cases)),'boundary':'Every frozen AST occurrence/pointer/hash,not every semantic context or source state. Decoder/printing success is not intrinsic proof or source/backend preservation.'}
if not args.cases_only:
 matrices=[json.loads((out/name).read_text()) for name in ['default.json','composed.json']]
 assert all(len(rows)==len(cases) for rows in matrices)
 changes=Counter();perDocument={};refusals=[0,0]
 for index,case in enumerate(cases):
  pair=[rows[index] for rows in matrices]
  for reader,row in enumerate(pair):
   assert row['caseId']==case['caseId'] and row['nodeType']==case['nodeType'] and row['route']==case['route']
   if case['route']=='none':assert row['natural']=={'status':'not-standalone'} and row['unknownRoot'] is None
   else:
    assert row['natural']['status'] in {'decoded','refused'} and row['unknownRoot']['status']=='refused';refusals[reader]+=1
   perDocument.setdefault(case['fixture'],[Counter(),Counter()])[reader][row['natural']['status']]+=1
  assert pair[0]['producerExpression']==pair[1]['producerExpression']
  if pair[0]['natural']!=pair[1]['natural']:changes[pair[0]['natural']['status']+'->'+pair[1]['natural']['status']]+=1
 assert refusals==[sum(c['route']!='none' for c in cases)]*2
 result.update(default=dict(Counter(r['natural']['status'] for r in matrices[0])),composed=dict(Counter(r['natural']['status'] for r in matrices[1])),unknownRootRefusalsEachReader=refusals[0],changes=dict(changes),perDocument={name:[dict(x) for x in rows] for name,rows in perDocument.items()},inputs={name:sha(out/name) for name in ['cases.json','default.json','composed.json']})
 if args.capture_summary:(out/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
 else:assert json.loads((out/'summary.json').read_text())==result, 'occurrence frozen summary mismatch'
print(json.dumps({key:value for key,value in result.items() if key not in {'perDocument','inputs'}}))
