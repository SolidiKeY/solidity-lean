"""Bind full structural-form observations to frozen source witnesses.
Also compare retained H68 raw/normalized identities without claiming semantics.
"""
from pathlib import Path
from collections import Counter,defaultdict
import argparse,hashlib,json,sys,subprocess
sys.dont_write_bytecode=True
from corpus_packet import verified_corpus,verified_readers
ROOT=Path(__file__).resolve().parents[3];OWNED=Path(__file__).resolve().parent
parser=argparse.ArgumentParser();parser.add_argument('--read-only',action='store_true');args=parser.parse_args()
source,packet=verified_corpus()
subprocess.run(['python3',str(OWNED/'verify-bulk.py')],check=True,cwd=ROOT)
out,readersManifest=verified_readers()
assert ROOT/readersManifest['censusDependencyManifest']==OWNED/'corpus-inventory-manifest.json'
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def canonical(value):return json.dumps(value,sort_keys=True,separators=(',',':'))
forms=json.loads((source/'forms.json').read_text());casePacket=json.loads((out/'cases.json').read_text());cases=casePacket['cases']
assert casePacket['basis']==packet['basis'] and casePacket['censusArchiveSha256']==packet['archiveSha256']
matrices=[json.loads((out/name).read_text()) for name in ['default.json','composed.json']]
assert len(forms)==len(cases)==1926 and all(len(rows)==1926 for rows in matrices)
assert len({r['caseId'] for r in cases})==1926
routes={r['nodeType']:r['route'] for r in json.loads((OWNED/'construct-reader-cases.json').read_text())['cases']}
cache={};changes=[];unknown=[]
for index,(form,case) in enumerate(zip(forms,cases)):
 assert case['caseId']==form['formId'] and case['nodeType']==form['form']['nodeType']
 assert all(case[key]==value for key,value in form['witness'].items())
 assert case['route']==routes.get(case['nodeType'],'none')
 path=ROOT/case['fixture']
 if path not in cache:cache[path]=(sha(path),json.loads(path.read_text()))
 digest,node=cache[path];assert digest==case['fixtureSha256']
 for part in case['pointer'].split('/')[1:]:
  key=part.replace('~1','/').replace('~0','~');node=node[int(key)] if isinstance(node,list) else node[key]
 assert node['nodeType']==case['nodeType']
 before,after=[rows[index] for rows in matrices]
 for row in [before,after]:
  assert row['caseId']==case['caseId'] and row['nodeType']==case['nodeType'] and row['route']==case['route']
  if case['route']=='none':assert row['natural']=={'status':'not-standalone'} and row['unknownRoot'] is None
  else:assert row['unknownRoot']['status']=='refused' and row['natural']['status'] in {'decoded','refused'}
 assert before['producerExpression']==after['producerExpression']
 if before['natural']!=after['natural']:changes.append({'caseId':case['caseId'],'nodeType':case['nodeType'],'witness':form['witness'],'default':before['natural'],'composed':after['natural']})
 if case['route']=='none':unknown.append(case['caseId'])
callableCounts=[sum(r['unknownRoot'] is not None for r in rows) for rows in matrices];assert callableCounts==[1632,1632]
# Pair only outputs of the SAME retained compiler execution, never unrelated worlds.
receipts=json.loads((OWNED/'artifacts/h68-bulk/evidence/h68/metadata-compilation.json').read_text())['fixtures']
pairRows=[]
def nodes(value,pointer=''):
 if isinstance(value,dict):
  if isinstance(value.get('nodeType'),str):yield pointer,value
  for key,child in value.items():yield from nodes(child,pointer+'/'+key.replace('~','~0').replace('/','~1'))
 elif isinstance(value,list):
  for index,child in enumerate(value):yield from nodes(child,pointer+'/'+str(index))
for receipt in receipts:
 rawPath=ROOT/receipt['rawAst'];normalPath=ROOT/receipt['fixture']
 assert sha(rawPath)==receipt['rawAstSha256'] and sha(normalPath)==receipt['fixtureSha256']
 raw=defaultdict(list)
 for pointer,node in nodes(json.loads(rawPath.read_text())):raw[(node['nodeType'],node.get('src'))].append((pointer,node))
 for pointer,node in nodes(json.loads(normalPath.read_text())):
  candidates=[(p,n) for p,n in raw[(node['nodeType'],node.get('src'))] if 'id' not in node or (type(n.get('id')) is type(node['id']) and n.get('id')==node['id'])]
  row={'fixture':receipt['fixture'],'pointer':pointer,'nodeType':node['nodeType'],'src':node.get('src'),'idPresent':'id' in node,'id':node.get('id'),'candidateRawPointers':[p for p,_ in candidates]}
  row['pairing']='unique' if len(candidates)==1 else 'missing' if not candidates else 'ambiguous'
  if len(candidates)==1:
   before=candidates[0][1]
   row['idFieldPresence']=('both' if 'id' in before and 'id' in node else 'raw-only' if 'id' in before else 'normalized-only' if 'id' in node else 'neither')
   row['referenceFieldPresence']=('both' if 'referencedDeclaration' in before and 'referencedDeclaration' in node else 'raw-only' if 'referencedDeclaration' in before else 'normalized-only' if 'referencedDeclaration' in node else 'neither')
   # Only exact identity or the existing explicit u32 signed normalization is allowed.
   if 'referencedDeclaration' in node:
    original=before.get('referencedDeclaration');current=node['referencedDeclaration']
    signed=original-2**32 if type(original) is int and 2**31<=original<2**32 else original
    assert type(current) is type(signed) and current==signed
    row['referenceParity']='u32-signed' if original!=current else 'identical'
   for field in ['name','memberName','operator','kind','prefix','tryCall']:
    if field in node:assert node[field]==before.get(field),(receipt['name'],pointer,field)
   if 'typeIdentifier' in node.get('typeDescriptions',{}):assert node['typeDescriptions']==before['typeDescriptions']
   row['retainedNodeIdMatches']=('id' not in node or node['id']==before.get('id'))
  pairRows.append(row)
if args.read_only:assert json.loads((out/'normalization-identities.json').read_text())==pairRows, 'retained normalization ledger mismatch'
else:(out/'normalization-identities.json').write_text(json.dumps(pairRows,indent=2)+'\n')
summary={'cases':len(cases),'kinds':len({r['nodeType'] for r in cases}),'default':dict(Counter(r['natural']['status'] for r in matrices[0])),'composed':dict(Counter(r['natural']['status'] for r in matrices[1])),'unknownRootRefusalsEachReader':callableCounts[0],'noStandaloneEntries':len(unknown),'changes':changes,'changedWitnesses':len(changes),'pairedNormalizedOccurrences':len(pairRows),'pairingCounts':dict(Counter(r['pairing'] for r in pairRows)),'idFieldPresence':dict(Counter(r.get('idFieldPresence','unpaired') for r in pairRows)),'referenceFieldPresence':dict(Counter(r.get('referenceFieldPresence','unpaired') for r in pairRows)),'outcomeTransitions':dict(Counter(x['default']['status']+'->'+x['composed']['status'] for x in changes)),'retainedReferenceParity':dict(Counter(r.get('referenceParity','not-retained-or-ambiguous') for r in pairRows)),'inputs':{name:sha(out/name) for name in ['cases.json','default.json','composed.json','normalization-identities.json']},'boundary':'All observed structural forms have one actual standalone outcome per reader or explicit no-entry status;not all scalar semantics/contexts/source states. Raw/normalized pairs use the same retained compiler packet,kind/src and retained ID;missing/ambiguous pairing remains unknown. Exact retained identity/signed-reference comparisons do not establish lexical scope,shadowing,overload selection,intrinsic closure or source/backend preservation. Producer comparison is expression printing only,not actual importer migration.'}
for key in ['cases','default','composed','unknownRootRefusalsEachReader','pairedNormalizedOccurrences','idFieldPresence','referenceFieldPresence']:
 assert summary[key]==readersManifest[key], 'reader manifest count mismatch: '+key
assert summary['outcomeTransitions']==readersManifest['changes'], 'reader manifest transition mismatch'
if args.read_only:assert json.loads((out/'summary.json').read_text())==summary, 'retained reader summary mismatch'
else:(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:summary[k] for k in ['cases','kinds','default','composed','unknownRootRefusalsEachReader','changedWitnesses','pairedNormalizedOccurrences','pairingCounts','retainedReferenceParity','idFieldPresence','referenceFieldPresence','outcomeTransitions']}))
