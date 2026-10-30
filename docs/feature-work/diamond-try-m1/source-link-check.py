from pathlib import Path
import json,hashlib,copy,re
r=Path('/workspace/solidity-lean');p=Path('/workspace/next10-diamond-try-evidence/m1-producer')
records=[x for x in json.loads((r/'docs/feature-work/diamond-try-physical-design/fixture-identities.json').read_text()) if x['fixture']=='malformed_panic.sol']
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def functions(ast):
 c=next(n for n in ast['nodes'] if n['nodeType']=='ContractDefinition' and n['name']=='C')
 return {n['name']:n for n in c['nodes'] if n['nodeType']=='FunctionDefinition'}
def shape(ast):
 fs=functions(ast);f=fs['f'];c=fs['c'];assert f['id']==7 and c['id']==105
 assert f['visibility']=='public' and f['stateMutability']=='pure' and f['returnParameters']['parameters']==[]
 params=f['parameters']['parameters'];assert len(params)==1 and params[0]['id']==2 and params[0]['scope']==7 and params[0]['typeDescriptions']['typeIdentifier']=='t_uint256'
 assert len(f['body']['statements'])==1;asm=f['body']['statements'][0];assert asm['nodeType']=='InlineAssembly' and asm['id']==5
 calls=asm['AST']['statements'];assert len(calls)==3
 ex=[s['expression'] for s in calls];assert all(x['nodeType']=='YulFunctionCall' for x in ex)
 assert [x['functionName']['name'] for x in ex]==['mstore','mstore','revert']
 assert [len(x['arguments']) for x in ex]==[2,2,2]
 def literal(x):assert x['nodeType']=='YulLiteral' and x['kind']=='number';return int(x['value'],0) if x['value'].startswith('0x') else int(x['value'])
 assert [literal(x) for x in ex[0]['arguments']]==[0,int('4e487b71'+'00'*28,16)]
 assert [literal(x) for x in ex[1]['arguments']]==[4,67]
 assert literal(ex[2]['arguments'][0])==0;arg=ex[2]['arguments'][1];assert arg['nodeType']=='YulIdentifier' and arg['name']=='size'
 refs=asm['externalReferences'];assert len(refs)==1 and refs[0]['declaration']==2 and refs[0]['src']==arg['src'] and not refs[0]['isSlot'] and not refs[0]['isOffset'] and refs[0]['valueSize']==1
 assert len(c['body']['statements'])==1;t=c['body']['statements'][0];assert t['nodeType']=='TryStatement'
 call=t['externalCall'];assert call['tryCall'] and len(call['arguments'])==1 and int(call['arguments'][0]['value'],0)==36
 target=call['expression'];assert target['nodeType']=='MemberAccess' and target['memberName']=='f' and target['referencedDeclaration']==7
 assert target['expression']['nodeType']=='Identifier' and target['expression']['name']=='this'
 clauses=t['clauses'];assert len(clauses)==3 and [cl['errorName'] for cl in clauses]==['','Panic','']
 def assertion(st,b):
  assert st['nodeType']=='ExpressionStatement';q=st['expression'];assert q['expression']['name']=='assert' and q['expression']['referencedDeclaration']==-3
  assert len(q['arguments'])==1 and q['arguments'][0]['value']==b
 assert len(clauses[0]['block']['statements'])==1;assertion(clauses[0]['block']['statements'][0],'false')
 ps=clauses[1]['parameters']['parameters'];assert len(ps)==1 and ps[0]['typeDescriptions']['typeIdentifier']=='t_uint256'
 panic=clauses[1]['block']['statements'];assert len(panic)==2;assertion(panic[0],'true');assert panic[1]['nodeType']=='Return' and panic[1]['expression']['referencedDeclaration']==ps[0]['id']
 assert len(clauses[2]['block']['statements'])==1;assertion(clauses[2]['block']['statements'][0],'false')
 return {'callee':f['id'],'parameter':params[0]['id'],'caller':c['id'],'calleeSpan':f['src'],'callerSpan':c['src'],'panicBinding':ps[0]['id'],'sizeUse':arg['src']}
def parse_bundles(text):
 result={}
 for m in re.finditer(r'def (legacy|viaIR)Bundle : BundleKey :=\s*\{(.*?)\n  \}',text,re.S):
  fields={}
  for line in m[2].splitlines():
   q=re.fullmatch(r'\s*(\w+) := (.*)\s*',line)
   if q:assert q[1] not in fields;fields[q[1]]=q[2].strip()
  result[m[1]]=fields
 assert set(result)=={'legacy','viaIR'}
 return result

def check_bundle(rec,bundles):
 fields=bundles[rec['pipeline']]
 expected={'pipeline':'.'+rec['pipeline'],'source':'originalSource'}
 for dest,src in [('compilerHash','compilerSha256'),('inputHash','inputSha256'),('outputHash','outputSha256'),('creationHash','creationSha256'),('runtimeHash','runtimeSha256')]:expected[dest]=json.dumps(rec[src])
 assert fields==expected,(rec['pipeline'],fields,expected)

rows=[]
compiler=p.parent/'compiler/soljson.js';assert sha(compiler)==records[0]['compilerSha256']
lean=(r/'Solidity/Evm/TryPanicProducer.lean').read_text();literal=re.search(r'def originalSource : String := (.*)',lean)[1]
for rec in records:
 assert sha(rec['sourcePath'])==rec['sourceSha256'] and sha(rec['inputPath'])==rec['inputSha256'] and sha(rec['outputPath'])==rec['outputSha256']
 source=Path(rec['sourcePath']).read_text();assert json.loads(literal)==source
 inp=json.loads(Path(rec['inputPath']).read_text());out=json.loads(Path(rec['outputPath']).read_text());assert inp['sources']['original.sol']['content']==source
 assert inp['settings']==rec['settings'];assert inp['settings']['viaIR']==(rec['pipeline']=='viaIR') and inp['settings']['evmVersion']=='osaka'
 ast=out['sources']['original.sol']['ast'];linked=shape(ast);contract=out['contracts']['original.sol']['C']
 for k,h in [('bytecode','creationSha256'),('deployedBytecode','runtimeSha256')]:assert hashlib.sha256(bytes.fromhex(contract['evm'][k]['object'])).hexdigest()==rec[h]
 assert contract['evm']['deployedBytecode']['object'].startswith('6080604052')
 assert contract['evm']['bytecode']['object'].startswith('6080604052')
 bundles=parse_bundles(lean);check_bundle(rec,bundles)
 identity_refusals=[]
 for mode in ['swapped-fields','swapped-pipeline-blocks','wrong-pipeline-tag','wrong-source-field']:
  bad=copy.deepcopy(bundles);fields=bad[rec['pipeline']]
  if mode=='swapped-fields':fields['inputHash'],fields['outputHash']=fields['outputHash'],fields['inputHash']
  if mode=='swapped-pipeline-blocks':bad['legacy'],bad['viaIR']=bad['viaIR'],bad['legacy']
  if mode=='wrong-pipeline-tag':fields['pipeline']='.viaIR' if rec['pipeline']=='legacy' else '.legacy'
  if mode=='wrong-source-field':fields['source']='"contract Wrong {}"'
  try:check_bundle(rec,bad)
  except AssertionError:identity_refusals.append(mode)
  else:raise AssertionError('identity control was admitted: '+mode)
 # Distinct genuine provenance refusals, never reference-byte comparisons.
 rejected=[]
 for mode in ['wrong-order','wrong-word','wrong-parameter-type','wrong-external-reference','wrong-callee','wrong-argument','wrong-handler']:
  bad=copy.deepcopy(ast);fs=functions(bad);asm=fs['f']['body']['statements'][0];t=fs['c']['body']['statements'][0]
  if mode=='wrong-order':asm['AST']['statements'][0],asm['AST']['statements'][1]=asm['AST']['statements'][1],asm['AST']['statements'][0]
  if mode=='wrong-word':asm['AST']['statements'][1]['expression']['arguments'][1]['value']='0x41'
  if mode=='wrong-parameter-type':fs['f']['parameters']['parameters'][0]['typeDescriptions']['typeIdentifier']='t_bool'
  if mode=='wrong-external-reference':asm['externalReferences'][0]['declaration']=3
  if mode=='wrong-callee':t['externalCall']['expression']['referencedDeclaration']=8
  if mode=='wrong-argument':t['externalCall']['arguments'][0]['value']='0x23'
  if mode=='wrong-handler':t['clauses'][1]['errorName']='Error'
  try:shape(bad)
  except (AssertionError,KeyError,ValueError):rejected.append(mode)
  else:raise AssertionError('control was admitted: '+mode)
 rows.append({'pipeline':rec['pipeline'],'identities':linked,'sourceSHA256':rec['sourceSha256'],'inputSHA256':rec['inputSha256'],'outputSHA256':rec['outputSha256'],'compilerSHA256':rec['compilerSha256'],'creationSHA256':rec['creationSha256'],'runtimeSHA256':rec['runtimeSha256'],'staticRuntimeProloguePrefix':contract['evm']['deployedBytecode']['object'][:10],'staticCreationProloguePrefix':contract['evm']['bytecode']['object'][:10],'prologueReachabilityOrResourceProof':False,'negativeShapeControls':rejected,'negativeBundleControls':identity_refusals,'newCompilation':False,'newReferenceExecution':False,'kernelSourceOrTargetAdequacy':False})
(p/'source-links.json').write_text(json.dumps(rows,indent=2)+'\n')
print('PASS two original whole-source/AST/compiler-pipeline identity checks; 14 mutated shape +8 bundle field/pipeline refusals; no compiler/engine or original-source admission')
