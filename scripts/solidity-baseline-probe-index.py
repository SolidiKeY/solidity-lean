#!/usr/bin/env python3
"""Bounded diagnostic matrix. Source-reader emission is never typed admission.

Read archived actual commands/results; never rerun, edit or replace the corpus.
"""
import argparse,gzip,hashlib,json,tarfile
from pathlib import Path
from collections import Counter
BASE=Path('tests/upstream/baseline-20261028')
PROBES=BASE/'probes'
def sha(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads(p.read_text())
DECLARATIONS={
 'hash': [('Solidity/Calculus/MemRead/Pass.lean',439,454),('Solidity/Examples/Tactics/Hashing.lean',166,186)],
 'copy': [('Solidity/Evm/Compile.lean',169,176),('Solidity/Evm/Compile.lean',212,218),('Solidity/Examples/Tactics/ArrayShapeCopy.lean',8,14)],
 'loop': [('docs/loops.md',57,62)],
 'jump': [('Solidity/Syntax/Elab/Lower.lean',453,461)],
 'payment': [('Solidity/Tools/Upstream.lean',269,284),('Solidity/Frontend/Problems.lean',161,169)],
 'tail': [('docs/solc-alignment.md',344,357),('Solidity/Calculus/CleanTailBoundary.lean',42,52)],
 'rethrow': [('Solidity/Frontend/SolcJson/Body.lean',2059,2087),('Solidity/Semantics/RevertMemory.lean',35,51)],
 'spec': [('Solidity/Frontend/Import.lean',536,555),('Solidity/Frontend/SolcJson/Contract.lean',746,762)],
 'source': [('Solidity/Frontend/Source.lean',180,222)],
}
KEYS={'keccakBuiltin':'hash','sha256Builtin':'hash','ripemd160Builtin':'hash','fixedArrays':'copy','bytesConcat':'loop','stringConcat':'loop','doWhileStatement':'jump','continueStatement':'jump','nonpayableEntry':'payment','danglingReferences':'tail','canonicalRethrow':'rethrow','comments':'spec','pragmaVersion':'source'}
OBSERVED={'increments':('PushedMember','increment'), 'valueTypeDeclarations':('NominalStruct','f'),'valueTypes':('NominalStruct','f')}
CATEGORIES={**{k:'named-proof-interface-limit' for k in ['keccakBuiltin','sha256Builtin','ripemd160Builtin','fixedArrays','bytesConcat','stringConcat']},'danglingReferences':'named-model-assumption-limit','nonpayableEntry':'diagnostic-capability-limit','compoundAssignment':'named-lowering-limit-unreproduced','doWhileStatement':'named-lowering-limit-unreproduced','continueStatement':'named-lowering-limit-unreproduced'}
def parse_plan(text):
 rows=[]
 for line in text.splitlines():
  if not line or line.startswith('#'):continue
  p=line.split('|',5)
  if len(p)!=6:raise ValueError('six plan fields required')
  rows.append(dict(zip(('id','positive','negative','proposed','question','recommendation'),p)))
 if len({r['id'] for r in rows})!=len(rows):raise ValueError('duplicate feature')
 return rows

def derive(root):
 if sha((root/BASE/'attribution/index.json').read_bytes())!='1373bb0acd6c82efb92c7e6acfa29a018d60b4ed66320a98b22eddb2a71f8bee':raise ValueError('prior index changed')
 old=load(root/BASE/'attribution/index.json');original=load(root/BASE/'gaps/gaps.json');probes=root/PROBES
 questions={r['id']:r for r in old['features'] if r['disposition']=='evidence-needed' or r['missingEvidence']!='none'}
 plan=parse_plan((probes/'matrix-plan.tsv').read_text())
 if set(questions)!={r['id'] for r in plan} or len(questions)!=40:raise ValueError('must cover exact25+15 questions')
 archive=probes/'evidence.tar.gz';ledger=load(probes/'archive.json')
 if sha(archive.read_bytes())!=ledger['sha256']:raise ValueError('archive drift')
 with tarfile.open(archive,'r:gz') as tf:
  files={m.name:tf.extractfile(m).read() for m in tf if m.isfile()}
 for p,info in ledger['files'].items():
  if p not in files or sha(files[p])!=info['sha256']:raise ValueError('archived file drift '+p)
 if set(files)!=set(ledger['files']):raise ValueError('unledgered archive files')
 records={}
 for path,data in files.items():
  if path.startswith('rechecked/runs/') and path.endswith('/record.json'):
   r=json.loads(data);records[(r['case'],r['pipeline'])]=r
 expected_cases=set(load(probes/'cases.json')['cases'])
 if set(records)!={(c,p) for c in expected_cases for p in ('legacy','viaIR')}:raise ValueError('missing case/pipeline')
 expected_reject=set(load(probes/'cases.json')['compilerRejections'])
 for (case,pipeline),record in records.items():
  src='rechecked/'+record['source']
  if sha(files[src])!=record['sourceSha256']:raise ValueError('source hash mismatch')
  compile=record['stages'][0]
  if compile['tool'].get('timedOut'):raise ValueError('timeout is not a compiler rejection')
  if compile['exitCode']!=(1 if case in expected_reject else 0):raise ValueError('unexpected compiler outcome '+case)
  for stage in record['stages'][1:]:
   if stage['exitCode']!=0:raise ValueError('failed reader invocation')
  for stage in record['stages']:
   if sha(files['rechecked/'+stage['log']])!=stage['logSha256']:raise ValueError('log drift')
  if record['compilerSha256']!='6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390':raise ValueError('compiler pin drift')
  if case in expected_reject:
   markers={'VersionReject':'requires different compiler version','WrongIdentifier':"Expected ';' but got 'function'",'WrongNominal':'Return argument type B','WrongBounds':'An enum type, contract type or an integer type is required','WrongAddress':'invalid checksum','InvalidDelete':'delete cannot be applied','HexArray':'string[2] memory is not implicitly convertible'}
   if markers[case] not in files['rechecked/'+compile['log']].decode():raise ValueError('not the expected compiler rejection')
   continue
  if sha(files[f'rechecked/runs/{case}/{pipeline}/source.ast.json'])!=record['astSha256']:raise ValueError('compiler AST hash drift')
  fixture=json.loads(files[f'rechecked/runs/{case}/{pipeline}/source.ast.json'])
  if fixture['header']['sourceSha256']!=record['sourceSha256'] or record['settings']['viaIR']!=(pipeline=='viaIR'):raise ValueError('source/pipeline provenance drift')
  complete=json.loads(files[f'rechecked/runs/{case}/{pipeline}/reader-complete.json'])
  if complete['functions']!=record['reader']['functions']:raise ValueError('original reader observations changed')
  record['completeReader']=complete
  for mutation in record.get('provenanceControls',[]):
   if mutation['result']['exitCode']!=0 or mutation['observation']['status']!='refused':raise ValueError('mutation refusal missing')
 # Exact UTF16/CRLF control, independently check source text and emitted locations.
 for pipeline in ('legacy','viaIR'):
  r=records[('CommentRanges',pipeline)];source=files['rechecked/inputs/CommentRanges.sol'].decode()
  if source.count('\r\n')!=3:raise ValueError('CRLF control lost')
  locations=r['sourceLocations'];starts=[x['range']['start'] for x in locations]
  if starts!=[dict(line=2,character=34),dict(line=2,character=77)]:raise ValueError('UTF16 source ranges differ')
 def controls(text):
  results=[]
  for item in text.split(','):
   case,sep,function=item.partition(':')
   if sep and function in ('compiler-digest','pragma-record'):
    for pipeline in ('legacy','viaIR'):
     rec=records[(case,pipeline)];obs=next(x for x in rec.get('provenanceControls',[]) if x['mutation']==function)
     results.append(dict(case=case,pipeline=pipeline,stage='provenance',observation=obs['observation'],exitCode=obs['result']['exitCode'],record=f'rechecked/runs/{case}/{pipeline}/record.json'))
    continue
   for pipeline in ('legacy','viaIR'):
    rec=records[(case,pipeline)];entry=dict(case=case,pipeline=pipeline,source=rec['source'],sourceSha256=rec['sourceSha256'],compileExitCode=rec['stages'][0]['exitCode'],record=f'rechecked/runs/{case}/{pipeline}/record.json')
    if sep:
     entry.update(function=function,stage='source-reader',rows=[r for r in rec.get('reader',{}).get('functions',[]) if r['function']==function],typedValidation='blocked; not executed/proved')
     if not entry['rows']:raise ValueError('missing selected function '+item)
     entry['defaultSpecificationCallbackRefusal']=any('not imported' in r['reason'] for r in entry['rows'])
    else:entry.update(stage='compiler',result='compiler-rejected' if entry['compileExitCode']==1 else 'compiler-accepted')
    results.append(entry)
  return results
 rows=[]
 for r in plan:
  q=questions[r['id']];positive=controls(r['positive']);negative=controls(r['negative']);kind=CATEGORIES.get(r['id'],'inventory-evidence-discrepancy')
  note='Current evidence is pinned compiler acceptance plus source-reader text/metadata. It does not establish native admission or behavior; existing controls/declarations are historical evidence, not freshly reproved.'
  observed=[]
  if r['id'] in OBSERVED:
   case,function=OBSERVED[r['id']]
   for pipeline in ('legacy','viaIR'):
    function_rows=[x for x in records[(case,pipeline)]['completeReader']['functions'] if x['function']==function]
    if not function_rows or any(x['status']!='reader-refused' or 'not imported' in x['reason'] for x in function_rows):raise ValueError('source refusal not established')
    observed.append(dict(case=case,pipeline=pipeline,function=function,rows=function_rows))
   kind='observed-source-reader-refusal'
   note='Valid pinned-compiler source is explicitly refused by the source reader in both modes. No typed execution or universal semantic claim.'
  if r['id']=='increments':r['question']='Postfix increment of a pushed struct member a.push().x++ is source-reader refused, even with the pure array receiver a. The effectful receiver companion is also refused; no receiver mutation is inferred.'
  if r['id'] in ('valueTypes','valueTypeDeclarations'):r['question']='A memory struct whose field is a scalar UDVT (Ticket is uint8) is source-reader refused as invisible declaration#3; a fixed array of wrapped Ticket values is emitted. This separates nominal struct fields from scalar/fixed-array support.'
  if r['id']=='comments':r['question']='Ordinary UTF8/CRLF comments have exact reader/range controls. BadClause retains malformed specification text at this reduced stage; production parser refusal is historical, not freshly reproduced.'
  if r['id']=='hexLiterals':r['positive']='SourceLiterals:byteSequences,HexArrayExplicit:f';positive=controls(r['positive']);negative+=controls('HexArray');r['question']='Raw hex literal array inference yields string[2] and is rejected by pinned solc; the explicitly cast bytes2 array is compiler-accepted and reader-emitted. No implicit raw-array Lean gap is established.'
  if r['id']=='structConstruction':note+=' NominalStruct fails during field-type reading, not construction execution; it is related dependency evidence, not a newly demonstrated construction rule defect.'
  if kind=='inventory-evidence-discrepancy':r['recommendation']='Retain current partial status; annotate manifest/localEvidence with these exact bounded compiler/reader controls and distinguish existing kernel controls from unavailable native validation. '+r['recommendation']
  if r['id']=='visibility':r['question']='The source reader preserves internal/public declaration tags and emitted helper text. Native entry selection/refusal is blocked, not freshly demonstrated.'
  if r['id'] in ('uncheckedBlock','uncheckedArithmetic','assertBuiltin'):
   r['question']='The source reader preserves the checked/unchecked/assertion forms and prior controls identify guard semantics. Panic vectors were prepared but not replayed; no new Panic-byte claim is made.'
  if r['id']=='compoundAssignment':r['question']='Effectful and ordinary pushed-member op= forms are reader-emitted. Later typed pure-receiver admission remains unobserved; no source-reader refusal is claimed.'
  phase_corrections={
   'addressTypes':'Payable/address conversion and noninteger wrapper forms are source-reader emitted; they were not executed. The native carrier/source-domain distinction is existing declared policy.',
   'expressionStatements':'Discarded increment and false-assertion forms are source-reader emitted. No current effect result or failure-byte vector was executed; existing guard theorems are separate historical evidence.',
   'deleteExpression':'Legal array-delete syntax is compiler-accepted and source-reader emitted; storage-pointer delete is compiler-rejected. No reset-length runtime result was observed.',
   'shortCircuit':'The source reader retains the lazy Boolean form containing the failing helper. Untaken-call behavior is prior control evidence, not newly executed here.',
   'doWhileStatement':'Plain do/continue and nested try/continue forms are reader-emitted. Lower.lowerStmt has a named later try-jump gate; routing and the later refusal were not exercised.',
   'continueStatement':'The source reader emits both continue forms. The later Lower.lowerStmt.hasJump refusal is declaration-backed and currently unreproduced; no current routing execution is claimed.',
   'canonicalRethrow':'Exact whole-buffer syntax is reader-emitted and wrong-offset syntax is reader-refused by the scope gate. TRun.revertData_mem transport is existing theorem evidence, not a fresh byte execution.',
   'structConstruction':'Ordinary scalar-member construction is reader-emitted; NominalStruct is refused during UDVT field-type reading. No construction execution or construction-specific rule defect is established.',
   'bytesConcat':'Concatenation syntax/content literals are reader-emitted; symbolic memory-writing loops lack the general heap-anonymising invariant interface. No new runtime concat content was observed.',
   'stringConcat':'String-concat source syntax is reader-emitted; symbolic constructed-memory content summaries remain a named loop interface limit. No current output content or allocation behavior was executed.',
   'danglingReferences':'The recycled-slot source is compiler-accepted and reader-emitted. CleanTail/TailMode provide existing model-specific controls; no fresh typed or EVM resurrection observation, or portable definedness guarantee, is claimed.',
  }
  r['question']=phase_corrections.get(r['id'],r['question'])
  citations=[]
  for path,start,end in DECLARATIONS.get(KEYS.get(r['id'],''),[]):
   lines=(root/path).read_text().splitlines();citations.append(dict(path=path,startLine=start,endLine=end,sha256=sha((root/path).read_bytes()),quote='\n'.join(lines[start-1:end])))
  row=dict(id=r['id'],originalMissingEvidence=q['missingEvidence'],classification=kind,boundedAssessment=r['question'],scopeNote=note,positiveControls=positive,negativeOrBoundaryControls=negative,observedRefusals=observed,currentDeclarations=citations,existingEvidence=q['localEvidence'],recommendation=r['recommendation'],nativeTypedValidation='blocked: single900s API refresh124; no current native admission/proof/replay result',baselineVariantAssociations=[])
  rows.append(row)
 case_results=[]
 for (case,pipeline),r in sorted(records.items()):
  fs=r.get('completeReader',{}).get('functions',[])
  case_results.append(dict(case=case,pipeline=pipeline,compileExitCode=r['stages'][0]['exitCode'],readerExitCode=r['stages'][1]['exitCode'] if len(r['stages'])>1 else None,sourceSha256=r['sourceSha256'],record=f'rechecked/runs/{case}/{pipeline}/record.json',readerEmitted=sum(f['status']=='reader-emitted' for f in fs),readerRefusals=[dict(function=f['function'],reason=f['reason'],defaultCallbackLimitation='not imported' in f['reason']) for f in fs if f['status']=='reader-refused'],dropped=r.get('completeReader',{}).get('dropped',[])))
 stats=Counter(r['classification'] for r in rows)
 return dict(schemaVersion=1,startingCommit='13edcbe42e6bf18b3f55e15ab03e6d8942651ca1',sourceBase='f4dee4a29c2e208b36db4a4161a4723c735cd775',originalCounts=original['counts'],originalQuestions=40,coverage=dict(evidenceNeededIds=old['evidenceNeededIds'],documentaryQuestionIds=[r['id'] for r in old['features'] if r['disposition']=='boundary' and r['missingEvidence']!='none']),allQuestionsHaveBoundedAssessment=True,nativeValidationComplete=False,semanticCoveragePromoted=False,counts=dict(stats),
  caseResults=case_results,
  evidence=dict(archiveSha256=ledger['sha256'],archiveFiles=len(files),priorIndexSha256=sha((root/BASE/'attribution/index.json').read_bytes()),planSha256=sha((probes/'matrix-plan.tsv').read_bytes()),generatorSha256=sha((root/'scripts/solidity-baseline-probe-index.py').read_bytes())),
  phaseLimit='Only pinned compilation, Source.read provenance validation, Admission.scan + readContract body/member extraction and sourceLocations ran. Private production specification callbacks and native typed elaboration/proof listing/replay did not run. Default-callback not-imported refusals are adapter limitations, not production failures.',
  controls=dict(compilerModes=44,sourceReaderModes=30,completeMetadataModes=30,provenanceMutationRefusals=4,utf16CrlfPositionsVerified=True,falsePropertyExecution='not run',wrongRuntimeExpectation='not run; no claim of a passed replay-negative control'),
  blockedCapabilities=['Stale full Frontend.Testing/Tools.Upstream graph after bounded900s refresh stopped124. Restoring current API artifacts is required for native typed, production specification-parser, proof-listing and runtime validation; no blind rebuild repeated.','Existing upstream replay constructs a fixed default-value TTx; a nonzero-msg.value external-entry discriminator is unavailable in that adapter.'],
  nextWaves={kind:[r['id'] for r in rows if r['classification']==kind] for kind in sorted(stats)},features=rows)

def render(x):
 lines=['# Bounded diagnostic matrix','',f"All40 exact prior questions are assessed: {x['counts']}. This is compiler/provenance/source-reader evidence; **native typed validation remains blocked**. No feature status or corpus result changes.",'',x['phaseLimit'],'',
 'The900-second narrow API refresh ended124 (not a pass). The original90-minute cold stop and unrun warm timing remain unchanged. No new build was attempted after that narrow stop. Prepared panic and deliberately wrong runtime vectors were **not replayed**.','',
 'Reader-emitted false assertions are still false assertions, not proved properties. BadClause is emitted at this reduced stage; default specification callbacks cannot stand in for production parser validation. Raw HexArray is compiler-invalid; HexArrayExplicit is its separately retained valid discriminator.','',
 'Reproduce the reduced diagnostics with `bash scripts/run-solidity-baseline-probes.sh /workspace/solidity-lean/.lake/FRESH_PROBE_OUTPUT`. It refuses to overwrite output and performs no build; a stale reader API is a blocked preflight. The exact failed900-second full-API refresh remains in the archive, not an automatic retry.','',
 'Extract raw records when needed with `tar -xzf evidence.tar.gz -C .` from this probes directory. All inputs/observations and both pipelines are preserved; these separate diagnostics never feed the original corpus verdicts.','',
 'Archive records contain exact sources, ASTs, generated wrappers, invocations, stage exits, reader text, all dropped/member/init metadata and both required modes. Integrity verifies hashes, exact40 IDs, mode completeness, expected compiler rejections, mutation refusals and independent UTF16/CRLF positions.','',
 '| Feature | Bounded disposition | Assessment | Missing current validation |','|---|---|---|---|']
 for r in x['features']:lines.append(f"| {r['id']} | {r['classification']} | {r['boundedAssessment']} | Native typed/proof/replay blocked; see exact controls and capability in matrix.json. |")
 lines+=['','## Exact case exits','', '| Case | Pipeline | Compiler exit | Source-reader exit | Emitted functions | Refused functions |','|---|---|---:|---:|---:|---:|']
 for c in x['caseResults']:
  lines.append(f"| [{c['case']}]({c['record']}) | {c['pipeline']} | {c['compileExitCode']} | {c['readerExitCode'] if c['readerExitCode'] is not None else 'not run'} | {c['readerEmitted']} | {len(c['readerRefusals'])} |")
 lines+=['','## Review corrections','', 'Independent finder/skeptic reviews required explicit per-row phase wording. BadClause emission and default specification-callback refusals are reduced-adapter results. Pushed-member increment, not receiver mutation, is the observed source shape. Raw HexArray was compiler-invalid; its explicit-cast companion is separate. NominalStruct fails in field-type reading, not a new construction rule. No prepared false-output/panic vector was replayed.','', 'The initial generated reader wrapper failed elaboration and was corrected with explicit tuple types. Every failed command and original input remains archived. A separate ScalarMatrixValid fixes an invalid payable-address cast; the original invalid source is preserved. The initial driver exit0 was not counted as a passing reader stage.','', '## Next diagnostic waves','']
 for kind,ids in x['nextWaves'].items():lines+=['- '+kind+': '+', '.join(ids)+'.']
 lines+=['','Run `python3 scripts/solidity-baseline-probe-index.py --check` for read-only archive/index integrity. See cases.json, matrix-plan.tsv and matrix.json for the exact per-feature controls, recommendations and declaration quotes. The existing inventory manifest is unchanged; generated inventory docs need no rewrite.','']
 return '\n'.join(lines).rstrip()+'\n'
def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1]);p.add_argument('--check',action='store_true');a=p.parse_args();x=derive(a.root);base=a.root/PROBES
 outputs={base/'matrix.json':json.dumps(x,indent=2,ensure_ascii=False)+'\n',base/'README.md':render(x)}
 for path,text in outputs.items():
  if a.check:
   if path.read_text()!=text:raise ValueError('stale output '+str(path))
  else:path.write_text(text)
 print(json.dumps(dict(questions=40,counts=x['counts'],nativeValidationComplete=False,originalCounts=x['originalCounts'])))
if __name__=='__main__':main()
