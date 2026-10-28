#!/usr/bin/env python3
"""Supplement the immutable baseline with native diagnostic evidence, no builds."""
import argparse,hashlib,json,tarfile
from pathlib import Path
from collections import Counter
BASE=Path('tests/upstream/baseline-20261028');HERE=BASE/'native-cache'
def sha(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads(p.read_text())
def derive(root):
 here=root/HERE;ledger=load(here/'archive.json');old=load(root/BASE/'probes/matrix.json')
 if sha((here/'evidence.tar.gz').read_bytes())!=ledger['sha256']:raise ValueError('archive digest mismatch')
 with tarfile.open(here/'evidence.tar.gz','r:gz') as tf:files={m.name:tf.extractfile(m).read() for m in tf if m.isfile()}
 if set(files)!=set(ledger['files']):raise ValueError('archive membership drift')
 for n,v in ledger['files'].items():
  if sha(files[n])!=v['sha256'] or len(files[n])!=v['bytes']:raise ValueError('archive file drift '+n)
 records={}
 for n,b in files.items():
  if n.startswith('runs/') and n.endswith('/record.json'):
   r=json.loads(b);key=(r['case'],r['pipeline']);
   if key in records:raise ValueError('duplicate native mode')
   records[key]=r
 if len(records)!=40 or any((c,p) not in records for c,_ in records for p in ['legacy','viaIR']):raise ValueError('native modes incomplete')
 calls=json.loads(files['native-invocations.json'])
 for call in calls:
  if call['exitCode']!=0 or call.get('timedOut'):raise ValueError('native command failed/limited')
  if call['command'][0]=='lake' and '--no-build' not in call['command']:raise ValueError('native diagnostic may build')
  if sha(files[call['log']])!=call['logSha256']:raise ValueError('invocation log digest drift')
 for (c,p),r in records.items():
  for stage in r['stages']:
   if stage not in calls:raise ValueError('missing command provenance')
  fixture=json.loads(files['run-inputs/'+c+'/'+p+'/source.ast.json'])
  if sha(files['run-inputs/'+c+'/'+p+'/source.ast.json'])!=r['fixtureSha256']:raise ValueError('fixture hash drift')
  if fixture['header']['sourceSha256']!=r['sourceSha256'] or fixture['header']['settings']['viaIR']!=(p=='viaIR'):raise ValueError('fixture source/mode mismatch')
  if fixture['header']['compilerSha256']!='6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390':raise ValueError('compiler pin drift')
  runtime=r.get('runtime',[])
  if runtime:
   result=runtime[0]
   if result['pipeline']!=p:raise ValueError('replay pipeline drift')
   if result['status']=='working':
    jobs=json.loads(files[f'runs/{c}/{p}/jobs.json']);vectors=jobs[0]['vectors'];obs=result['observed']
    if len(vectors)!=len(obs):raise ValueError('observations missing')
    for v,o in zip(vectors,obs):
     if o['signature']!=v['signature'] or o['failed']!=v['failure'] or o['values']!=v['expected'] or o['revertBytes']!=v['revertBytes']:raise ValueError('replay expectation mismatch hidden')
   elif result['status']!='broken' or result['reason']!='frontend import gaps' or not result.get('gaps'):raise ValueError('unexpected/blocked native result')
   elif result.get('observed'):raise ValueError('refused batch falsely claims execution')
 for p in ('legacy','viaIR'):
  r=records['NativePositive',p];negative=r['negativeRuntime'][0]
  if negative['status']!='broken' or 'runtime expectation mismatch: identifiers()'!=negative['reason'] or negative['observed'][0]['values']!=['7'] or negative['expected']['expected']!=['8']:raise ValueError('negative replay guard absent')
  obs=r['runtime'][0]['observed'];by={o['signature']:o for o in obs}
  for name,code in [('falseBounds()',1),('uncheckedCaller()',17),('writeFail()',1)]:
   if by[name]['revertBytes']!=[78,72,123,113]+[0]*31+[code]:raise ValueError('panic bytes differ')
  if by['readCounter()']['values']!=['3']:raise ValueError('rollback observation differs')
  mutation=records['PushedMemberMutation',p]['runtime'][0]
  if [o['values'] for o in mutation['observed']]!=[['107'],['207']]:raise ValueError('receiver-mutation control differs')
 boundaries=json.loads(files['boundary-records.json'])
 if len(boundaries)!=6:raise ValueError('boundary controls incomplete')
 for b in boundaries:
  if b.get('timedOut'):raise ValueError('boundary timed out')
  fixtureBytes=files['boundary-inputs/'+b['control']+'/'+b['pipeline']+'/source.ast.json']
  if sha(fixtureBytes)!=b['fixtureSha256']:raise ValueError('boundary fixture hash mismatch')
  logPath=str(Path(b['log']).relative_to(root/HERE))
  if sha(files[logPath])!=b['logSha256']:raise ValueError('boundary log mismatch')
  if b['control']=='internal-entry':
   if b['exitCode']!=0 or b['result'][0]['status']!='broken' or 'no imported ABI entry' not in b['result'][0]['reason']:raise ValueError('internal entry refusal absent')
  elif b['exitCode']!=1:raise ValueError('provenance inconsistency not refused')
  else:
   wanted='compiler binary provenance does not match its exact pin' if b['control']=='compiler-digest' else 'recorded pragmas disagree with the source AST'
   if wanted not in files[logPath].decode():raise ValueError('wrong native refusal')
 audit=json.loads(files['audit.json']);verified=json.loads(files['hash-verification.json'])
 if not verified['narrowClosureSourceAndOleanChecksPass'] or verified['checkedModules']!=76:raise ValueError('cache identity incomplete')
 # The old matrix remains historical. Add exact native controls; never rewrite it.
 rows=[]
 for oldrow in old['features']:
  fid=oldrow['id'];controls=[]
  for control in oldrow['positiveControls']+oldrow['negativeOrBoundaryControls']:
   c,p=control['case'],control['pipeline'];r=records.get((c,p))
   if r is None:continue
   fname=control.get('function');typed=[x for x in r['typedImport'] if fname is None or x['sourceName']==fname]
   runtime=r.get('runtime',[]);observed=[o for o in (runtime[0].get('observed',[]) if runtime else []) if fname is None or o['signature'].split('(')[0]==fname]
   item=dict(case=c,pipeline=p,function=fname,typedRows=typed,replayStatus=runtime[0]['status'] if runtime else 'not requested',selectedObservations=observed,record=f'runs/{c}/{p}/record.json')
   if item not in controls:controls.append(item)
  companions=[]
  names=[]
  if fid in ['identifiers','wrapUnwrap','typeBounds','assertBuiltin','uncheckedBlock','uncheckedArithmetic','expressionStatements']:names.append('NativePositive')
  if fid=='comments':names.append('CommentSpecPositive')
  if fid=='increments':names.append('PushedMemberPositive')
  if fid in ['doWhileStatement','continueStatement']:names.append('TryContinuePositive')
  if fid=='compoundAssignment':names.append('PushedMemberMutation')
  for c in names:
   for p in ('legacy','viaIR'):
    r=records[c,p];companions.append(dict(case=c,pipeline=p,typedRows=r['typedImport'],replay=r.get('runtime'),negativeReplay=r.get('negativeRuntime'),record=f'runs/{c}/{p}/record.json'))
  classification=oldrow['classification'];remaining=oldrow['boundedAssessment'];required='Selected native import/replay controls are complete in both modes. No universal semantic proof or status promotion follows.'
  if fid in ['increments','valueTypeDeclarations','valueTypes','doWhileStatement','continueStatement']:
   classification='observed-native-import-refusal'
   remaining={'increments':'Postfix a.push().x++ is refused during production source/native import, even for a pure array receiver; plain member increment companion executes.', 'valueTypeDeclarations':'A memory struct with scalar UDVT field Ticket is refused in member-type dependency lookup; scalar wrappers and fixed UDVT arrays execute.', 'valueTypes':'UDVT struct member lookup is refused; scalar/fixed-array wrapper controls execute. This is a specific nominal field shape.', 'doWhileStatement':'Continue inside try inside a do-loop is refused by the exact loop jump gate; ordinary do/continue executes.', 'continueStatement':'The try-inside-loop jump gate refuses continue; the standalone ordinary continuation control returns2.'}[fid]
  if fid=='compoundAssignment':
   classification='inventory-documentation-discrepancy';remaining='State-mutating receiver().push().x += 7 and constant member store both execute, yielding107/207 in each mode. The old blanket receiver-call/mutation refusal is too broad; postfix pushed-member increment remains separately refused.'
  if fid=='comments':remaining='Production specification callbacks now run: nested-comment specification imports and executes; malformed BadClause is refused with solidity.specificationSyntax. Ordinary UTF8/CRLF controls execute. No comment-stripping defect established.'
  if fid=='canonicalRethrow':remaining='Exact whole-buffer rethrow executes with exact[1,2]bytes; wrong offset remains profile-excluded. General assembly and computed-data formula limitations are not promoted.'
  fresh_assessments={
   'identifiers':'Scoped shadowing returns7, and existing SourceIdentifiers controls typed-import and execute in both modes. No new identifier defect is established by these bounded controls.',
   'numericLiterals':'Exact-rational/extreme literal controls execute; literals() returns1. Generated runtime ERC7201 overflow remains a separate arithmetic-folding gap, not a literal attribution.',
   'unicodeLiterals':'Unicode byte length4 and existing byte-sequence assertions execute in both modes; no UTF8-specific defect is established.',
   'addressLiterals':'Packed-address and array address-kind controls execute; prior pinned compiler checksum rejection remains compiler evidence, not a valid-source defect.',
   'pragmaVersion':'Pinned-compiler accepted source imports natively; production importer refuses mismatched compiler/pragma records. Prior >=0.9 rejection is compiler evidence. No authentication of arbitrary consistent handwritten JSON is claimed.',
   'visibility':'Public entry returns7, internal helper imports as internal, and unchanged external replay refuses checkedHelper(uint8) as no imported ABI entry. This does not certify the full lifetime action set.',
   'addressTypes':'Concrete payable/address conversion returns7 and bool/address wrapper assertions execute in both modes. Native carrier versus source160-bit premise remains declared policy.',
   'unaryArithmetic':'Narrow signed negation returns5 and existing signed literal assertions execute; no new unary source failure established.',
   'bitwise':'Fixed-byte complement returns0 and signed bitwise literal assertions execute; no recursive-resource failure is attributed to bitwise lowering.',
   'shifts':'Signed int8 right shift returns ABI word -4, and huge-count literal controls execute. Existing general lowering proof scope is not promoted.',
   'comparisons':'Signed comparison returns1 and enum/integer bound assertions execute. Unsupported structural aggregate equality is not invented as a missing Solidity shape.',
   'shortCircuit':'The Boolean expression containing a failing die() helper returns1 without failure in both modes; this is bounded lazy-evaluation evidence, not universal source correspondence.',
   'blocks':'Nested declaration-ID shadowing returns outer value7 and localMagic assertions execute; scoped native elaboration succeeds.',
   'uncheckedBlock':'Local uint8 increment wraps to0; a checked helper called from unchecked fails with exact Panic0x11. Both modes preserve the lexical caller/callee distinction.',
   'expressionStatements':'Discarded increment returns counter1; postfix capture returns4 after asserting old3. False assertions produce exact Panic0x01, not a proved false property.',
   'deleteExpression':'Legal array delete executes and returns length0. Prior storage-pointer delete is compiler-invalid and remains excluded from implementation-gap evidence.',
   'assertBuiltin':'False-bound and write-fail assertions emit exact36-byte Panic0x01; the failed write rolls back so later counter read is3. Existing guard lemmas have standard axioms only.',
   'keccakBuiltin':'Equal-content Keccak control returns1. The existing64-literal-byte content closer remains a named proof-automation boundary, not a runtime hash defect or injectivity axiom.',
   'sha256Builtin':'Equal-content SHA256 control returns1. Shared literal-content closer limits and existing same-content interfaces remain distinct from runtime execution.',
   'ripemd160Builtin':'Equal-content RIPEMD160 control returns1. Symbolic/literal-content proof limits do not establish missing executable hash semantics.',
   'wrapUnwrap':'Unsigned, bool/address and signed-minus-one wrapper controls typed-import and execute in both modes. UDVT struct-field refusal remains a separately named aggregate dependency gap.',
   'thisAddress':'Self identity returns1 under the adapter transaction. The existing160-bit source premise is policy; this observation is not a new proof of that environment bound.',
   'typeBounds':'uint8 max returns255 while int8 min and enum max assertions pass; false max254 emits Panic0x01. Signed enum conversion remains causally separate.',
   'uncheckedArithmetic':'Narrow arithmetic wraps to0 in unchecked; called checked helper preserves Panic0x11. No checked ERC7201 folding failure is reassigned here.',
   'hexLiterals':'Explicit bytes2 hex array returns291; exact hex/Unicode byte controls execute. Raw inferred string[2] hex array was rejected by solc, not Lean.',
   'freeFunctions':'Resolved plusOne free call returns5 in both modes; conditional function-value admission remains separate from ordinary free-function identity lookup.',
   'fixedArrays':'Storage-to-memory fixed-array snapshot returns7 after source storage mutation. Generic fixedCopy/fixedCopyMem exclusion in the verified EVM fragment remains a named compiler-interface limit.',
   'structConstruction':'Ordinary scalar-member construction returns7. The nominal companion fails during UDVT member-type lookup, not a newly demonstrated construction rule defect.',
   'bytesConcat':'Concatenated bytes length2 and both byte-content assertions execute; general symbolic heap-writing loop summaries remain the named proof-interface limit.',
   'stringConcat':'Byte length of concatenated string returns2; this is concrete runtime evidence, not a general symbolic constructed-content theorem.',
   'danglingReferences':'The selected recycled-slot model path returns5. This is not generated EVM evidence or a portable all-version definedness guarantee; clean-tail/callback premises remain explicit.',
  }
  remaining=fresh_assessments.get(fid,remaining)
  if fid=='nonpayableEntry':
   classification='diagnostic-capability-limit';remaining='Ordinary zero-value public entry executes; internal helper is not an imported ABI entry. Nonzero msg.value external-entry rejection remains untested because unchanged replay fixes default msgValue0.';required='Requires a faithful existing value-aware external-entry diagnostic; the current replay input has no msg.value override. Do not substitute an internal raw run.'
  boundaryControls=[b for b in boundaries if (fid=='pragmaVersion' and b['control'] in ['compiler-digest','pragma-record']) or (fid in ['visibility','nonpayableEntry'] and b['control']=='internal-entry')]
  rows.append(dict(boundaryControls=boundaryControls,id=fid,previousClassification=oldrow['classification'],classification=classification,assessment=remaining,nativeControls=controls,isolatedCompanions=companions,existingDeclarations=oldrow['currentDeclarations'],recommendation=('Clarify that source receiver calls/mutation in these compound/store forms work; retain only exact demonstrated refusals and do not promote feature status.' if fid=='compoundAssignment' else 'Record these exact native controls and any named refusal/interface policy in localEvidence; retain partial status. No universal source/compiler proof or feature implementation is demanded by this diagnostic.'),remainingValidation=required,baselineVariantAssociations=[]))
 # Explicitly review tempting equal-message corpus matches rather than assigning
 # a contract-reference field to a UDVT feature based on the diagnostic string.
 originalGaps=load(root/BASE/'gaps/gaps.json')
 candidates=[g for g in originalGaps['exactVariantGaps'] if any(g['path'].endswith('/'+n) for n in ['mediocre_dynamic_v2.sol','mediocre_static_v2.sol'])]
 consideredSources=[]
 with tarfile.open(root/'tests/upstream/solidity-0.8.38.tar.gz','r:gz') as upstream:
  for path in sorted({c['path'] for c in candidates}):
   source=upstream.extractfile(path).read();consideredSources.append(dict(path=path,sha256=sha(source),source=source.decode()))
 rootTesting=audit['modules']['Solidity.Frontend.Testing'];checks=rootTesting.get('importArtifactChecks',[]);saved={x['module'] for x in checks}
 stale=dict(sourceClosureModules=len(audit['targetClosures']['Solidity.Frontend.Testing']),savedSetupImportArtifacts=len(checks),currentDirectImportsMissingFromSavedSetup=sorted(set(rootTesting['directImports'])-saved),savedImportRefsDifferingFromCurrent=sorted({x['module'] for x in checks if not x['byteIdenticalToLocal']}),closureModulesWithNoLocalTrace=[n for n in audit['targetClosures']['Solidity.Frontend.Testing'] if not audit['modules'][n]['trace']['exists']],scope='These are stale/missing saved descriptor observations, not a proven list of modules requiring recompilation. No Testing preflight or build attempted because closure identity is not satisfied.')
 return dict(schemaVersion=1,startingCommit='c4a5a2f1e90887fa86df4df39b48a791a679b09d',sourceBase='f4dee4a29c2e208b36db4a4161a4723c735cd775',originalCounts=originalGaps['counts'],questions=40,archiveSha256=ledger['sha256'],archiveFiles=len(files),cache=dict(narrowSourceModules=76,hashChecks=verified,noBuildNativePreflightExit=0,configuration='Current root lakefile unchanged. Retained diagnostic config differs only by weak-j1 flags; current commands add-j1 explicitly and LEAN_NUM_THREADS1. No config edits.'),staleTesting=stale,
  nativeAdapter='UNCHANGED Solidity.Frontend.Import production solc_import testing entrypoints and Solidity.Tools.Upstream #upstream_batch/replay; constructor, ABI/ranges, failure bytes, rollback and1000loop fuel unchanged.',
  nativeValidationComplete=False,nativeImportAndReplayAvailable=True,remainingNativeValidation='Nonzero msg.value external-entry discriminator unavailable in unchanged adapter. Testing proof-search/listing closure remains stale but is not required for these native observations.',
  statistics=dict(typedImportModes=len(records),replayModes=sum('runtime'in r for r in records.values()),replayStatuses=dict(Counter(r['runtime'][0]['status'] for r in records.values() if'runtime'in r)),matchingRuntimeObservations=sum(len(r['runtime'][0].get('observed',[])) for r in records.values() if'runtime'in r),wrongExpectedValueControls=2,productionProvenanceRefusals=4,internalAbiEntryRefusals=2,typedOnlyModes=2),
  resultInterpretation='12 broken replay batches are explicit frontend refusals, not observed semantic mismatches. Whole refused batches have no execution observations. Positive companions are separate retained inputs, not dropped functions/expectations.',
  theoremAxiomChecks='Existing entryGuard_failed/success/prior were imported and printed; each uses only propext,Classical.choice,Quot.sound. No new semantic theorem/axiom. Native execution observations are not kernel postcondition proofs or EVM evidence.',
  nativeCases=[dict(case=c,pipeline=p,typedRows=r['typedImport'],replay=r.get('runtime'),negativeReplay=r.get('negativeRuntime'),record=f'runs/{c}/{p}/record.json') for (c,p),r in sorted(records.items())],
  originalVariantAttributionAudit=dict(considered=candidates,consideredSources=consideredSources,associated=[],reason='The original mediocre_* fixtures have contract C fields, not UDVT Ticket fields. Same diagnostic text is insufficient causal evidence for UDVT attribution; no original variant/verdict was reclassified. No exact original pushed-postfix/try-jump variant was established.'),
  features=rows,nextWaves={kind:[r['id'] for r in rows if r['classification']==kind] for kind in sorted({r['classification'] for r in rows})},generatorSha256=sha((root/'scripts/solidity-baseline-native-index.py').read_bytes()))
def render(x):
 lines=['# Native cache diagnosis and diagnostic follow-up','', 'The native diagnostic adapter was already reusable. **No project-module build was run.** A mixed preflight had conflated the76-module Upstream branch with the257-module Testing proof branch. Lake-native hashes verified every narrow source/olean against its trace, recorded imports match current bytes, and the narrower no-build preflight succeeded.','',
  'StatePartsScoped was successfully built in the retained900-second attempt; its earlier active snapshot was not a semantic failure or terminal blocker. Testing\'s current direct ProveChunked import is absent from its saved setup. The stale proof branch remains separate; no retry or increased limits were used.','',
  f"Actual native results: {x['statistics']}. Broken replay batches retain named import refusals; their positive functions were not silently executed. The isolated companion inputs are separate. The deliberate expected8control observes7 and is correctly rejected.",'',
  'Both modes now observe Panic0x01, Panic0x11 and rollback to counter3; scoped identifiers, scalar wrappers, type bounds, hashes/concats and other selected scalar controls match. Malformed NatSpec is refused through production callbacks. UDVT struct fields, pushed-member postfix increment and try-nested loop jumps retain exact native refusals.','',
  'A real state-mutating receiver compound/store control returns107then207, superseding the blanket receiver-call/mutation refusal. This does not admit every pushed-member form. Exact rethrow produces[1,2]; wrong-offset assembly remains excluded.','',
  '**nativeValidationComplete remains false:** unchanged replay fixes default msg.value0, so nonzero payment rejection is untested. The Testing proof listing/search frontend remains stale; no proof listing, new semantic theorem or generated EVM observation is claimed. Historical cold timeout and warm-unrun remain unchanged.','',
  'Reproduce with `bash scripts/run-solidity-baseline-native.sh /workspace/solidity-lean/.lake/FRESH_NATIVE_OUTPUT`; it validates cache identities before any native preflight, contains no build command and never edits config. Read-only archive/index validation: `python3 scripts/solidity-baseline-native-index.py --check`.','',
 'Extract `evidence.tar.gz` into this directory for raw case links. All original baseline and prior diagnostic evidence remains unchanged.','',
  '| Feature | Native disposition | Assessment |','|---|---|---|']
 for r in x['features']:lines.append(f"| {r['id']} | {r['classification']} | {r['assessment']} |")
 lines+=['','## Per-case evidence','', '| Case | Mode | Typed report | Replay |','|---|---|---|---|']
 for c in x['nativeCases']:lines.append(f"| [{c['case']}]({c['record']}) | {c['pipeline']} | retained | {c['replay'][0]['status'] if c['replay'] else 'typed only'} |")
 lines+=['','## Historical snapshots','', 'The gap index at66629757, attribution index at13edcbe4 and reader-only matrix atc4a5a2f1 remain unchanged snapshot evidence. Their documentary hashes refer to those checkpoints; later documentation appendices legitimately differ. Replay their generators against the recorded checkpoint, not current appended prose. This milestone validates preserved bytes and the new native index; it does not silently regenerate those reports.','', '## Next waves','']
 for k,ids in x['nextWaves'].items():lines+=['- '+k+': '+', '.join(ids)+'.']
 lines+=['','Existing named memory/hash/compiler-fragment limits remain declaration-backed limits, not universal missing-proof demands. Inventory evidence recommendations do not promote statuses. See matrix.json for exact controls, historical declaration links and the rejected original-variant association candidates.','']
 return '\n'.join(lines).rstrip()+'\n'
def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1]);p.add_argument('--check',action='store_true');a=p.parse_args();x=derive(a.root);out=a.root/HERE
 for path,text in [(out/'matrix.json',json.dumps(x,indent=2,ensure_ascii=False)+'\n'),(out/'README.md',render(x))]:
  if a.check:
   if path.read_text()!=text:raise ValueError('stale native index '+str(path))
  else:path.write_text(text)
 print(json.dumps(dict(statistics=x['statistics'],nativeValidationComplete=x['nativeValidationComplete'],originalCounts=x['originalCounts'])))
if __name__=='__main__':main()
