#!/usr/bin/env python3
"""Derive diagnostic gap indexes from an unchanged upstream runner report.

No fixture, observation, expectation, pipeline or verdict is rewritten. Keyword
routing is deliberately a many-to-many work queue, never feature attribution.
"""
import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROUTES = {
 'step-01-entrypoints': r'getter|entry.?point|imported.function|fallback|receive|functionDispatch|override|multiple return',
 'step-02-source-units': r'multi.source|source.?unit|remapping|using.?for|qualified.*error',
 'step-03-expressions': r'tuple|conditional|slice|range.?access|conversion|literal|shift|UDVT',
 'step-04-panic-revert': r'panic|revert|error.data|revertStrings|allocation',
 'step-06-world': r'host|external|contract.?world|creation|new.?contract|library|balance',
 'step-07-recursive': r'recurs|cyclic|type.?graph',
 'step-10-revert-proof-interface': r'catchData|computed.*revert|revert.*proof',
 'step-11-diamond-calls': r'diamond|callback|send|transfer',
 'step-12-specs': r'loop.?invariant|modifies|callback|static.*restrict|specification',
 'step-08-transient': r'transient|tload|tstore',
 'profile-decision-environment-logs': r'block\.|tx\.|blockhash|chainid|basefee|event|emit|log expectation',
 'excluded-machine-semantics': r'assembly|delegatecall|physical|storage.layout|gas expectation|gas.cost',
 'resource': r'timeout|timed.out|exhaust|resource|SIGKILL|SIGABRT|memory.limit|heartbeats|maximum.recursion|out.of.memory|ETIMEDOUT|ended.before.checkpoint|exitCode.{0,4}137',
}

# Reviewed source boundaries, not automatic interpretations of broad requirements.
BOUNDARIES = [
 ('slice-aliases', ['calldataLocation','memoryAliasing','rangeAccess'],
  'docs/calldata-slice-copies.md',
  'Uninitialized/rebound virtual slice descriptors and effectful/conditional calldata alias initializers; general writable whole-calldata copying and reference-element materialization remain explicit boundaries.'),
 ('pushed-members', ['arrayPush','arrayPushReference'],
  'docs/feature-work/aggregates.md',
  'Generated pushed-member stores require pure receivers; receiver mutation/calls and callback-capable RHS forms remain unsupported.'),
 ('source-admission', ['pragmaAbicoder','constants','exactConstants'],
  'docs/feature-work/source-admission.md',
  'Legacy ABI-v1 decoder admission and general constant-materialization bounds. Exact rational/literal support already exists; scalar-v1 replay does not establish raw-v1 decoding.'),
 ('source-units', ['sourceUnits','imports','usingFor','extensionCalls'],
  'docs/feature-work/declarations-metadata.md',
  'Multi-source provenance/remappings and broader using-for applicability remain to reproduce. Qualified error selectors already have bounded support.'),
 ('source-assurance', ['featureDetection','typeValidation'],
  'docs/feature-work/source-admission.md',
  'Executable admission scans are not extraction-completeness or lowering-equivalence proofs; external solc provenance neither authenticates handwritten JSON nor validates bytecode.'),
 ('allocation-panic', ['newMemory','panicCodes'],
  'docs/feature-work/abi-hashes.md',
  'Enormous-memory replay remains resource-blocked; allocation Panic(0x41) coverage is not established. Retained arithmetic/assertion bytes do not turn resource exhaustion into expected allocation panic.'),
 ('require-errors', ['requireBuiltin'],
  'docs/feature-work/abi-hashes.md',
  'Named error constructors inside require remain a source boundary; positional enum-free aggregate errors and named direct reverts have existing support.'),
 ('revert-proof-interface', ['revertStatement','revertBuiltin','revertPayloads','catchClauses'],
  'docs/semantic-gaps.md',
  'Computed catch-data bytes are executable but lack the general exact-data proof link; memory operands without static patterns admit arbitrary bytes and catchDataDiamond is false. Callback catches remain outside ordinary coverage.'),
 ('events', ['evaluationOrder','namedArguments','emitStatement','eventDeclarations'],
  'docs/feature-work/calls-exceptions.md',
  'Named event argument lists and qualified event names remain refused. Direct positional operands already execute; observable log traces remain excluded pending profile decision D2.'),
 ('entries', ['publicGetters','receiveFunction','fallbackFunction','overrideDeclarations'],
  'docs/feature-work/declarations-metadata.md',
  'Reference/enum/contract/function getter results; unsupported aggregate getters; general receive/fallback payment registration. Restricted later declaration milestones supersede older Left lists.'),
 ('dispatch', ['functionValues','internalFunctionTypes','externalFunctionTypes','functionSelector','functionAddress'],
  'docs/feature-work/finite-dispatch.md',
  'Reference arguments and signatures outside zero-argument internal bytes-memory return; external multi-return; renamed inherited/overloaded external selector identities; nominal signatures.'),
 ('aggregates', ['inlineArrays','tupleExpressions','tupleTypes','conditional','rangeAccess','calldataLocation','referenceCopyRules','implicitConversions'],
  'docs/feature-work/aggregates.md',
  'Reference-element slices; writable whole-calldata copies; external reference arguments; heterogeneous reference-return tuples; nominal aggregate identities; fixed-byte-width widening in snapshot copies requires shifting. Latest mixed-reference repairs already work.'),
 ('recursive', ['recursiveTypes','structTypes','structDeclarations','storageCopy','memoryLocation'],
  'docs/feature-work/recursive-types.md',
  'Ordinary importer/state/term/rule migration; ObsEq operation congruence and path commutation; heap-cycle copy policy. Standalone graph API does not establish ordinary source execution.'),
 ('world', ['newContract','creationTry','externalLibraryCalls','externalTypedCalls','libraries','worldAssumptions'],
  'docs/feature-work/contract-world.md',
  'General dynamic source creation and world composition; ABI/memory transfer, typed catches, callbacks/transient transfer; general library arguments/aggregate results; certified Reachable source wrappers. Gas remains excluded.'),
 ('abi', ['abiEncode','abiEncodePacked','abiEncodeWithSelector','abiEncodeWithSignature','abiEncodeCall','abiDecode','abiEntryValidation','errorDeclarations','revertPayloads','ecrecoverBuiltin'],
  'docs/feature-work/abi-hashes.md',
  'Named aggregate require constructors; noncanonical/lazy ABI entry layouts; nominal enum aggregate cardinality/legality; recursive graph ABI traversal; general external reference results; recursive round-trip and precompile equivalence proofs. M6 supersedes earlier scalar-only and custom-error gaps.'),
 ('transient', ['transientState'], 'docs/feature-work/transient-storage.md',
  'General composed source-world execution and source shapes beyond primitive/function-tag cells. Logical cells, self-call sharing, reset and rollback already exist; assembly/layout/gas/delegatecall remain excluded.'),
 ('specs', ['whileStatement','forStatement','staticCallRestriction','termination','callbackSemantics'],
  'docs/coverage-plan.md',
  'Step 12: quantified diamond loop invariants; finer modifies/aliases; view callees and reference recursion under callbacks; later self-calls; reachable-state diamond specs and old/net closer reads. Runtime corpus does not measure these proof interfaces.'),
]

def digest(path):
 return hashlib.sha256(path.read_bytes()).hexdigest()

def derive(report, manifest, root):
 rows=report['results']; paths=[r['path'] for r in rows]
 if len(paths)!=len(set(paths)): raise ValueError('duplicate fixture paths')
 gaps=[]; routes=defaultdict(list); unrouted=[]
 for row in rows:
  required=row.get('requiredPipelines',[])
  variants=row.get('variants',[])
  modes=[v.get('pipeline') for v in variants]
  if len(modes)!=len(set(modes)): raise ValueError('duplicate pipeline variant: '+row['path'])
  missing=[p for p in required if not any(v.get('pipeline')==p for v in variants)]
  if row['status']=='working' and (missing or any(v.get('status')!='working' for v in variants)): raise ValueError('working fixture lacks required pipelines: '+row['path'])
  for v in variants:
   for g in v.get('gaps',[]):
    gaps.append({'path':row['path'],'pipeline':v.get('pipeline'),'fixtureStatus':row['status'],'variantStatus':v.get('status'),'gap':g})
  if row['status']=='working': continue
  # Full JSON text retains nested diagnostics; routing never changes the row.
  haystack=json.dumps(row,ensure_ascii=False)
  matched=[name for name,pattern in ROUTES.items() if re.search(pattern,haystack,re.I)]
  item={'path':row['path'],'stage':row['stage'],'status':row['status'],'reason':row.get('reason'),'requiredPipelines':required,'missingPipelines':missing}
  for name in matched: routes[name].append(item)
  if not matched: unrouted.append(item)
 partial=[]
 for f in manifest['features']:
  if f['current']!='partial': continue
  boundaries=[b[0] for b in BOUNDARIES if f['id'] in b[1]]
  partial.append({'id':f['id'],'current':f['current'],'requirement':f['requirement'],'localEvidence':f.get('localEvidence',[]),'reviewedBoundaryGroups':boundaries,
   'attribution':'Reviewed documentation boundary; corpus routing is not feature completeness evidence.' if boundaries else 'No feature-specific remaining shape established by this diagnostic index; retain partial and consult localEvidence. Do not infer support from absence of a matching fixture.'})
 return {'metadata':report['metadata'],'corpusComplete':None,'partialFeatureGapInventoryComplete':False,'counts':{s:sum(r['status']==s for r in rows) for s in ('working','broken','blocked')},
  'stages':{stage:{s:sum(r['status']==s and r['stage']==stage for r in rows) for s in ('working','broken','blocked')} for stage in sorted({r['stage'] for r in rows})},
  'exactVariantGaps':gaps,'routes':{name:routes[name] for name in ROUTES},'unrouted':unrouted,'partialFeatures':partial,
  'reviewedBoundaries':[{'id':b[0],'features':b[1],'document':b[2],'documentSha256':digest(root/b[2]),'remaining':b[3]} for b in BOUNDARIES],
  'limitations':['Diagnostic evidence, not a universal semantic proof.','Many-to-many keyword queues are triage candidates, not semantic feature attribution.','All unworking fixtures remain indexed, including native harness and excluded/profile-decision cases.','No manifest status, expected observation or source pipeline is changed.']}

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--base',required=True,help='Starting origin/master commit; semantic sources must still match'); p.add_argument('results',type=Path); p.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1]); p.add_argument('--out',type=Path,required=True)
 a=p.parse_args(); root=a.root.resolve(); report=json.loads((a.results/'results.json').read_text()); summary=json.loads((a.results/'summary.json').read_text()); manifest=json.loads((root/'docs/solidity-features.json').read_text())
 metadata=report['metadata']
 for key,value in metadata.items():
  if summary.get(key)!=value: raise ValueError('summary/report provenance disagreement: '+key)
 if metadata.get('filter') is not None: raise ValueError('filtered run is not a full baseline')
 snapshot=json.loads((root/'tests/upstream/snapshot.json').read_text())
 expected={f['path'] for f in snapshot['files'] if re.search(r'\.(sol|yul|json|stack|ssa|asm|asmjson)$',f['path'])}
 if {r['path'] for r in report['results']}!=expected or summary['totalFixtureFiles']!=len(expected): raise ValueError('full snapshot fixture coverage differs')
 if metadata['archiveSha256']!=snapshot['archiveSha256']: raise ValueError('snapshot archive provenance differs')
 if metadata['runnerSha256']!=digest(root/'scripts/solidity-upstream.mjs') or metadata['compilerCodeAdapterSha256']!=digest(root/'scripts/solc-code.mjs'): raise ValueError('runner provenance differs')
 h=hashlib.sha256()
 for path in sorted((root/'Solidity').rglob('*.lean'),key=lambda p: str(p)):
  h.update((str(path.relative_to(root))+'\0').encode()); h.update(path.read_bytes())
 if metadata['modelSha256']!=h.hexdigest(): raise ValueError('current model provenance differs')
 subprocess.run(['git','diff','--exit-code',a.base,'--','Solidity','scripts/solidity-upstream.mjs','scripts/solc-code.mjs'],cwd=root,check=True,stdout=subprocess.DEVNULL)
 if summary['completedFixtureFiles']!=len(report['results']): raise ValueError('summary/report count disagreement')
 if not summary['complete']: raise ValueError('incomplete baseline: preserve it as blocked; do not issue complete gap lists')
 result=derive(report,manifest,root)
 if result['counts']!=summary['counts'] or result['stages']!=summary['stages']: raise ValueError('summary verdict counts differ')
 result['corpusComplete']=summary['complete']; result['provenance']={'startingCommit':a.base,'reportSha256':digest(a.results/'results.json'),'summarySha256':digest(a.results/'summary.json'),'manifestSha256':digest(root/'docs/solidity-features.json')}
 historical=root/'tests/upstream/results/results.json'
 if historical.exists():
  old=json.loads(historical.read_text()); before={r['path']:r for r in old['results']}
  result['historicalComparison']={'reportSha256':digest(historical),'metadata':old['metadata'],'limitation':'Historical and current runners/models differ: status changes are diagnostic, not a controlled implementation-only comparison.','totalComparedFixtures':len(report['results']),'fixturesWithChangedStatusOrPipelines':[{'path':r['path'],'historicalStatus':before.get(r['path'],{}).get('status'),'currentStatus':r['status'],'historicalRequiredPipelines':before.get(r['path'],{}).get('requiredPipelines',[]),'currentRequiredPipelines':r.get('requiredPipelines',[])} for r in report['results'] if before.get(r['path'],{}).get('status')!=r['status'] or before.get(r['path'],{}).get('requiredPipelines',[])!=r.get('requiredPipelines',[])]}
 a.out.mkdir(parents=True,exist_ok=False)
 (a.out/'gaps.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
 for name,rows in {**result['routes'],'unrouted':result['unrouted']}.items():
  (a.out/(name+'.txt')).write_text(''.join(r['path']+'\n' for r in rows))
 print(json.dumps({'counts':result['counts'],'exactVariantGaps':len(result['exactVariantGaps']),'partialFeatures':len(result['partialFeatures']),'routes':{k:len(v) for k,v in result['routes'].items()},'unrouted':len(result['unrouted'])},indent=2))
if __name__=='__main__': main()
