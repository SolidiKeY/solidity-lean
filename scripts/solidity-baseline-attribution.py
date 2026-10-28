#!/usr/bin/env python3
"""Reproduce the reviewed follow-up without modifying original baseline evidence.

The TSV is human-reviewed evidence, not keyword classification. An evidence-needed
row is an exact open diagnostic question, not an invented missing implementation.
"""
import argparse
import hashlib
import json
from pathlib import Path
import tarfile

BASE = Path('tests/upstream/baseline-20261028')
IMMUTABLE = {
 str(BASE/'gaps/gaps.json'): '33a03184bb0ec6c4ce0e8947ece7eb5c0041993beae0b05c87cda097f71eb01c',
 str(BASE/'unmapped-partial-features.txt'): '777285e4edc927810958f950e51e1d0e90fb50e2a211da4db587d537a2420fdb',
 str(BASE/'portable-evidence.tar.gz'): '5a200e1932c0d12392dd0a27b52b238e622b7f84643b706263d48052078e32ed',
 'docs/solidity-features.json': 'e86f5b65e6384ce4d0354d7935e7dfefe4842ba4043f71500fa7993757c63b9b',
 'tests/upstream/solidity-0.8.38.tar.gz': '9200f2a26b08be5b77faf877c44f5cfbf5ea95f1bccc45dae559d2fbc7cefb2d',
}

CITATIONS = {
 'source': [('docs/feature-work/source-admission.md', 10, 56), ('docs/feature-work/source-admission.md', 80, 106)],
 'specsyntax': [('docs/feature-work/declarations-metadata.md', 1644, 1660)],
 'agg': [('docs/feature-work/aggregates.md',40,60),('docs/feature-work/aggregates.md',191,225)],
 'abi': [('docs/feature-work/abi-hashes.md',34,78)],
 'world': [('docs/feature-work/contract-world.md',38,80)],
 'dispatch': [('docs/semantic-gaps.md',59,65),('docs/feature-work/finite-dispatch.md',47,63)],
 'basector': [('Solidity/Frontend/SolcJson/Contract.lean',1780,1787)],
 'mixed': [('docs/feature-work/declarations-metadata.md',1460,1469)],
 'operator': [('docs/feature-work/numeric-operators.md',8,46)],
 'modifier': [('docs/solc-alignment.md',612,629),('Solidity/Syntax/Elab/Lower.lean',605,616)],
 'lifetime': [('docs/lifetime.md',37,47),('docs/lifetime.md',140,158)],
 'mutability': [('docs/options.md',74,78),('docs/feature-work/contract-world.md',59,79)],
 'initial': [('docs/feature-work/declarations-metadata.md',1187,1210),('Solidity/Frontend/SolcJson/Contract.lean',1634,1642)],
 'enum': [('docs/feature-work/declarations-metadata.md',1453,1459),('docs/feature-work/declarations-metadata.md',1494,1500)],
 'inputs': [('docs/source-inputs.md',1,27),('docs/semantic-gaps.md',17,30)],
 'recursive': [('docs/feature-work/recursive-types.md',1,8),('docs/feature-work/recursive-types.md',34,46),('docs/solc-alignment.md',572,589)],
 'numericlatest': [('docs/feature-work/numeric-operators.md',649,678)],
 'push': [('docs/feature-work/aggregates.md',98,109)],
 'tails': [('docs/solc-alignment.md',344,371),('docs/solc-alignment.md',568,571),('docs/options.md',376,399)],
 'code': [('docs/feature-work/declarations-metadata.md',1443,1452),('docs/feature-work/source-admission.md',21,25)],
 'scoped': [('Solidity/Syntax/Scoped.lean',6,31),('docs/feature-work/source-admission.md',116,125)],
 'alignment': [('docs/solc-alignment.md',27,30)],
 'jumps': [('Solidity/Syntax/Elab/Lower.lean',450,480),('docs/loops.md',57,62)],
 'calls': [('docs/feature-work/calls-exceptions.md',34,40),('docs/feature-work/calls-exceptions.md',58,68),('docs/semantic-gaps.md',34,45),('docs/feature-work/calls-exceptions.md',95,106)],
 'rethrow': [('Solidity/Frontend/SolcJson/Body.lean',2059,2087)],
 'panic': [('Solidity/Syntax/Elab/Arms.lean',1861,1867),('Solidity/Tools/Upstream.lean',108,134)],
 'modular': [('docs/solc-alignment.md',63,83),('docs/feature-work/abi-hashes.md',565,570),('Solidity/Syntax/Elab/Arms.lean',325,338)],
 'hash': [('docs/semantic-gaps.md',229,243),('docs/solc-alignment.md',32,32)],
 'codecproof': [('docs/semantic-gaps.md',57,59),('docs/loops.md',57,62)],
 'recursion': [('docs/feature-work/numeric-operators.md',519,580)],
 'options': [('docs/options.md',30,36),('docs/options.md',271,280)],
 'arraybound': [('docs/solc-alignment.md',572,589)],
}
# Explicit source/reason associations, never a feature-name search. Related
# syntax in an excluded/host-blocked fixture alone does not prove a defect.
ASSOCIATIONS = {
 'stringLiterals': [('array/indexAccess/inline_array_index_access_strings.sol','has narrow positions')],
 'enumDeclarations': [('enums/enum_explicit_overflow.sol','a int where a uint is expected')],
 'enumTypes': [('enums/enum_explicit_overflow.sol','a int where a uint is expected')],
 'dynamicArrays': [('structs/recursive_structs.sol','recursive through an array')],
 'mappings': [('structs/struct_reference.sol','recursive through a mapping')],
 'storageLocation': [('structs/struct_reference.sol','recursive through a mapping')],
 'indexAccess': [('array/indexAccess/memory_arrays_dynamic_index_access_write.sol','has narrow positions'),('array/indexAccess/inline_array_index_access_strings.sol','has narrow positions')],
 'arithmetic': [('builtinFunctions/erc7201_overflow_expression.sol','out of the range of uint')],
 'checkedArithmetic': [('builtinFunctions/erc7201_overflow_expression.sol','out of the range of uint')],
 'assignment': [('array/string_literal_assign_to_storage_bytes.sol','tuple assignment to two targets')],
}

def sha(data): return hashlib.sha256(data).hexdigest()
def file_sha(path): return sha(path.read_bytes())
def load(path): return json.loads(path.read_text())
def canonical(x): return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def write(path,x): path.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')

def parse_table(text):
 rows=[]
 for line in text.splitlines():
  if not line or line.startswith('#'): continue
  p=[x.strip() for x in line.split('|')]
  if len(p)!=6: raise ValueError('expected six TSV columns: '+line)
  fid,kind,wave,key,remaining,missing=p
  if kind not in ('boundary','evidence-needed'): raise ValueError('invalid disposition')
  if not all(p): raise ValueError('empty attribution column')
  if kind=='evidence-needed' and missing=='none': raise ValueError('missing exact evidence question')
  rows.append(dict(id=fid,disposition=kind,nextWave=wave,citationKey=key,remaining=remaining,missingEvidence=missing))
 if len({r['id'] for r in rows})!=len(rows): raise ValueError('duplicate feature')
 return rows

def derive(root):
 base=root/BASE
 for path,expected in IMMUTABLE.items():
  if file_sha(root/path)!=expected: raise ValueError('immutable input hash mismatch '+path)
 old=load(base/'gaps/gaps.json'); manifest=load(root/'docs/solidity-features.json')
 original=[x['id'] for x in old['partialFeatures'] if not x['reviewedBoundaryGroups']]
 saved=(base/'unmapped-partial-features.txt').read_text().splitlines()
 if saved!=original or len(original)!=84: raise ValueError('historical unresolved list changed')
 rows=parse_table((base/'attribution/reviewed.tsv').read_text())
 if [r['id'] for r in rows]!=original: raise ValueError('reviewed rows must exactly cover the original 84 in order')
 features={f['id']:f for f in manifest['features']}
 # Read the immutable combined report from the committed archive, so this
 # works in a clone with none of the ignored raw work directories.
 archive=base/'portable-evidence.tar.gz'
 with tarfile.open(archive,'r:gz') as tf:
  report_member=str(BASE/'combined/results.json')
  report=json.load(tf.extractfile(report_member))
 if len(report['results'])!=9660: raise ValueError('incomplete archived corpus')
 counts={s:sum(r['status']==s for r in report['results']) for s in ('working','broken','blocked')}
 if counts!=old['counts']: raise ValueError('historical counts disagree')
 exact=[]
 for i,r in enumerate(report['results']):
  for j,v in enumerate(r.get('variants',[])):
   for k,g in enumerate(v.get('gaps',[])):
    exact.append((dict(path=r['path'],pipeline=v['pipeline'],fixtureStatus=r['status'],variantStatus=v['status'],gap=g),f'/results/{i}/variants/{j}/gaps/{k}',r.get('requiredPipelines',[])))
 if [x[0] for x in exact]!=old['exactVariantGaps']: raise ValueError('exact gap objects changed')
 local_paths=sorted({p for fid in original for p in features[fid].get('localEvidence',[])})
 local=[dict(path=p,sha256=file_sha(root/p),bytes=(root/p).stat().st_size) for p in local_paths]
 quotes={}
 for key in {r['citationKey'] for r in rows}:
  quotes[key]=[]
  for p,start,end in CITATIONS[key]:
   lines=(root/p).read_text().splitlines()
   if not 1<=start<=end<=len(lines): raise ValueError('invalid citation '+p)
   quotes[key].append(dict(path=p,startLine=start,endLine=end,sha256=file_sha(root/p),quote='\n'.join(lines[start-1:end])))
 with tarfile.open(root/'tests/upstream/solidity-0.8.38.tar.gz','r:gz') as upstream:
  for row in rows:
   f=features[row['id']]
   if f['current']!='partial': raise ValueError('manifest status changed')
   row.update(requirement=f['requirement'],localEvidence=f.get('localEvidence',[]),citations=quotes[row.pop('citationKey')],observedGaps=[])
   for suffix,reason in ASSOCIATIONS.get(row['id'],[]):
    matches=[x for x in exact if x[0]['path'].endswith('/'+suffix) and reason in x[0]['gap']['reason']]
    if not matches: raise ValueError('unreproduced association '+suffix)
    modes={x[0]['pipeline'] for x in matches}
    # Our selected associations all require both modes; never silently use one.
    if modes!={'legacy','viaIR'}: raise ValueError('missing associated mode '+suffix)
    p=matches[0][0]['path']; src=upstream.extractfile(p).read(); lines=src.decode().splitlines()
    for gap,pointer,required in matches:
     row['observedGaps'].append(dict(**gap,archiveMember=report_member,jsonPointer=pointer,requiredPipelines=required,sourceArchive='tests/upstream/solidity-0.8.38.tar.gz',sourcePath=p,sourceSha256=sha(src),sourceText='\n'.join(f'{i+1}: {s}' for i,s in enumerate(lines))))
   row['runtimeAssessment']='Direct source-backed association; exact variants and upstream source retained.' if row['observedGaps'] else 'All 661 fresh gap objects reviewed; no direct causal association established for this row. This does not assert no runtime fixture exists, or no remaining proof-interface gap.'
   row['proofAssessment']='Documentation/source inspection only. No new kernel proof or compiler/EVM execution was performed.'
 waves={}
 for row in rows:
  wave=waves.setdefault(row['nextWave'],dict(establishedBoundaryIds=[],evidenceNeededIds=[],documentaryBoundaryNeedingRuntimeReproductionIds=[]))
  wave['establishedBoundaryIds' if row['disposition']=='boundary' else 'evidenceNeededIds'].append(row['id'])
  if row['disposition']=='boundary' and row['missingEvidence']!='none': wave['documentaryBoundaryNeedingRuntimeReproductionIds'].append(row['id'])
 return dict(schemaVersion=1,baseCommit='f4dee4a29c2e208b36db4a4161a4723c735cd775',followupStartingCommit='66629757c15a819af17bb2d97e18c9bea4777351',
  provenance=dict(originalGapIndexSha256=file_sha(base/'gaps/gaps.json'),originalUnresolvedListSha256=file_sha(base/'unmapped-partial-features.txt'),manifestSha256=file_sha(root/'docs/solidity-features.json'),portableArchiveSha256=file_sha(archive),upstreamArchiveSha256=file_sha(root/'tests/upstream/solidity-0.8.38.tar.gz'),reviewTableSha256=file_sha(base/'attribution/reviewed.tsv'),generatorSha256=file_sha(root/'scripts/solidity-baseline-attribution.py')),
  originalUnresolvedIds=original,counts=counts,exactGapCount=len(exact),localEvidenceFiles=local,
  inheritedReviewedFeatures=[f for f in old['partialFeatures'] if f['reviewedBoundaryGroups']],inheritedBoundaryGroups=old['reviewedBoundaries'],
  originalReviewedFeatureCount=76,followupReviewedFeatureCount=len(rows),partialFeatureCount=160,diagnosticReviewComplete=True,
  assessmentCounts=dict(documentedOrSourceBoundaries=sum(r['disposition']=='boundary' for r in rows),evidenceNeeded=sum(r['disposition']=='evidence-needed' for r in rows),documentedBoundariesWithAdditionalEvidenceQuestions=sum(r['disposition']=='boundary' and r['missingEvidence']!='none' for r in rows),directObservedRows=sum(bool(r['observedGaps']) for r in rows)),
  semanticGapAttributionComplete=False, # exact open questions are not invented gaps
  evidenceNeededIds=[r['id'] for r in rows if r['disposition']=='evidence-needed'],
  scope='Diagnostic supplement only; original 76 reviewed boundary groups and original 84 unresolved IDs remain immutable historical evidence. The 84 rows now each have an explicit assessment. Evidence-needed rows are unresolved semantic attribution, not completed feature coverage.',
  nextWaves=waves,features=rows,
  unchanged='Original counts, observations, required pipelines, inputs, expectations, manifest statuses, keyword routing, and all performance outcomes remain unchanged. No D1/D2 decision, general step13 work, new Lean validation, or feature implementation.')

def render(x):
 lines=['# Feature attribution follow-up','',x['scope'],'',
  'Reproduce with `python3 scripts/solidity-baseline-attribution.py --check`. The committed TSV is the reviewed input; JSON retains exact source quotes, hashes, archived report JSON pointers, required modes and upstream source text. No name-based routing is treated as attribution.','',
  f"Reviewed all {x['followupReviewedFeatureCount']} formerly unmapped IDs; {len(x['evidenceNeededIds'])} retain specific missing-evidence questions. `diagnosticReviewComplete` means every row was assessed; `semanticGapAttributionComplete=false` means those questions have not become established gaps. The prior 76 boundary associations remain historical, not revalidated completeness claims.",'',
  f"Separately, {x['assessmentCounts']['documentedBoundariesWithAdditionalEvidenceQuestions']} established documentary boundaries retain an additional reproduction/assurance question. These are not included in the {len(x['evidenceNeededIds'])} evidence-needed rows; none is a newly claimed runtime defect without the explicit source/variant links.",'',
  'A row without observedGaps does not mean no fixture exists or no proof gap remains. Documentary limits can be established without a runtime counterexample; exact missing reproduction/assurance is listed per row. None of these inspections is a new kernel proof.','',
  '| Feature | Assessment | Next wave | Remaining shape or limit | Exact missing evidence |','|---|---|---|---|---|']
 for r in x['features']:
  cite=r['citations'][0]; link=f"../../../../{cite['path']}"
  lines.append(f"| `{r['id']}` | {r['disposition']} | {r['nextWave']} | {r['remaining']} ([source]({link})) | {r['missingEvidence']} |")
 lines+=['','## Next waves','', 'These are feature-specific diagnostic queues, not changes to other lanes or profile decisions. Existing keyword queues remain untouched.','']
 for wave,q in sorted(x['nextWaves'].items()):
  lines += [f'### {wave}','', 'Established boundaries: '+', '.join(q['establishedBoundaryIds'])+'.','', 'Evidence needed: '+(', '.join(q['evidenceNeededIds']) or 'none')+'.','', 'Documented boundaries still needing a dedicated runtime reproduction: '+(', '.join(q['documentaryBoundaryNeedingRuntimeReproductionIds']) or 'none')+'.','']
 return '\n'.join(lines).rstrip()+'\n'

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1]);p.add_argument('--check',action='store_true');a=p.parse_args();root=a.root.resolve();x=derive(root)
 outputs={root/BASE/'attribution/index.json':json.dumps(x,indent=2,ensure_ascii=False)+'\n',root/BASE/'attribution/README.md':render(x)}
 for path,text in outputs.items():
  if a.check:
   if not path.exists() or path.read_text()!=text: raise ValueError('stale attribution output '+str(path))
  else: path.write_text(text)
 print(json.dumps(dict(reviewed=len(x['features']),evidenceNeeded=len(x['evidenceNeededIds']),observedFeatures=sum(bool(r['observedGaps']) for r in x['features']),exactGapCount=x['exactGapCount'],counts=x['counts'],semanticGapAttributionComplete=x['semanticGapAttributionComplete'],check=a.check)))
if __name__=='__main__': main()
