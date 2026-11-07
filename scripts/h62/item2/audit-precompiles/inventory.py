#!/usr/bin/env python3
"""Full frozen source signature/hypothesis inventory. Does not promote proof status.

All explicit binders are retained with exact source text. Effective source-scope
variables are recorded separately; only used variables are prepended to full types.
The manual proof-role table is reviewed, not inferred from binder names or types.
"""
import argparse, collections, hashlib, json, pathlib, re
from census import BASE, ROOT, census, mask
ROLE_FILE=ROOT/'tests/h62/item2/audit-precompiles/hypothesis-roles.json'


def boundary(text):
 depth=0
 for i,c in enumerate(text):
  if c in '([{': depth+=1
  elif c in ')]}': depth-=1
  elif c==':' and depth==0: return i
 raise ValueError('no type boundary: '+text)


def groups(text):
 result=[];i=0
 while i<len(text):
  if text[i].isspace():i+=1;continue
  start=i;op=text[i]
  if op not in '({[':raise ValueError('unsupported binder syntax: '+text[i:])
  stack=[{'(':')','{':'}','[':']'}[op]];i+=1
  while stack and i<len(text):
   c=text[i]
   if c in '({[':stack.append({'(':')','{':'}','[':']'}[c])
   elif c in ')}]':
    if c!=stack.pop():raise ValueError('binder delimiters')
   i+=1
  if stack:raise ValueError('unclosed binder')
  raw=text[start:i];inner=raw[1:-1]
  try:j=boundary(inner)
  except ValueError:
   if op!='[':raise
   result.append({'source':raw,'names':[],'type':inner.strip(),'style':'instance'})
   continue
  names=inner[:j].split();typ=inner[j+1:].strip()
  if not names or not typ:raise ValueError('empty binder')
  result.append({'source':raw,'names':names,'type':typ,'style':{'(':'explicit','{':'implicit','[':'instance'}[op]})
 return result


def source_context(source,line):
 """Active namespace/section/mutual-scoped variable commands, not history."""
 prefix='\n'.join(mask(source).splitlines()[:line-1])
 frames=[{'vars':[]}]
 for s in prefix.splitlines():
  m=re.match(r'^[ \t]*(namespace|section|mutual|end|variable)\b(.*)',s)
  if not m:continue
  kind,tail=m.groups()
  if kind in ['namespace','section','mutual']:frames.append({'vars':[]})
  elif kind=='end':
   if len(frames)>1:frames.pop()
  else:frames[-1]['vars'].extend(groups(tail.strip()))
 return [v for f in frames for v in f['vars']]


def split_declaration(d):
 prefix=('private ' if d['visibility']=='private' else '')+'theorem '+d['name'].rsplit('.',1)[-1]
 if not d['signature'].startswith(prefix):raise ValueError('unexpected declaration header')
 rest=d['signature'][len(prefix):].strip();j=boundary(rest)
 return rest[:j].strip(),rest[j+1:].strip()


def mentioned(name,text):
 return re.search(r'(?<![\w\'])'+re.escape(name)+r'(?![\w\'])',text) is not None


def receipts(path):
 data=json.loads((path/'statement-coverage.json').read_text())
 return {r['name']:r for r in data['rows']}


def owner_wait(path):
 if path.startswith('Bridge/'):
  return ['solidity-h62-6-20261106/migrate-bridge','solidity-sol-20261103/precompile-agreement','solidity-h62-6-20261106/migrate-precompiles']
 if path=='Solidity/Stipend/Rule.lean':return ['solidity-h62-6-20261106/migrate-syntax']
 if any('/'+part+'.lean' in path for part in ['Bls12381','PointEval','Osaka']):
  return ['solidity-h62-6-20261106/migrate-precompiles']
 return []


def checked_type_receipt(evidence):
 proof=ROOT/'tests/h62/item2/audit-precompiles/TypeFidelity.lean'
 meta=json.loads((evidence/'type-fidelity-final.json').read_text())
 assert meta['exit']==0 and not meta.get('resource_stop') and not meta['timeout'] and meta['inputs_unchanged']
 assert meta['cwd']==str(ROOT) and meta['command'][-1]==str(proof.relative_to(ROOT))
 assert meta['input_sha256'][str(proof)]==hashlib.sha256(proof.read_bytes()).hexdigest()
 assert all(pathlib.Path(p).is_file() and hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()==h for p,h in meta['input_sha256'].items())
 from fidelity import generate as frozen_types
 assert proof.read_text()==frozen_types()
 return 'type-fidelity-final.json'


def checked_fixture_receipt(evidence):
 proof=ROOT/'tests/h62/item2/audit-precompiles/JointPremiseFixture.lean'
 meta=json.loads((evidence/'joint-fixture.json').read_text())
 assert meta['exit']==0 and meta['inputs_unchanged'] and not meta.get('resource_stop') and not meta['timeout']
 assert meta['cwd']==str(ROOT) and meta['command'][-1]==str(proof.relative_to(ROOT))
 assert meta['input_sha256'][str(proof)]==hashlib.sha256(proof.read_bytes()).hexdigest()
 assert all(pathlib.Path(p).is_file() and hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()==h for p,h in meta['input_sha256'].items())
 log=(evidence/'joint-fixture.log').read_text()
 assert "H62.AuditPrecompiles.msm_joint_premises_fixture' depends on axioms: [propext]" in log and 'sorryAx' not in log
 return dict(theorem='H62.AuditPrecompiles.msm_joint_premises_fixture',receipt='joint-fixture.json',kind='isolated numeric constraints; original BLS interface not imported',counts_as_original_statement_witness=False)


def in_memory_raw_target(source,patch):
 """Strict supplied Raw diff reconstruction; never writes or invokes patch tools."""
 text=patch.decode();parts=text.splitlines(keepends=True);lines=source.decode().splitlines(keepends=True)
 assert parts[0]=='diff --git a/Solidity/Syntax/Raw.lean b/Solidity/Syntax/Raw.lean\n'
 assert parts[2]=='--- a/Solidity/Syntax/Raw.lean\n' and parts[3]=='+++ b/Solidity/Syntax/Raw.lean\n'
 out=[];cursor=0;i=4;hunks=0
 while i<len(parts):
  m=re.match(r'@@ -(\d+),(\d+) \+(\d+),(\d+) @@',parts[i]);assert m,'unexpected hunk'
  start,count,new_start,new_count=map(int,m.groups());assert start-1>=cursor
  out.extend(lines[cursor:start-1]);cursor=start-1;assert len(out)==new_start-1
  i+=1;old_used=new_used=0
  while i<len(parts) and not parts[i].startswith('@@ '):
   line=parts[i];kind=line[0];body=line[1:];assert kind in ' +-'
   if kind in ' -':assert lines[cursor]==body,'source context differs';cursor+=1;old_used+=1
   if kind in ' +':out.append(body);new_used+=1
   i+=1
  assert (old_used,new_used)==(count,new_count)
  hunks+=1
 assert hunks==5
 out.extend(lines[cursor:])
 return ''.join(out).encode()


def pending_wait_disposition(rows,evidence):
 """Attach current producer waits. Content-addressed partial input is never acceptance."""
 packet=json.loads((ROOT/'tests/h62/item2/audit-precompiles/partial-Raw-receipt.json').read_text())
 raw=(evidence/packet['inline_patch_evidence']).read_bytes()
 assert hashlib.sha256(raw).hexdigest()==packet['reported_host_patch_sha256']==packet['inline_excerpt_sha256']
 source=(ROOT/'Solidity/Syntax/Raw.lean').read_bytes()
 assert hashlib.sha256(in_memory_raw_target(source,raw)).hexdigest()==packet['reconstructed_source_sha256']==packet['reported_source_sha256']
 assert (ROOT/'Solidity/Syntax/Raw.lean').read_bytes()==source
 assert packet['reconstructed_source_sha_verified'] and packet['strict_in_memory_hunks_verified']==5
 assert packet['reported_axiom_growth_entries']==30 and packet['axiom_growth_root_review'].startswith('pending')
 assert not packet['dependency_accepted'] and not packet['trust_accepted'] and not packet['holds_lifted'] and not packet['original_source_modified']
 disposition=json.loads((ROOT/'tests/h62/item2/audit-precompiles/h70-waits.json').read_text())['current_disposition']
 assert disposition['compiler_success_owner']=='claudecloud/move5-20261106/v14-g43'
 assert disposition['compiler_route_status']=='staged-pending-delivery' and not disposition['compiler_delivery_confirmed']
 assert not disposition['partial_Raw_is_dependency_acceptance']
 matrix={}
 for row in rows:
  if row['kernel_applicability_checked']:continue
  if row['file'].startswith('Bridge/'):
   group='Bridge-compatible-dependencies';target='Compatible pinned-v4.35 Bridge dependencies from migrate-bridge AND precompile-agreement; transitive BLS prerequisite still pending.'
  elif row['file']=='Solidity/Stipend/Rule.lean':
   group='Syntax-Raw';target='Solidity/Syntax/Raw.lean; partial source received, root review of 30 reported axiom-growth entries and full dependency acceptance still pending.'
  else:
   assert row['file'] in ['Solidity/Precompiles/Bls12381.lean','Solidity/Precompiles/PointEval.lean','Solidity/Precompiles/Osaka.lean']
   group='Bls12381';target='Solidity/Precompiles/Bls12381.lean:171/172; migrate-precompiles receipt pending.'
  row['pending_wait_group']=group;row['pending_wait_target']=target;row['dependency_receipt_accepted']=False
  counts=matrix.setdefault(group,{'statements':0,'categories':collections.Counter()})
  counts['statements']+=1;counts['categories'][row['category']]+=1
 assert {k:v['statements'] for k,v in matrix.items()}=={'Bls12381':29,'Syntax-Raw':12,'Bridge-compatible-dependencies':73}
 assert sum(v['statements'] for v in matrix.values())==114
 return dict(groups=matrix,current_disposition=disposition,partial_Raw=dict(status='partial-held',content_hashes_verified=True,trust_accepted=False,dependency_accepted=False,reported_axiom_growth_entries=30,root_review='pending'),boundary='Exclusive primary wait groups classify the same 114 pending cases. Transitive providers may overlap. No kernel status or witness count changes.')


def generate(evidence):
 fixture=checked_fixture_receipt(evidence)
 type_receipt=checked_type_receipt(evidence)
 source=census();roles=json.loads(ROLE_FILE.read_text())['proof_binders'];coverage=receipts(evidence)
 rows=[];all_proofs=[]
 for f in source['files']:
  text=(ROOT/f['path']).read_text()
  opens=re.findall(r'(?m)^open[^\n]*',mask(text))
  imports=re.findall(r'(?m)^import[ \t]+([^\n]+)',mask(text))
  for d in f['declarations']:
   binders_text,conclusion=split_declaration(d)
   explicit=groups(binders_text)
   active=source_context(text,d['line'])
   if any(not b['names'] for b in explicit+active):raise ValueError('anonymous active instance requires elaboration: '+d['name'])
   # Scope variables enter a declaration only if their names occur in its type.
   # Frozen scope contains no mutually dependent implicit variable groups.
   inherited=[b for b in active if any(mentioned(n,binders_text+' '+conclusion) for n in b['names'])]
   effective=[];known=[];proof_names=roles.get(d['name'],{})
   for origin,bs in [('source-scope',inherited),('declaration',explicit)]:
    for b in bs:
     for n in b['names']:
      scope=proof_names.get(n)
      role='proof-hypothesis' if scope else ('type-parameter' if b['type']=='Type' else 'data-parameter')
      effective.append(dict(name=n,source_group=b['source'],type=b['type'],style=b['style'],origin=origin,role=role,premise_scope=scope,depends_on=[k for k in known if mentioned(k,b['type'])]))
      known.append(n)
   found={b['name'] for b in effective if b['role']=='proof-hypothesis'}
   if found!=set(proof_names):raise ValueError('proof annotation does not match frozen binder '+d['name'])
   proofs=[b for b in effective if b['role']=='proof-hypothesis'];data=[b for b in effective if b['role']!='proof-hypothesis']
   category='proof-premises' if proofs else ('unconditional-data-domain' if data else 'closed-statement')
   allbinders=' '.join(b['source'] for b in inherited)+(' ' if inherited and binders_text else '')+binders_text
   full=('∀ '+allbinders+', '+conclusion) if allbinders else conclusion
   checked=coverage[d['name']]['status']!='pending'
   group={'id':d['name']+'.all-hypotheses','proof_binders':[b['name'] for b in proofs],
          'configuration_binders':[b['name'] for b in proofs if b['premise_scope']=='configuration'],
          'input_binders':[b['name'] for b in proofs if b['premise_scope']=='per-input'],
          'requirement':'One common data/configuration tuple must satisfy all hypotheses; separate inhabitance is insufficient.',
          'kernel_joint_witness_checked':coverage[d['name']]['status']=='witness-checked'}
   row=dict(name=d['name'],file=f['path'],line=d['line'],visibility=d['visibility'],source_owner=f['owner'],signature=d['signature'],signature_sha256=d['signature_sha256'],conclusion=conclusion,active_source_variables=active,effective_source_scope_variables=inherited,binders=effective,source_full_type=full,source_full_type_sha256=hashlib.sha256(full.encode()).hexdigest(),namespace=d['name'].rsplit('.',1)[0],package_root=('Bridge' if f['path'].startswith('Bridge/') else '.'),file_imports=imports,file_open_commands=opens,category=category,joint_premises=group,explicit_global_premise_structures=[],applicability_status=coverage[d['name']]['status'],kernel_applicability_checked=checked,kernel_full_type_checked=checked,kernel_full_type_receipt=(type_receipt if checked else None),private_constant_name_pending=d['visibility']=='private',wait_for=owner_wait(f['path']) if not checked else [],full_type_boundary='Source reconstruction with active frozen variables. Only the 24 buildable public types have kernel full-type receipts; private elaborated names remain pending.')
   if d['name'] in ['Solidity.Precompiles.Bls12381.msmGas_succ','Solidity.Precompiles.Bls12381.msmGas_mono']:row['isolated_joint_constraint_fixture']=fixture
   if category=='closed-statement':row['remaining_work']='No hypothesis/input tuple to witness; import original constant and verify entire frozen closed statement plus axioms after producer receipt. Not promoted as checked.'
   elif not checked:row['remaining_work']='Construct one tuple with all data and hypotheses together; instantiate original theorem and check full frozen type after producer receipt.'
   else:row['remaining_work']='Retain checked receipt; complete assignment-wide compiler/observation/final gates.'
   if any(t in binders_text for t in ['Loc C','Stmt C','Prog C','LoopAnn C','Body C','Val C','Src C']):
    row['dependent_domain_caution']='Choose one Contract C supporting every typed program/location/annotation in this statement; Contract inhabitance alone is insufficient.'
   if d['name'].endswith('identity_unaffordable'):
    row['feasibility_caution']='huge is a per-input representability condition. A symbolic logical ByteArray-size construction is not a feasible allocation/external-EVM witness. No runtime feasibility or vacuity result is inferred.'
   if d['name'].endswith('pointEval_result'):
    row['feasibility_caution']='h requires one actual successful KZG input/output pair. Source #guard vectors are computed controls, not a simultaneous kernel premise witness.'
   rows.append(row);all_proofs.extend(proofs)
 if set(roles)!={r['name'] for r in rows if r['category']=='proof-premises'}:raise ValueError('unmatched annotation')
 counts=collections.Counter(r['category'] for r in rows)
 assert len(rows)==len({r['name'] for r in rows})==138
 assert counts=={'proof-premises':37,'unconditional-data-domain':73,'closed-statement':28},counts
 assert len(all_proofs)==47 and sum(b['premise_scope']=='configuration' for b in all_proofs)==7
 assert sum(r['kernel_applicability_checked'] for r in rows)==24
 pending=collections.Counter(r['category'] for r in rows if not r['kernel_applicability_checked'])
 assert pending=={'proof-premises':30,'unconditional-data-domain':56,'closed-statement':28},pending
 waits=pending_wait_disposition(rows,evidence)
 return dict(base=BASE,pending_wait_disposition=waits,source_classification_complete=True,kernel_inventory_complete=False,statements=138,source_classified=138,isolated_fixtures_checked=1,proof_hypothesis_statements=37,proof_hypothesis_binders=47,configuration_proof_binders=7,input_proof_binders=40,unconditional_data_statements=73,closed_statements=28,kernel_applicability_checked=24,pending=114,pending_categories=dict(pending),boundary='Source classification is complete; kernel signature/applicability census remains incomplete. No pending statement, owner theorem, or producer receipt is promoted.',global_context_notes=[
  {'name':'FieldOps','kind':'implementation typeclass','source':'Solidity/Precompiles/Field.lean:85','distinction':'No active quantified FieldOps/NeZero premise binder occurs in these 138 theorem signatures. Concrete field instances are implementation context, not per-input validity witnesses.'},
  {'name':'Solidity.Precompiles.Osaka.fixed','kind':'global data object','source':'Solidity/Precompiles/Osaka.lean:84','distinction':'The frozen definition supplies one Fixed object. Source presence/record inhabitance does not establish a successful call on every input or an actual compiler-success theorem; BLS-dependent revalidation still waits.'},
  {'name':'Solidity.Stipend.Obligation','kind':'global compiler predicate, not a premise record in this census','source':'Solidity/Stipend/Rule.lean:173','distinction':'Separate actual V14/G43 compiler-success theorem remains pending under the coordinator decision; data/function assignments are not compiler execution witnesses.'},
  {'name':'C : Contract','kind':'implicit global data parameter in 12 declarations','source':'Solidity/Stipend/Rule.lean:53','distinction':'Retain C in every full type and choose the same C for all dependent input terms; Contract inhabitance alone does not supply Loc/Val/Prog/Body feasibility.'}],rows=rows)


def markdown(data):
 out=['# Frozen precompile signature and hypothesis inventory','',
      'Source classification: 138/138. Kernel type/applicability coverage: 24/138; 114 pending.',
      'Source reconstruction is not elaborated-type verification, premise satisfiability, compiler success, or external-EVM evidence. Private names below are lexical source IDs.', '',
      '37 statements have 47 top-level proof binders (7 configuration constraints, 40 per-input); nested quantifiers remain inside their exact predicate types.',
      '73 statements have data/type parameters only; 28 are closed and still need whole-statement fidelity checks.', '']
 for r in data['rows']:
  out += ['## '+r['name'],'', 'Source: '+r['file']+':'+str(r['line']),
          'Owner: '+r['source_owner'], 'Package root: '+r['package_root'],
          'Imports: '+', '.join(r['file_imports']), 'Open commands: '+'; '.join(r['file_open_commands']),
          'Category: '+r['category'],
          'Applicability: '+r['applicability_status'],
          'Full kernel type checked: '+str(r['kernel_full_type_checked']), '',
          'Frozen declaration:', '```text',r['signature'],'```','',
          'Full source type with effective implicit context:', '```text',r['source_full_type'],'```','',
          'Binders (all names/types retained; scope is configuration or per-input only for proof hypotheses):']
  if not r['binders']:out += ['- None: closed statement.']
  for b in r['binders']:
   out += ['- '+b['name']+' : '+b['type'].replace('\n',' ')+'; '+b['role']+'; '+str(b['premise_scope'])+'; '+b['origin']]
  if r.get('pending_wait_target'):out += ['', 'Exact producer wait: '+r['pending_wait_target']+' Dependency accepted: False.']
  out += ['', 'Joint requirement: '+r['joint_premises']['requirement'],
          'Remaining: '+r['remaining_work'], 'Wait for: '+(', '.join(r['wait_for']) or 'assignment-wide producer/final gates')]
  if r.get('dependent_domain_caution'):out += ['Caution: '+r['dependent_domain_caution']]
  if r.get('feasibility_caution'):out += ['Caution: '+r['feasibility_caution']]
  if r.get('isolated_joint_constraint_fixture'):out += ['Isolated fixture is checked but does not promote this original BLS declaration.']
  out += ['']
 return '\n'.join(out).rstrip()+'\n'


if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--evidence',type=pathlib.Path,required=True);p.add_argument('--check',action='store_true');a=p.parse_args()
 data=generate(a.evidence);dest=a.evidence/'hypothesis-inventory.json';rendered=json.dumps(data,indent=2,ensure_ascii=False)+'\n'
 md=a.evidence/'hypothesis-inventory.md'
 if a.check:
  assert dest.read_text()==rendered,'source inventory differs'
  assert md.read_text()==markdown(data),'readable source inventory differs'
 else:
  dest.write_text(rendered);md.write_text(markdown(data))
 print('SOURCE_CLASSIFICATION 138/138; proof-statements=37 proof-binders=47 data-only=73 closed=28; KERNEL_CHECKED24 PENDING114')
