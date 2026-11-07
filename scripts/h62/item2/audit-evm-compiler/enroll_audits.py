#!/usr/bin/env python3
"""Reproduce enrollment from reviewable audit commands, not a bulk hand ledger.
Requires the frozen source census and successful final Lean receipts.
"""
import argparse,collections,json,pathlib,re
ROOT=pathlib.Path(__file__).resolve().parents[4]
p=argparse.ArgumentParser();p.add_argument('--source',required=True);p.add_argument('--evidence',required=True);p.add_argument('--output',required=True);group=p.add_mutually_exclusive_group();group.add_argument('--selectors-only',action='store_true');group.add_argument('--copy-selectors-only',action='store_true');group.add_argument('--loop-selectors-only',action='store_true');a=p.parse_args()
census=json.loads(pathlib.Path(a.source).read_text());e=pathlib.Path(a.evidence)
rows=census['statements'];links=[];seen=set()
cases = [
 ('RefutationAudit',r'#audit_refutation "([^"\n]+)" as ([^\s]+)','intentional-impossibility-checked'),
 ('EntryAudit',r'#audit_joint_from "([^"\n]+)" using "([^"\n]+)" as ([^\s]+)','joint-witness-checked')]
if a.selectors_only:cases=[('SelectorAudit',r'#audit_joint_witness "([^"\n]+)" as ([^\s]+) := by','joint-witness-checked')]
if a.copy_selectors_only:cases=[('CopySelectorAudit',r'#audit_joint_witness "([^"\n]+)" as ([^\s]+) := by','joint-witness-checked')]
if a.loop_selectors_only:cases=[('LoopSelectorAudit',r'#audit_joint_witness "([^"\n]+)" as ([^\s]+) := by','joint-witness-checked')]
for module,pattern,status in cases:
 path='tests/h62/item2/audit-evm-compiler/'+module+'.lean';text=(ROOT/path).read_text()
 receipt=json.loads((e/('final-'+module+'.json')).read_text())
 if receipt['exit']!=0:raise ValueError('unsuccessful Lean receipt')
 log=(e/('final-'+module+'.log')).read_text()
 for match in re.finditer(pattern,text):
  original=match[1];proof=match[match.lastindex]
  candidates=[r for r in rows if r['candidate_name']==original]
  if len(candidates)!=1:raise ValueError('ambiguous source identity: '+original)
  row=candidates[0];key=row['file']+':'+str(row['line'])
  if key in seen:raise ValueError('duplicate enrollment')
  seen.add(key)
  if module in ['SelectorAudit','CopySelectorAudit']:
   fixtures=re.findall(r'#audit_input_fixture "([^"\n]+)" as ([^\s]+)',text[:match.start()])
   if not fixtures:raise ValueError('missing correlated input fixture')
   certificate,fixture=fixtures[-1]
   fixture_marker='INPUT-FIXTURE: '+certificate+' => '+fixture
   if fixture_marker not in log:raise ValueError('missing checked fixture evidence')
   classification='Per-input compilation result, backend selector proof, contexts, resources, state and machine jointly witnessed using the closed '+certificate+'. Original is a selector equivalence; Input is not an additional original premise and no success claim is inferred.'
   if original.endswith('.object_rep'):
    classification='Per-input compilation result, backend selector, contexts, resources and both entry/output state and machine are jointly instantiated from '+certificate+'. The iff conclusion is not a premise: neither Rep truth nor execution success is claimed.'
   elif original.endswith('.memory_copy_free_input'):
    classification+=' The defaulted hasArrayCopy=false hypothesis is supplied explicitly together with the backend guard; the inhabited fixture source reverts at its destination check.'
   marker='JOINT: '+original+' => '+proof
  elif module=='LoopSelectorAudit':
   classification='Complete original data tuple uses typed nonempty loop/scoped-loop programs and real certificates from unchanged lower compilers, with backend selector proofs where required. Input and Room occur only in the iff conclusion; neither is asserted by this premise-satisfiability result.'
   if original.endswith('.construction_rep'):
    classification='Complete original compilation/backend/resource/entry/output data tuple; construction output is arbitrary typed logical data. Neither Rep truth nor source execution success follows. Existing closed construction fixture is reused unchanged.'
   marker='JOINT: '+original+' => '+proof
  elif module=='RefutationAudit':
   reason=re.search(r'-- Intentional: ([^\n]+)\n$',text[:match.start()])
   if not reason:raise ValueError('missing intentional classification')
   classification='H69 intentional negative control/separation: '+reason[1]+' Full reducing hypothesis package is impossible, not an ordinary success witness.'
   marker='REFUTATION: '+original+' => '+proof
  else:
   classification='Per-input program, compilation result, contexts, resource bounds, state, machine and Input certificate jointly supplied by the closed '+match[2]+'. No global producer premise or original conclusion used.'
   marker='JOINT-CERTIFICATE: '+original+' <= '+match[2]+' => '+proof
  if marker not in log or "'"+proof+"' depends on axioms:" not in log:raise ValueError('missing checked proof evidence')
  links.append(dict(original=original,statement_id=key,source_signature_sha256=row['source_signature_sha256'],status=status,proof=proof,module=path,classification=classification))
counts=collections.Counter(link['status'] for link in links)
expected={'joint-witness-checked':5} if (a.selectors_only or a.copy_selectors_only or a.loop_selectors_only) else {'intentional-impossibility-checked':29,'joint-witness-checked':1}
if counts!=expected:raise ValueError('unexpected enrollment split')
pathlib.Path(a.output).write_text(json.dumps(dict(base=census['base'],links=links),indent=2)+'\n')
print(json.dumps(dict(enrolled=len(links),intentional=counts.get('intentional-impossibility-checked',0),joint=counts.get('joint-witness-checked',0))))
