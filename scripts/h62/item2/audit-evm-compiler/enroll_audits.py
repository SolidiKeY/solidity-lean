#!/usr/bin/env python3
"""Reproduce enrollment from reviewable audit commands, not a bulk hand ledger.
Requires the frozen source census and successful final Lean receipts.
"""
import argparse,collections,json,pathlib,re
ROOT=pathlib.Path(__file__).resolve().parents[4]
p=argparse.ArgumentParser();p.add_argument('--source',required=True);p.add_argument('--evidence',required=True);p.add_argument('--output',required=True);a=p.parse_args()
census=json.loads(pathlib.Path(a.source).read_text());e=pathlib.Path(a.evidence)
rows=census['statements'];links=[];seen=set()
for module,pattern,status in [
 ('RefutationAudit',r'#audit_refutation "([^"\n]+)" as ([^\s]+)','intentional-impossibility-checked'),
 ('EntryAudit',r'#audit_joint_from "([^"\n]+)" using "([^"\n]+)" as ([^\s]+)','joint-witness-checked')]:
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
  if module=='RefutationAudit':
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
if counts!={'intentional-impossibility-checked':29,'joint-witness-checked':1}:raise ValueError('expected exactly 29 refutations and one joint witness')
pathlib.Path(a.output).write_text(json.dumps(dict(base=census['base'],links=links),indent=2)+'\n')
print(json.dumps(dict(enrolled=len(links),intentional=29,joint=1)))
