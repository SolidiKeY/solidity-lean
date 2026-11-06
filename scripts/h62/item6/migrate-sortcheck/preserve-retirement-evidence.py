import json,re,hashlib,shutil
from pathlib import Path
root=Path('/workspace/migrate-sortcheck-evidence'); out=Path('/workspace/migrate-sortcheck-retirement-staging/evidence'); out.mkdir(exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def copy(p,name):
 p=Path(p); q=out/name; shutil.copy2(p,q); return {'source':str(p),'artifact':name,'sha256':sha(q)}
files={
'old-full-interfaces.log':root/'old-tests3/tests.h62.item6.migrate-sortcheck.Interfaces.log',
'old-canonical.log':root/'h76/old-canonical-final/tests.h62.item6.migrate-sortcheck.CanonicalInterfaces.log',
'new-canonical.log':root/'h76/applied-canonical-final/tests.h62.item6.migrate-sortcheck.CanonicalInterfaces.log',
'new-unshimmed-interfaces.log':root/'resume-20261106/new-parser-interfaces/ParserInterfaces.log',
'generated-api-comparison.json':root/'h76/applied-interface-comparison.json',
'audit-roadmap-HANDOFF.md':root/'incoming/audit-roadmap-63d6ef9f-HANDOFF.md',
'implementation-owner-interface-result.json':Path('/workspace/migrate-sortcheck-handoff-93ab25f2/owner-interface-result.json'),
'implementation-reviews.md':root/'h76/reviews-final.md',
'old-clean-result.json':root/'resume-20261106/old-lake-clean/result.json',
'new-per-file-result.json':root/'h76/per-file-committed/result.json',
'new-native-result.json':root/'h76/native-conformance-final/result.json',
'new-directory-result.json':root/'h76/committed-directory-gate/result.json',
'H76-retained-SHA256SUMS':root/'h76/H76-retained-SHA256SUMS',
'H76-archive-SHA256SUMS':root/'h76/H76-archive-SHA256SUMS'}
provenance=[copy(p,n) for n,p in files.items()]
text=(out/'old-full-interfaces.log').read_text()
records=[]
for m in re.finditer(r'^DECLARATION ([^\n]+)\nTYPE (.*?)\nAXIOMS ([^\n]*)$',text,re.M|re.S):
 records.append({'name':m[1],'old_pretty_signature':m[2],'old_axioms':m[3],'visibility':'not captured; no name-based exclusion accepted'})
assert len(records)==658 and len({r['name'] for r in records})==658
old={r['name']:r for r in records}
def canon(p):
 lines=p.read_text().splitlines(); rows=[json.loads(l[len('CANONICAL '):]) for l in lines if l.startswith('CANONICAL ')]; assert len(rows)==int(next(l.split()[1] for l in lines if l.startswith('CANONICAL_COUNT '))); return {r[0]:r for r in rows}
a=canon(out/'old-canonical.log'); b=canon(out/'new-canonical.log'); assert len(a)==331 and len(b)==339
aliases=[]
for family in ['ReadDomain','ReadSite','SortVarcond']:
 n='Solidity.TacletAnnotations.'+family+'.toCtorIdx'; assert a[n][1:]==b[n][1:]
 aliases.append({'name':n,'old_signature':old[n]['old_pretty_signature'],'old_canonical_signature':a[n],'new_unshimmed_signature':None,'new_unshimmed_status':'absent in prior unshimmed export; see preserved raw log','shim_signature':old[n]['old_pretty_signature'],'shim_canonical_signature':b[n],'shim_source_signature':'type_of% '+family+'.ctorIdx','shim_body':family+'.ctorIdx','metadata':'protected, reducible, deprecated since 2025-08-25, completion blacklist','source_head':'93ab25f24dcb00c9a07a834a53c030c0f57b70d9'})
d=json.loads((out/'generated-api-comparison.json').read_text())
helpers=[{'name':n,'old_signature':old[n]['old_pretty_signature'],'old_canonical_signature':a[n],'new_canonical_signature':b[n],'shim_signature':None,'status':'old public shape not restored; H78 producer compatibility work remains'} for n in d['changed_alpha_structural_types']]
result={'boundary':'Static preservation of existing exports only; no new Lean run, public visibility or complete new Faithfulness export. All old records retained without underscore/debug filtering. Canonical arrays encode universes, binder kinds/order and names separately. No cross-version equivalence/compatibility acceptance implied.','old_full_records':records,'old_partial_canonical_count':len(a),'new_partial_canonical_count':len(b),'implemented_shims':aliases,'unshimmed_changed_helpers':helpers,'per_declaration_axiom_changes':d['axiom_deltas'],'raw_binder_name_changes':d.get('binder_name_deltas',d.get('binder_name_changes',{})),'full_comparison_artifact':'generated-api-comparison.json','provenance':provenance}
(out/'public-api-preservation.json').write_text(json.dumps(result,indent=2)+'\n')
(out/'goal-pause-capability.json').write_text(json.dumps({'requested_state':'PAUSED','exposed_goal_tools':['codex_goals_stop_goal(outcome=complete|blocked)'],'pause_tool_exposed':False,'transition_attempted_this_retirement':False,'reason':'No PAUSED operation available. Prior stop_goal rejected missing trusted CCA goal/source-turn context. Complete/blocked is not an authorized substitute.','implementation_state':'stopped','runtime_goal_state':'unconfirmed'},indent=2)+'\n')
print('Preserved',len(records),'old records;',len(aliases),'actual shims;',len(helpers),'unshimmed helpers')
