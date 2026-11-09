#!/usr/bin/env python3
"""Inventory direct cached IR references; dynamic calls stay unresolved.
IR interpretation prioritizes the ir view over the main view, as in pinned
Lean.Compiler.IR.findEnvDecl. Constructor references are not function calls.
"""
import argparse,collections,hashlib,json,pathlib,runpy
HERE=pathlib.Path(__file__).resolve().parent
API=runpy.run_path(str(HERE/'audit.py'));HASH=runpy.run_path(str(HERE/'module_graph.py'))['sha']

def measure(path,view):
 receipt=json.loads(pathlib.Path(str(path)+'.receipt.json').read_text())
 assert receipt['producer_sha256']==HASH(HERE/'IRExport.lean') and receipt['index_sha256']==HASH(path)
 assert receipt['modules_sha256']==HASH(HERE/'modules.txt')
 assert pathlib.Path(receipt['reference_view']).resolve()==view.resolve(),'Reference view differs from export receipt'
 assert 'version 4.24.0,' in receipt['lean'] and '797c613' in receipt['lean'],'Wrong native IR toolchain'
 src=API['sources']();paths=runpy.run_path(str(HERE/'native_summary.py'))['module_paths'](src,view);source_provenance={m:API['provenance'](p,src[p]) for m,p in paths.items()};provenance=collections.defaultdict(collections.Counter)
 totals=collections.Counter();areas=collections.defaultdict(collections.Counter);attributes=[];current=None;group={}
 def flush(module,records):
  if module is None:return
  area='.'.join(module.split('.')[:2]);c=collections.Counter();c['modules_with_ir']+=int(bool(records))
  for name,versions in records.items():
   row=versions.get('ir',versions.get('main'));c['functions']+=1
   if len(versions)==2:
    a={k:v for k,v in versions['main'].items() if k!='phase'};b={k:v for k,v in versions['ir'].items() if k!='phase'}
    c['dual_view_functions']+=1;c['differing_dual_views']+=int(a!=b)
   assert len(row['functions'])==len(row['function_owners']) and len(row['constructors'])==len(row['constructor_owners'])
   c['extern_functions']+=int(row['extern']);c['dynamic_call_sites']+=row['dynamic_calls']
   c['functions_with_dynamic_calls']+=int(row['dynamic_calls']>0)
   c['static_function_reference_occurrences']+=len(row['functions']);c['constructor_type_metadata_occurrences']+=len(row['constructors'])
   c['unresolved_function_owner_occurrences']+=sum(m is None for m in row['function_owners'])
   c['foreign_emission_functions']+=int(row['owner_module']!=module)
  areas[area].update(c);provenance[source_provenance[module]].update(c)
 for line in path.open():
  r=json.loads(line)
  if r['module']!=current:flush(current,group);current=r['module'];group={}
  if r['record']=='implemented_by':attributes.append(r);continue
  assert r['record']=='function' and r['phase'] in ('main','ir')
  versions=group.setdefault(r['name'],{});assert r['phase'] not in versions;versions[r['phase']]=r;totals['raw_function_rows']+=1
 flush(current,group)
 for c in areas.values():totals.update(c)
 pairs={(r['name'],r['implementation']) for r in attributes};old={tuple(p) for p in json.loads((HERE/'compiler-edges.json').read_text())}
 summary=dict(base=API['BASE'],status='partial',graph_sha256=HASH(path),counts=dict(sorted(totals.items())),areas={k:dict(sorted(v.items())) for k,v in sorted(areas.items())},provenance={k:dict(sorted(v.items())) for k,v in sorted(provenance.items())},implemented_by_entries=len(attributes),implemented_by_pairs=len(pairs),aggregate_override_pairs_missing_from_module_entries=len(old-pairs),module_override_pairs_missing_from_aggregate=len(pairs-old),
  verdict='Direct IR references are measured; higher-order and reflective dependencies remain unresolved. No deletion certification follows.',
  boundaries=['Main/IR duplicate views are counted once using the native ir-first priority.',
   'Raw constructors fields contain constructor and case datatype metadata, including anonymous/irrelevant names; these are not declaration-use edges.',
   'Counts describe serialized IR functions, including boxed, closure and specialization helpers; they are not source declaration counts.',
   'Dynamic application sites are unresolved. Native owner hints do not solve higher-order targets or runtime name construction.',
   'This inventory does not establish the exact CI entrypoint closure or complete declaration liveness.'])
 return summary,sorted(attributes,key=lambda r:(r['module'],r['name'],r['implementation']))

def main():
 p=argparse.ArgumentParser();p.add_argument('--graph',type=pathlib.Path,required=True);p.add_argument('--out',type=pathlib.Path,required=True);p.add_argument('--view',type=pathlib.Path,required=True);p.add_argument('--check',action='store_true');a=p.parse_args();summary,attributes=measure(a.graph,a.view);a.out.mkdir(parents=True,exist_ok=True)
 for name,obj in [('ir-summary.json',summary),('module-compiler-attributes.json',attributes)]:
  body=json.dumps(obj,indent=2,sort_keys=True)+'\n';assert len(body.encode())<1000000
  if a.check:assert (a.out/name).read_text()==body,'STALE '+name
  else:(a.out/name).write_text(body)
 print('IR_INVENTORY_PASS',summary['counts']['functions'],summary['counts']['dynamic_call_sites'],summary['implemented_by_pairs'])
if __name__=='__main__':main()
