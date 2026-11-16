#!/usr/bin/env python3
"""Summarize the cached per-module native expression graph, not full liveness.
Only Solidity.Theorems theorem roots are classified; CI/check roots remain open.
Editor reference files supply module headers only, never edges or source ranges.
"""
import argparse,collections,csv,json,pathlib,runpy
HERE=pathlib.Path(__file__).resolve().parent
API=runpy.run_path(str(HERE/'audit.py'));NATIVE=runpy.run_path(str(HERE/'module_graph.py'))

def module_paths(src,view):
 result={}
 for p in src:
  f=view/pathlib.Path(p.removeprefix('vendor/LeanTeX/').removeprefix('Bridge/')).with_suffix('.ilean')
  if not f.is_file():continue
  m=json.loads(f.read_text())['module'];assert m not in result,(m,p,result.get(m));result[m]=p
 return result

def measure(source_root,graph,view):
 src=API['assert_sources'](source_root);source_provenance={p:API['provenance'](p,t) for p,t in src.items()};g=NATIVE['load'](graph);paths=module_paths(src,view)
 assert set(paths)=={m for m,r in g.modules.items() if r['selected']}
 roots={key for key,r in g.nodes.items() if key[0]=='Solidity.Theorems' and r['kind']=='theorem' and r['selection'] is not None}
 all_used,root_boundary=g.root_closure('Solidity.Theorems',[n for m,n in roots]);used=all_used & g.nodes.keys();line_counts={p:t.count('\n')+(int(bool(t) and not t.endswith('\n'))) for p,t in src.items()};areas=collections.defaultdict(collections.Counter);directories=collections.defaultdict(collections.Counter);provenance=collections.defaultdict(collections.Counter);lines=collections.defaultdict(lambda:collections.defaultdict(set))
 for key,r in g.nodes.items():
  p=paths[key[0]];cls='facade_used' if key in used else 'outside_facade_closure'
  destinations=(areas['/'.join(p.split('/')[:2])],directories[str(pathlib.PurePosixPath(p).parent)],provenance[source_provenance[p]])
  for c in destinations:c[cls+'_serialized_constants']+=1
  if r['range'] is None:
   for c in destinations:c['without_native_source_range']+=1
   continue
  a,b,c,d=r['range'];assert 0<=a<=c<=line_counts[p],(key,r['range'])
  lines[p][cls].update(range(a+1,c+(1 if d else 0)+1))
 for p in paths.values():
  destinations=(areas['/'.join(p.split('/')[:2])],directories[str(pathlib.PurePosixPath(p).parent)],provenance[source_provenance[p]]);taken=set()
  for cls in ('facade_used','outside_facade_closure'):
   charged=lines[p][cls]-taken;taken.update(charged)
   for c in destinations:c[cls+'_native_range_lines']+=len(charged)
  assert len(taken)<=line_counts[p],p
  for c in destinations:c['unattributed_physical_lines']+=line_counts[p]-len(taken)
 summary=dict(base=API['BASE'],status='partial',graph_sha256=NATIVE['sha'](graph),serialized_constant_records=len(g.nodes),unique_selected_constant_names=len({n for m,n in g.nodes}),selected_modules=len(paths),selected_module_system_modules=sum(g.modules[m]['is_module'] for m in paths),all_loaded_modules=len(g.modules),all_loaded_constant_records=len(g.records),facade_reached_loaded_records=len(all_used),all_loaded_collision_names=len(g.collisions),selected_to_selected_expression_edges=sum(map(len,g.edges.values())),selected_to_dependency_reference_occurrences=sum(g.external.values()),unresolved_references=dict(sorted(g.unresolved.items())),facade_root_boundary=dict(root_boundary),facade_theorem_roots=len(roots),facade_reached_records=len(used),source_line_unit='Raw LF physical lines, excluding an empty line after terminal LF',legacy_splitlines_indexed_lines=sum(len(src[p].splitlines()) for p in paths.values()),indexed_physical_lines=sum(line_counts[p] for p in paths.values()),missing_files=len(src)-len(paths),provenance={k:dict(sorted(v.items())) for k,v in sorted(provenance.items())},
  boundaries=['Module/name pairs preserve per-module serialized constant identities, including realized auxiliaries.',
   'Native declaration ranges replace editor-index source bindings; no editor-index reference edges are used.',
   'Facade closure traverses all serialized imported bodies in the fixed final Solidity.Theorems environment, including unselected core/dependency modules; ordinary project graph edges model defining-module compilation contexts.',
   'Reference providers follow cached import DFS order and the pinned native import subsumption relation.',
   'Only the named theorem facade is rooted here. Outside its closure does not mean unused.',
   'Compiler/attribute extensions, discarded anonymous check proofs, command execution, dynamic effects and missing-module consumers remain outside this native-expression graph.'],deletable_now_verified_lines=0)
 return summary,areas,directories

def main():
 p=argparse.ArgumentParser();p.add_argument('--source-root',type=pathlib.Path,required=True);p.add_argument('--graph',type=pathlib.Path,required=True);p.add_argument('--view',type=pathlib.Path,required=True);p.add_argument('--out',type=pathlib.Path,required=True);p.add_argument('--check',action='store_true');a=p.parse_args();summary,areas,directories=measure(a.source_root,a.graph,a.view);a.out.mkdir(parents=True,exist_ok=True)
 outputs={'native-summary.json':json.dumps(summary,sort_keys=True,indent=2)+'\n'}
 import io
 for name,rows in [('native-areas.csv',areas),('native-directories.csv',directories)]:
  out=io.StringIO();fields=sorted(set().union(*(r.keys() for r in rows.values())));w=csv.writer(out,lineterminator='\n');w.writerow(['path']+fields)
  for k,r in sorted(rows.items()):w.writerow([k]+[r[f] for f in fields])
  outputs[name]=out.getvalue()
 for name,body in outputs.items():
  assert len(body.encode())<1000000
  if a.check:assert (a.out/name).read_text()==body,'STALE '+name
  else:(a.out/name).write_text(body)
 print('NATIVE_MODULE_GRAPH_PASS',summary['serialized_constant_records'],summary['selected_to_selected_expression_edges'],summary['unresolved_references'])
if __name__=='__main__':main()
