#!/usr/bin/env python3
"""Per-module native expression graph. No editor-reference alias edges.
Namespace resolution follows direct-import DFS order and pinned Lean's native
subsumption matrix. Unavailable reference providers remain explicit boundaries.
"""
import collections,functools,hashlib,json,pathlib,sys
HERE=pathlib.Path(__file__).resolve().parent

def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()

class NativeGraph:
 def __init__(self,modules,nodes,collisions):
  self.modules=modules;self.records=nodes;self.nodes={key:r for key,r in nodes.items() if modules[key[0]]['selected']};self.collisions=collisions
  assert not any(r.get('is_module',False) for r in modules.values() if r['selected']),'Selected module-system contexts require visibility modelling'
  self.providers=collections.defaultdict(list);self.orders={};self.visible={};self.ranks={};self.relation_indices={}
  for m,r in modules.items():
   order=[];seen=set()
   for dep in r['imports']:
    assert dep in self.orders,'Module records not topologically ordered: '+dep
    for ancestor in self.orders[dep]:
     if ancestor not in seen:seen.add(ancestor);order.append(ancestor)
   assert m not in seen
   order.append(m);seen.add(m);self.orders[m]=tuple(order);self.visible[m]=seen
   for name in r['names']:self.providers[name].append(m)
  for name,relation in collisions.items():
   assert set(self.providers[name])==set(relation['modules']),'Collision-provider mismatch'
   self.relation_indices[name]={m:i for i,m in enumerate(relation['modules'])}
  self.edges={};self.external=collections.Counter();self.unresolved=collections.Counter();self.resolved_collisions=0
  for key,r in self.nodes.items():
   targets=set()
   for name in set(r['refs']):
    provider,reason=self.resolve(key[0],name)
    if provider is None:self.unresolved[reason]+=1;continue
    target=(provider,name)
    if target in self.nodes:targets.add(target)
    else:self.external[provider]+=1
   self.edges[key]=targets

 @functools.lru_cache(maxsize=None)
 def resolve(self,context,name):
  providers=self.providers.get(name,[])
  if not providers:return None,'missing_constant_name'
  candidates=[m for m in providers if m in self.visible[context]]
  if not candidates:return None,'provider_outside_import_closure'
  if len(candidates)==1:return candidates[0],None
  relation=self.collisions.get(name)
  if relation is None:return None,'missing_collision_relation'
  indices=self.relation_indices[name]
  if context not in self.ranks:self.ranks[context]={m:i for i,m in enumerate(self.orders[context])}
  candidates.sort(key=self.ranks[context].__getitem__)
  selected=candidates[0]
  for new in candidates[1:]:
   if relation['subsumes'][indices[new]][indices[selected]]:selected=new
   elif not relation['subsumes'][indices[selected]][indices[new]]:return None,'incompatible_visible_versions'
  return selected,None

 def closure(self,seeds):
  seen=set();pending=list(seeds)
  while pending:
   node=pending.pop()
   if node in seen:continue
   seen.add(node);pending.extend(self.edges.get(node,()))
  return seen

 def root_closure(self,context,names):
  """Resolve every nested reference in the root's fixed final environment."""
  seen=set();pending=list(names);boundary=collections.Counter()
  while pending:
   name=pending.pop();provider,reason=self.resolve(context,name)
   if provider is None:boundary[reason]+=1;continue
   key=(provider,name)
   if key not in self.records:boundary['missing_native_record']+=1;continue
   if key in seen:continue
   seen.add(key);pending.extend(self.records[key]['refs'])
  return seen,boundary

def load(path,verify_receipt=True):
 if verify_receipt:
  receipt=json.loads(pathlib.Path(str(path)+'.receipt.json').read_text())
  assert 'version 4.24.0,' in receipt['lean'] and '797c613' in receipt['lean'],'Unsupported native import model toolchain'
  assert receipt['index_sha256']==sha(path),'Native graph receipt mismatch'
  assert receipt['producer_sha256']==sha(HERE/'ModuleExport.lean'),'Stale native exporter revision'
  assert receipt['modules_sha256']==sha(HERE/'modules.txt'),'Native module-universe mismatch'
 modules={};nodes={};collisions={};own_names=collections.defaultdict(list)
 for line in path.open():
  r=json.loads(line);kind=r['record']
  if kind=='module':
   m=sys.intern(r['module']);assert m not in modules
   r['imports']=[sys.intern(x) for x in r['imports']];r['names']=[sys.intern(x) for x in r['names']];modules[m]=r
  elif kind=='constant':
   m=sys.intern(r['module']);name=sys.intern(r['name']);key=(m,name);assert key not in nodes
   r['refs']=[sys.intern(x) for x in r['refs']];nodes[key]=r;own_names[m].append(name)
  elif kind=='collision':
   name=sys.intern(r['name']);assert name not in collisions;collisions[name]=r
  else:raise ValueError('Unknown native record '+kind)
 for m,r in modules.items():
  assert own_names[m]==r['names'],'Missing per-module constants: '+m
 graph=NativeGraph(modules,nodes,collisions)
 return graph
