"""Validate and seal all exact type DAGs; deterministic H44 manifest generator."""
import collections,hashlib,json,sys
from pathlib import Path
raw,census_path,output=map(Path,sys.argv[1:4])
census=json.loads(census_path.read_text()); modules={m for m,v in census['modules'].items() if v['assigned']}
hashes={m:hashlib.sha256() for m in modules}; counts=collections.Counter(); kinds=collections.Counter(); names=set(); total_nodes=0; previous_name=None
# Kinds: s=exact repr string, n=natural, b=boolean, e=backward expression edge.
shapes={'bvar':'n','fvar':'s','mvar':'s','sort':'s','const':'ss','app':'ee','lam':'sees','forallE':'sees','letE':'seeeb','lit':'s','mdata':'se','proj':'sne'}
for line in raw.open():
    row=json.loads(line); assert set(row)=={'kind','level_params','module','name','type_graph'}
    mod=row['module']; assert mod in modules
    assert isinstance(row['name'],str) and row['name'] and row['name'] not in names; names.add(row['name'])
    assert previous_name is None or previous_name<row['name'], 'unsorted names'
    previous_name=row['name']
    assert row['kind'] in {'theorem','definition','inductive','constructor','recursor','opaque','axiom'}
    assert isinstance(row['level_params'],list) and all(isinstance(x,str) for x in row['level_params'])
    g=row['type_graph']; assert set(g)=={'nodes','root'} and isinstance(g['nodes'],list)
    nodes=g['nodes']; root=g['root']; assert type(root) is int and 0<=root<len(nodes)
    edges={}; seen_nodes=set()
    for i,node in enumerate(nodes):
        assert isinstance(node,list) and node and node[0] in shapes
        shape=shapes[node[0]]; assert len(node)==len(shape)+1
        assert node[0] not in {'fvar','mvar'}, 'constant type not closed'
        edges[i]=[]
        for spec,value in zip(shape,node[1:]):
            if spec=='s': assert isinstance(value,str)
            elif spec=='b': assert type(value) is bool
            else:
                assert type(value) is int and value>=0
                if spec=='e': assert value<i; edges[i].append(value)
        packed=json.dumps(node,sort_keys=True,separators=(',',':')); assert packed not in seen_nodes;seen_nodes.add(packed)
    reachable=set(); todo=[root]
    while todo:
        n=todo.pop()
        if n not in reachable: reachable.add(n);todo.extend(edges[n])
    assert len(reachable)==len(nodes), 'unreachable nodes'
    canonical=(json.dumps(row,sort_keys=True,separators=(',',':'))+'\n').encode()
    hashes[mod].update(canonical);counts[mod]+=1;kinds[row['kind']]+=1;total_nodes+=len(nodes)
assert set(counts)==modules, 'missing module API coverage'
assert kinds['axiom']==0, 'unexpected EVM axiom declaration'
# Every assigned file is represented, including explicit empty API entries if any.
manifest={'format':1,'algorithm':'SHA256 of name-sorted canonical JSONL per module, containing exact structural Expr DAGs; binder names/info and metadata retained','raw_sha256':hashlib.file_digest(raw.open('rb'),'sha256').hexdigest(),'raw_bytes':raw.stat().st_size,'assigned_modules':len(modules),'modules_with_declarations':sum(counts[m]>0 for m in modules),'zero_declaration_modules':sorted(modules-set(counts)),'declarations':len(names),'type_graph_nodes':total_nodes,'kinds':dict(kinds),'module_api_hashes':{m:{'declarations':counts[m],'sha256':hashes[m].hexdigest(),'source_sha256':census['modules'][m]['sha256']} for m in sorted(modules)},'new_api':None,'boundary':'Old metadata only; source proof checks are separate, new API comparison blocked.'}
assert counts.total()==len(names)
output.write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:manifest[k] for k in ['assigned_modules','modules_with_declarations','declarations','type_graph_nodes','kinds','raw_sha256']}))
