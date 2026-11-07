"""Exact expression DAG validation and tree-to-DAG controls; never a proof checker."""
import json
TAG='expr-dag-v1'
def canonical(x):return json.dumps(x,ensure_ascii=False,sort_keys=True,separators=(',',':'))
def nat(x):return type(x) is int and x>=0
def name(x):
    while isinstance(x,list) and len(x)==3 and x[0] in ['str','num']:
        if not (isinstance(x[2],str) if x[0]=='str' else nat(x[2])):raise ValueError('invalid name payload')
        x=x[1]
    if x!=['anonymous']:raise ValueError('invalid name')
def level(x):
    pending=[x]
    while pending:
        x=pending.pop()
        if not isinstance(x,list) or not x:raise ValueError('invalid level')
        if x==['zero']:continue
        if x[0]=='succ' and len(x)==2:pending.append(x[1]);continue
        if x[0] in ['max','imax'] and len(x)==3:pending.extend(x[1:]);continue
        if x[0]=='param' and len(x)==2:name(x[1]);continue
        raise ValueError('invalid level/metavariable')
def child_positions(node):
    if not isinstance(node,list) or not node or not isinstance(node[0],str):raise ValueError('invalid expression node')
    tag=node[0];arity={'bvar':2,'sort':2,'const':3,'app':3,'lam':5,'forall':5,'let':6,'nat':2,'string':2,'proj':4}
    if tag not in arity or len(node)!=arity[tag]:raise ValueError('invalid expression tag/arity')
    return {'app':[1,2],'lam':[2,3],'forall':[2,3],'let':[2,3,4],'proj':[3]}.get(tag,[])
def fields(node):
    tag=node[0]
    if tag in ['bvar','nat'] and not nat(node[1]):raise ValueError('invalid natural literal/index')
    if tag=='string' and not isinstance(node[1],str):raise ValueError('invalid string literal')
    if tag=='sort':level(node[1])
    if tag=='const':
        name(node[1])
        if not isinstance(node[2],list):raise ValueError('invalid universe list')
        for x in node[2]:level(x)
    if tag in ['lam','forall','let','proj']:name(node[1])
    if tag in ['lam','forall'] and node[4] not in ['default','implicit','strictImplicit','instImplicit']:raise ValueError('invalid binder annotation')
    if tag=='let' and type(node[5]) is not bool:raise ValueError('invalid let nondependency flag')
    if tag=='proj' and not nat(node[2]):raise ValueError('invalid projection index')
def pack(root,nodes):
    """Canonical left-to-right postorder with exact node interning."""
    pending=[(root,False)];done={};keys={};out=[]
    while pending:
        source,post=pending.pop()
        if source in done:continue
        node=nodes[source];positions=child_positions(node)
        if not post:
            pending.append((source,True))
            pending.extend((node[i],False) for i in reversed(positions));continue
        result=list(node)
        for i in positions:result[i]=done[node[i]]
        key=canonical(result)
        if key not in keys:keys[key]=len(out);out.append(result)
        done[source]=keys[key]
    return [TAG,done[root],out]
def validate(dag):
    if not isinstance(dag,list) or len(dag)!=3 or dag[0]!=TAG:raise ValueError('missing DAG envelope')
    root,nodes=dag[1:]
    if not nat(root) or not isinstance(nodes,list) or not nodes or root!=len(nodes)-1:raise ValueError('invalid root/node table')
    seen=set()
    for index,node in enumerate(nodes):
        positions=child_positions(node);fields(node)
        for i in positions:
            if not nat(node[i]) or node[i]>=index:raise ValueError('forward/cyclic/invalid reference')
        key=canonical(node)
        if key in seen:raise ValueError('duplicate node')
        seen.add(key)
    normalized=pack(root,nodes)
    if normalized!=dag:raise ValueError('unreachable/noncanonical node table')
    return dag
def loads(text):
    if not isinstance(text,str):raise ValueError('DAG expression must be text')
    return validate(json.loads(text))
def from_tree(text):
    """Control conversion, without expanding shared DAGs back into trees."""
    tree=json.loads(text);pending=[(tree,False)];done={};keys={};nodes=[]
    while pending:
        node,post=pending.pop();source=id(node)
        if source in done:continue
        positions=child_positions(node)
        if not post:
            pending.append((node,True));pending.extend((node[i],False) for i in reversed(positions));continue
        result=list(node)
        for i in positions:result[i]=done[id(node[i])]
        fields(result);key=canonical(result)
        if key not in keys:keys[key]=len(nodes);nodes.append(result)
        done[source]=keys[key]
    return validate([TAG,done[id(tree)],nodes])
