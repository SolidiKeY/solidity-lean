#!/usr/bin/env python3
"""H62 graph overlay. Only Lean-exported types supply dependency edges.

A catalog selects exported declarations and assigns stable IDs, areas and owners.
Claims are separate from producer ownership, and never change the prose registry.
"""
import argparse
import fcntl
import hashlib
import json
import math
import os
from pathlib import Path
import tempfile
import time
import uuid


def canonical(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False)+'\n').encode()


def digest(value):
    return hashlib.sha256(canonical(value)).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def atomic(path, value):
    path = Path(path)
    fd, tmp = tempfile.mkstemp(prefix='.'+path.name+'.', dir=path.parent)
    try:
        with os.fdopen(fd, 'wb') as out:
            out.write(canonical(value))
            out.flush()
            os.fsync(out.fileno())
        os.replace(tmp, path)
        parent = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(parent)
        finally:
            os.close(parent)
    finally:
        if os.path.exists(tmp):
            os.unlink(tmp)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def hash_field(value, length):
    return isinstance(value, str) and len(value) == length and all(c in '0123456789abcdef' for c in value)


def validate_owners(catalog, ownership):
    if ownership is None:
        require(catalog.get('fixture') is True, 'production graph requires an ownership snapshot')
        return
    require(catalog.get('fixture') is not True, 'fixture catalog cannot claim production ownership')
    items = {item['id']: item for item in ownership['items']}
    require(len(items) == len(ownership['items']), 'duplicate ownership item')
    for node in catalog['nodes']+catalog.get('pendingInputs',[]):
        assignments = [node]+[r for r in node.get('binderRoles',{}).values() if r.get('kind')=='premise']
        for assignment in assignments:
            ref = assignment.get('ownerReference')
            require(ref in items, 'dead owner reference: '+str(ref))
            require(assignment['owner'] == items[ref]['owner'], 'owner snapshot mismatch: '+ref)


def build(export, catalog, base, tree, ownership=None):
    validate_owners(catalog, ownership)
    require(hash_field(base, 40) and hash_field(tree, 40), 'invalid base/tree SHA1')
    require(export.get('schema') == 1 and export.get('source') == 'Lean.ConstantInfo.type', 'not an elaborated Lean export')
    rows = export['declarations']
    by_decl = {row['declaration']: row for row in rows}
    require(len(rows) == len(by_decl), 'duplicate exported declaration')
    for row in rows:
        for key in ('typeReferences','taggedReferences','proofReferences','fieldDeclarations','axioms'):
            require(isinstance(row[key], list) and all(isinstance(x,str) for x in row[key]), 'invalid exporter list: '+key)
        for key in ('binders','fields'):
            require(isinstance(row[key],list), 'invalid binder inventory')
            for binder in row[key]:
                require(isinstance(binder['isProp'],bool) and all(isinstance(binder[k],str) and binder[k] for k in ('name','type','typeExpr')), 'invalid typed binder')
        require(isinstance(row['isTheorem'], bool), 'missing theorem evidence')
    specs = catalog['nodes']
    pending = catalog.get('pendingInputs', [])
    require(isinstance(pending,list), 'invalid pending input inventory')
    require(specs or pending, 'empty catalog')
    require(len({n['id'] for n in specs}) == len(specs), 'duplicate node ID')
    require(len({n['declaration'] for n in specs}) == len(specs), 'duplicate catalog declaration')
    all_ids = [n['id'] for n in specs+pending]
    require(len(set(all_ids)) == len(all_ids), 'duplicate typed/pending node ID')
    mapping = {n['declaration']: n['id'] for n in specs}
    require(set(by_decl).issubset(set(mapping)), 'catalog must cover every exported declaration')
    nodes = {}
    for spec in sorted(specs, key=lambda n: n['id']):
        name = spec['declaration']
        require(name in by_decl and by_decl[name].get('exists') is True, 'dead declaration: '+name)
        row = by_decl[name]
        require(spec.get('area') and spec.get('owner'), 'missing area/owner: '+name)
        kind = spec['kind']
        require(kind in ('statement', 'premise', 'helper'), 'invalid node kind')
        require(row['role'] in ('unclassified', kind), 'tag/catalog kind mismatch: '+name)
        require(row.get('typeExpr') and row.get('type'), 'missing elaborated type')
        require(all(r in mapping for r in row['taggedReferences']), 'omitted tagged dependency: '+name)
        deps = sorted({mapping[r] for r in row['typeReferences'] if r in mapping})
        # Proof-body edges are retained separately; they do not determine readiness.
        proof = sorted({mapping[r] for r in row['proofReferences'] if r in mapping})
        premises = []
        inventory = {str(i): b for i,b in enumerate(row['binders'])}
        inventory.update({'field:'+str(i): b for i,b in enumerate(row['fields'])})
        roles = spec.get('binderRoles', {})
        require(set(roles) == set(inventory), 'unclassified/missing typed binder: '+name)
        for key, binder in inventory.items():
            assignment = roles[key]
            require(assignment.get('kind') in ('parameter','premise'), 'invalid binder role')
            known_premise = any(r in mapping and next(s['kind'] for s in specs if s['declaration']==r)=='premise' for r in binder['references'])
            forced = binder['isProp'] or key.startswith('field:') or known_premise
            require(not forced or assignment['kind']=='premise', 'proof/interface binder cannot be a data parameter')
            if assignment['kind'] == 'parameter':
                require(assignment.get('reason'), 'data parameter needs an audited reason')
            else:
                require(assignment.get('owner'), 'typed premise needs producer owner')
                premises.append({'id': spec['id']+'#'+key, 'name': binder['name'],
                                 'type': binder['type'], 'typeExpr': binder['typeExpr'],
                                 'owner': assignment['owner'], 'status': 'open'})
        completed = spec.get('completed', False)
        require(isinstance(completed, bool), 'completed must be Boolean')
        if completed:
            require(row.get('isTheorem') is True, 'completion requires a checked theorem: '+name)
            require(not (set(row['axioms'])-{'propext', 'Classical.choice', 'Quot.sound'}), 'unapproved axiom: '+name)
            require(not premises, 'cannot complete a theorem with open named premises: '+name)
        nodes[spec['id']] = dict(spec, dependencies=deps, proofDependencies=proof,
                                 proofHelpers=[p for p in proof if next(n['kind'] for n in specs if n['id']==p)=='helper'],
                                 premises=premises, type=row['type'], typeExpr=row['typeExpr'])
    for entry in sorted(pending, key=lambda n:n['id']):
        required = {'id','area','owner','ownerReference','inputArtifact','reason','source'}
        require(set(entry) == required and all(isinstance(v,str) and v for v in entry.values()),
                'pending input must contain only nonempty provenance/owner fields')
        nodes[entry['id']] = dict(entry, kind='pending-input', inputStatus='pending-input',
                                 declaration=None, exists=None, type=None, typeExpr=None,
                                 dependencies=[], dependenciesKnown=False,
                                 proofDependencies=[], proofHelpers=[], premises=[],
                                 premiseInventoryComplete=False)
    # A premise/helper can appear in a type. It remains a typed edge, not a proof edge.
    colors, order = {}, []
    def visit(key):
        require(colors.get(key) != 'gray', 'statement dependency cycle: '+key)
        if colors.get(key) == 'black':
            return
        colors[key] = 'gray'
        for dep in nodes[key]['dependencies']:
            require(dep in nodes, 'dead dependency: '+dep)
            visit(dep)
        colors[key] = 'black'
        order.append(key)
    for key in nodes:
        visit(key)
    for key in order:
        node = nodes[key]
        blocked = node.get('inputStatus') == 'pending-input' or bool(node['premises']) or any(nodes[d]['status'] != 'done' for d in node['dependencies'])
        if node.get('completed'):
            require(not blocked, 'completion has unresolved dependencies: '+key)
            status = 'done'
        elif blocked:
            status = 'blocked'
        elif node.get('kind') == 'helper':
            status = 'open'
        else:
            status = 'ready'
        node['status'] = status
    def summary(keys):
        counts = dict.fromkeys(('open','ready','blocked','done'), 0)
        for key in keys:
            counts[nodes[key]['status']] += 1
        counts['total'] = len(keys)
        pending_count = sum(nodes[k].get('inputStatus') == 'pending-input' for k in keys)
        known = sum(len(nodes[k]['premises']) for k in keys)
        counts['typedDeclarations'] = len(keys)-pending_count
        counts['pendingInputs'] = pending_count
        counts['knownOpenPremises'] = known
        counts['premiseInventoryComplete'] = pending_count == 0
        counts['openPremises'] = None if pending_count else known
        return counts
    areas = {a: summary([k for k,n in nodes.items() if n['area'] == a]) for a in sorted({n['area'] for n in nodes.values()})}
    roots = catalog.get('roots', {})
    progress = {}
    for label, keys in sorted(roots.items()):
        require(keys and all(k in nodes for k in keys), 'dead/empty progress root: '+label)
        closure = set()
        def collect(k):
            if k not in closure:
                closure.add(k)
                for d in nodes[k]['dependencies']:
                    collect(d)
        for key in keys:
            collect(key)
        progress[label] = dict(summary(sorted(closure)), nodes=sorted(closure))
    result = dict(schema=1, fixture=catalog.get('fixture') is True, ownershipSha256=digest(ownership) if ownership is not None else None,
                  base=base, tree=tree, exportSha256=digest(export), catalogSha256=digest(catalog),
                  nodes=list(nodes.values()), areas=areas, counts=summary(list(nodes)), progress=progress)
    result['graphSha256'] = digest(result)
    return result


def validate_graph(graph):
    payload = {k:v for k,v in graph.items() if k != 'graphSha256'}
    require(graph.get('graphSha256') == digest(payload), 'graph checksum mismatch')
    require(hash_field(graph.get('base'),40) and hash_field(graph.get('tree'),40), 'invalid graph provenance')


def transact(path, graph, operation, node, owner, token=None, ttl=300, now=None):
    """POSIX advisory lock + fsync + atomic replace; stale tokens never mutate state."""
    validate_graph(graph)
    require(operation in ('claim','renew','release'), 'invalid claim operation')
    require((now is None or math.isfinite(now)) and math.isfinite(ttl) and 0 < ttl <= 86400, 'invalid lease time')
    by_id = {n['id']: n for n in graph['nodes']}
    require(node in by_id, 'unknown node')
    require(by_id[node].get('inputStatus') != 'pending-input', 'pending-input node cannot be claimed')
    require(owner == by_id[node]['owner'], 'producer owner mismatch')
    require(by_id[node]['status'] != 'done', 'completed node cannot be claimed')
    path = Path(path)
    with open(str(path)+'.lock', 'a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        now = time.time() if now is None else now
        state = read(path) if path.exists() else dict(schema=1, graphSha256=graph['graphSha256'], revision=0, claims={})
        require(state['schema'] == 1 and state['graphSha256'] == graph['graphSha256'], 'stale graph state')
        old = state['claims'].get(node)
        if operation == 'claim':
            require(old is None or old['expires'] <= now, 'node already claimed')
            claim = dict(owner=owner, token=uuid.uuid4().hex, expires=now+ttl)
            state['claims'][node] = claim
        else:
            require(old is not None and old['owner'] == owner and old['token'] == token and old['expires'] > now, 'stale owner/token')
            claim = dict(old, expires=now+ttl)
            if operation == 'renew':
                state['claims'][node] = claim
            else:
                del state['claims'][node]
        state['revision'] += 1
        atomic(path, state)
        return dict(revision=state['revision'], **claim)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    gen = sub.add_parser('build')
    for arg in ('export','catalog','base','tree','output'):
        gen.add_argument('--'+arg, required=True)
    gen.add_argument('--ownership')
    claim = sub.add_parser('claim')
    for arg in ('graph','state','operation','node','owner'):
        claim.add_argument('--'+arg, required=True)
    claim.add_argument('--token')
    claim.add_argument('--ttl', type=float, default=300)
    args = parser.parse_args()
    try:
        if args.command == 'build':
            result = build(read(args.export), read(args.catalog), args.base, args.tree, read(args.ownership) if args.ownership else None)
            atomic(args.output, result)
            print(canonical(result['counts']).decode().strip())
        else:
            print(canonical(transact(args.state, read(args.graph), args.operation, args.node, args.owner, args.token, args.ttl)).decode().strip())
    except (ValueError, KeyError, TypeError) as exc:
        parser.exit(2, str(exc)+'\n')

if __name__ == '__main__':
    main()
