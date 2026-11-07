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


def validate_source_snapshot(catalog):
    if catalog.get('sourceSnapshot') is None:
        require(not any('sourceLocator' in n for n in catalog.get('pendingInputs', [])), 'source locator lacks snapshot')
        return None
    import importlib.util
    spec = importlib.util.spec_from_file_location('h62_source_policy', Path(__file__).with_name('source_intake.py'))
    policy = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(policy)
    return policy.validate_catalog_snapshot(catalog)


def validate_owners(catalog, ownership, source=None):
    if ownership is None:
        require(catalog.get('fixture') is True, 'production graph requires an ownership snapshot')
        return
    require(catalog.get('fixture') is not True, 'fixture catalog cannot claim production ownership')
    items = {item['id']: item for item in ownership['items']}
    require(len(items) == len(ownership['items']), 'duplicate ownership item')
    records = catalog['nodes']+catalog.get('pendingInputs',[])
    if source is not None:
        records += source['sourceInputBindings']+source['sharedPublicObligations']
    for node in records:
        assignments = [node]+[r for r in node.get('binderRoles',{}).values() if r.get('kind')=='premise']
        for assignment in assignments:
            ref = assignment.get('ownerReference')
            require(ref in items, 'dead owner reference: '+str(ref))
            require(assignment['owner'] == items[ref]['owner'], 'owner snapshot mismatch: '+ref)


def build(export, catalog, base, tree, ownership=None):
    source = validate_source_snapshot(catalog)
    validate_owners(catalog, ownership, source)
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
    checked_helper_targets = {}
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
        for position,(key, binder) in enumerate(inventory.items()):
            assignment = roles[key]
            require(assignment.get('kind') in ('parameter','premise'), 'invalid binder role')
            known_premise = any(r in mapping and next(s['kind'] for s in specs if s['declaration']==r)=='premise' for r in binder['references'])
            forced = binder['isProp'] or key.startswith('field:') or known_premise
            require(not forced or assignment['kind']=='premise', 'proof/interface binder cannot be a data parameter')
            if assignment['kind'] == 'parameter':
                require(assignment.get('reason'), 'data parameter needs an audited reason')
            else:
                require(assignment.get('owner'), 'typed premise needs producer owner')
                premise = {'id': spec['id']+'#'+key, 'name': binder['name'],
                           'type': binder['type'], 'typeExpr': binder['typeExpr'],
                           'owner': assignment['owner'], 'status': 'open'}
                evidence = binder.get('witness')
                if evidence is not None:
                    expected_scope = 'field' if key.startswith('field:') else 'binder'
                    expected_index = int(key.split(':')[-1])
                    require(evidence['consumer']==name and evidence['scope']==expected_scope and
                            type(evidence['index']) is int and evidence['index']==expected_index,
                            'witness consumer/location mismatch')
                    require(evidence['kernelChecked'] is True, 'witness lacks kernel check')
                    require(evidence['axioms']==[], 'witness must be axiom-free')
                    require(all(isinstance(evidence[k],str) and evidence[k] for k in
                                ('declaration','checkedDeclaration','binderTypeExpr','expectedTypeExpr','helperTypeExpr')),
                            'missing checked witness identity/type')
                    require(evidence['binderTypeExpr']==binder['typeExpr'] and
                            evidence['expectedTypeExpr']==evidence['helperTypeExpr'], 'witness type evidence mismatch')
                    expected_prior = list(inventory)[:position]
                    require(evidence['priorBinders']==expected_prior, 'witness prerequisite inventory mismatch')
                    producer = next((s for s in specs if s['declaration']==evidence['declaration']),None)
                    require(producer is not None and producer['kind'] in ('statement','helper'), 'dead/unclassified witness declaration')
                    require(producer['owner']==assignment['owner'], 'witness producer owner mismatch')
                    producer_row = by_decl.get(evidence['declaration'])
                    require(producer_row is not None and producer_row.get('exists') is True and producer_row['axioms']==[],
                            'witness producer missing or axiom-dependent')
                    helper = evidence['checkedDeclaration']
                    require(helper not in checked_helper_targets, 'duplicate checked witness helper')
                    checked_helper_targets[helper]=(name,key)
                    blocked_by = [p['id'] for p in premises if p['status']!='done']
                    premise.update(witness=evidence,blockedByPremises=blocked_by,
                                   status='open' if blocked_by else 'done')
                premises.append(premise)
        completed = spec.get('completed', False)
        require(isinstance(completed, bool), 'completed must be Boolean')
        if completed:
            require(row.get('isTheorem') is True, 'completion requires a checked theorem: '+name)
            require(not (set(row['axioms'])-{'propext', 'Classical.choice', 'Quot.sound'}), 'unapproved axiom: '+name)
            require(all(p['status']=='done' for p in premises), 'cannot complete a theorem with open named premises: '+name)
        nodes[spec['id']] = dict(spec, dependencies=deps, proofDependencies=proof,
                                 proofHelpers=[p for p in proof if next(n['kind'] for n in specs if n['id']==p)=='helper'],
                                 premises=premises, witnessDependencies=sorted({mapping[p['witness']['declaration']] for p in premises if 'witness' in p}),
                                 type=row['type'], typeExpr=row['typeExpr'])
    for entry in sorted(pending, key=lambda n:n['id']):
        required = {'id','area','owner','ownerReference','inputArtifact','reason','source'}
        require(set(entry) in (required, required|{'sourceLocator'}) and all(isinstance(entry[k],str) and entry[k] for k in required),
                'pending input must contain only nonempty provenance/owner fields')
        nodes[entry['id']] = dict(entry, kind='pending-input', inputStatus='pending-input',
                                 declaration=None, exists=None, type=None, typeExpr=None,
                                 dependencies=[], dependenciesKnown=False,
                                 proofDependencies=[], proofHelpers=[], witnessDependencies=[], premises=[],
                                 premiseInventoryComplete=False)
        if 'sourceLocator' in entry:
            nodes[entry['id']]['declaration'] = entry['sourceLocator']['declaration']
            nodes[entry['id']]['declarationEvidence'] = 'static-source-only'
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
        blocked = node.get('inputStatus') == 'pending-input' or any(p['status']!='done' for p in node['premises']) or any(nodes[d]['status'] != 'done' for d in node['dependencies'])
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
        known = sum(p['status']!='done' for k in keys for p in nodes[k]['premises'])
        counts['typedDeclarations'] = len(keys)-pending_count
        counts['pendingInputs'] = pending_count
        counts['knownOpenPremises'] = known
        counts['dischargedPremises'] = sum(p['status']=='done' for k in keys for p in nodes[k]['premises'])
        counts['premiseInventoryComplete'] = pending_count == 0
        counts['openPremises'] = None if pending_count else known
        if source is not None:
            located = [nodes[k]['sourceLocator'] for k in keys if 'sourceLocator' in nodes[k]]
            counts['sourceLocatedInputs'] = len(located)
            counts['distinctLocatedSourceDeclarations'] = len({n['declaration'] for n in located})
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
    if source is not None:
        result['sourceEvidence'] = source
        result['sourceCounts'] = dict(explicitDeclarationLocators=len(source['declarationLocators']),
            namedOpenPublicFields=len(source['sharedPublicObligations']),
            sourceContextBindings=len(source['sourceInputBindings']),
            certificatePackageAssumptions=sum(n['role']=='certificate-package' for n in source['sourceInputBindings']),
            reportedBridgeRequests=len(source['reportedProducerGaps']),
            dischargedPremises=0, atomicOpenPremises=None, premiseInventoryComplete=False)
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
