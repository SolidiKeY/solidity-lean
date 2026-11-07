#!/usr/bin/env python3
"""Guard G49 source locators from becoming elaborated statements or discharged premises.

This is exact published-source intake, not a Lean parser or a type-dependency
exporter. Named anchors locate reviewed source only. No edges or kernel facts
are inferred from text, producer checking claims, or flattened binder metadata.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

MASTER = '706e36825929d6d0084dc08b88de9349abcd25aa'
CHECKPOINT = '5f7c70b16090b25ea706dddf3e666d94fb5a09fe'
INVENTORY_SHA = 'af4f1a69410a9df1f408d2e2d9d9b82b39f926ce48c6bb601c16092514ed733e'
ROOT = Path(__file__).resolve().parents[4]
PREFIX = 'Solidity.Roadmap.G49Final.'
FOLDED = 'Solidity/Roadmap/G49Final/FoldedPublic.lean'
THEOREM = PREFIX + 'g49_g50_of_fold'
PUBLIC = PREFIX + 'PublicObligations'
DECLARATIONS = {
    'Solidity/Roadmap/G49Final/BridgeGoal.lean': [
        ('abbrev', 'BridgeGoal'), ('def', 'BridgeGoal.pass'),
        ('theorem', 'BridgeGoal.envAbs_eq'), ('theorem', 'BridgeGoal.need_eq'),
        ('theorem', 'BridgeGoal.local'), ('def', 'cert_bridge')],
    FOLDED: [('def', 'sourceEnv'), ('def', 'foldedExport'), ('def', 'pipeline'),
             ('theorem', 'pipeline_env'), ('structure', 'PublicObligations'),
             ('def', 'FoldStatement'), ('theorem', 'g49_g50_of_fold')],
    'Solidity/Roadmap/G49Final/PassChain.lean': [('theorem', 'pass_chain')],
    'Solidity/Roadmap/G49Final/PassCorrect.lean': [
        ('structure', 'Behaviour'), ('def', 'Behaviour.Ready'), ('structure', 'PassCorrect'),
        ('def', 'PassCorrect.refl'), ('def', 'PassCorrect.trans'), ('inductive', 'PassList'),
        ('def', 'PassList.fold'), ('theorem', 'public_end_to_end')],
    'Solidity/Roadmap/G49Final/PassCorrectAdapters.lean': [
        ('def', 'Behaviour.ofLang'), ('def', 'cert_adapter'), ('def', 'lowering_adapter'),
        ('def', 'compilation_adapter'), ('def', 'execution_adapter'), ('def', 'p8b_adapter'),
        ('structure', 'SourceProgram'), ('def', 'source_from_admitted'),
        ('theorem', 'source_ready'), ('theorem', 'PassCorrect.refines')],
}
PUBLIC_FIELDS = ('sourceApproved', 'sourceNonVacuous', 'targetApproved', 'keccak',
                 'coverage', 'bothPipelines', 'artifact', 'fixed', 'session', 'ifixed',
                 'isession', 'creates_table', 'hashes_source', 'decode_reach', 'decode_commutes')
INPUTS = ('S', 'I', 'Asm', 'V', 'lowering', 'backend', 'execution', 'compiler', 'decode')
THEOREM_BINDERS = INPUTS + ('obligations',)
IDS = ('G49.01', 'G49.02', 'G49.03', 'G50.01', 'G50.02')
FACTORIES = ('bare_prefix_bridge','compiler_agreement_bridge','p1_frame_bridge','v08_world_phase_bridge','p10_execution_bridge')
METADATA = {
    'shapes': 'tests/h55/g49-final-theorem/h64-shapes.json',
    'bridges': 'tests/h55/g49-final-theorem/bridge-requests.json',
}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def require(ok, message):
    if not ok:
        raise ValueError(message)


def git(*args):
    return subprocess.check_output(['git', '--no-replace-objects', *args], cwd=ROOT)


def strict_json(data):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, 'duplicate JSON key: ' + key)
            result[key] = value
        return result
    def constant(value):
        raise ValueError('non-JSON constant: ' + value)
    return json.loads(data, object_pairs_hook=unique, parse_constant=constant)


def verify_inventory(raw, read_source, expected_sha=INVENTORY_SHA):
    require(sha(raw) == expected_sha, 'coordinator inventory SHA256 mismatch')
    lines = raw.splitlines(keepends=True)
    require(lines[0].decode().strip() == 'Static source inventory from fetched origin/master ' + MASTER,
            'inventory master mismatch')
    require(CHECKPOINT.encode() in lines[1], 'inventory checkpoint mismatch')
    starts = [i for i, line in enumerate(lines) if line.startswith(b'PATH ')]
    bodies, files = {}, {}
    for number, index in enumerate(starts):
        path, digest = lines[index].rstrip(b'\r\n')[5:].split(b' sha256 ')
        path, digest = path.decode(), digest.decode()
        require(path in DECLARATIONS and path not in files, 'unexpected/duplicate source path')
        require(len(digest) == 64 and all(c in '0123456789abcdef' for c in digest), 'invalid source SHA256')
        source = read_source(path)
        require(sha(source) == digest, 'published source hash mismatch: ' + path)
        end = starts[number+1] if number+1 < len(starts) else len(lines)
        inline = b''.join(lines[index+1:end])
        require(inline.startswith(source) and all(c in b'\r\n' for c in inline[len(source):]),
                'inline inventory differs from exact source: ' + path)
        files[path], bodies[path] = digest, source
    require(set(files) == set(DECLARATIONS), 'incomplete source inventory')
    return files, bodies


def hash_field(value, length):
    return isinstance(value,str) and len(value)==length and all(c in "0123456789abcdef" for c in value)


def validate_catalog_snapshot(catalog):
    source = catalog.get('sourceSnapshot')
    if source is None:
        require(not any('sourceLocator' in n for n in catalog.get('pendingInputs', [])), 'source locator lacks snapshot')
        return None
    require(isinstance(source,dict) and source.get('evidence')=='static-source-only', 'invalid source evidence boundary')
    expected_keys = {'evidence','sourceCommit','sourceTree','checkpoint','inventorySha256','files','metadataFiles',
        'declarationLocators','theorem','aggregateBinder','sourceBinderNames','sourceInputBindings',
        'sharedPublicObligations','reportedProducerGaps','historicalProducerCheck',
        'producerReportedCheckedDeclarations','producerReportedSourceHashes','exhaustiveLaneCoverage',
        'freshLeanRun','premiseInventoryComplete'}
    require(set(source)==expected_keys, 'unexpected source snapshot fields')
    require(not catalog['nodes'] and catalog.get('fixture') is not True, 'source-only catalog cannot supply typed/fixture nodes')
    require(source.get('freshLeanRun') is False and source.get('premiseInventoryComplete') is False and
            source.get('exhaustiveLaneCoverage') is False, 'source metadata cannot claim elaboration or completeness')
    for name in ('sourceCommit','sourceTree','checkpoint'):
        require(hash_field(source.get(name),40), 'invalid source provenance: '+name)
    require(hash_field(source.get('inventorySha256'),64), 'invalid source inventory hash')
    for field in ('files','metadataFiles'):
        require(isinstance(source.get(field),dict) and source[field], 'missing source file manifest')
        for path,digest_ in source[field].items():
            require(isinstance(path,str) and path and not Path(path).is_absolute() and '..' not in Path(path).parts and
                    hash_field(digest_,64), 'invalid source file/hash')
    declarations = source['declarationLocators']
    require(isinstance(declarations,list) and declarations, 'missing source declaration locators')
    names = {}
    for row in declarations:
        require(set(row)=={'declaration','file','fileSha256','line','sourceForm'} and
                isinstance(row['declaration'],str) and row['declaration'] and
                source['files'].get(row['file'])==row['fileSha256'] and
                type(row['line']) is int and row['line']>0 and
                row['sourceForm'] in ('abbrev','def','theorem','structure','inductive'), 'invalid source declaration locator')
        require(row['declaration'] not in names, 'duplicate source declaration locator')
        names[row['declaration']] = row
    require(source['theorem'] in names and names[source['theorem']]['sourceForm']=='theorem', 'missing source theorem locator')
    inputs = source['sourceInputBindings']
    fields = source['sharedPublicObligations']
    require(isinstance(inputs,list) and isinstance(fields,list), 'invalid named source input inventory')
    input_map, field_map = {}, {}
    for row in inputs:
        require(set(row)=={'name','ownerReference','owner','status','role'} and
                all(isinstance(row[k],str) and row[k] for k in ('name','ownerReference','owner')) and
                row['status']=='open' and row['role'] in ('certificate-package','context-or-function'),
                'source input cannot claim discharge')
        require(row['name'] not in input_map, 'duplicate named source input')
        input_map[row['name']] = row
    for row in fields:
        require(set(row)=={'name','container','ownerReference','owner','status','evidence','line'} and
                all(isinstance(row[k],str) and row[k] for k in ('name','container','ownerReference','owner')) and
                row['container'] in names and names[row['container']]['sourceForm']=='structure' and
                type(row['line']) is int and row['line']>names[row['container']]['line'] and
                row['status']=='open' and row['evidence']=='static-source-only', 'source field cannot claim typed discharge')
        require(row['name'] not in field_map, 'duplicate named source field')
        field_map[row['name']] = row
    require(set(input_map)==set(INPUTS) and set(field_map)==set(PUBLIC_FIELDS),
            'pinned source input/field inventory cannot omit or add names')
    require(all(row['role']==('certificate-package' if name in ('lowering','backend','execution') else
                'context-or-function') for name,row in input_map.items()), 'pinned source package roles changed')
    require(set(names)=={PREFIX+short for rows in DECLARATIONS.values() for _,short in rows},
            'pinned explicit declaration inventory changed')
    binder_names = source['sourceBinderNames']
    require(isinstance(binder_names,list) and all(isinstance(x,str) and x for x in binder_names) and
            len(set(binder_names))==len(binder_names) and
            set(binder_names)==set(input_map)|{source['aggregateBinder']}, 'source labels are not telescope indices')
    gaps = source['reportedProducerGaps']
    require(isinstance(gaps,list) and len({x['requiredFactory'] for x in gaps})==len(gaps), 'invalid reported producer gaps')
    require({x['requiredFactory'] for x in gaps}==set(FACTORIES), 'pinned producer gap inventory changed')
    entries = catalog.get('pendingInputs', [])
    require(len(entries)==len(IDS) and {x['id'] for x in entries}==set(IDS) and
            all(x.get('sourceLocator') is not None for x in entries), 'pinned five located pending views required')
    for gap in gaps:
        require(set(gap)=={'family','requiredFactory','producerReportedStatus','deliveredDeclaration','locallyVerifiedDelivery'} and
                isinstance(gap['family'],str) and gap['family'] and isinstance(gap['requiredFactory'],str) and gap['requiredFactory'] and
                gap['producerReportedStatus']=='pending' and gap['deliveredDeclaration'] is None and
                gap['locallyVerifiedDelivery'] is False, 'source gap metadata cannot verify delivery')
    for entry in catalog.get('pendingInputs', []):
        locator = entry.get('sourceLocator')
        if locator is None:
            continue
        require(set(locator)=={'declaration','file','fileSha256','sourceCommit','evidence','ownerSlots'} and
                locator['declaration']==source['theorem'] and locator['evidence']=='static-source-only' and
                locator['sourceCommit']==source['sourceCommit'] and
                locator['file']==names[source['theorem']]['file'] and
                locator['fileSha256']==source['files'][locator['file']], 'source locator provenance mismatch')
        slots = locator['ownerSlots']
        require(isinstance(slots,list) and slots and all(set(x)=={'scope','name'} and isinstance(x['name'],str) for x in slots),
                'source slots use names, not typed binder indices')
        actual = {(x['scope'],x['name']) for x in slots}
        expected = {('binder',n) for n,r in input_map.items() if r['ownerReference']==entry['ownerReference']}
        expected |= {('PublicObligations-field',n) for n,r in field_map.items() if r['ownerReference']==entry['ownerReference']}
        require(len(actual)==len(slots) and actual==expected, 'source owner slice omitted or reassigned a named input')
    return source


def assemble(files, bodies, metadata, metadata_hashes, ownership, tree):
    shapes, bridges = metadata['shapes'], metadata['bridges']
    require(shapes['exhaustiveLaneCoverage'] is False, 'representative inventory must remain nonexhaustive')
    owners = shapes['owners']
    require(set(owners) == set(INPUTS + PUBLIC_FIELDS), 'unexpected producer ownership slots')
    require(set(shapes['binderOrder']) == set(INPUTS + PUBLIC_FIELDS), 'incomplete flattened metadata')
    require(len({row['id'] for row in ownership['items']})==len(ownership['items']), 'duplicate logical ownership item')
    owner_map = {row['id']: row['owner'] for row in ownership['items'] if isinstance(row.get('owner'),str) and row['owner']}
    require(all(ref in owner_map for ref in owners.values()), 'unresolved logical owner reference')
    declarations = []
    for path, selections in DECLARATIONS.items():
        lines = bodies[path].decode().splitlines()
        require('namespace Solidity.Roadmap.G49Final' in lines, 'unexpected source namespace')
        for form, short in selections:
            anchor = form + ' ' + short + ' '
            found = [n for n, line in enumerate(lines, 1) if line.startswith(anchor)]
            require(len(found) == 1, 'missing/ambiguous reviewed source anchor: ' + short)
            declarations.append(dict(declaration=PREFIX+short, file=path, fileSha256=files[path],
                                     line=found[0], sourceForm=form))
    lines = bodies[FOLDED].decode().splitlines()
    start = next(i for i, line in enumerate(lines) if line.startswith('structure PublicObligations '))
    end = next(i for i, line in enumerate(lines) if line.startswith('def FoldStatement '))
    obligations = []
    for name in PUBLIC_FIELDS:
        found = [n+1 for n in range(start+1, end) if lines[n].startswith('  '+name+' :')]
        require(len(found) == 1, 'missing/ambiguous source obligation: ' + name)
        ref = owners[name]
        obligations.append(dict(name=name, container=PUBLIC, ownerReference=ref, owner=owner_map[ref],
                                status='open', evidence='static-source-only', line=found[0]))
    inputs = [dict(name=name, ownerReference=owners[name], owner=owner_map[owners[name]], status='open',
                   role='certificate-package' if name in ('lowering','backend','execution') else 'context-or-function')
              for name in INPUTS]
    gaps = []
    for family in bridges['families']:
        require(family['status'] == 'pending' and family['deliveredDeclaration'] is None,
                'changed producer delivery metadata requires review')
        gaps.append(dict(family=family['family'], requiredFactory=family['factory'],
                         producerReportedStatus='pending', deliveredDeclaration=None,
                         locallyVerifiedDelivery=False))
    require(len(gaps) == 5 and {x['requiredFactory'] for x in gaps} == set(FACTORIES), 'unexpected bridge-family inventory')
    snapshot = dict(evidence='static-source-only', sourceCommit=MASTER, sourceTree=tree,
                    checkpoint=CHECKPOINT, inventorySha256=INVENTORY_SHA, files=files,
                    metadataFiles={METADATA[k]:v for k,v in metadata_hashes.items()},
                    declarationLocators=declarations, theorem=THEOREM, aggregateBinder='obligations',
                    sourceBinderNames=list(THEOREM_BINDERS), sourceInputBindings=inputs,
                    sharedPublicObligations=obligations, reportedProducerGaps=gaps,
                    historicalProducerCheck=bridges['checkedAgainst'],
                    producerReportedCheckedDeclarations=shapes['checkedDeclarations'],
                    producerReportedSourceHashes=shapes['sourceHashes'],
                    exhaustiveLaneCoverage=False, freshLeanRun=False, premiseInventoryComplete=False)
    pending = []
    for key in IDS:
        slots = [dict(scope='binder', name=n) for n in INPUTS if owners[n] == key]
        slots += [dict(scope='PublicObligations-field', name=n) for n in PUBLIC_FIELDS if owners[n] == key]
        require(slots, 'source does not justify this owner slice: '+key)
        pending.append(dict(id=key, area=key.split('.')[0], owner=owner_map[key], ownerReference=key,
                            inputArtifact='elaborated G49Final declaration/field export and compatibility validation',
                            reason='Published conditional declaration located; types, dependency edges and producers remain unverified.',
                            source='Coordinator exact-master inventory plus published representative ownership metadata',
                            sourceLocator=dict(declaration=THEOREM, file=FOLDED, fileSha256=files[FOLDED],
                                               sourceCommit=MASTER, evidence='static-source-only', ownerSlots=slots)))
    return dict(nodes=[], pendingInputs=pending,
                roots={'G49':list(IDS[:3]), 'G50':list(IDS[3:])}, sourceSnapshot=snapshot)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inventory', type=Path, default=Path('/workspace/h62-coordinator-inputs/g49-master-source-inventory.txt'))
    parser.add_argument('--ownership', type=Path, default=Path('/workspace/h62-coordinator-inputs/ownership.json'))
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    require(not any(name in os.environ for name in ('GIT_GRAFT_FILE','GIT_SHALLOW_FILE')), 'custom history environment unavailable')
    require(git('rev-parse','--is-shallow-repository').strip()==b'false', 'shallow ancestry unavailable')
    grafts = Path(git('rev-parse','--git-path','info/grafts').decode().strip())
    if not grafts.is_absolute():
        grafts = ROOT / grafts
    require(not grafts.exists(), 'grafted ancestry unavailable')
    git('merge-base','--is-ancestor',CHECKPOINT,MASTER)
    git('merge-base','--is-ancestor',MASTER,'origin/master')
    files, bodies = verify_inventory(args.inventory.read_bytes(), lambda p: git('show', MASTER+':'+p))
    raw = {key:git('show',MASTER+':'+path) for key,path in METADATA.items()}
    metadata = {key:strict_json(value) for key,value in raw.items()}
    catalog = assemble(files,bodies,metadata,{key:sha(value) for key,value in raw.items()},
                       strict_json(args.ownership.read_bytes()),git('rev-parse',MASTER+'^{tree}').decode().strip())
    import graph
    graph.build({'schema':1,'source':'Lean.ConstantInfo.type','declarations':[]},catalog,
                'c6f550e281a7e5affa9a99bc2cdaed556dec00e4',
                git('rev-parse',MASTER+'^{tree}').decode().strip(),graph.read(args.ownership))
    args.output.write_bytes((json.dumps(catalog,sort_keys=True,indent=2)+'\n').encode())
    print('G49_SOURCE_INTAKE_PASS: source locators only; no fresh Lean/type/premise discharge')


if __name__ == '__main__':
    main()
