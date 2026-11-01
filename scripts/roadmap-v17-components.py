#!/usr/bin/env python3
"""Private committed-source staging and retained component accounting, never release closure."""
import argparse
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('v17_component_kernel', ROOT/'scripts/roadmap-v17-kernel.py')
k = importlib.util.module_from_spec(spec); spec.loader.exec_module(k)
p, e = k.p, k.e
SHA1 = re.compile(r'[0-9a-f]{40}')
BUILD_GATES = {'runtime-keysort', 'generator-solcases', 'clean-default', 'clean-compiler',
               'clean-frontend', 'warm-default', 'warm-compiler', 'warm-frontend'}
IDENTITY = ('revision', 'sourceTree', 'sourceToolchainKey', 'inputs', 'runtime', 'buildTools', 'serialConfigSha256')
IMPORTED_HELPER_SHA256={str(path):p.resources.hash_file(path) for path in
    (Path(__file__),Path(k.__file__),Path(p.__file__),Path(e.__file__),Path(p.resources.__file__),k.TEMPLATE)}


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def no_promotion(value):
    if isinstance(value, dict):
        for key, child in value.items():
            if key in ('releaseClosed', 'semanticPremisesDischarged'):
                e.require(child is False, 'attempted semantic/release promotion')
            no_promotion(child)
    elif isinstance(value, list):
        for child in value: no_promotion(child)


def git(directory, *args):
    env = dict(os.environ)
    for key in list(env):
        if key.startswith('GIT_'): del env[key]
    env.update(GIT_CONFIG_NOSYSTEM='1', GIT_CONFIG_GLOBAL='/dev/null',
               GIT_CONFIG_SYSTEM='/dev/null', GIT_NO_REPLACE_OBJECTS='1', GIT_OPTIONAL_LOCKS='0')
    return subprocess.check_output(['git', '--no-replace-objects', '--no-pager', '-c', 'core.hooksPath=/dev/null', '-c','core.fsmonitor=false', '-c','gc.auto=0', '-c','maintenance.auto=false',
        '-c', 'core.attributesFile=/dev/null', '-c', 'core.autocrlf=false',
        '-C', str(directory), *args], env=env, stderr=subprocess.PIPE, timeout=60)


def safe_config(directory):
    # Names only: never print credentials/config values. No include expansion.
    allowed={'core.repositoryformatversion','core.filemode','core.bare','core.logallrefupdates',
             'core.ignorecase','core.precomposeunicode','extensions.worktreeconfig',
             'user.name','user.email','remote.origin.url','remote.origin.fetch'}
    scopes=['--local']
    try:worktree=git(directory,'config','--local','--type=bool','--get','extensions.worktreeConfig').decode().strip()
    except subprocess.CalledProcessError as error:
        e.require(error.returncode==1,'malformed private worktree configuration');worktree='false'
    e.require(worktree in ('true','false'),'unknown private worktree configuration')
    if worktree=='true':scopes.append('--worktree')
    for scope in scopes:
        keys=git(directory,'config',scope,'--no-includes','--name-only','--list').decode().splitlines()
        e.require(all(key.lower() in allowed or re.fullmatch(r'branch\..*\.(remote|merge)',key.lower()) for key in keys),
                  'unsafe private Git configuration key')


def source_inventory(directory, head):
    """Check EVERY tracked blob against checked-out bytes, including executable mode."""
    safe_config(directory)
    files = {}
    for raw in git(directory, 'ls-tree', '-rz', '--full-tree', head).split(b'\0'):
        if not raw: continue
        meta, path_raw = raw.split(b'\t', 1)
        mode, kind, oid = meta.decode().split()
        name = path_raw.decode('utf8'); path = PurePosixPath(name)
        e.require(mode in ('100644', '100755') and kind == 'blob', 'symlink/submodule/nonblob source')
        e.require(name not in files and not path.is_absolute() and '..' not in path.parts
                  and str(path) == name and '\\' not in name and all(x.lower()!='.git' for x in path.parts), 'unsafe/duplicate source path')
        actual = directory / name
        e.require(actual.resolve() == actual and actual.is_file() and not actual.is_symlink(), 'escaping source')
        data = actual.read_bytes()
        blob = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        e.require(blob == oid and bool(actual.stat().st_mode & 0o111) == (mode == '100755'),
                  'checkout bytes/mode differ from committed blob')
        files[name] = {'gitBlob': oid, 'sha256': e.digest(data), 'mode': mode}
    e.require(files, 'empty private source')
    actual_files=set()
    for base,dirs,names in os.walk(directory,followlinks=False):
        base=Path(base)
        if base==directory:dirs[:]=[name for name in dirs if name!='.git']
        for name in list(dirs):e.require(not (base/name).is_symlink(),'symlink private directory')
        for name in names:
            path=base/name
            if path==directory/'.git':continue
            e.require(path.is_file() and not path.is_symlink(),'nonregular private file')
            actual_files.add(str(path.relative_to(directory)))
    e.require(actual_files==set(files),'untracked/missing private source bytes')
    e.require(not (directory/'.lake').exists(), 'source stage contains a build/cache tree')
    return files


def source_closures(directory, modules):
    """Trusted lexical inventory only; Bridge never becomes a core/kernel import."""
    old_root,old_git=k.ROOT,e.git
    k.ROOT=directory;e.git=lambda root,*args:git(root,*args).decode().strip()
    try:
        def one(module):
            if module.startswith('Solidity.'):return k.source_closure(module)
            e.require(module.startswith('SolidityBridge.') and k.NAME.fullmatch(module),'unsupported source layer')
            active=set();rows={};order=[]
            def visit(name):
                e.require(name not in active,'cyclic Bridge imports')
                if name in rows:return
                if name.startswith('Solidity.'):
                    core=k.source_closure(name)
                    for dep in core['order']:
                        if dep not in rows:rows[dep]=core['modules'][dep];order.append(dep)
                    return
                e.require(name.startswith('SolidityBridge.'),'unsupported Bridge dependency')
                rel='Bridge/'+name.replace('.','/')+'.lean'
                e.require(e.git(directory,'ls-files','--error-unmatch',rel)==rel,'untracked Bridge source')
                path=e.local_file(directory,rel);imports=[]
                for line in k.uncomment(path.read_text()).splitlines():
                    line=line.strip()
                    if not line:continue
                    if line.startswith('import '):
                        dep=line[7:].strip();e.require(k.NAME.fullmatch(dep),'unsupported Bridge import syntax');imports.append(dep)
                    elif line.startswith(('import','prelude','module','public import','private import')):raise ValueError('unsupported Bridge header')
                    else:break
                active.add(name)
                for dep in imports:
                    if dep.startswith(('Solidity.','SolidityBridge.')):visit(dep)
                    else:e.require(dep.split('.')[0] in ('Init','Lean','Std'),'unsupported Bridge external input')
                active.remove(name);rows[name]={'source':rel,'sha256':e.digest(path.read_bytes()),'imports':imports};order.append(name)
            visit(module);return {'order':order,'modules':rows}
        return {module:one(module) for module in modules}
    finally:k.ROOT,e.git=old_root,old_git


def module_path(module):
    e.require(isinstance(module,str) and k.NAME.fullmatch(module),'invalid module identity')
    e.require(module.startswith(('Solidity.','SolidityBridge.')),'unsupported module layer')
    return ('Bridge/' if module.startswith('SolidityBridge.') else '')+module.replace('.','/')+'.lean'


def validate_package(expected):
    e.require(set(expected) == {'head', 'tree', 'base', 'ref', 'bundleSha256', 'modules'}, 'invalid package request')
    e.require(all(isinstance(expected[x], str) and SHA1.fullmatch(expected[x]) for x in ('head','tree','base')),
              'invalid full commit/tree identity')
    e.require(expected['base'] == e.BASE and e.HEX.fullmatch(expected['bundleSha256']), 'wrong frozen base/bundle hash')
    e.require(isinstance(expected['ref'], str) and expected['ref'].startswith('refs/heads/')
              and not any(c.isspace() for c in expected['ref']), 'invalid advertised ref')
    modules = expected['modules']
    e.require(isinstance(modules, list) and 1 <= len(modules) <= 16 and modules == sorted(set(modules))
              and all(isinstance(m,str) and k.NAME.fullmatch(m) and m.startswith('Solidity.') for m in modules),
              'invalid requested module set')
    return expected


def stage(bundle, expected, destination):
    """Only source preparation. Never compile, execute peer scripts, or alter task refs."""
    validate_package(expected)
    modules = expected['modules']
    bundle, destination = Path(bundle), Path(destination)
    e.require(bundle.is_absolute() and bundle.resolve() == bundle and bundle.is_file()
              and not bundle.is_symlink(), 'noncanonical bundle')
    e.require(destination.is_absolute() and destination.resolve() == destination
              and destination.is_relative_to('/workspace/scratch') and not destination.exists()
              and destination.parent.is_dir(), 'private source destination must be new and canonical')
    before = {'head': git(ROOT,'rev-parse','HEAD').decode().strip(),
              'status': git(ROOT,'status','--porcelain','--untracked-files=all').decode()}
    digest = p.resources.hash_file(bundle)
    e.require(digest == expected['bundleSha256'], 'wrong bundle bytes')
    advertised = [line.split() for line in git(ROOT,'bundle','list-heads',str(bundle)).decode().splitlines()]
    e.require(sum(row == [expected['head'], expected['ref']] for row in advertised) == 1,
              'missing/ambiguous exact advertised checkpoint')
    started = time.monotonic()
    try:
        # Local shared object storage; no network, hooks, peer config or cache copies.
        git(ROOT, 'clone', '--shared', '--no-checkout', '--template=', str(ROOT), str(destination))
        safe_config(destination)
        git(destination, 'bundle', 'verify', str(bundle))
        git(destination, 'fetch', '--no-tags', '--no-write-fetch-head', str(bundle),
            expected['ref']+':refs/v17-input/checkpoint')
        head = git(destination,'rev-parse','refs/v17-input/checkpoint^{commit}').decode().strip()
        tree = git(destination,'rev-parse',head+'^{tree}').decode().strip()
        e.require(head == expected['head'] and tree == expected['tree'], 'wrong checkpoint commit/tree')
        git(destination, 'merge-base', '--is-ancestor', expected['base'], head)
        # Verify tree entry kinds BEFORE checkout, so symlinks/submodules never materialize.
        entries = git(destination,'ls-tree','-rz','--full-tree',head).split(b'\0')
        e.require(all(not row or row.split(b' ',1)[0] in (b'100644',b'100755') for row in entries),
                  'unsupported symlink/submodule tree')
        for raw in entries:
            if not raw:continue
            name=raw.split(b'\t',1)[1].decode('utf8');parts=PurePosixPath(name)
            e.require(not parts.is_absolute() and '..' not in parts.parts and str(parts)==name
                      and all(x.lower()!='.git' for x in parts.parts) and '\\' not in name,'unsafe committed path')
        git(destination, 'checkout', '--detach', head)
        files = source_inventory(destination,head)
        old_root, old_git = k.ROOT, e.git
        try:
            k.ROOT = destination
            e.git = lambda root,*args:git(root,*args).decode().strip()
            closures = source_closures(destination,modules)
            snapshot = e.snapshot(destination)
        finally: k.ROOT, e.git = old_root, old_git
        e.require(time.monotonic()-started <= 300, 'source preparation cumulative budget exceeded')
        return {'schema':1, 'sourceOnly':True, 'destination':str(destination), 'package':expected,
                'snapshot':snapshot, 'files':files, 'moduleClosures':closures,
                'independentKernelReplay':'PENDING', 'sourcePreparationTiming':{'gitCommandSeconds':60,'postRunAcceptanceSeconds':300,'requiresOuterProcessTimeout':True}, 'semanticPremisesDischarged':False, 'releaseClosed':False}
    finally:
        e.require(p.resources.hash_file(bundle) == digest, 'bundle changed during staging')
        e.require(before == {'head':git(ROOT,'rev-parse','HEAD').decode().strip(),
                             'status':git(ROOT,'status','--porcelain','--untracked-files=all').decode()},
                  'task checkout changed during staging')


def attachment(ref):
    e.require(set(ref) == {'path','sha256'} and isinstance(ref['path'],str) and e.HEX.fullmatch(ref['sha256']),
              'invalid attachment reference')
    path = Path(ref['path'])
    e.require(path.is_absolute() and path.resolve() == path and path.is_file() and not path.is_symlink(),
              'invalid attachment path')
    data = path.read_bytes()
    e.require(e.digest(data) == ref['sha256'], 'corrupt/mutated attachment')
    return path, e.loads(data)


def identity(snapshot):
    return {key:snapshot[key] for key in IDENTITY}


PROFILE_FILES=('docs/solidity-scope.md','docs/feature-work/roadmap-decisions-impact.md')


def profile_identity(source):
    return e.digest(canonical({name:source['files'][name]['sha256'] for name in PROFILE_FILES}).encode())


def aggregate(plan, stages):
    """Retained per-component provenance only. All ledger/semantic closure remains OPEN."""
    e.require(set(plan) == {'schema','ledgerSha256','components','targetSnapshot'}, 'invalid component plan')
    e.require(type(plan['schema']) is int and plan['schema']==1, 'invalid plan schema')
    ledger = e.load(ROOT/e.LEDGER)
    e.require(plan['ledgerSha256'] == e.digest((ROOT/e.LEDGER).read_bytes()), 'changed frozen obligation ledger')
    no_promotion(plan)
    e.require(isinstance(plan['components'],list) and plan['components'], 'empty component plan')
    specs = {}; results = {}; shared = {}; conflicts=[]
    for spec in plan['components']:
        e.require(set(spec) == {'id','stage','snapshot','interface','requires','mandatoryGates','kernelRecords','observations','cachePairs'},
                  'invalid component specification')
        name = spec['id']; e.require(isinstance(name,str) and name and name not in specs, 'duplicate/invalid component')
        specs[name] = spec
        e.require(isinstance(spec['requires'],dict) and name not in spec['requires'], 'invalid component dependency')
        interface = spec['interface']
        e.require(set(interface) == {'modules','declarationRequests','profileSha256','orderedObservations'}, 'invalid source interface')
        e.require(e.HEX.fullmatch(interface['profileSha256']) and isinstance(interface['modules'],dict)
                  and interface['modules'], 'missing interface identity')
        e.require(isinstance(interface['declarationRequests'],list), 'invalid declaration requests')
        for d in interface['declarationRequests']:
            e.require(set(d)=={'name','module','kind','metadataSha256','propositionPremises'} and d['module'] in interface['modules']
                      and isinstance(d['name'],str) and k.NAME.fullmatch(d['name'])
                      and d['kind'] in ('theorem','definition') and (d['metadataSha256'] is None or isinstance(d['metadataSha256'],str) and e.HEX.fullmatch(d['metadataSha256'])) and isinstance(d['propositionPremises'],list)
                      and all(isinstance(x,str) for x in d['propositionPremises']), 'invalid declaration request')
        obligations = ['semantic-feature-match-unreviewed', 'independent-kernel-replay-pending']
        if interface['declarationRequests']: obligations.append('source-declarations-not-checked-metadata')
        if any(d['propositionPremises'] for d in interface['declarationRequests']): obligations.append('conditional-premises-not-discharged')
        source = stages.get(name)
        if source is None:
            results[name]={'sourceReady':False,'retainedEvidenceConsistent':False,'obligations':obligations+['missing-source-package']}
            continue
        no_promotion(source)
        e.require(interface['profileSha256']==profile_identity(source),'producer profile/decision source differs')
        e.require(source.get('sourceOnly') is True and type(source.get('schema')) is int and source.get('schema')==1, 'invalid source-stage receipt')
        e.require(e.digest(canonical(source).encode()) == spec['stage'], 'wrong source-stage receipt')
        e.require(identity(source['snapshot']) == identity(spec['snapshot']), 'wrong producer source/tool/config identity')
        # Re-read committed tree and current private bytes; a staged receipt alone is not enough.
        package=source['package']
        validate_package(package)
        root = Path(source['destination'])
        e.require(root.resolve()==root and root.is_relative_to('/workspace/scratch'), 'invalid staged source path')
        e.require(git(root,'rev-parse','HEAD').decode().strip()==package['head'], 'stale staged revision')
        git(root,'merge-base','--is-ancestor',e.BASE,package['head'])
        e.require(package['tree']==source['snapshot']['sourceTree'],'package tree/snapshot disagreement')
        e.require(source_inventory(root,source['package']['head']) == source['files'], 'stale staged source files')
        e.require(git(root,'rev-parse','HEAD^{tree}').decode().strip()==source['snapshot']['sourceTree'] and source['snapshot']['revision']==source['package']['head'], 'staged snapshot/tree contradiction')
        old_root,old_git=k.ROOT,e.git
        try:
            k.ROOT=root;e.git=lambda directory,*args:git(directory,*args).decode().strip()
            e.require(source_closures(root,source['package']['modules'])==source['moduleClosures'], 'forged/truncated import closure')
            interface_closures=source_closures(root,list(interface['modules']))
        finally:k.ROOT,e.git=old_root,old_git
        for module, sha in interface['modules'].items():
            rel=module_path(module)
            e.require(source['files'][rel]['sha256']==sha,
                      'wrong module/source binding')
            for dep, row in interface_closures[module]['modules'].items():
                e.require(source['files'][row['source']]['sha256']==row['sha256'], 'wrong import source binding')
                if dep in shared and shared[dep]['sha256']!=row['sha256']:
                    conflicts.append({'module':dep,'firstComponent':shared[dep]['component'],'firstSha256':shared[dep]['sha256'],'secondComponent':name,'secondSha256':row['sha256']})
                else:shared[dep]={'sha256':row['sha256'],'component':name}
        gates = {}; missing = []; failed = []
        e.require(isinstance(spec['mandatoryGates'],dict) and (spec['mandatoryGates'] or spec['kernelRecords']), 'empty mandatory evidence set')
        for gate, ref in spec['mandatoryGates'].items():
            e.require(gate in BUILD_GATES, 'unsupported retained gate; use its existing live consumer separately')
            if ref is None: missing.append(gate); continue
            path, record = attachment(ref)
            e.require(record['before']==spec['snapshot'], 'gate source/tool/config differs from component')
            ok = p.validate(record,path.parent,spec['snapshot'],gate,live_outputs=False)
            gates[gate]=record
            if not ok: failed.append(gate)
        # Delegate exact AST/type/value/dependency/axiom checks to the EXISTING extractor validator.
        e.require(isinstance(spec['kernelRecords'],dict), 'invalid kernel record map')
        requested={d['name']:d for d in interface['declarationRequests']}
        e.require(len(requested)==len(interface['declarationRequests']), 'duplicate declaration request')
        extracted={};missing_kernels=[]
        for module,ref in spec['kernelRecords'].items():
            e.require(module in interface['modules'], 'unmatched kernel record module')
            if ref is None:missing_kernels.append(module);continue
            e.require(module.startswith('Solidity.'),'Bridge kernel records require the existing Bridge consumer, not a relaxed core extractor')
            e.require(set(ref)=={'record','replay'},'both retained extraction and replay are required')
            _,record=attachment(ref['record']);_,replay=attachment(ref['replay'])
            e.require(record['before']['repository']==str(root) and replay['before']['repository']==str(root),
                      'kernel records are not from exact private source tree')
            old_root,old_provenance_root,old_git=k.ROOT,p.ROOT,e.git
            try:
                k.ROOT=root;p.ROOT=root;e.git=lambda directory,*args:git(directory,*args).decode().strip()
                # Same complete extractor validation and replay matcher; no second proof engine.
                req=k.validate_record(record,spec['snapshot'])
                k.validate_record(replay,spec['snapshot']);k.match_replay(record,replay)
            finally:k.ROOT,p.ROOT,e.git=old_root,old_provenance_root,old_git
            e.require(req['module']==module,'wrong defining kernel module')
            for row in record['result']['rows']:
                e.require(row['name'] in requested and row['name'] not in extracted,'unmatched/duplicate kernel declaration')
                d=requested[row['name']]
                e.require(row['module']==d['module'] and row['kind']==d['kind'],'wrong checked declaration kind/module')
                e.require(d['metadataSha256'] is not None and d['metadataSha256']==e.digest(k.canonical(row)),
                          'missing/mismatched exact checked type/value/dependency/axiom requirement')
                extracted[row['name']]={key:row[key] for key in ('name','module','kind','typeSha256','valueSha256','axioms','propositionBinders')}
                if row['propositionBinders']:obligations.append('checked-conditional-premises-not-discharged:'+row['name'])
        for declaration_name in requested:
            if declaration_name not in extracted:obligations.append('missing-retained-kernel-metadata:'+declaration_name);missing_kernels.append(declaration_name)
        if requested and not missing_kernels:
            obligations.remove('independent-kernel-replay-pending');obligations.remove('source-declarations-not-checked-metadata');obligations.append('retained-kernel-replay-matched-not-final-joint-proof')
        e.require(isinstance(spec['cachePairs'],list), 'invalid clean/cache pair list')
        for pair in spec['cachePairs']:
            e.require(set(pair)=={'clean','warm'} and pair['clean'].startswith('clean-') and pair['warm'].startswith('warm-')
                      and pair['clean'] in spec['mandatoryGates'] and pair['warm'] in spec['mandatoryGates'], 'unaccounted clean/cache pair')
            if pair['clean'] not in gates or pair['warm'] not in gates or any(gates[x]['exit'] for x in pair.values()):
                obligations.append('clean-cache-pair-incomplete'); continue
            p.pair_consistency(gates[pair['clean']],gates[pair['warm']])
        e.require(isinstance(spec['observations'],list), 'invalid observations')
        observed=[];observation_ids=set();missing_observations=[]
        e.require(interface['orderedObservations']==[{'id':o['id'],'sha256':o['expectedSha256']} for o in spec['observations']], 'unmatched ordered observation contract')
        for obs in spec['observations']:
            e.require(set(obs)=={'id','expectedSha256','artifact'} and isinstance(obs['id'],str), 'invalid observation binding')
            e.require(obs['id'] not in observation_ids and e.HEX.fullmatch(obs['expectedSha256']), 'duplicate/invalid observation')
            observation_ids.add(obs['id'])
            if obs['artifact'] is None: obligations.append('missing-observation:'+obs['id']); missing_observations.append(obs['id']); continue
            e.require(obs['artifact']['sha256']==obs['expectedSha256'], 'unmatched ordered observation identity')
            attachment(obs['artifact']); observed.append(obs['id'])
        # Hash matching is attachment accounting, not an oracle for observations.
        if spec['observations']: obligations.append('observation-semantic-replay-not-established-by-aggregation')
        obligations += ['missing-gate:'+gate for gate in missing]+['failed-gate:'+gate for gate in failed]
        results[name]={'sourceReady':True,'retainedEvidenceConsistent':not missing and not failed and not missing_observations and not missing_kernels, 'retainedDeclarationMetadata':extracted,
                       'interfaceSha256':e.digest(canonical(interface).encode()), 'producerRevision':spec['snapshot']['revision'],
                       'matchesTargetSnapshot':identity(spec['snapshot'])==identity(plan['targetSnapshot']),
                       'orderedObservationIds':observed,'obligations':obligations}
    for name,spec in specs.items():
        results[name]['requiredProducerSourcesReady']=True
        results[name]['requiredProducerEvidenceConsistent']=True
        for dep,sha in spec['requires'].items():
            e.require(dep in specs and e.HEX.fullmatch(sha), 'unknown/unbound required producer component')
            actual=e.digest(canonical(specs[dep]['interface']).encode())
            e.require(sha==actual, 'mismatched producer interface')
            if not results[dep]['sourceReady']:
                results[name]['requiredProducerSourcesReady']=False;results[name]['obligations'].append('missing-producer:'+dep)
            if not results[dep]['retainedEvidenceConsistent']:
                results[name]['requiredProducerEvidenceConsistent']=False;results[name]['obligations'].append('producer-evidence-incomplete:'+dep)
    # Cyclic producer requirements cannot masquerade as independently ready components.
    active=set();done=set();source_blocked={};evidence_blocked={}
    def visit(name):
        e.require(name not in active,'cyclic component requirements')
        if name in done:return
        active.add(name)
        required_source=set();required_evidence=set()
        for dep in specs[name]['requires']:
            visit(dep);required_source.update(source_blocked[dep]);required_evidence.update(evidence_blocked[dep])
        results[name]['requiredProducerSourcesReady']=not required_source
        results[name]['requiredProducerEvidenceConsistent']=not required_evidence
        results[name]['unreadyRequiredSourceComponents']=sorted(required_source)
        results[name]['unreadyRequiredEvidenceComponents']=sorted(required_evidence)
        source_blocked[name]=required_source|({name} if not results[name]['sourceReady'] else set())
        evidence_blocked[name]=required_evidence|({name} if not results[name]['retainedEvidenceConsistent'] else set())
        active.remove(name);done.add(name)
    for name in specs:visit(name)
    e.require(set(stages)<=set(specs),'unmatched extra component package')
    for conflict in conflicts:
        for owner in (conflict['firstComponent'],conflict['secondComponent']):
            results[owner]['obligations'].append('joint-source-conflict:'+conflict['module'])
    return {'schema':1,'components':results,'jointSourceConflicts':conflicts,'openRows':e.inventory(ledger),
            'jointValidation':'PENDING actual combined concrete tree, imports, proofs and gates',
            'accountingComplete':False,'semanticPremisesDischarged':False,'releaseClosed':False,
            'boundary':'Authenticated committed sources and retained gate/attachment accounting; no new kernel or observation sufficiency proof.'}


def hardened_snapshot(directory):
    old=e.git
    try:
        e.git=lambda root,*args:git(root,*args).decode().strip()
        return e.snapshot(directory)
    finally:e.git=old


def consumer_identity():
    """Require committed consumer code and a clean exact source/tool snapshot."""
    snapshot=hardened_snapshot(ROOT)
    paths=[Path(__file__),Path(k.__file__),Path(p.__file__),Path(e.__file__),Path(p.resources.__file__),k.TEMPLATE]
    helpers={}
    for path in paths:
        relative=str(path.relative_to(ROOT));data=path.read_bytes()
        e.require(e.digest(data)==IMPORTED_HELPER_SHA256[str(path)],'consumer helper changed since import')
        e.require(data==git(ROOT,'show',snapshot['revision']+':'+relative),'loaded consumer helper differs from committed source')
        helpers[relative]=e.digest(data)
    return {'snapshot':snapshot,'helperSha256':helpers}


def collect_target(source, req, out):
    """One actual core-module query+replay, with the unchanged complete extractor."""
    req=k.request(req);validate_package(source['package']);no_promotion(source)
    consumer_before=consumer_identity()
    e.require(type(source.get('schema')) is int and source['schema']==1 and source.get('sourceOnly') is True,'invalid target source-stage schema')
    root=Path(source['destination']);out=Path(out)
    e.require(root.resolve()==root and root.is_relative_to('/workspace/scratch'), 'invalid private target source')
    e.require(out.is_absolute() and out.resolve()==out and out.is_relative_to('/workspace/scratch')
              and not out.is_relative_to(root) and not out.exists(), 'NEW external target evidence directory required')
    e.require(git(root,'rev-parse','HEAD').decode().strip()==source['package']['head'], 'target source revision changed')
    git(root,'merge-base','--is-ancestor',e.BASE,source['package']['head'])
    e.require(source_inventory(root,source['package']['head'])==source['files'], 'target source files changed')
    e.require(module_path(req['module']) in source['files'], 'missing concrete producer module')
    out.mkdir(parents=True)
    before_code=p.resources.hash_file(Path(__file__))
    summary={'schema':1,'producerHead':source['package']['head'],'request':req,
             'consumerRevision':consumer_before['snapshot']['revision'],'consumerBefore':consumer_before,
             'consumerSha256':before_code,'recordExit':None,'replayExit':None,'postInputExit':0,
             'semanticPremisesDischarged':False,'releaseClosed':False}
    old_root,old_provenance_root,old_git=k.ROOT,p.ROOT,e.git
    current=None
    try:
        k.ROOT=root;p.ROOT=root;e.git=lambda directory,*args:git(directory,*args).decode().strip()
        current=hardened_snapshot(root)
        e.require(current['sourceTree']==source['package']['tree'],'target package tree changed')
        e.require(identity(current)==identity(source['snapshot']), 'staged source/tool/config differs at query launch')
        record=k.collect(req,out/'extract');summary['recordExit']=record['exit'];summary['recordCommandExit']=record.get('commandExit')
        summary['record']={'path':str(out/'extract/record.json'),'sha256':p.resources.hash_file(out/'extract/record.json')}
        if record['exit']==0:
            k.validate_record(record,current)
            replay=k.collect(req,out/'replay');summary['replayExit']=replay['exit'];summary['replayCommandExit']=replay.get('commandExit')
            summary['replay']={'path':str(out/'replay/record.json'),'sha256':p.resources.hash_file(out/'replay/record.json')}
            if replay['exit']==0:
                k.validate_record(replay,current);k.match_replay(record,replay)
                summary['checkedDeclarations']=[{key:row[key] for key in ('name','module','kind','typeSha256','valueSha256','axioms','propositionBinders')} for row in record['result']['rows']]
                summary['completeLiveReplayMatched']=True
                unexpected=sorted({axiom for row in record['result']['rows'] for axiom in row['axioms']}-{'propext','Classical.choice','Quot.sound'})
                summary['unexpectedAxioms']=unexpected
                if unexpected:summary['consumerValidationExit']=1;summary['error']='unexpected scoped axioms'
    except (ValueError,KeyError,TypeError,OSError,subprocess.SubprocessError) as error:
        summary['consumerValidationExit']=2;summary['error']=str(error)
    finally:
        k.ROOT,p.ROOT,e.git=old_root,old_provenance_root,old_git
        try:
            e.require(before_code==p.resources.hash_file(Path(__file__)),'consumer implementation changed')
            e.require(source_inventory(root,source['package']['head'])==source['files'],'target source changed after query')
            summary['targetAfter']=hardened_snapshot(root)
            e.require(current is None or summary['targetAfter']==current,'target revision/tree/tool/config changed after query')
            summary['consumerAfter']=consumer_identity()
            e.require(summary['consumerAfter']==consumer_before,'consumer revision/tree/helper/tool/config changed after query')
        except (ValueError,OSError,subprocess.SubprocessError) as error:
            summary['postInputExit']=125;summary['postInputError']=str(error)
        summary['exit']=next((code for code in (summary['recordExit'],summary['replayExit'],summary.get('consumerValidationExit',0),summary['postInputExit']) if code is not None and code!=0),0)
        if not summary.get('completeLiveReplayMatched') and summary['exit']==0:summary['exit']=2
        (out/'component.json').write_text(json.dumps(summary,indent=2)+'\n')
    return summary


def main():
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument('mode',choices=['stage','aggregate','collect']);cli.add_argument('--request',type=Path,required=True)
    cli.add_argument('--bundle',type=Path);cli.add_argument('--destination',type=Path)
    cli.add_argument('--stages',type=Path);cli.add_argument('--out',type=Path);args=cli.parse_args()
    with open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a+') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        if args.mode=='collect':
            e.require(args.stages and args.out,'source receipt and new output required')
            result=collect_target(e.load(args.stages),e.load(args.request),args.out)
            print(json.dumps(result,indent=2));return result['exit']
        if args.mode=='stage':
            e.require(args.bundle and args.destination,'bundle and NEW private destination required')
            result=stage(args.bundle,e.load(args.request),args.destination)
        elif args.mode=='aggregate':
            e.require(args.stages,'stage receipt map required')
            result=aggregate(e.load(args.request),e.load(args.stages))
        print(json.dumps(result,indent=2))
if __name__=='__main__':
    try:raise SystemExit(main())
    except (ValueError,KeyError,TypeError,OSError,subprocess.SubprocessError) as error:
        print(json.dumps({'error':str(error),'semanticPremisesDischarged':False,'releaseClosed':False}));raise SystemExit(2)
