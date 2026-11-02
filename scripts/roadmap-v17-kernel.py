#!/usr/bin/env python3
"""Narrow live Lean metadata extraction. Never discharges semantic premises.

Every collection freshly compiles the requested repository source/import closure
with an isolated LEAN_PATH. Installed toolchain inputs are hashed, not rebuilt.
The optional claim consumer ALWAYS replays; sealed logs alone are not live proof.
"""
import argparse
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import time
import uuid

ROOT = Path(__file__).resolve().parents[1]
sp = importlib.util.spec_from_file_location('kernel_runtime', ROOT/'scripts/roadmap-v17-provenance.py')
p = importlib.util.module_from_spec(sp); sp.loader.exec_module(p)
e = p.e
TEMPLATE = ROOT/'scripts/roadmap-v17-kernel-query.lean'
NAME = re.compile(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z')
KINDS = {'axiom','definition','theorem','opaque','quotient','inductive','constructor','recursor'}
BEGIN = 'V17_KERNEL_BEGIN'
END = 'V17_KERNEL_END'


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()


def request(value):
    e.require(set(value)=={'schema','module','declarations'} and type(value['schema']) is int and value['schema']==1, 'invalid request schema')
    module=value['module']
    e.require(isinstance(module,str) and NAME.fullmatch(module) and module.startswith('Solidity.'), 'unsupported module/namespace')
    e.require(isinstance(value['declarations'],list) and 0<len(value['declarations'])<=16, 'request requires 1..16 declarations')
    seen=set()
    for item in value['declarations']:
        e.require(set(item)=={'name','kind'}, 'invalid declaration request')
        n=item['name']
        e.require(isinstance(n,str) and NAME.fullmatch(n) and n.startswith('Solidity.'), 'unsupported declaration namespace')
        e.require(n not in seen and item['kind'] in KINDS, 'duplicate name or unsupported kind')
        seen.add(n)
    return value


def uncomment(source):
    # Only the header is interpreted, with nested block/line comments removed.
    out=[]; i=0; depth=0
    while i<len(source):
        if source.startswith('/-',i): depth+=1; out.append('  '); i+=2
        elif depth and source.startswith('-/',i): depth-=1; out.append('  '); i+=2
        elif depth: out.append('\n' if source[i]=='\n' else ' '); i+=1
        elif source.startswith('--',i):
            end=source.find('\n',i); i=len(source) if end<0 else end; out.append(' ')
        else:
            # No string can occur in the supported module header.
            if source[i]=='"': return ''.join(out)+source[i:]
            out.append(source[i]); i+=1
    e.require(depth==0, 'unclosed header comment')
    return ''.join(out)


def source_closure(module):
    active=set(); done={}; ordered=[]
    def visit(n):
        e.require(n not in active, 'cyclic repository imports')
        if n in done: return
        rel=n.replace('.','/')+'.lean'
        e.require(e.git(ROOT,'ls-files','--error-unmatch',rel)==rel, 'untracked repository source')
        path=e.local_file(ROOT,rel)
        e.require(path==ROOT/rel, 'symlinked source')
        text=path.read_text(); imports=[]
        for line in uncomment(text).splitlines():
            line=line.strip()
            if not line: continue
            if line.startswith('import '):
                m=line[7:].strip(); e.require(NAME.fullmatch(m), 'unsupported import syntax')
                imports.append(m)
            elif line.startswith(('import','prelude','module','public import','private import')):
                raise ValueError('unsupported module header syntax')
            else: break
        active.add(n)
        for dep in imports:
            if dep.startswith('Solidity.'): visit(dep)
            else: e.require(dep.split('.')[0] in ('Init','Lean','Std'), 'unsupported external repository import')
        active.remove(n)
        done[n]={'source':rel,'sha256':e.digest(path.read_bytes()),'imports':imports}
        ordered.append(n)
    visit(module)
    return {'order':ordered,'modules':done}


def lean_name(n):
    result='Lean.Name.anonymous'
    for part in n.split('.'): result='(Lean.Name.str '+result+' '+json.dumps(part)+')'
    return result


def query_bytes(req):
    source=TEMPLATE.read_text().replace('-- V17_PROJECT_IMPORTS','import '+req['module'])
    names=', '.join('('+lean_name(x['name'])+', '+lean_name(req['module'])+', '+json.dumps(x['kind'])+')' for x in req['declarations'])
    source += '\nrun_cmd do\n  let result ← Lean.Elab.Command.liftTermElabM (Solidity.Roadmap.V17.KernelQuery.extract #['+names+'])\n  Lean.Elab.Command.liftIO (IO.println ("'+BEGIN+'\\n" ++ result.compress ++ "\\n'+END+'"))\n'
    return source.encode()


def pipeline_bytes(req, closure, out):
    fresh=out/'fresh'
    lines=['set -eu','export LEAN_PATH='+shlex.quote(str(fresh)), 'unset LEAN_SRC_PATH']
    for module in closure['order']:
        artifact=fresh/(module.replace('.','/')+'.olean')
        lines += ['mkdir -p '+shlex.quote(str(artifact.parent)),
                  shlex.join(['lean','-j1','--tstack=131072','--root='+str(ROOT),'-o',str(artifact),str(ROOT/closure['modules'][module]['source'])])]
    lines += [shlex.join(['lean','-j1','--tstack=131072','--root='+str(out),str(out/'Query.lean')])+' > '+shlex.quote(str(out/'query.stdout'))+' 2> '+shlex.quote(str(out/'query.stderr')),
              shlex.join(['lean','-j1','--tstack=131072','--root='+str(out),str(out/'Axioms.lean')])+' > '+shlex.quote(str(out/'axioms.stdout'))+' 2> '+shlex.quote(str(out/'axioms.stderr'))]
    return ('\n'.join(lines)+'\n').encode()


def axiom_query(req):
    # Names are validated simple fully-qualified identifiers.
    return ('import '+req['module']+'\n'+''.join('#print axioms '+x['name']+'\n' for x in req['declarations'])).encode()


tool_inputs = p.resources.tool_inputs


def parse_output(data):
    text=data.decode('utf-8')
    e.require(text.startswith(BEGIN+'\n') and text.endswith('\n'+END+'\n'), 'missing/truncated kernel output frame')
    e.require(text.splitlines().count(BEGIN)==1 and text.splitlines().count(END)==1, 'duplicate kernel output frame')
    value=e.loads(text[len(BEGIN)+1:-len(END)-2])
    e.require(set(value)=={'schema','rows','imports','releaseClosed'} and value['schema']==1 and value['releaseClosed'] is False, 'invalid kernel output schema')
    return value


def validate_expr(tree):
    """Wire-structure checks only: this is not a second Lean type checker."""
    remaining=[100000]
    def natural(n):
        e.require(isinstance(n,str) and re.fullmatch(r'0|[1-9][0-9]*',n), 'invalid structural natural')
    def name(n,depth=0):
        e.require(depth<=512 and isinstance(n,list) and n, 'malformed structural name')
        if n==['anonymous']: return
        e.require(len(n)==3 and n[0] in ('str','num') and isinstance(n[2],str), 'malformed structural name')
        if n[0]=='num': natural(n[2])
        name(n[1],depth+1)
    def level(n,depth=0):
        e.require(depth<=512 and isinstance(n,list) and n, 'malformed universe')
        tag=n[0]
        if tag=='zero': e.require(len(n)==1,'malformed universe'); return
        if tag=='param': e.require(len(n)==2,'malformed universe'); name(n[1]); return
        e.require(tag in ('succ','max','imax') and len(n)==(2 if tag=='succ' else 3),'unresolved/malformed universe')
        for x in n[1:]: level(x,depth+1)
    def expr(n,bound=0,depth=0):
        remaining[0]-=1
        e.require(remaining[0]>=0 and depth<512 and isinstance(n,list) and n, 'truncated/oversized expression')
        tag=n[0]
        if tag=='bvar':
            e.require(len(n)==2,'invalid bound variable'); natural(n[1]); e.require(int(n[1])<bound,'unbound declaration variable')
        elif tag=='sort': e.require(len(n)==2,'invalid sort'); level(n[1])
        elif tag=='const':
            e.require(len(n)==3 and isinstance(n[2],list),'invalid constant'); name(n[1])
            for u in n[2]: level(u)
        elif tag=='app':
            e.require(len(n)==3,'truncated application'); expr(n[1],bound,depth+1); expr(n[2],bound,depth+1)
        elif tag in ('lam','forall'):
            e.require(len(n)==5 and n[2] in ('default','implicit','strictImplicit','instImplicit'),'invalid binder'); name(n[1]); expr(n[3],bound,depth+1); expr(n[4],bound+1,depth+1)
        elif tag=='let':
            e.require(len(n)==6 and type(n[2]) is bool,'invalid let'); name(n[1]); expr(n[3],bound,depth+1); expr(n[4],bound,depth+1); expr(n[5],bound+1,depth+1)
        elif tag=='nat': e.require(len(n)==2,'invalid literal'); natural(n[1])
        elif tag=='string': e.require(len(n)==2 and isinstance(n[1],str),'invalid literal')
        elif tag=='proj': e.require(len(n)==4,'invalid projection'); name(n[1]); natural(n[2]); expr(n[3],bound,depth+1)
        elif tag=='mdata':
            e.require(len(n)==3 and isinstance(n[1],list),'invalid metadata')
            for item in n[1]:
                e.require(isinstance(item,list) and len(item)==2,'invalid metadata entry'); name(item[0]); v=item[1]
                e.require(isinstance(v,list) and len(v)==2 and v[0] in ('string','bool','name','nat','int'),'unsupported metadata')
                if v[0]=='name': name(v[1])
                elif v[0]=='bool': e.require(type(v[1]) is bool,'invalid metadata boolean')
                elif v[0]=='nat': natural(v[1])
                else: e.require(isinstance(v[1],str),'invalid metadata value')
            expr(n[2],bound,depth+1)
        else: raise ValueError('unsupported/unresolved expression node')
    expr(tree)


def check_axiom_text(data, rows):
    found={}
    text=data.decode('utf-8'); position=0
    pattern=re.compile(r"'([^'\n]+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])")
    while position<len(text):
        while position<len(text) and text[position].isspace(): position+=1
        if position==len(text): break
        match=pattern.match(text,position)
        e.require(match is not None and match[1] not in found,'unexpected/duplicate actual axiom output')
        body=match[2]
        atoms=[] if body is None or not body.strip() else [x.strip() for x in body.split(',')]
        e.require(all(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*',x) for x in atoms)
                  and len(atoms)==len(set(atoms)), 'malformed/duplicate printed axiom')
        found[match[1]]=sorted(atoms);position=match.end()
        e.require(position==len(text) or text[position] in '\r\n', 'missing axiom record boundary')
    e.require(found=={row['name']:row['axioms'] for row in rows}, 'actual printed axioms disagree')


def ast_names(node):
    """Constants are exactly Expr.const occurrences; projections are separate."""
    constants=set(); projections=set()
    def name(n):
        if n==['anonymous']: return ''
        e.require(isinstance(n,list) and len(n)==3 and n[0] in ('str','num'), 'malformed structural name')
        parent=name(n[1]); part=n[2]
        e.require(isinstance(part,str), 'malformed structural name component')
        return (parent+'.' if parent else '')+part
    def walk(n):
        if not isinstance(n,list): return
        if n and n[0]=='const': constants.add(name(n[1]))
        if n and n[0]=='proj': projections.add(name(n[1]))
        for child in n: walk(child)
    walk(node)
    return sorted(constants), sorted(projections)


def normalize_output(value, req, out, closure, installed, toolchain_prefix):
    e.require(len(value['rows'])==len(req['declarations']), 'missing/extra kernel declaration')
    rows=[]
    fields={'name','nameAst','module','kind','unsafe','partial','levels','type','value','typeDisplaySupplemental','typeDependencies','valueDependencies','axioms','binderCount','propositionBinders','semanticPremisesDischarged'}
    for raw, expected in zip(value['rows'],req['declarations']):
        e.require(set(raw)==fields,'unexpected/truncated declaration fields')
        e.require(raw['name']==expected['name'] and raw['module']==req['module'] and raw['kind']==expected['kind'], 'wrong kernel declaration identity/module/kind')
        e.require(raw['unsafe'] is False and raw['partial'] is False and raw['semanticPremisesDischarged'] is False, 'unsafe/partial/semantic discharge claim')
        e.require(raw['nameAst']==name_ast(expected['name']), 'wrong structural declaration name')
        validate_expr(raw['type'])
        if raw['value'] is not None: validate_expr(raw['value'])
        e.require(raw['kind'] not in ('theorem','definition','opaque') or raw['value'] is not None,'missing compiled declaration value')
        for key,tree in [('typeDependencies',raw['type']),('valueDependencies',raw['value'])]:
            deps,projections=ast_names(tree)
            e.require(raw[key]==deps, 'forged direct dependency list')
            raw[key.replace('Dependencies','ProjectionDependencies')]=projections
        e.require(isinstance(raw['type'],list) and raw['type'], 'missing exact type')
        e.require(type(raw['binderCount']) is int and raw['binderCount']>=0,'invalid binder count')
        e.require(raw['propositionBinders']==sorted(set(raw['propositionBinders'])) and all(type(i) is int and 0<=i<raw['binderCount'] for i in raw['propositionBinders']), 'invalid hypothesis indices')
        e.require(raw['axioms']==sorted(set(raw['axioms'])), 'duplicate/unsorted axioms')
        raw['typeSha256']=e.digest(canonical(raw['type'])); raw['valueSha256']=e.digest(canonical(raw['value']))
        raw['conditional']=bool(raw['propositionBinders'])
        rows.append(raw)
    imports={}
    for item in value['imports']:
        n=item['module']; path=Path(item['olean']).resolve()
        e.require(n not in imports, 'duplicate loaded module')
        if n.startswith('Solidity.'):
            e.require(n in closure['modules'] and path==(out/'fresh'/(n.replace('.','/')+'.olean')).resolve(), 'stale/unexpected repository olean')
            sha=e.digest(path.read_bytes())
        else:
            if path.is_relative_to('/opt/v17-toolchain'):
                # Map only the exact recorded read-only toolchain alias.
                path=(toolchain_prefix/path.relative_to('/opt/v17-toolchain')).resolve()
            e.require(str(path) in installed, 'unbound installed import')
            sha=installed[str(path)]
        imports[n]={'path':str(path),'sha256':sha}
    e.require(set(closure['modules'])<=imports.keys(), 'missing requested source import closure')
    return {'schema':1,'rows':rows,'imports':imports,'releaseClosed':False,'semanticPremisesDischarged':False}


def name_ast(n):
    value=['anonymous']
    for part in n.split('.'): value=['str',value,part]
    return value


resource_snapshot = p.resource_snapshot
check_headroom = p.check_headroom


def collect(req, out):
    req=request(req); p.ensure_no_unresolved()
    e.require(not out.exists() and out.is_absolute() and out.resolve()==out and not out.is_relative_to(ROOT) and out.is_relative_to(Path('/workspace')), 'new external evidence directory required')
    out.mkdir(parents=True)
    (out/'request.json').write_bytes(canonical(req))
    before=None; closure=None; installed=None; resources=None; free=None
    preflight={'requirements':{'admissionPolicy':p.resources.ADMISSION_POLICY,'memoryCapBytes':p.CAP,'availableRamFloorBytes':p.resources.RESERVE,'requiredEffectiveBytes':p.resources.RESERVE,'diskFreeBytes':p.resources.MIN_FREE_DISK}}
    try:
        disk=os.statvfs(ROOT); free=disk.f_bavail*disk.f_frsize
        preflight['diskFreeBytes']=free
        before=e.snapshot(ROOT); closure=source_closure(req['module']); installed=tool_inputs(before)
        resources=resource_snapshot(); check_headroom(resources)
        e.require(free>=p.resources.MIN_FREE_DISK,'disk guard')
    except (OSError,ValueError,subprocess.SubprocessError) as err:
        observed=getattr(err,'observations',None)
        if observed is not None: preflight['resourceObservations']=observed
        elif resources is not None: preflight['resourceObservations']={'measurements':resources}
        measurements=preflight.get('resourceObservations',{}).get('measurements',{})
        effective=measurements.get('headroomBytes')
        preflight['comparisons']={'effectiveAtLeastAdmissionFloor':effective>=p.resources.RESERVE if type(effective) is int else None,'diskAtLeastRequired':free>=p.resources.MIN_FREE_DISK if type(free) is int else None}
        failure={'schema':1,'admissionPolicy':p.resources.ADMISSION_POLICY,'exit':2,'preflightExit':2,'commandExit':None,'launched':False,'phase':'preflight','request':req,'error':str(err),'preflight':preflight,'before':before,'sourceClosure':closure,'installedInputsSha256':e.digest(canonical(installed)) if installed is not None else None,'releaseClosed':False,'semanticPremisesDischarged':False}
        (out/'record.json').write_text(json.dumps(failure,indent=2)+'\n'); return failure
    e.require(not (out/'fresh').exists(),'fresh compilation directory is not empty')
    (out/'Query.lean').write_bytes(query_bytes(req))
    (out/'Axioms.lean').write_bytes(axiom_query(req)); (out/'pipeline.sh').write_bytes(pipeline_bytes(req,closure,out))
    for tool in e.BUILD_TOOL_NAMES:
        path=out/(tool+'-launcher'); path.write_bytes(p.launcher_bytes(tool)); path.chmod(0o755)
    command=['sh',str(out/'pipeline.sh')]; container='roadmap-v17-'+uuid.uuid4().hex
    argv=p.docker_create_argv(out,before,container,command)
    (out/'docker-argv.json').write_bytes(canonical(argv)); (out/'execution.sh').write_text(p.execution_script(out,command,Path(before['runtime']['lake']['path'])))
    p.UNRESOLVED.write_bytes(canonical({'container':container,'revision':before['revision']}))
    cid=None; proc=None; code=125; command_exit=None; samples=[]; errors=[]; begin=time.monotonic()
    def remaining():
        left=300-(time.monotonic()-begin)
        if left<=0: raise subprocess.TimeoutExpired('kernel extraction deadline',300)
        return min(5,left)
    try:
        cid=p.docker(*argv,timeout=remaining()).stdout.decode().strip()
        with (out/'command.stdout').open('wb') as log:
            env=os.environ.copy()
            for key in ('DOCKER_HOST','DOCKER_CONTEXT','DOCKER_TLS','DOCKER_TLS_VERIFY','DOCKER_CERT_PATH'): env.pop(key,None)
            proc=subprocess.Popen(['docker','--host=unix:///var/run/docker.sock','start','-a',cid],env=env,stdout=log,stderr=subprocess.STDOUT)
            while True:
                state=p.docker('inspect','--format','{{.State.Status}}',cid,timeout=remaining()).stdout.decode().strip()
                if state in ('exited','dead'):
                    command_exit=proc.wait(timeout=remaining()); code=command_exit; break
                if state=='running':
                    try: top=p.docker('top',cid,'-ww','-eo','pid,stat,comm,rss,args',timeout=remaining()).stdout.decode()
                    except subprocess.CalledProcessError:
                        if p.docker('inspect','--format','{{.State.Status}}',cid,timeout=remaining()).stdout.decode().strip()!='running': continue
                        raise
                    samples.append(p.process_sample(top,Path(before['runtime']['lean']['path'])))
                elif state!='created': raise ValueError('unexpected extraction container state')
                remaining(); time.sleep(0.05)
    except (OSError,ValueError,subprocess.SubprocessError) as err:
        errors.append({'phase':'execution','error':str(err),'stderr':str(getattr(err,'stderr',None))})
        code=124 if isinstance(err,subprocess.TimeoutExpired) else 125
    finally:
        elapsed=time.monotonic()-begin
        try: p.docker('rm','-f',container,timeout=5); p.UNRESOLVED.unlink(missing_ok=True)
        except (OSError,subprocess.SubprocessError) as err:
            if p.missing_container(err): p.UNRESOLVED.unlink(missing_ok=True)
            else: errors.append({'phase':'cleanup','error':str(err)}); code=125
        if proc and proc.poll() is None:
            proc.kill()
            try: proc.wait(timeout=2)
            except subprocess.TimeoutExpired: errors.append({'phase':'attach cleanup','error':'unreaped client'}); code=125
    try: after=e.snapshot(ROOT)
    except (OSError,ValueError,subprocess.SubprocessError) as err: after={'error':str(err)}; code=125
    try: installed_after=tool_inputs(before)
    except (OSError,ValueError,subprocess.SubprocessError) as err:
        installed_after={'error':str(err)}; errors.append({'phase':'installed inputs after','error':str(err)}); code=125
    result=None
    if code==0:
        try:
            result=normalize_output(parse_output((out/'query.stdout').read_bytes()),req,out,closure,installed,Path(before['runtime']['lean']['path']).parent.parent)
            check_axiom_text((out/'axioms.stdout').read_bytes(),result['rows'])
        except (ValueError,KeyError,TypeError,OSError,RecursionError) as err: errors.append({'phase':'output validation','error':str(err)}); code=125
    record={'schema':1,'directory':str(out),'before':before,'after':after,'request':req,'sourceClosure':closure,
            'templateSha256':e.digest(TEMPLATE.read_bytes()),'querySha256':e.digest((out/'Query.lean').read_bytes()),
            'pipelineSha256':e.digest((out/'pipeline.sh').read_bytes()),'dockerArgvSha256':e.digest((out/'docker-argv.json').read_bytes()),
            **resources,'admissionPolicy':p.resources.ADMISSION_POLICY,'diskFreeBytes':free,'commandExit':command_exit,'installedBefore':installed,'installedAfter':installed_after,'exit':code,'elapsedSeconds':elapsed,'containerName':container,
            'sampleFormat':p.SAMPLE_FORMAT,'freshStartAbsent':True,'samples':samples,'errors':errors,'result':result,'releaseClosed':False,'semanticPremisesDischarged':False}
    record['attachments']={str(path.relative_to(out)):e.digest(path.read_bytes()) for path in out.rglob('*') if path.is_file()}
    if record['exit']==0:
        try: validate_record(record,before)
        except (ValueError,KeyError,TypeError,OSError,RecursionError,subprocess.SubprocessError) as err:
            record['errors'].append({'phase':'collection integrity','error':str(err)}); record['exit']=125
    (out/'record.json').write_text(json.dumps(record,indent=2)+'\n')
    return record


def check_runtime(r, current, out):
    p.resources.check_record_resources(r)
    e.require(r['freshStartAbsent'] is True and r['sampleFormat']==p.SAMPLE_FORMAT,'missing fresh execution/runtime evidence')
    e.require(0<r['elapsedSeconds']<=305,'execution budget exceeded')
    mandatory={'request.json','Query.lean','Axioms.lean','pipeline.sh','docker-argv.json','execution.sh','command.stdout','query.stdout','query.stderr','axioms.stdout','axioms.stderr','memoryMax','swapMax','memoryPeak','realLeanSha256','lakeSha256','leanVersion','lakeVersion','leanNumThreads'}
    mandatory.update(tool+'-launcher' for tool in e.BUILD_TOOL_NAMES)
    mandatory.update('tool-'+tool for tool in e.BUILD_TOOL_NAMES)
    mandatory.update('entrypoint-'+tool for tool in e.BUILD_TOOL_NAMES)
    mandatory.update('fresh/'+n.replace('.','/')+'.olean' for n in r['sourceClosure']['order'])
    e.require(mandatory<=r['attachments'].keys(),'missing mandatory extraction attachment')
    expected={'request.json':canonical(r['request']),'Query.lean':query_bytes(r['request']),'Axioms.lean':axiom_query(r['request']),
              'pipeline.sh':pipeline_bytes(r['request'],r['sourceClosure'],out),
              'execution.sh':p.execution_script(out,['sh',str(out/'pipeline.sh')],Path(current['runtime']['lake']['path'])).encode()}
    for name,data in expected.items(): e.require((out/name).read_bytes()==data,'changed extraction input: '+name)
    read=lambda name:(out/name).read_text().strip()
    e.require(int(read('memoryMax'))==p.CAP and int(read('swapMax'))==0 and 0<int(read('memoryPeak'))<=p.CAP,'wrong extraction cap/peak/swap')
    e.require(read('leanVersion')==current['runtime']['lean']['version'] and read('lakeVersion')==current['runtime']['lake']['version'] and read('leanNumThreads')=='1','wrong observed extraction toolchain')
    for tool in e.BUILD_TOOL_NAMES:
        e.require((out/(tool+'-launcher')).read_bytes()==p.launcher_bytes(tool),'changed extraction serializer')
        e.require(read('tool-'+tool).split()[0]==current['buildTools'][tool]['sha256'] and read('entrypoint-'+tool).split()[0]==e.digest(p.launcher_bytes(tool)),'wrong observed extraction entrypoint')
    e.require(read('realLeanSha256').split()[0]==current['runtime']['lean']['sha256'] and read('lakeSha256').split()[0]==current['runtime']['lake']['sha256'],'wrong observed binary hashes')
    e.require(r['samples'] and all(s['leanWorkers']<=1 and s['unclassifiedLeanWorkers']==0 and not s['unknownLeanProcesses'] for s in r['samples']),'unverified extraction process samples')


def validate_record(r, current):
    e.require(r['commandExit']==0 and type(r['commandExit']) is int,'nonzero command exit')
    e.require(r['schema']==1 and r['exit']==0 and type(r['exit']) is int, 'missing/nonzero extraction gate')
    e.require(r['before']==r['after']==current, 'stale source/revision/toolchain extraction')
    e.require(r['installedBefore']==r['installedAfter']==tool_inputs(current), 'changed installed import inputs')
    req=request(r['request']); out=Path(r['directory'])
    e.require(out.is_absolute() and out.resolve()==out and out.is_relative_to(Path('/workspace')) and not out.is_relative_to(ROOT),'invalid evidence directory')
    e.require(re.fullmatch(r'roadmap-v17-[0-9a-f]{32}',r['containerName']) is not None,'invalid container identity')
    e.require(r['sourceClosure']==source_closure(req['module']), 'changed source import closure')
    e.require(r['templateSha256']==e.digest(TEMPLATE.read_bytes()) and r['querySha256']==e.digest(query_bytes(req)), 'changed extraction query/template')
    e.require(r['pipelineSha256']==e.digest(pipeline_bytes(req,r['sourceClosure'],out)), 'changed extraction pipeline')
    for name,sha in r['attachments'].items(): p.read_bound(out,name,sha)
    e.require(e.loads((out/'docker-argv.json').read_bytes())==p.docker_create_argv(out,current,r['containerName'],['sh',str(out/'pipeline.sh')]), 'changed extraction Docker configuration')
    check_runtime(r,current,out)
    parsed=normalize_output(parse_output((out/'query.stdout').read_bytes()),req,out,r['sourceClosure'],r['installedBefore'],Path(current['runtime']['lean']['path']).parent.parent)
    check_axiom_text((out/'axioms.stdout').read_bytes(),parsed['rows'])
    e.require(parsed==r['result'], 'forged extracted type/axiom/premise result')
    e.require(r['semanticPremisesDischarged'] is False and r['releaseClosed'] is False, 'unearned semantic closure')
    return req


def match_claims(claims, live):
    e.require(set(claims)=={'schema','declarations','semanticPremisesDischarged'} and claims['schema']==1 and claims['semanticPremisesDischarged'] is False, 'semantic discharge is not provided by extraction')
    e.require(len(claims['declarations'])==len(live['rows']), 'missing/extra declaration claims')
    fields={'name','module','kind','typeSha256','valueSha256','typeDependencies','valueDependencies','axioms','binderCount','propositionBinders'}
    for claim,row in zip(claims['declarations'],live['rows']):
        e.require(set(claim)==fields and claim=={key:row[key] for key in fields}, 'forged declaration/type/axiom/premise claim')
    return {'declarationEvidenceMatched':True,'semanticPremisesDischarged':False,'releaseClosed':False}


def match_replay(old, replay):
    e.require(replay['before']==replay['after']==old['before']==old['after'],'replay revision/source/tool/config differs')
    e.require(replay['installedBefore']==replay['installedAfter']==old['installedBefore']==old['installedAfter'],'replay installed inputs differ')
    e.require(old['result']['rows']==replay['result']['rows'],'live declaration replay differs')


def main():
    a=argparse.ArgumentParser(description=__doc__)
    a.add_argument('mode',choices=['collect','verify']); a.add_argument('--request',type=Path); a.add_argument('--record',type=Path); a.add_argument('--claims',type=Path); a.add_argument('--out',type=Path,required=True)
    args=a.parse_args()
    with open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a+') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        if args.mode=='collect':
            e.require(args.request is not None,'--request required'); r=collect(e.load(args.request),args.out)
            print(json.dumps({'exit':r['exit'],'releaseClosed':False,'record':str(args.out/'record.json')})); return r['exit']
        e.require(args.record is not None and args.claims is not None,'--record/--claims required')
        old=e.load(args.record); req=validate_record(old,e.snapshot(ROOT))
        replay=collect(req,args.out)
        e.require(replay['exit']==0,'live replay failed')
        validate_record(replay,e.snapshot(ROOT))
        # Absolute fresh import paths differ between runs; declarations must match exactly.
        match_replay(old,replay)
        result=match_claims(e.load(args.claims),replay['result']); print(json.dumps(result)); return 0


if __name__=='__main__':
    try: raise SystemExit(main())
    except (ValueError,KeyError,TypeError,OSError,RecursionError,subprocess.SubprocessError) as err:
        print(json.dumps({'error':str(err),'releaseClosed':False})); raise SystemExit(2)
