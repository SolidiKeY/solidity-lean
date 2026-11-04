#!/usr/bin/env python3
"""Own-container UID-appropriate procfs transport. JSON consistency is NOT execution proof.
No capabilities, user switches, host-proc mounts or relaxed v1 cgroup rules.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import sys
import time
import types

MAX_MESSAGE=16*1024*1024
FLAGS=dict(kernelValidated=False,semanticPremisesDischarged=False,releaseClosed=False)

def require(ok,message):
    if not ok:raise ValueError(message)

def canonical(value):return json.dumps(value,sort_keys=True,separators=(',',':')).encode()
def digest(value):return hashlib.sha256(value).hexdigest()

def load_observer(expected_sha):
    path=Path(__file__).with_name('roadmap-v17-process-identity.py');data=path.read_bytes()
    require(re.fullmatch('[0-9a-f]{64}',expected_sha) and digest(data)==expected_sha,'observer source mismatch')
    module=types.ModuleType('v17_transport_observer');module.__file__=str(path)
    exec(compile(data,str(path),'exec'),module.__dict__)
    return module

def nspids(raw,pid):
    require(isinstance(raw,str) and len(raw)<=16384,'invalid status observation')
    lines=[x for x in raw.splitlines() if x.startswith('NSpid:')]
    require(len(lines)==1,'missing/duplicate PID namespace mapping')
    words=lines[0].split()[1:]
    require(words and len(words)<=32 and all(re.fullmatch('[1-9][0-9]*',x) for x in words),'malformed PID mapping')
    values=[int(x) for x in words];require(values[0]==pid,'wrong outer PID mapping');return values

def public_process(m,pid):
    require(m.integer(pid,True),'invalid public PID')
    root=os.open('/proc',os.O_RDONLY|os.O_DIRECTORY|os.O_CLOEXEC|os.O_NOFOLLOW);directory=None
    try:
        directory=os.open(str(pid),os.O_RDONLY|os.O_DIRECTORY|os.O_CLOEXEC|os.O_NOFOLLOW,dir_fd=root)
        observer_first=namespace(os.getpid(),'time');time_first=namespace(pid,'time')
        begin=time.clock_gettime_ns(time.CLOCK_BOOTTIME)
        first=m.read_at(directory,'stat');group_first=m.read_at(directory,'cgroup');status_first=m.read_at(directory,'status')
        status_last=m.read_at(directory,'status');group_last=m.read_at(directory,'cgroup');last=m.read_at(directory,'stat')
        end=time.clock_gettime_ns(time.CLOCK_BOOTTIME)
        time_last=namespace(pid,'time');observer_last=namespace(os.getpid(),'time')
        out=dict(pid=pid,observerTimeNamespaceBefore=observer_first,observerTimeNamespaceAfter=observer_last,beforeTimeNamespace=time_first,afterTimeNamespace=time_last,beginBootNs=begin,endBootNs=end,beforeStat=first,afterStat=last,beforeCgroup=group_first,afterCgroup=group_last,beforeStatus=status_first,afterStatus=status_last)
        stable_public(m,out);return out
    finally:
        if directory is not None:os.close(directory)
        os.close(root)

def stable_public(m,value):
    require(isinstance(value,dict),'missing public observation');pid=value['pid']
    require(m.integer(value['beginBootNs']) and m.integer(value['endBootNs']) and value['endBootNs']>=value['beginBootNs'],'invalid public observation clock')
    a=m.parse_stat(value['beforeStat'],pid);b=m.parse_stat(value['afterStat'],pid)
    require(a['starttime']==b['starttime'] and a['state'] not in ('Z','X','x') and b['state'] not in ('Z','X','x'),'public PID changed/exited')
    group=m.parse_cgroup(value['beforeCgroup']);require(group==m.parse_cgroup(value['afterCgroup']),'public cgroup changed')
    require(isinstance(value['beforeTimeNamespace'],str) and re.fullmatch(r'time:\[[0-9]+\]',value['beforeTimeNamespace']) and value['beforeTimeNamespace']==value['afterTimeNamespace']==value['observerTimeNamespaceBefore']==value['observerTimeNamespaceAfter'],'changed/missing time namespace')
    ids=nspids(value['beforeStatus'],pid);require(ids==nspids(value['afterStatus'],pid),'PID namespace mapping changed')
    return dict(pid=pid,starttime=a['starttime'],cgroup=group,nspids=ids,timeNamespace=value['beforeTimeNamespace'])

def request_valid(request):
    require(isinstance(request,dict) and set(request)=={'schema','nonce','containerId','observerSha256','transportSha256','pids','binding'},'malformed request')
    require(type(request['schema']) is int and request['schema']==1,'unsupported request schema')
    require(isinstance(request['nonce'],str) and re.fullmatch('[0-9a-f]{32}',request['nonce']),'invalid request nonce')
    for key in ['containerId','observerSha256','transportSha256']:
        require(isinstance(request[key],str) and re.fullmatch('[0-9a-f]{64}',request[key]),'invalid request identity')
    pids=request['pids'];require(isinstance(pids,list) and 1<=len(pids)<=128 and all(type(x) is int and x>0 for x in pids) and len(set(pids))==len(pids),'invalid/duplicate requested PIDs')
    binding=request['binding'];require(isinstance(binding,dict) and set(binding)=={'consumerHead','sourceToolchainKey'},'missing revision/input binding')
    require(isinstance(binding['consumerHead'],str) and re.fullmatch('[0-9a-f]{40}',binding['consumerHead']) and isinstance(binding['sourceToolchainKey'],str) and re.fullmatch('[0-9a-f]{64}',binding['sourceToolchainKey']),'invalid revision/input binding')

def namespace(pid,name):
    value=os.readlink('/proc/'+str(pid)+'/ns/'+name)
    require(re.fullmatch(name+r':\[[0-9]+\]',value),'unsupported namespace identity');return value

def inside_observations(request):
    request_valid(request);require(digest(Path(__file__).read_bytes())==request['transportSha256'],'transport source mismatch')
    m=load_observer(request['observerSha256'])
    init_before=m.observe_process(1);pid_ns=namespace(1,'pid');cg_ns=namespace(1,'cgroup');time_ns=namespace(1,'time')
    require(namespace(os.getpid(),'pid')==pid_ns and namespace(os.getpid(),'cgroup')==cg_ns and namespace(os.getpid(),'time')==time_ns,'observer outside init namespaces')
    caps={}
    root=os.open('/sys/fs/cgroup',os.O_RDONLY|os.O_DIRECTORY|os.O_CLOEXEC|os.O_NOFOLLOW)
    try:
        for name in ['memory.max','memory.swap.max','cpu.max']:caps[name]=m.read_at(root,name).strip()
    finally:os.close(root)
    rows=[]
    for pid in request['pids']:
        row=dict(pid=pid)
        try:
            before=dict(pid=namespace(pid,'pid'),cgroup=namespace(pid,'cgroup'),time=namespace(pid,'time'))
            row['observation']=m.observe_process(pid)
            after=dict(pid=namespace(pid,'pid'),cgroup=namespace(pid,'cgroup'),time=namespace(pid,'time'))
            row.update(namespacesBefore=before,namespacesAfter=after,outcome='observed')
        except (OSError,ValueError,KeyError,TypeError) as error:row.update(outcome='unavailable',errorType=type(error).__name__,error=str(error))
        rows.append(row)
    return dict(schema=1,requestSha256=digest(canonical(request)),nonce=request['nonce'],containerId=request['containerId'],observerSha256=request['observerSha256'],transportSha256=request['transportSha256'],binding=request['binding'],actorUid=os.getuid(),initBefore=init_before,initAfter=m.observe_process(1),pidNamespace=pid_ns,cgroupNamespace=cg_ns,timeNamespace=time_ns,initTimeNamespaceAfter=namespace(1,'time'),observerTimeNamespaceAfter=namespace(os.getpid(),'time'),observedCaps=caps,rows=rows,**FLAGS)

def validate_reply(m,request,reply,inspection,public_init_before,public_init_after,public_workers_before,public_workers_after):
    """Consistency checks only; caller must bind actual live own-CID exec transport."""
    request_valid(request);require(isinstance(reply,dict) and type(reply.get('schema')) is int and reply['schema']==1,'unsupported reply')
    for key in ['nonce','containerId','observerSha256','transportSha256','binding']:require(reply.get(key)==request[key],'reply/request identity mismatch')
    require(reply.get('requestSha256')==digest(canonical(request)) and all(reply.get(k) is False for k in FLAGS),'replayed/promoted reply')
    require(inspection['Id']==request['containerId'] and re.fullmatch('/roadmap-v17-[0-9a-f]{32}',inspection['Name']),'wrong live task')
    state=inspection['State'];cfg=inspection['HostConfig'];require(state['Running'] is True and m.integer(state['Pid'],True),'task not live')
    require(all(type(cfg[k]) is int for k in ['Memory','MemorySwap','NanoCpus']) and cfg['Memory']==cfg['MemorySwap']==12884901888 and cfg['NanoCpus']==10**9 and cfg['NetworkMode']=='none','wrong task policy')
    first=stable_public(m,public_init_before);last=stable_public(m,public_init_after)
    require(first==last and first['pid']==state['Pid'] and len(first['nspids'])>=2 and first['nspids'][-1]==1,'wrong/stale host init mapping')
    parts=Path(first['cgroup']).parts;require(request['containerId'] in parts or 'docker-'+request['containerId']+'.scope' in parts,'host cgroup not bound to task')
    a=m.stable_observation(reply['initBefore']);b=m.stable_observation(reply['initAfter'])
    require(a==b and a['pid']==1 and a['starttime']==first['starttime'] and a['cgroup']=='/','wrong inner init/cgroup/time namespace')
    require(m.integer(reply['actorUid']) and re.fullmatch(r'pid:\[[0-9]+\]',reply['pidNamespace']) and re.fullmatch(r'cgroup:\[[0-9]+\]',reply['cgroupNamespace']),'malformed observer namespace')
    require(reply['timeNamespace']==reply['initTimeNamespaceAfter']==reply['observerTimeNamespaceAfter']==first['timeNamespace'],'unsupported/changed shared clock namespace')
    require(reply['observedCaps']=={'memory.max':'12884901888','memory.swap.max':'0','cpu.max':'100000 100000'},'missing/malformed/unlimited kernel resource observations')
    require(public_init_before['endBootNs']<=reply['initBefore']['beginBootNs'] and reply['initBefore']['endBootNs']<=reply['initAfter']['beginBootNs'] and reply['initAfter']['endBootNs']<=public_init_after['beginBootNs'],'unbracketed init observation')
    rows=reply['rows'];require(isinstance(rows,list) and all(isinstance(x,dict) and type(x.get('pid')) is int for x in rows) and [x['pid'] for x in rows]==request['pids'],'omitted/duplicate/reordered PID reply')
    bound=[]
    for row in rows:
        require(row['outcome']=='observed','missing worker identity')
        outer_before=public_workers_before[row['pid']];outer_after=public_workers_after[row['pid']]
        host_a=stable_public(m,outer_before);host_b=stable_public(m,outer_after)
        require(host_a==host_b and host_a['cgroup']==first['cgroup'] and host_a['timeNamespace']==first['timeNamespace'] and len(host_a['nspids'])==len(first['nspids']) and host_a['nspids'][-1]==row['pid'],'wrong/reused outer worker mapping')
        inner=m.stable_observation(row['observation']);require(inner['pid']==row['pid'] and inner['starttime']==host_a['starttime'] and inner['cgroup']=='/','inner/outer worker mismatch')
        require(reply['initBefore']['endBootNs']<=row['observation']['beginBootNs'] and row['observation']['endBootNs']<=reply['initAfter']['beginBootNs'] and outer_before['endBootNs']<=row['observation']['beginBootNs'] and row['observation']['endBootNs']<=outer_after['beginBootNs'],'unbracketed worker observation')
        wanted=dict(pid=reply['pidNamespace'],cgroup=reply['cgroupNamespace'],time=reply['timeNamespace'])
        require(row['namespacesBefore']==row['namespacesAfter']==wanted,'worker namespace changed/mismatched')
        bound.append(dict(hostPid=host_a['pid'],innerPid=inner['pid'],starttime=inner['starttime'],executableSha256=row['observation']['executableSha256']))
    return dict(consistencyOnly=True,bindings=bound,liveTransportAuthenticated=False,**FLAGS)

def unique_object(pairs):
    result={}
    for key,value in pairs:
        require(key not in result,'duplicate JSON field');result[key]=value
    return result

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--inside',action='store_true',required=True);parser.parse_args()
    resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(60,)*2)
    raw=sys.stdin.buffer.read(65537);require(len(raw)<=65536,'oversized request')
    request=json.loads(raw,object_pairs_hook=unique_object);reply=inside_observations(request);encoded=canonical(reply);require(len(encoded)<=MAX_MESSAGE,'oversized reply');sys.stdout.buffer.write(encoded+b'\n')
if __name__=='__main__':main()
