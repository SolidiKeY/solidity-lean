#!/usr/bin/env python3
"""Committed V17 orchestration of the published differential runner; no proof closure."""
import argparse
import fcntl
import importlib.util
import json
import os
from pathlib import Path
import subprocess

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('differential_provenance',ROOT/'scripts/roadmap-v17-provenance.py')
p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p);e=p.e
GATE='operational-published-generated-differential'
NODE=Path('/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin/node')
COMPILER=ROOT/'.lake/soljson/soljson-v0.8.38+commit.1835d247.js'
COMPILER_SHA='6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390'
LIBRARIES=(('/usr/bin/git','/opt/v17-git/git'),
('/usr/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2','/opt/v17-git/loader'),
('/lib/x86_64-linux-gnu/libc.so.6','/opt/v17-git/lib/libc.so.6'),
('/lib/x86_64-linux-gnu/libpcre2-8.so.0','/opt/v17-git/lib/libpcre2-8.so.0'),
('/lib/x86_64-linux-gnu/libz.so.1','/opt/v17-git/lib/libz.so.1'))
FLAGS={'semanticPremisesDischarged':False,'releaseClosed':False,'kernelValidated':False}


def save(out,name,value):
    (out/name).write_text(json.dumps(value,indent=2)+'\n')


def final_exit(result):
    for key in ('collectorExit','verificationExit','postInputExit'):
        value=result[key]
        e.require(value is None or type(value) is int and 0<=value<=255,'invalid phase exit')
        if value is not None and value!=0:return value
    raw=result.get('rawCommandExit')
    e.require(raw is None or type(raw) is int and 0<=raw<=255,'invalid raw command exit')
    if raw is not None and raw!=0:return raw
    return 0 if all(result[key]==0 for key in ('collectorExit','verificationExit','postInputExit')) and raw==0 and result['outputsVerified'] is True else 2


def input_files():
    runtime=ROOT/'scripts/evm-reference'
    files={str(path.relative_to(ROOT)):p.resources.hash_file(path)
           for path in sorted(runtime.rglob('*')) if path.is_file()}
    for source,_ in LIBRARIES:files[source]=p.resources.hash_file(Path(source))
    for path in (NODE,COMPILER,ROOT/'.lake/build/bin/solcases',Path(__file__),
                 ROOT/'scripts/roadmap-v17-runtime.mjs',ROOT/'scripts/roadmap-v17-compare.mjs',
                 Path(p.__file__),Path(e.__file__),Path(p.resources.__file__)):
        files[str(path)]=p.resources.hash_file(path)
    e.require(COMPILER.is_file() and not COMPILER.is_symlink()
              and files[str(COMPILER)]==COMPILER_SHA and COMPILER.stat().st_size==10798266,
              'missing/wrong approved compiler cache')
    return files


def same_inputs(before,after):
    e.require(before==after,'changed execution source/tool/dependency inputs')


def check_native_identity(native,current,files):
    e.require(native['revision']==current['revision'] and native['tree']==current['sourceTree']
              and native['leanVersion']==current['runtime']['lean']['version']
              and native['lakeVersion']==current['runtime']['lake']['version'],
              'native identity differs from exact outer snapshot')
    e.require(native['compiler']=={'path':str(COMPILER),'bytes':10798266,'sha256':COMPILER_SHA,'version':'0.8.38+commit.1835d247.Emscripten.clang'},'wrong native compiler')
    e.require(native['node']['path']==str(NODE.resolve()) and native['node']['sha256']==files[str(NODE)],'wrong native Node executable')


def git_wrapper():
    return ('#!/bin/sh\nset -e\n'
      'version=$(/opt/v17-git/loader --library-path /opt/v17-git/lib /opt/v17-git/git --version)\n'
      '[ "$version" = "git version 2.47.3" ]\n'
      'printf "V17_GIT_RUNTIME %s\\n" "$version" >&2\n'
      'exec /opt/v17-git/loader --library-path /opt/v17-git/lib /opt/v17-git/git "$@"\n').encode()


def mount_runtime(argv,wrapper):
    argv=list(argv);at=argv.index(p.IMAGE)
    extra=['--mount','type=bind,src='+str(NODE)+',dst='+str(NODE)+',readonly']
    for source,destination in ((str(wrapper),'/usr/local/bin/git'),)+LIBRARIES:
        extra+=['--mount','type=bind,src='+source+',dst='+destination+',readonly']
    extra+=['-e','GIT_CONFIG_COUNT=1','-e','GIT_CONFIG_KEY_0=safe.directory',
            '-e','GIT_CONFIG_VALUE_0='+str(ROOT)]
    argv[at:at]=extra
    return argv


def configure(wrapper):
    """Only route the owned operational gate; preserve every original cap/check."""
    old_command,old_docker=p.gate_command,p.docker_create_argv
    e.require(GATE not in p.TARGETS,'duplicate operational gate')
    p.TARGETS[GATE]=([],[])
    p.gate_command=lambda gate,out:([str(NODE),str(ROOT/'scripts/roadmap-v17-runtime.mjs'),
                                  'run',str(out/'result')] if gate==GATE else old_command(gate,out))
    p.docker_create_argv=lambda out,current,name,command:mount_runtime(old_docker(out,current,name,command),wrapper)
    return old_command,old_docker


def verify_native(out,current,files):
    directory=out/'execution';record=e.load(directory/'provenance.json')
    e.require(p.validate(record,directory,current,GATE),'nonpassing capped collector receipt')
    log=p.read_bound(directory,record['log'],record['logSha256'])
    command=[str(NODE),'--input-type=module','-e',
      "import {verifyOutputs,reportBinding} from './scripts/roadmap-v17-runtime.mjs';import {readFileSync} from 'node:fs';const root=process.argv[1];const manifest=verifyOutputs(readFileSync(0,'utf8'),root);const inputs=JSON.parse(readFileSync(root+'/inputs-before.json'));reportBinding(JSON.parse(readFileSync(root+'/report.json')),inputs);console.log(JSON.stringify(manifest));",str(directory/'result')]
    raw=subprocess.check_output(command,input=log,cwd=ROOT,timeout=60)
    e.require(len(raw)<=16*1024*1024,'oversized verifier output')
    manifest=e.loads(raw)
    check_native_identity(e.load(directory/'result/inputs-before.json'),current,files)
    return manifest


def retain_receipt(out,result):
    """Recover reported raw phases even after transport/collection exceptions.

    This is byte accounting only; validation remains a separate result field.
    """
    path=out/'execution/provenance.json'
    if not path.exists():return
    e.require(path.is_file() and not path.is_symlink() and path.stat().st_size<=16*1024*1024,
              'invalid/oversized receipt')
    with path.open('rb') as stream:raw=stream.read(16*1024*1024+1)
    e.require(len(raw)<=16*1024*1024,'oversized receipt')
    record=e.loads(raw);e.require(isinstance(record,dict),'nonobject receipt')
    e.require(type(record.get('schema')) is int and record['schema']==3,'unsupported recovered receipt')
    command=record.get('commandExit')
    e.require(command is None or type(command) is int and 0<=command<=255,'invalid raw command exit')
    e.require(type(record.get('exit')) is int and 0<=record['exit']<=255,'invalid collector receipt exit')
    result['rawCommandExit']=command;result['reportedReceiptExit']=record['exit']
    result['provenanceSha256']=e.digest(raw)


def collect(out):
    out=Path(out)
    e.require(out.is_absolute() and out.resolve()==out and out.is_relative_to('/workspace/scratch')
              and not out.exists(),'NEW canonical external evidence directory required')
    out.mkdir()
    result={'schema':1,'collectorExit':None,'rawCommandExit':None,'verificationExit':0,
            'postInputExit':0,'outputsVerified':False,'receiptValidated':False,'phaseErrors':[],**FLAGS}
    current=None;before=None;wrapper=None;old=None
    try:
        p.ensure_no_unresolved()
        current=e.snapshot(ROOT)  # Requires the committed clean consumer.
        for name in ('scripts/roadmap-v17-differential.py','scripts/roadmap-v17-runtime.mjs'):
            e.require((ROOT/name).read_bytes()==subprocess.check_output(['git','show',current['revision']+':'+name],cwd=ROOT,timeout=60),
                      'uncommitted execution consumer')
        before=input_files()
        measurements=p.resource_snapshot();result['preflightResources']=measurements;p.check_headroom(measurements)
        stat=os.statvfs(ROOT);disk=stat.f_bavail*stat.f_frsize
        e.require(disk>=p.resources.MIN_FREE_DISK,'disk admission refused')
        wrapper=out/'git-wrapper';wrapper.write_bytes(git_wrapper());wrapper.chmod(0o755)
        request={'schema':1,'snapshot':current,'files':before,'driverSha256':p.resources.hash_file(Path(__file__)),
                 'wrapperSha256':p.resources.hash_file(wrapper),'budgets':p.BUDGET,
                 'admissionPolicy':p.resources.ADMISSION_POLICY,'resources':measurements,'diskFreeBytes':disk,**FLAGS}
        save(out,'request.json',request)
        old=configure(wrapper)
        from types import SimpleNamespace
        result['collectorExit']=p.collect(SimpleNamespace(gate=GATE,out=out/'execution'))
        receipt=e.load(out/'execution/provenance.json');result['rawCommandExit']=receipt['commandExit']
        result['provenanceSha256']=p.resources.hash_file(out/'execution/provenance.json')
        if result['collectorExit']==0:
            manifest=verify_native(out,current,before);save(out,'verified-output-manifest.json',manifest)
            result['outputsVerified']=True;result['receiptValidated']=True
    except (ValueError,KeyError,TypeError,OSError,subprocess.SubprocessError) as error:
        result['verificationExit']=2
        result['phaseErrors'].append({'phase':'collection-or-verification','error':str(error),
                                     'observations':getattr(error,'observations',None)})
    finally:
        try:
            retain_receipt(out,result)
        except (ValueError,KeyError,TypeError,OSError) as error:
            result['verificationExit']=2;result['phaseErrors'].append({'phase':'receipt-recovery','error':str(error)})
        try:
            if before is not None:same_inputs(before,input_files())
            if current is not None:e.require(e.snapshot(ROOT)==current,'source changed during execution')
            if wrapper is not None:e.require(wrapper.read_bytes()==git_wrapper(),'Git wrapper changed')
        except (ValueError,KeyError,TypeError,OSError,subprocess.SubprocessError) as error:
            result['postInputExit']=125;result['phaseErrors'].append({'phase':'post-inputs','error':str(error)})
        finally:
            if old is not None:
                p.gate_command,p.docker_create_argv=old;p.TARGETS.pop(GATE,None)
        result['exit']=final_exit(result);save(out,'outcome.json',result)
    return result


def main():
    cli=argparse.ArgumentParser(description=__doc__);cli.add_argument('--out',type=Path,required=True);args=cli.parse_args()
    with open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a+') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        result=collect(args.out)
    print(json.dumps(result,indent=2));return result['exit']
if __name__=='__main__':raise SystemExit(main())
