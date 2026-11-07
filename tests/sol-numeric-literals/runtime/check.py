#!/usr/bin/env python3
"""Run one owned-container command, with aggregate cap and H1 reserve checks."""
import fcntl,hashlib,json,os,pathlib,subprocess,sys,time
root=pathlib.Path('/workspace/solidity-lean'); evidence=pathlib.Path('/workspace/sol-numeric-literals-gate-output')
evidence.mkdir(exist_ok=True)
name='sol-nl-proof-worker'
label=sys.argv[1]; command=sys.argv[2:]
if not command: raise SystemExit('usage: check.py LABEL COMMAND...')
lock=open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a')
fcntl.flock(lock,fcntl.LOCK_EX)
def reserve():
    info=dict(line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines())
    avail=int(info['MemAvailable'].split()[0])*1024
    current=int(pathlib.Path('/sys/fs/cgroup/memory.current').read_text())
    cap=int(pathlib.Path('/sys/fs/cgroup/memory.max').read_text())
    return min(avail,cap-current)
assert reserve()>=4*1024**3, 'H1 reserve unavailable'
container_id=subprocess.check_output(['docker','inspect','--format','{{.Id}}',name],text=True).strip()
pre='set -eu; test "$(cat /sys/fs/cgroup/memory.max)" = 12884901888; test "$(cat /sys/fs/cgroup/memory.swap.max)" = 0; source /workspace/.setup/activate.sh; export LEAN_NUM_THREADS=1; export PATH=/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:/workspace/solidity-lean/tests/sol-numeric-literals/runtime/bin:$PATH; exec "$@"'
source_hashes={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((root/'Solidity/Frontend/NumericLiteralProofs').rglob('*.lean'))}
def dependency_hashes():
    files=list((root/'Solidity/Backend/PrimitivePackets/Constants').rglob('*.lean'))+[root/'tests/primitive-packets-1105/Constants/Audit.lean']
    return {str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)}
dependency_sources=dependency_hashes()
log=evidence/(label+'.log'); start=time.monotonic(); minimum=reserve(); stopped=False
with log.open('w') as out:
    process=subprocess.Popen(['docker','exec',container_id,'bash','-c',pre,'bash',*command],stdout=out,stderr=subprocess.STDOUT)
    while process.poll() is None:
        minimum=min(minimum,reserve())
        if minimum<4*1024**3:
            subprocess.run(['docker','stop',container_id],stdout=subprocess.DEVNULL); stopped=True; break
        time.sleep(.5)
    process_code=process.wait()
    code=process_code if not stopped or process_code!=0 else 125
peak=subprocess.run(['docker','exec',container_id,'cat','/sys/fs/cgroup/memory.peak'],text=True,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL).stdout.strip()
after_hashes={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((root/'Solidity/Frontend/NumericLiteralProofs').rglob('*.lean'))}
assert source_hashes==after_hashes, "proof source changed during check"
assert dependency_sources==dependency_hashes(), "Constants/audit source changed during check"
row=dict(proof_sources=source_hashes,dependency_sources=dependency_sources,container_id=container_id,command=command,exit=code,process_exit=process_code,seconds=round(time.monotonic()-start,3),container_memory_peak_bytes=int(peak) if peak else None,minimum_parent_headroom_bytes=minimum,resource_stop=stopped,log=str(log),container=name,limits=dict(memory_max=12884901888,memory_swap_max=0,lean_num_threads=1))
(evidence/(label+'.json')).write_text(json.dumps(row,indent=2)+'\n')
summary={k:v for k,v in row.items() if k!="proof_sources"};summary["proof_module_count"]=len(source_hashes)
print(json.dumps(summary));print(log.read_text()[-10000:]);sys.exit(code)
