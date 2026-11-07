#!/usr/bin/env python3
"""Serial bounded validation of the registered packet against published master."""
import hashlib,json,pathlib,subprocess,time,os
here=pathlib.Path(__file__).resolve().parent
repo=here.parents[3]
out=pathlib.Path(os.environ.get('VALIDATE_OUTPUT','/workspace/lane-evidence/monetary-bounds/registration'));out.mkdir(parents=True,exist_ok=True)
config=here/'serial.toml'
commands=[
 ('runtime','lean --version; /workspace/.setup/tools/lean-4.24.0-linux/bin/lake --version; cat /sys/fs/cgroup/memory.max /sys/fs/cgroup/memory.swap.max'),
 ('packet',f'lake -f {config} build Solidity.Lowering.P8.HelperPackets.MonetaryBounds.AxiomPins'),
 ('per-file',f'lake -f {config} env lean --tstack=131072 -j1 --setup .lake/build/ir/Solidity/Lowering/P8/HelperPackets/MonetaryBounds/Laws.setup.json Solidity/Lowering/P8/HelperPackets/MonetaryBounds/Laws.lean; lake -f {config} env lean --tstack=131072 -j1 --setup .lake/build/ir/Solidity/Lowering/P8/HelperPackets/MonetaryBounds/Controls.setup.json Solidity/Lowering/P8/HelperPackets/MonetaryBounds/Controls.lean; lake -f {config} env lean --tstack=131072 -j1 --setup .lake/build/ir/Solidity/Lowering/P8/HelperPackets/MonetaryBounds/AxiomPins.setup.json Solidity/Lowering/P8/HelperPackets/MonetaryBounds/AxiomPins.lean'),
 ('roots','bash scripts/coord-tools/register.sh --check'),
 ('fragments','bash scripts/coord-tools/fragments.sh --check'),
 ('module-map','python3 scripts/coord-tools/module-map.py origin/master'),
 ('axiom-inventory','node scripts/check-axiom-pins.mjs'),
 ('trust','bash scripts/check-trust.sh'),
 ('layers','node scripts/check-layers.mjs'),
 ('orphans','node scripts/check-orphans.mjs'),
 ('doc-paths','bash scripts/check-doc-paths.sh')]
def available():
 host=int(next(s.split()[1] for s in pathlib.Path('/proc/meminfo').read_text().splitlines() if s.startswith('MemAvailable:')))*1024
 cg=pathlib.Path('/sys/fs/cgroup');limit=(cg/'memory.max').read_text().strip()
 return min(host,int(limit)-int((cg/'memory.current').read_text())) if limit!='max' else host
if os.environ.get("VALIDATE_ONLY"):
 commands=[x for x in commands if x[0] in os.environ["VALIDATE_ONLY"].split(",")]
results=[]
for name,cmd in commands:
 minimum=available()
 if minimum<4*1024**3:raise SystemExit('STOP: less than 4 GiB effective reserve')
 args=['docker','--host=unix:///var/run/docker.sock','run','--rm','--name','money-registration-gate','--memory=12g','--memory-swap=12g','--cpus=1','--user=1000:1000','-v','/workspace:/workspace','-v','/opt:/opt:ro','-v','/usr:/usr:ro','-w',str(repo),'ubuntu:24.04','bash','-c','set -eu; test "$(cat /sys/fs/cgroup/memory.max)" = 12884901888; test "$(cat /sys/fs/cgroup/memory.swap.max)" = 0; source /workspace/.setup/activate.sh; export LEAN_NUM_THREADS=1 LAKE_CACHE_DIR=/workspace/.setup/cache/lake; export PATH=/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH; '+cmd]
 started=time.monotonic();stopped=False
 with (out/(name+'.log')).open('w') as log:
  log.write('COMMAND: '+cmd+'\n');log.flush()
  proc=subprocess.Popen(args,stdout=log,stderr=subprocess.STDOUT)
  while proc.poll() is None:
   minimum=min(minimum,available())
   if minimum<4*1024**3:
    subprocess.run(['docker','stop','money-registration-gate'],stdout=log,stderr=log);stopped=True
   time.sleep(.25)
 results.append({'name':name,'command':cmd,'status':'pass' if proc.returncode==0 and not stopped else 'fail','exit':proc.returncode,'seconds':round(time.monotonic()-started,3),'minimum_effective_available_bytes':minimum,'reserve_stop':stopped,'evidence':str(out/(name+'.log'))})
 (out/os.environ.get('VALIDATE_RESULTS','gates.json')).write_text(json.dumps(results,indent=2)+'\n')
 print(name,results[-1]['status'],flush=True)
