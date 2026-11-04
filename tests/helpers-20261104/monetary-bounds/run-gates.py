#!/usr/bin/env python3
"""Run serial checks in the verified hard Docker envelope; retain exact outcomes."""
import json, os, pathlib, subprocess, time
root=pathlib.Path(__file__).resolve().parent
out=pathlib.Path(os.environ.get('GATE_OUTPUT', str(root/'evidence'))); out.mkdir(parents=True, exist_ok=True)
producer='/workspace/monetary-producer-input'
config='/workspace/solidity-lean/tests/helpers-20261104/monetary-bounds/lakefile.toml'
commands=[
 ('h35-packet', 'lake build Solidity.Lowering.P8.HelperPackets.MonetaryBounds.AxiomPins; lake env lean --tstack=131072 -j1 --setup .lake/build/ir/Solidity/Lowering/P8/HelperPackets/MonetaryBounds/Laws.setup.json Solidity/Lowering/P8/HelperPackets/MonetaryBounds/Laws.lean; lake env lean --tstack=131072 -j1 --setup .lake/build/ir/Solidity/Lowering/P8/HelperPackets/MonetaryBounds/Controls.setup.json Solidity/Lowering/P8/HelperPackets/MonetaryBounds/Controls.lean; lake env lean --tstack=131072 -j1 --setup .lake/build/ir/Solidity/Lowering/P8/HelperPackets/MonetaryBounds/AxiomPins.setup.json Solidity/Lowering/P8/HelperPackets/MonetaryBounds/AxiomPins.lean'),
 ('mcp-diagnostics', "export LEAN_MCP_SERVER_CMD='/workspace/solidity-lean/.venv/bin/python -m lean_lsp_mcp --lean-project-path /workspace/monetary-producer-input'; export LEAN_MCP_START_WAIT=45 LEAN_MCP_TIMEOUT=90 LEAN_LSP_MAX_OPEN_FILES=1; trap 'scripts/coord-tools/lean-mcp stop' EXIT; scripts/coord-tools/lean-mcp diag Solidity/Lowering/P8/HelperPackets/MonetaryBounds/Laws.lean; scripts/coord-tools/lean-mcp diag Solidity/Lowering/P8/HelperPackets/MonetaryBounds/Controls.lean; scripts/coord-tools/lean-mcp diag Solidity/Lowering/P8/HelperPackets/MonetaryBounds/AxiomPins.lean"),
 ('keysort-explicit-root', 'lake env lean --tstack=131072 -j1 --setup .lake/build/ir/SolkeyCheck.setup.json SolkeyCheck.lean; lake exe solkeycheck'),
 ('keysort-serial-rebuild', f'rm -f .lake/build/lib/lean/SolkeyCheck.trace .lake/build/lib/lean/SolkeyCheck.olean; lake --no-cache -v -f {config} build solkeycheck; lake -f {config} exe solkeycheck'),
 ('resource-proof', f'lake -f {config} build Solidity.Lowering.P8.HelperPackets.MonetaryBounds.AxiomPins'),
 ('runtime', 'lean --version; lake --version; cat /sys/fs/cgroup/memory.max /sys/fs/cgroup/memory.swap.max'),
 ('packet', f'lake -f {config} build Solidity.Lowering.P8.HelperPackets.MonetaryBounds.AxiomPins'),
 ('keysort-final', f'lake -f {config} exe solkeycheck'),
 ('run-lean', './run-lean.sh'),
 ('trust', 'bash scripts/check-trust.sh'),
 ('layers', 'node scripts/check-layers.mjs'),
 ('roots', 'bash scripts/coord-tools/register.sh --check'),
 ('orphans', 'node scripts/check-orphans.mjs'),
 ('doc-paths', 'bash scripts/check-doc-paths.sh'),
 ('axiom-inventory', 'node scripts/check-axiom-pins.mjs'),
]
if os.environ.get('GATE_ONLY'):
 commands=[x for x in commands if x[0] in os.environ['GATE_ONLY'].split(',')]
results=[]
for name,command in commands:
 def mem():
  available=int(next(s.split()[1] for s in pathlib.Path('/proc/meminfo').read_text().splitlines() if s.startswith('MemAvailable:')))*1024
  cg=pathlib.Path('/sys/fs/cgroup')
  limit=(cg/'memory.max').read_text().strip()
  return min(available,int(limit)-int((cg/'memory.current').read_text())) if limit!='max' else available
 minimum=mem()
 if minimum<4*1024**3: raise SystemExit('VM reserve below 4 GiB')
 args=['docker','--host=unix:///var/run/docker.sock','run','--rm','--name','h26-money-gate','--memory=12g','--memory-swap=12g','--cpus=1','--user=1000:1000','-v','/workspace:/workspace','-v','/opt:/opt:ro','-v','/usr:/usr:ro','-w',producer,'ubuntu:24.04','bash','-c',
 'set -eu; test "$(cat /sys/fs/cgroup/memory.max)" = 12884901888; test "$(cat /sys/fs/cgroup/memory.swap.max)" = 0; source /workspace/.setup/activate.sh; export LEAN_NUM_THREADS=1; export PATH=/workspace/solidity-lean/tests/helpers-20261104/monetary-bounds/bin:/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH; '+command]
 with (out/(name+'.log')).open('w') as log:
  log.write('COMMAND: '+command+'\n'); log.flush()
  proc=subprocess.Popen(args,stdout=log,stderr=subprocess.STDOUT)
  stopped=False
  while proc.poll() is None:
   minimum=min(minimum,mem())
   if minimum<4*1024**3:
    subprocess.run(['docker','stop','h26-money-gate'],stdout=log,stderr=log); stopped=True
   time.sleep(.25)
 result={'name':name,'command':command,'exit':proc.returncode,'status':'pass' if proc.returncode==0 and not stopped else 'fail','minimum_available_bytes':minimum,'reserve_stop':stopped,'log':str(out/(name+'.log'))}
 results.append(result); (out/os.environ.get('GATE_RESULTS','gates.json')).write_text(json.dumps(results,indent=2)+'\n')
 print(name,result['status'],flush=True)
