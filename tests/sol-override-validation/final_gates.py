"""Run the repository-required gates, preserving failure statuses and outputs.
Requires the writer lock, the existing bounded container and frozen SolKey.
"""
import json
from pathlib import Path
import subprocess
import time
ROOT=Path(__file__).resolve().parents[2]
E=ROOT/'tests/sol-override-validation/evidence'
PATH='/workspace/solidity-lean/tests/sol-override-validation/runtime/bin:/workspace/.setup/tools/lean-4.24.0-linux/bin:/opt/codex/runtimes/codex-primary-runtime/dependencies/python/bin:/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:/usr/local/bin:/usr/bin:/bin'
prefix=['docker','exec','-e','LEAN_NUM_THREADS=1','-e','PATH='+PATH,'-e','SOLKEY_RULES=/workspace/.setup/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key','sol-ov-session']
results=[]
def run(name,args,seconds=180):
    command=prefix+['timeout','--kill-after=10',str(seconds)]+args
    started=time.time()
    with (E/(name+'.log')).open('w') as output:
        result=subprocess.run(command,stdout=output,stderr=subprocess.STDOUT)
    results.append(dict(name=name,command=command,exitCode=result.returncode,status='pass' if result.returncode==0 else 'fail',seconds=round(time.time()-started,2),evidence=str(E/(name+'.log'))))
    (E/'final-gates.json').write_text(json.dumps(results,indent=2)+'\n')
    print(name+': exit '+str(result.returncode),flush=True)
    return result.returncode
run('versions',['sh','-c','lean --version; lake --version; cat /sys/fs/cgroup/memory.max /sys/fs/cgroup/memory.swap.max; cat /sys/fs/cgroup/memory.events'])
for source in sorted((ROOT/'Solidity/Frontend/OverrideValidation').glob('*.lean')):
    run('final-diag-'+source.stem,['scripts/coord-tools/lean-mcp','diag',str(source)])
for name in ['Trust','GraphControls','AdvancedControls']:
    run('final-diag-'+name,['scripts/coord-tools/lean-mcp','diag','tests/sol-override-validation/'+name+'.lean'])
run('mcp-stop',['scripts/coord-tools/lean-mcp','stop'])
for name in ['Trust','GraphControls','AdvancedControls']:
    run('final-proof-'+name,['lake','env','lean','-j1','--tstack=131072','tests/sol-override-validation/'+name+'.lean'])
run('final-keysort',['bash','scripts/check-solkey.sh'],600)
run('final-run-lean',['bash','./run-lean.sh'],1800)
run('final-axiom-inventory',['node','scripts/check-axiom-pins.mjs'])
run('final-doc-paths',['bash','scripts/check-doc-paths.sh'])
run('final-core-checkpoint',['lake','build','Solidity'],1800)
run('final-resources',['sh','-c','cat /sys/fs/cgroup/memory.max /sys/fs/cgroup/memory.swap.max /sys/fs/cgroup/memory.peak /sys/fs/cgroup/memory.events'])
