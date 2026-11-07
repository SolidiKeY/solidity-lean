#!/usr/bin/env python3
"""Private Lake environment for official toolchain gates; serial real Lean compiler."""
import argparse,json,os,shlex,subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument("--toolchain",type=Path,required=True);p.add_argument("--runtime",type=Path,required=True);p.add_argument("--phase",choices=["keysort","sort","full"],required=True);a=p.parse_args()
root=Path.cwd().resolve();tc=a.toolchain.resolve();runtime=a.runtime.resolve();runtime.mkdir(parents=True,exist_ok=True)
shim=runtime/"toolchain";(shim/"bin").mkdir(parents=True,exist_ok=True)
for directory in ["lib","include","src","share"]:
 target=shim/directory
 if (tc/directory).exists() and not target.exists():target.symlink_to(tc/directory,target_is_directory=True)
for target in (tc/"bin").iterdir():
 link=shim/"bin"/target.name
 if target.name not in ["lean","lake"] and not link.exists():link.symlink_to(target)
marker=runtime/"first-failure";marker.unlink(missing_ok=True)
lean_wrapper = r"""#!/usr/bin/env python3
import fcntl,os,subprocess,sys
from pathlib import Path
with open(__TASK_LOCK_PATH__,"w") as lock:
 fcntl.flock(lock,fcntl.LOCK_EX)
 if Path(__TASK_MARKER_PATH__).exists():
  print("migration gate: earlier Lean failure; no further Lean jobs launched",file=sys.stderr);raise SystemExit(1)
 log=Path(__TASK_MARKER_PATH__).parent/(os.environ.get("SYNTAX_GATE_PHASE","gate")+"-lean-"+str(os.getpid())+".log")
 with log.open("wb") as output:
  code=subprocess.call([__TASK_REAL_LEAN__,"-j1","-M11000","--tstack=131072"]+sys.argv[1:],stdout=output,stderr=subprocess.STDOUT)
 sys.stdout.buffer.write(log.read_bytes());sys.stdout.buffer.flush()
 if code:Path(__TASK_MARKER_PATH__).write_text("exit="+str(code)+" args="+repr(sys.argv[1:])+"\n")
 raise SystemExit(code)
"""
lean_wrapper=lean_wrapper.replace("__TASK_LOCK_PATH__",repr(str(runtime/"lean-job.lock"))).replace("__TASK_MARKER_PATH__",repr(str(marker))).replace("__TASK_REAL_LEAN__",repr(str(tc/"bin/lean")))
compile(lean_wrapper,"generated-lean-wrapper","exec")
(shim/"bin/lean").write_text(lean_wrapper);(shim/"bin/lean").chmod(0o755)
config=root/".lake/migrate-syntax.toml";config.parent.mkdir(exist_ok=True)
text=(root/"lakefile.toml").read_text().replace("enableArtifactCache = true","enableArtifactCache = false")
text='srcDir = '+json.dumps(str(root))+'\nbuildDir = '+json.dumps(str(root/".lake/build"))+'\n'+text
config.write_text(text)
lake_wrapper="#!/bin/sh\nif [ \"$1\" = --version ]; then exec "+shlex.quote(str(tc/"bin/lake"))+" --version; fi\nexec "+shlex.quote(str(tc/"bin/lake"))+" --keep-toolchain --no-cache --fail-fast --file "+shlex.quote(str(config))+' "$@"\n'
(shim/"bin/lake").write_text(lake_wrapper);(shim/"bin/lake").chmod(0o755)
env=dict(os.environ,PATH=str(shim/"bin")+":"+os.environ["PATH"],LEAN_SYSROOT=str(shim),LAKE_OVERRIDE_LEAN="true",LEAN_NUM_THREADS="1",SYNTAX_GATE_PHASE=a.phase,XDG_CACHE_HOME=str(runtime/"private-cache"),SOLKEY_RULES="/workspace/.setup/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key")
try:
 for command in [[str(shim/"bin/lean"),"--version"],[str(shim/"bin/lake"),"--version"]]:subprocess.run(command,env=env,check=True)
 command=[str(shim/"bin/lake"),"build","Solidity.KeySort"] if a.phase=="keysort" else ["bash","scripts/check-solkey.sh"] if a.phase=="sort" else ["bash","./run-lean.sh"]
 if a.phase=="sort":
  subprocess.run([str(shim/"bin/lake"),"build","solkeycheck"],env=env,check=True)
 print("PHASE",a.phase,"COMMAND",command,flush=True)
 raise SystemExit(subprocess.call(command,env=env))
finally:
 if marker.exists():(runtime/(a.phase+"-first-failure")).write_bytes(marker.read_bytes())
 config.unlink(missing_ok=True)
