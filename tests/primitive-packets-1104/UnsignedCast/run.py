#!/usr/bin/env python3
"""Serial bounded Lean checks for the owned unsigned-cast packet."""
import fcntl, hashlib, json, os, subprocess, sys, time
from pathlib import Path
if not __debug__:
    raise SystemExit("Optimization disables gate assertions")
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/"tests/primitive-packets-1104/UnsignedCast/evidence"
CACHE=Path("/workspace/solidity-lean/.lake")
TOOLS=Path("/home/agent/sol-qn-tools")
mode=sys.argv[1]; target=sys.argv[2]
assert mode in ("build","check","stdin","tools","keysort","checkpoint")
with open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a") as lock:
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    OUT.mkdir(exist_ok=True)
    original=(ROOT/"lakefile.toml").read_bytes()
    config=ROOT/"tests/primitive-packets-1104/UnsignedCast/runtime.lakefile.toml"
    text=original.decode().replace('version = "0.1.0"',f'version = "0.1.0"\nsrcDir = "{ROOT}"\nbuildDir = "{CACHE}/build"\nweakLeanArgs = ["-j1"]')
    text=text.replace('srcDir = "vendor/LeanTeX"',f'srcDir = "{ROOT}/vendor/LeanTeX"')
    name=f"ucast-{os.getpid()}";label=target.replace("/","_").replace(".","_")
    command=["docker","--host=unix:///var/run/docker.sock","run","--rm","--name",name,"--memory=12g","--memory-swap=12g","--network=none","--mount",f"type=bind,src={ROOT},dst={ROOT}","--mount",f"type=bind,src={CACHE},dst={CACHE}","--mount",f"type=bind,src={TOOLS},dst=/tools,readonly","-w",str(ROOT),"-e","LEAN_NUM_THREADS=1"]
    stdin=None
    runtime_bin=ROOT/"tests/primitive-packets-1104/UnsignedCast/runtime-bin"
    if mode=="checkpoint":
        # Serialize independently spawned corpus probes as well as ordinary Lake calls.
        node=Path("/opt/codex/runtimes/codex-primary-runtime/dependencies/node")
        python=Path(sys.executable).resolve().parent.parent
        gitdir=Path("/workspace/solidity-lean/.git")
        command += ["--mount","type=bind,src=/usr,dst=/usr,readonly",
          "--mount",f"type=bind,src={node},dst={node},readonly",
          "--mount",f"type=bind,src={python},dst={python},readonly",
          "--mount",f"type=bind,src={gitdir},dst={gitdir},readonly",
          "--mount",f"type=bind,src={CACHE},dst={ROOT}/.lake",
          "-e",f"PATH={runtime_bin}:{node}/bin:{python}/bin:/usr/bin:/bin",
          "-e","PYTHONDONTWRITEBYTECODE=1","-e","GIT_CONFIG_COUNT=1",
          "-e","GIT_CONFIG_KEY_0=safe.directory","-e",f"GIT_CONFIG_VALUE_0={ROOT}",
          "-e","GATE_BASE=6f3eedf0788ee1f8a3bcf230558c712ecdca04d5",
          "-e",f"GATE_LOGS={OUT}/checkpoint",
          "-e",f"SOLKEY_EXAMPLES={ROOT}/tests/migration/solkey/keyext.solidity.examples",
          "-e",f"SOLKEY_RULES={ROOT}/tests/migration/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key"]
        command += ["debian:trixie-slim","bash","scripts/coord-tools/gate.sh","full"]
    elif mode=="tools":
        command += ["debian:trixie-slim","bash","-c","/tools/lean-4.24.0-linux/bin/lean -j1 --version\n/tools/lean-4.24.0-linux/bin/lake --version\ncat /sys/fs/cgroup/memory.max\ncat /sys/fs/cgroup/memory.swap.max"]
    elif mode=="keysort":
        command += ["debian:trixie-slim","bash","-c",f"set -eu\n/tools/lean-4.24.0-linux/bin/lake -f {config} build solkeycheck\n{CACHE}/build/bin/solkeycheck --key tests/migration/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key"]
    if mode=="build":
        command += ["debian:trixie-slim","/tools/lean-4.24.0-linux/bin/lake","-f",str(config),"build",target]
    elif mode in ("check","stdin"):
        command += ["-e",f"LEAN_PATH={CACHE}/build/lib/lean"]
        if mode=="stdin":
            command += ["-i"];stdin=(ROOT/target).read_text()
        command += ["debian:trixie-slim","/tools/lean-4.24.0-linux/bin/lean","-j1","--tstack=131072", "--stdin" if mode=="stdin" else target]
    process=None;start=time.monotonic();minimum=None
    logpath=OUT/(label+"-"+mode+"-"+str(time.time_ns())+".log")
    config_created=False
    runtime_created=False
    receipt_path=OUT/(logpath.name+".json")
    receipt={"mode":mode,"target":target,"command":command,"exit":None,
      "lakefile_sha256":hashlib.sha256(original).hexdigest(),
      "runner_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      "sources":{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
        for directory in [ROOT/"Solidity/Backend/PrimitivePackets/UnsignedCast",ROOT/"tests/primitive-packets-1104/UnsignedCast"]
        for p in directory.glob("*.lean")}}
    receipt_path.write_text(json.dumps(receipt,indent=2)+"\n")
    try:
        with config.open("x") as config_file:
            config_created=True
            config_file.write(text)
        if mode=="checkpoint":
            runtime_bin.mkdir()
            runtime_created=True
            wrapper=runtime_bin/"lake"
            wrapper.write_text('#!'+str(sys.executable)+'\nimport os,sys\na=sys.argv[1:]\nif "lean" in a: a += ["-j1"]\nos.execv("/usr/bin/flock",["flock","/tmp/ucast-child-lean.lock","/tools/lean-4.24.0-linux/bin/lake","-f",'+repr(str(config))+']+a)\n')
            wrapper.chmod(0o755)
        with logpath.open("w") as log:
            log.write("COMMAND "+json.dumps(command)+"\n");log.flush()
            process=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,stdin=subprocess.PIPE if stdin else subprocess.DEVNULL,text=True)
            if stdin: process.stdin.write(stdin);process.stdin.close()
            while process.poll() is None:
                available=next(int(line.split()[1])*1024 for line in Path("/proc/meminfo").read_text().splitlines() if line.startswith("MemAvailable:"))
                root=Path("/sys/fs/cgroup");relative=next(line.split(":",2)[2] for line in Path("/proc/self/cgroup").read_text().splitlines() if line.startswith("0::"));group=root/relative.lstrip("/")
                while group==root or root in group.parents:
                    maximum=(group/"memory.max").read_text().strip();current=int((group/"memory.current").read_text())
                    if maximum!="max":available=min(available,max(0,int(maximum)-current))
                    if group==root:break
                    group=group.parent
                minimum=available if minimum is None else min(minimum,available)
                if available<4*1024**3:
                    raise RuntimeError("H1 reserve below4GiB; do not start additional work")
                time.sleep(1)
            log.write(f"EXIT {process.returncode}\nSECONDS {time.monotonic()-start:.3f}\nMINIMUM_AVAILABLE_BYTES {minimum}\n")
        print(logpath, "exit",process.returncode,flush=True)
        raise SystemExit(process.returncode)
    finally:
        error=sys.exc_info()[0]
        if process is not None and process.poll() is None:
            # Cleanup only on failure/interruption, never for a scheduling rebalance.
            subprocess.run(["docker","--host=unix:///var/run/docker.sock","stop","-t","1",name],check=True)
            process.wait()
        if runtime_created:
            (runtime_bin/"lake").unlink(missing_ok=True)
            runtime_bin.rmdir()
        if config_created:
            config.unlink(missing_ok=True)
        assert (ROOT/"lakefile.toml").read_bytes()==original
        if error not in (None,SystemExit):
            with logpath.open("a") as log:
                log.write("EXCEPTION "+error.__name__+"\n")
                log.write(f"EXIT {None if process is None else process.returncode}\nSECONDS {time.monotonic()-start:.3f}\nMINIMUM_AVAILABLE_BYTES {minimum}\n")
        receipt.update({"exit":None if process is None else process.returncode,
          "process_started":process is not None,"seconds":time.monotonic()-start,
          "error":None if error in (None,SystemExit)else error.__name__,
          "minimum_available_bytes":minimum,"log_sha256":hashlib.sha256(logpath.read_bytes()).hexdigest()})
        receipt_path.write_text(json.dumps(receipt,indent=2)+"\n")
