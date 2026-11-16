#!/usr/bin/env python3
"""Run a V16 check in the established 12GiB/no-swap local Docker cgroup.
No toolchain/network/dependency setup. A single task-owned temporary Lake
configuration appends -j1; tracked configurations and proof budgets are untouched.
"""
import argparse, fcntl, os, pathlib, shlex, subprocess, importlib.util, json, sys, shutil
sys.dont_write_bytecode = True

ROOT = pathlib.Path(__file__).resolve().parents[1]
BASE = "2fe1f8932f96be15b00df03ba2cde46f64a87758"
BRANCH = "codex/solidity-v12-v17-20261031/v16-correctness-transfer"
IMAGE = "ubuntu@sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852"

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--compatibility-v2", action="store_true", help="H279 scoped versioned capture; does not accept the V1 global audit")
    ap.add_argument("--log", type=pathlib.Path, required=True)
    ap.add_argument("command", nargs=argparse.REMAINDER)
    args = ap.parse_args()
    cmd = args.command
    if cmd[:1] == ["--"]: cmd = cmd[1:]
    full = cmd == ["./run-lean.sh"]
    if not cmd or (cmd[0] != "lake" and not full): ap.error("only direct lake commands or ./run-lean.sh are supported")
    if (cmd[1:3] == ["env", "lean"] or cmd[1:2] == ["lean"]) and "-j1" not in cmd:
        ap.error("direct Lean checks require explicit -j1")
    tool_bin = pathlib.Path(shutil.which("lake") or "/missing-lake").resolve().parent
    if not (tool_bin/"lake").is_file() or not (tool_bin/"lean").is_file(): ap.error("pinned Lean/Lake unavailable")
    version = subprocess.check_output([str(tool_bin/"lean"),"--version"],text=True)
    if "Lean (version 4.24.0," not in version or "797c613eb9b6d4ec95db23e3e00af9ac6657f24b" not in version: ap.error("wrong pinned Lean")
    if (ROOT/"lean-toolchain").read_text().strip() != "leanprover/lean4:v4.24.0": ap.error("changed pinned toolchain")
    if shutil.disk_usage(ROOT).free < 4*1024**3: ap.error("4GiB disk reserve unavailable")
    memory = dict((line.split(':',1)[0],int(line.split()[1])*1024) for line in pathlib.Path('/proc/meminfo').read_text().splitlines())
    if memory['MemAvailable'] < 12*1024**3: ap.error("12GiB available-memory reserve unavailable")
    env = os.environ.copy()
    for k in ["DOCKER_HOST", "DOCKER_CONTEXT", "DOCKER_TLS", "DOCKER_TLS_VERIFY", "DOCKER_CERT_PATH"]:
        env.pop(k, None)
    lock = pathlib.Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")
    with lock.open("a") as lk, args.log.open("x") as log:
        fcntl.flock(lk, fcntl.LOCK_EX | fcntl.LOCK_NB)
        if subprocess.check_output(["git", "branch", "--show-current"], cwd=ROOT, text=True).strip() not in (BRANCH, BRANCH+"-recovery"):
                ap.error("wrong branch")
        subprocess.run(["git", "merge-base", "--is-ancestor", BASE, "HEAD"], cwd=ROOT, check=True)
        log.write("Locked checkout status:\n" + subprocess.check_output(["git", "status", "--short", "--branch"], cwd=ROOT, text=True)); log.flush()
        spec=importlib.util.spec_from_file_location("v16_provenance",ROOT/"scripts/roadmap-v16-accounting.py")
        provenance=importlib.util.module_from_spec(spec);spec.loader.exec_module(provenance)
        binding_fn=provenance.current_binding
        binding_prefix="V16-BINDING"
        if args.compatibility_v2:
            v2spec=importlib.util.spec_from_file_location("v16_compatibility_v2",ROOT/"scripts/roadmap-v16-mixed-compatibility-v2.py")
            v2=importlib.util.module_from_spec(v2spec);v2spec.loader.exec_module(v2)
            binding_fn=v2.capture_binding
            binding_prefix="V16-COMPAT-V2-BINDING"
        binding=binding_fn(ROOT)
        log.write(binding_prefix+"-BEFORE "+json.dumps(binding,sort_keys=True)+"\n");log.flush()
        alt = ROOT / "lakefile.v16-runtime.toml"
        # Exclusive creation protects unexpected local work.
        config=(ROOT/"lakefile.toml").read_text()
        if 'weakLeanArgs = ["--tstack=131072"]' not in config:
            ap.error("expected library configuration missing")
        config=config.replace('weakLeanArgs = ["--tstack=131072"]','weakLeanArgs = ["--tstack=131072", "-j1"]')
        # Libraries/executables without stack overrides still get explicit -j1.
        sections=config.split("[[lean_")
        for i in range(1,len(sections)):
            if "weakLeanArgs" not in sections[i]:
                first,rest=sections[i].split("\n",1)
                sections[i]=first+'\nweakLeanArgs = ["-j1"]\n'+rest
        config="[[lean_".join(sections)
        config += '\n[[lean_lib]]\nname = "tests"\nglobs = ["tests.+"]\nweakLeanArgs = ["--tstack=131072", "-j1"]\n'
        shell_env=ROOT/".lake/v16-shell-env.bash"
        if full and shell_env.exists(): ap.error("unexpected existing full-gate shell config")
        with alt.open("x") as f: f.write(config)
        if full:
            with shell_env.open("x") as f:
                f.write('lake() { '+shlex.quote(str(tool_bin/'lake'))+' --file "$V16_LAKE_CONFIG" "$@"; }\nexport -f lake\n')
        try:
            if cmd[0] == "lake": cmd[1:1] = ["-f", alt.name]
            else: cmd=["./run-lean.sh"]
            # A direct metadata/audit run must not import stale V16 oleans.
            if cmd[:3] == ["lake","-f",alt.name] and "env" in cmd:
                modules=[".".join(p.relative_to(ROOT).with_suffix("").parts) for p in sorted([p for area in ["Solidity/Roadmap/V16","Solidity/Examples/Roadmap/V16"] for p in (ROOT/area).rglob("*.lean")])]
                preparatory=["lake","-f",alt.name,"build"]+modules
            else: preparatory=[]
            monitor = "(while true; do awk '/^Name:/ {n=$2} /^VmRSS:/ {t += $2; if(n==\"lean\") l++; if(n ~ /^(clang|gcc|cc1)/) c++} END {print \"RSS_KiB=\" t \" LEAN_WORKERS=\" l+0 \" CC_WORKERS=\" c+0}' /proc/[0-9]*/status; sleep 0.1; done) & mon=$!; "
            shell = '[ \"$(cat /sys/fs/cgroup/memory.max)\" = 12884901888 ] && [ \"$(cat /sys/fs/cgroup/memory.swap.max)\" = 0 ] || exit 91; cat /sys/fs/cgroup/memory.max /sys/fs/cgroup/memory.swap.max; ' + monitor + "timeout 5400 sh -c " + shlex.quote(((shlex.join(preparatory) + " && ") if preparatory else "") + shlex.join(cmd)) + '; r=$?; kill "$mon"; wait "$mon" 2>/dev/null; cat /sys/fs/cgroup/memory.peak; exit "$r"'
            argv = ["docker", "--host=unix:///var/run/docker.sock", "run", "--rm", "--network=none",
                "--memory=12g", "--memory-swap=12g", "--user", "1000:1000",
                "--mount", "type=bind,src=/workspace,dst=/workspace", "--mount", "type=bind,src=/usr,dst=/usr,readonly", "--mount", "type=bind,src=/opt,dst=/opt,readonly", "-w", str(ROOT),
                "-e", "LEAN_NUM_THREADS=1", "-e", "PATH="+str(tool_bin)+":/usr/bin:/bin", "-e", "LAKE_CACHE_DIR="+env.get("LAKE_CACHE_DIR","/workspace/.setup/cache/lake"),
                *(["-e","PATH="+str(tool_bin)+":/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:/usr/bin:/bin",
                    "-e","BASH_ENV="+str(shell_env),"-e","V16_LAKE_CONFIG="+str(alt),
                    "-e","SOLKEY_ROOT=/workspace/.setup/solkey",
                    "-e","SOLKEY_RULES=/workspace/.setup/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key"] if full else []),
                IMAGE, "sh", "-c", shell]
            log.write("$ " + shlex.join(argv) + "\n"); log.flush()
            r = subprocess.run(argv, env=env, stdout=log, stderr=subprocess.STDOUT)
            after=binding_fn(ROOT)
            log.write(binding_prefix+"-AFTER "+json.dumps(after,sort_keys=True)+"\n")
            result=r.returncode if after==binding else 92
            log.write("exit=" + str(result) + "\n")
            return result
        finally:
            alt.unlink()
            if full: shell_env.unlink()

if __name__ == "__main__": raise SystemExit(main())
