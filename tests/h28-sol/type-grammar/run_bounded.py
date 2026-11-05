#!/usr/bin/env python3
"""Serial task gate: explicit Lean -j1, 12 GiB aggregate, no swap, 4 GiB reserve.
The container has no network; all inputs are local. A failed guard is a failure.
"""
import fcntl, hashlib, importlib.util, json, os, pathlib, subprocess, sys, time, uuid
from resource_guard import available_bytes, heavy_lock
root = pathlib.Path(__file__).resolve().parents[3]
area = root / "tests/h28-sol/type-grammar"
image = "ubuntu@sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852"
lock = open("/tmp/solidity-lean-feature-groups-20261025/writer.lock", "a")
fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
runtime_lock = heavy_lock()
env = os.environ.copy()
for key in ("DOCKER_HOST", "DOCKER_CONTEXT", "DOCKER_TLS", "DOCKER_TLS_VERIFY", "DOCKER_CERT_PATH"):
    env.pop(key, None)
docker = ["docker", "--host=unix:///var/run/docker.sock"]
active = subprocess.run(docker + ["ps", "--filter", "name=^/h28-type-mcp$", "--format", "{{.Names}}"], env=env, capture_output=True, text=True, timeout=10)
if active.returncode or active.stdout.strip():
    raise SystemExit("MCP runtime active or uninspectable; stop it before a build")
if available_bytes() < 4*1024**3:
    raise SystemExit("Insufficient enclosing-VM or host headroom")
mode = sys.argv[1]
if mode == "lean-fixtures":
    command = "/opt/codex/runtimes/codex-primary-runtime/dependencies/python/bin/python3 -B tests/h28-sol/type-grammar/check_fixture_coverage.py; lake -f tests/h28-sol/type-grammar/runtime.toml lean tests/h28-sol/type-grammar/ParserFixtureMain.lean -- -j1 --tstack=131072"
elif mode == "solc":
    command = "/opt/h28-node --max-old-space-size=4096 tests/h28-sol/type-grammar/run_solc.mjs /opt/h28-solc/soljson-v0.8.38+commit.1835d247.js"
elif mode == "runtime":
    command = "lean --version; lake --version; lean -j1 --tstack=131072 Solidity/KeySort.lean; echo RUNTIME_GATE_PASS"
elif mode == "layouts":
    command = "lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.Layouts"
elif mode == "counterexamples":
    command = "lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.Counterexamples"
elif mode == "composition":
    command = "lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.Composition"
elif mode == "boundaries":
    command = "lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.Boundaries"
elif mode == "type-regions":
    command = "lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.TypeRegions"
elif mode == "type-regions-matched":
    command = "bash -c 'TIMEFORMAT=\"LEAN_MATCHED_REAL=%R LEAN_MATCHED_USER=%U LEAN_MATCHED_SYS=%S\"; for h28_trial in 1 2 3; do time lake -f tests/h28-sol/type-grammar/runtime.toml env lean -j1 --tstack=131072 Solidity/Frontend/TypeGrammarH28/TypeRegions.lean || exit $?; done'"
elif mode == "parser-input":
    command = "lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.Checked.Parser"
elif mode == "parser-basics":
    command = "lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.ParserBasics"
elif mode == "exactness":
    command = "lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.Exactness"
elif mode == "parser-lengths":
    command = "lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.ParserLengths"
elif mode == "parser-functions":
    command = "lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.ParserFunctions"
elif mode == "parser-fn-attrs":
    command = "lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.ParserFnAttrs"
elif mode == "parser-params":
    command = "lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.ParserParams"
elif mode == "parser-ready":
    command = "lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.ParserReady"
elif mode == "parser-dynamic-closure":
    command = "lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.ParserDynamicClosure"
elif mode == "parser-mapping":
    command = "lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.ParserMapping"
elif mode == "parser-contexts":
    command = "lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.ParserContexts"
elif mode == "parser-arrays":
    command = "lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.ParserArrays"
elif mode == "parser-paths":
    command = "lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.ParserPaths"
elif mode == "parser-checks":
    command = "lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.ParserChecks"
elif mode == "check-input":
    specification = importlib.util.spec_from_file_location("h28_source_graph", root/"scripts/v08-build-graph.py")
    graph_module = importlib.util.module_from_spec(specification)
    old_bytecode = sys.dont_write_bytecode
    sys.dont_write_bytecode = True
    try:
        specification.loader.exec_module(graph_module)
    finally:
        sys.dont_write_bytecode = old_bytecode
    ordered = graph_module.SourceGraph(root).closure(["Solidity.Frontend.Checked.Check"])
    command = "; ".join("lake -f tests/h28-sol/type-grammar/runtime.toml build " + m for m in ordered)
elif mode == "axioms":
    command = "lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.Layouts; lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.Counterexamples; lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.Composition; lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.Boundaries; lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.TypeRegions; lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.ParserBasics; lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.ParserChecks; lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.ParserPaths; lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.ParserArrays; lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.ParserContexts; lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.ParserMapping; lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.ParserDynamicClosure; lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.ParserReady; lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.ParserParams; lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.ParserFnAttrs; lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.ParserFunctions; lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.ParserLengths; lake -f tests/h28-sol/type-grammar/runtime.toml build Solidity.Frontend.TypeGrammarH28.Exactness; lake -f tests/h28-sol/type-grammar/runtime.toml lean tests/h28-sol/type-grammar/AxiomAudit.lean -- -j1 --tstack=131072"
else:
    raise SystemExit("unsupported gate")
script = "export PATH=/opt/lean/bin:$PATH; set -eu; trap 'printf CGROUP_PEAK=; cat /sys/fs/cgroup/memory.peak' EXIT; test \"$(cat /sys/fs/cgroup/memory.max)\" = 12884901888; test \"$(cat /sys/fs/cgroup/memory.swap.max)\" = 0; " + command
name = "h28-type-" + uuid.uuid4().hex[:12]
cmd = docker + ["run", "--name", name, "--network", "none", "--memory", "12g", "--memory-swap", "12g", "--cpus", "1", "--user", "1000:1000",
    "--mount", "type=bind,src=" + str(root) + ",dst=" + str(root),
    "--mount", "type=bind,src=/workspace/.setup/tools/lean-4.24.0-linux,dst=/opt/lean,readonly",
    "--mount", "type=bind,src=/workspace/.setup/cache/lake,dst=/workspace/.setup/cache/lake",
    "-w", str(root), "-e", "LEAN_NUM_THREADS=1", "-e", "LAKE_CACHE_DIR=/workspace/.setup/cache/lake", image, "sh", "-c", script]
if mode == "solc":
    insertion = cmd.index("-w")
    cmd[insertion:insertion] = ["--mount", "type=bind,src=/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin/node,dst=/opt/h28-node,readonly", "--mount", "type=bind,src=/workspace/scratch/h28-type-grammar/solc,dst=/opt/h28-solc,readonly"]
if mode == "lean-fixtures":
    insertion = cmd.index("-w")
    cmd[insertion:insertion] = ["--mount", "type=bind,src=/opt/codex/runtimes/codex-primary-runtime/dependencies/python,dst=/opt/codex/runtimes/codex-primary-runtime/dependencies/python,readonly"]
logpath = area / "evidence" / (name + ".log")
started = time.monotonic()
peak_rss = 0
minimum_headroom = available_bytes()
inputs = sorted((root/"Solidity/Frontend/TypeGrammarH28").glob("*.lean")) + sorted(area.glob("*.py")) + sorted(area.glob("*.lean")) + [area/"runtime.toml", root/"scripts/v08-build-graph.py"]
inputs += sorted(area.glob("*.mjs")) + [area/"fixtures.json"] + sorted((area/"fixtures").rglob("*.sol"))
if mode == "lean-fixtures":
    inputs.extend([area/"evidence/solc-type-cases.json", area/"evidence/solc-results.json"])
source_hashes = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
checked_head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
stopped = None
with logpath.open("w") as log:
    log.write(json.dumps(cmd) + "\n"); log.flush()
    proc = subprocess.Popen(cmd, env=env, stdout=log, stderr=subprocess.STDOUT)
    try:
        while proc.poll() is None:
            top = subprocess.run(docker + ["top", name, "-eo", "pid,rss"], env=env, capture_output=True, text=True)
            if top.returncode == 0:
                peak_rss = max(peak_rss, sum(int(line.split()[1])*1024 for line in top.stdout.splitlines()[1:] if len(line.split()) == 2))
            mem_available = available_bytes()
            minimum_headroom = min(minimum_headroom, mem_available)
            if mem_available < 4*1024**3 or time.monotonic()-started > 600:
                stopped = "HEADROOM_OR_600S_GUARD"
                subprocess.run(docker + ["stop", "-t", "5", name], env=env, capture_output=True)
                break
            time.sleep(0.5)
        exit_code = proc.wait(timeout=15)
    except BaseException:
        subprocess.run(docker + ["stop", "-t", "5", name], env=env, capture_output=True)
        raise
    peak = subprocess.run(docker + ["inspect", "--format", "{{.HostConfig.Memory}} {{.HostConfig.MemorySwap}} {{.State.OOMKilled}} {{.State.ExitCode}}", name], env=env, capture_output=True, text=True)
    log.write("\nCONTAINER " + peak.stdout)
unchanged = all(hashlib.sha256((root/p).read_bytes()).hexdigest()==h for p,h in source_hashes.items())
if not unchanged: stopped = "SOURCE_CHANGED_DURING_GATE"
summary = dict(mode=mode, head=checked_head, source_hashes=source_hashes, source_unchanged=unchanged, minimum_vm_or_host_headroom_bytes=minimum_headroom, command=cmd, exit=exit_code, guard=stopped, elapsed_s=time.monotonic()-started, sampled_peak_rss_bytes=peak_rss, log=str(logpath), limits=peak.stdout.strip())
logpath.with_suffix(".json").write_text(json.dumps(summary, indent=2)+"\n")
print(json.dumps(summary))
raise SystemExit(1 if stopped or exit_code else 0)
