#!/usr/bin/env python3
"""One owned check: cgroup limits, writer lock, H1 monitor, bound evidence and cleanup."""
import argparse, fcntl, hashlib, json, os, re, shlex, signal, subprocess, time
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
DOCKER = ["docker", "--host=unix:///var/run/docker.sock"]
CONTAINER = os.environ.get("SOL_C3_CONTAINER", "sol-c3-checks")
RESERVE = 4 * 1024**3

TIMING_CODE = ("import resource,subprocess,sys,time; start=time.monotonic(); "
               "r=subprocess.run(sys.argv[1:]); "
               "print('Elapsed seconds: '+str(time.monotonic()-start),flush=True); "
               "print('Maximum child resident set size (kbytes): '+str(resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss),flush=True); "
               "code=r.returncode if r.returncode>=0 else 128-r.returncode; "
               "print('Raw child return code: '+str(r.returncode),flush=True); "
               "print('Exit status: '+str(code),flush=True); sys.exit(code)")

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--log", required=True)
    ap.add_argument("command", nargs=argparse.REMAINDER)
    args = ap.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        ap.error("missing command")
    log = (ROOT / args.log).resolve()
    assert log.is_relative_to(ROOT / "tests/sol-c3-exactness/evidence")
    env = os.environ.copy()
    for key in ["DOCKER_HOST", "DOCKER_CONTEXT", "DOCKER_TLS", "DOCKER_TLS_VERIFY", "DOCKER_CERT_PATH"]:
        env.pop(key, None)
    def docker(*a):
        return subprocess.check_output(DOCKER + list(a), env=env, text=True).strip()
    def available():
        host = int(re.search(r"MemAvailable:\s+(\d+)", Path("/proc/meminfo").read_text())[1]) * 1024
        cg = Path("/sys/fs/cgroup")
        cap, used = (cg / "memory.max").read_text().strip(), int((cg / "memory.current").read_text())
        return min(host, int(cap) - used) if cap != "max" else host
    def interrupted(signum, frame):
        raise InterruptedError("monitor received signal " + str(signum))
    with Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        before = subprocess.check_output(["git", "status", "--short"], cwd=ROOT, text=True)
        head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        limits = json.loads(docker("inspect", CONTAINER, "--format", "{{json .HostConfig}}"))
        assert limits["Memory"] == 12884901888 and limits["MemorySwap"] == 12884901888
        assert limits["NanoCpus"] == 1000000000
        minimum = available()
        assert minimum >= RESERVE, "H1 reserve unavailable before check"
        if docker("inspect", CONTAINER, "--format", "{{.State.Running}}") == "false":
            docker("start", CONTAINER)
        assert docker("exec", CONTAINER, "cat", "/sys/fs/cgroup/memory.max") == "12884901888"
        assert docker("exec", CONTAINER, "cat", "/sys/fs/cgroup/memory.swap.max") == "0"
        lean_version = docker("exec", CONTAINER, "lean", "--version")
        lake_version = docker("exec", CONTAINER, "lake", "--version")
        m = json.loads((ROOT / "tests/sol-c3-exactness/manifest.json").read_text())
        paths = set(m["source_pins"]) | {str(p.relative_to(ROOT)) for p in
            (ROOT / "Solidity/Frontend/C3Exactness").rglob("*.lean")} | {
            "scripts/check-sol-c3-exactness.py", "tests/sol-c3-exactness/run-bounded.py",
            "tests/sol-c3-exactness/lakefile.worker.toml", "tests/sol-c3-exactness/bin/lake",
            "tests/sol-c3-exactness/manifest.json"}
        paths |= {"tests/sol-c3-exactness/check-fixtures.mjs", "tests/sol-c3-exactness/final-checks.py", "tests/sol-c3-exactness/axiom-registration.json", "tests/sol-c3-exactness/release-owned-file-cache.py"}
        paths |= {str(p.relative_to(ROOT)) for p in (ROOT / "tests/sol-c3-exactness/fixtures").rglob("*") if p.is_file()}
        snapshot = {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in sorted(paths)}
        extra_path = os.environ.get("SOL_C3_EXTRA_PATH", "")
        script = ("set -eu; source /workspace/.setup/activate.sh; export LEAN_NUM_THREADS=1; "
                  "export LEAN_LSP_MAX_OPEN_FILES=1; "
                  "export PATH=/opt/codex/runtimes/codex-primary-runtime/dependencies/python/bin:$PATH; "
                  "export PATH=/workspace/solidity-lean/tests/sol-c3-exactness/bin:$PATH; "
                  "export LEAN_MCP_SERVER_CMD='.venv/bin/python -m lean_lsp_mcp --lean-project-path /workspace/solidity-lean'; "
                  + ('export PATH=' + shlex.quote(extra_path) + ':$PATH; ' if extra_path else '') +
                  'exec python3 -c ' + shlex.quote(TIMING_CODE) + ' "$@"')
        cmd = DOCKER + ["exec", CONTAINER, "bash", "-c", script, "sol-c3-check"] + command
        start = time.monotonic()
        pressure, was_interrupted, error, proc = False, False, None, None
        peak, rc = None, 1
        signal.signal(signal.SIGTERM, interrupted)
        signal.signal(signal.SIGINT, interrupted)
        try:
            with log.open("w") as output:
                proc = subprocess.Popen(cmd, cwd=ROOT, env=env, stdout=output, stderr=subprocess.STDOUT)
                while proc.poll() is None:
                    minimum = min(minimum, available())
                    if minimum < RESERVE:
                        pressure = True
                        raise RuntimeError("H1 reserve pressure")
                    time.sleep(0.25)
                rc = proc.wait()
                peak = int(docker("exec", CONTAINER, "cat", "/sys/fs/cgroup/memory.peak"))
        except BaseException as exc:
            was_interrupted, error = True, type(exc).__name__ + ": " + str(exc)
        finally:
            if was_interrupted or pressure or rc != 0:
                # Keep the lock until the owned workload is confirmed stopped.
                signal.signal(signal.SIGTERM, signal.SIG_IGN)
                signal.signal(signal.SIGINT, signal.SIG_IGN)
                while True:
                    subprocess.run(DOCKER + ["kill", CONTAINER], env=env, check=False,
                                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                    try:
                        if docker("inspect", CONTAINER, "--format", "{{.State.Running}}") == "false":
                            break
                    except subprocess.CalledProcessError:
                        pass
                    time.sleep(0.25)
                if proc is not None:
                    try:
                        proc.wait(timeout=2)
                    except subprocess.TimeoutExpired:
                        proc.kill(); proc.wait()
            receipt = {"command": command, "exit": rc, "elapsed_seconds": time.monotonic()-start,
                "minimum_parent_available_bytes": minimum, "pressure_stop": pressure,
                "interrupted": was_interrupted, "error": error,
                "memory_limit_bytes": 12884901888, "swap_limit_bytes": 0,
                "container_cumulative_peak_bytes": peak, "log": str(log),
                "log_sha256": hashlib.sha256(log.read_bytes()).hexdigest(),
                "input_hashes": snapshot, "lean_version": lean_version, "lake_version": lake_version,
                "checked_head": head, "git_status_before": before}
            log.with_suffix(log.suffix + ".json").write_text(json.dumps(receipt, indent=2) + "\n")
            print(json.dumps({k: receipt[k] for k in ("command", "exit", "elapsed_seconds",
            "minimum_parent_available_bytes", "pressure_stop", "interrupted", "log")}))
        raise SystemExit(1 if pressure or was_interrupted else rc)

if __name__ == "__main__":
    main()
