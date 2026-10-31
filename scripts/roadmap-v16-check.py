#!/usr/bin/env python3
"""Run a V16 check in the established 12GiB/no-swap local Docker cgroup.
No toolchain/network/dependency setup. A single task-owned temporary Lake
configuration appends -j1; tracked configurations and proof budgets are untouched.
"""
import argparse, fcntl, os, pathlib, shlex, subprocess

ROOT = pathlib.Path(__file__).resolve().parents[1]
BASE = "2fe1f8932f96be15b00df03ba2cde46f64a87758"
BRANCH = "codex/solidity-v12-v17-20261031/v16-correctness-transfer"
IMAGE = "ubuntu@sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852"

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--log", type=pathlib.Path, required=True)
    ap.add_argument("command", nargs=argparse.REMAINDER)
    args = ap.parse_args()
    cmd = args.command
    if cmd[:1] == ["--"]: cmd = cmd[1:]
    if not cmd or cmd[0] != "lake": ap.error("only direct lake commands are supported")
    if cmd[1:3] == ["env", "lean"] and "-j1" not in cmd:
        ap.error("direct lean via lake env requires explicit -j1")
    env = os.environ.copy()
    for k in ["DOCKER_HOST", "DOCKER_CONTEXT", "DOCKER_TLS", "DOCKER_TLS_VERIFY", "DOCKER_CERT_PATH"]:
        env.pop(k, None)
    lock = pathlib.Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")
    with lock.open("a") as lk, args.log.open("x") as log:
        fcntl.flock(lk, fcntl.LOCK_EX | fcntl.LOCK_NB)
        if subprocess.check_output(["git", "branch", "--show-current"], cwd=ROOT, text=True).strip() != BRANCH:
                ap.error("wrong branch")
        subprocess.run(["git", "merge-base", "--is-ancestor", BASE, "HEAD"], cwd=ROOT, check=True)
        log.write("Locked checkout status:\n" + subprocess.check_output(["git", "status", "--short", "--branch"], cwd=ROOT, text=True)); log.flush()
        alt = ROOT / "lakefile.v16-runtime.toml"
        # Exclusive creation protects unexpected local work.
        with alt.open("x") as f:
            f.write((ROOT / "lakefile.toml").read_text().replace(
                'weakLeanArgs = ["--tstack=131072"]',
                'weakLeanArgs = ["--tstack=131072", "-j1"]'))
        try:
            if cmd[0] == "lake": cmd[1:1] = ["-f", alt.name]
            monitor = "(while true; do awk '/^VmRSS:/ {t += $2} END {print \"RSS_KiB=\" t}' /proc/[0-9]*/status; sleep 0.1; done) & mon=$!; "
            shell = '[ \"$(cat /sys/fs/cgroup/memory.max)\" = 12884901888 ] && [ \"$(cat /sys/fs/cgroup/memory.swap.max)\" = 0 ] || exit 91; cat /sys/fs/cgroup/memory.max /sys/fs/cgroup/memory.swap.max; ' + monitor + shlex.join(cmd) + '; r=$?; kill "$mon"; wait "$mon" 2>/dev/null; cat /sys/fs/cgroup/memory.peak; exit "$r"'
            argv = ["docker", "--host=unix:///var/run/docker.sock", "run", "--rm", "--network=none",
                "--memory=12g", "--memory-swap=12g", "--user", "1000:1000",
                "--mount", "type=bind,src=/workspace,dst=/workspace", "-w", str(ROOT),
                "-e", "LEAN_NUM_THREADS=1", "-e", "PATH=/workspace/.setup/tools/lean-4.24.0-linux/bin:/usr/bin:/bin",
                IMAGE, "sh", "-c", shell]
            log.write("$ " + shlex.join(argv) + "\n"); log.flush()
            r = subprocess.run(argv, env=env, stdout=log, stderr=subprocess.STDOUT)
            log.write("exit=" + str(r.returncode) + "\n")
            return r.returncode
        finally:
            alt.unlink()

if __name__ == "__main__": raise SystemExit(main())
