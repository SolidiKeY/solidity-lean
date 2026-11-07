#!/usr/bin/env python3
"""Run a single audit gate with exclusive lock, -j1, no swap, 4GiB reserve.

No systemd-run. Uses the VM's 16GiB cgroup, RLIMIT_AS=12GiB for
children, aggregate RSS/current-memory guards, and a per-command timeout.
Outputs (including the alternate Lake config) stay in an off-git directory.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
TOOL = Path("/workspace/.setup/tools/lean-4.24.0-linux/bin")
CAP = 12 * 1024**3
RESERVE = 4 * 1024**3


def processes(group):
    members = []
    for item in Path("/proc").iterdir():
        if not item.name.isdecimal():
            continue
        try:
            pid = int(item.name)
            if os.getpgid(pid) != group:
                continue
            status = (item/"status").read_text().splitlines()
            rss = sum(int(x.split()[1])*1024 for x in status if x.startswith("VmRSS:"))
            exe = (item/"exe").resolve().name
            members.append((pid, exe, rss))
        except (OSError, ProcessLookupError):
            pass
    return members


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--evidence", type=Path, required=True)
    p.add_argument("--tag", required=True)
    p.add_argument("--timeout", type=int, default=3600)
    p.add_argument("command", nargs=argparse.REMAINDER)
    args = p.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    assert command
    if any(Path(x).name == "lean" for x in command):
        assert "-j1" in command or "--version" in command, "direct Lean requires explicit -j1"
    args.evidence.mkdir(parents=True, exist_ok=True)
    lockdir = Path("/tmp/solidity-lean-feature-groups-20261025")
    lockdir.mkdir(exist_ok=True)
    lock = (lockdir/"writer.lock").open("a")
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    status = subprocess.check_output(["git", "status", "--short", "--branch"], cwd=ROOT, text=True)
    # Alternate TOML changes resource flags only and leaves the tracked lakefile intact.
    config = args.evidence/"bounded-lakefile.toml"
    config.write_text('weakLeanArgs = ["-j1"]\n' + (ROOT/"lakefile.toml").read_text())
    shimdir = args.evidence/"bin"
    shimdir.mkdir(exist_ok=True)
    shim = shimdir/"lake"
    import shlex
    shim.write_text("#!/bin/sh\nexec " + shlex.quote(str(TOOL/"lake")) +
        " -f " + shlex.quote(str(config)) + ' "$@"\n')
    shim.chmod(0o755)
    env = dict(os.environ, LEAN_NUM_THREADS="1", XDG_CACHE_HOME="/workspace/.setup/cache",
        SOLKEY_RULES="/workspace/.setup/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key")
    env["PATH"] = str(shimdir)+":"+str(TOOL)+":"+env["PATH"]
    cg = Path("/sys/fs/cgroup")
    limit = (cg/"memory.max").read_text().strip()
    assert limit != "max" and int(limit) >= CAP+RESERVE, "VM cap smaller than job+reserve"
    assert int((cg/"memory.swap.current").read_text()) == 0
    assert all(int(x.split()[1]) == 0 for x in Path("/proc/meminfo").read_text().splitlines() if x.startswith("SwapTotal:")), "swap must be disabled"
    assert int((cg/"memory.current").read_text()) < int(limit)-RESERVE, "insufficient preflight reserve"
    tool_versions = {
        "lean_version": subprocess.check_output([str(TOOL/"lean"), "--version"], text=True).strip(),
        "lake_version": subprocess.check_output([str(TOOL/"lake"), "--version"], text=True).strip(),
        "lean_binary_sha256": hashlib.sha256((TOOL/"lean").read_bytes()).hexdigest(),
        "lake_binary_sha256": hashlib.sha256((TOOL/"lake").read_bytes()).hexdigest(),
        "toolchain_file_sha256": hashlib.sha256((ROOT/"lean-toolchain").read_bytes()).hexdigest(),
    }
    input_hashes = {str((ROOT/arg).resolve()): hashlib.sha256((ROOT/arg).read_bytes()).hexdigest()
        for arg in command if arg.endswith(".lean") and (ROOT/arg).is_file()}
    def setup():
        os.setsid()
        resource.setrlimit(resource.RLIMIT_AS, (CAP, CAP))
    logpath = args.evidence/(args.tag+".log")
    start = time.monotonic()
    peak = 0
    reason = None
    with logpath.open("w") as log:
        log.write("command="+json.dumps(command)+"\n"+status)
        log.flush()
        child = subprocess.Popen(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT, preexec_fn=setup)
        try:
            while child.poll() is None:
                members = processes(child.pid)
                rss = sum(r[2] for r in members)
                peak = max(peak, rss)
                if sum(exe == "lean" for _, exe, _ in members) > 1:
                    reason = "multiple Lean processes; serial gate required"
                if rss > CAP or int((cg/"memory.current").read_text()) > int(limit)-RESERVE:
                    reason = "memory cap/reserve guard"
                if int((cg/"memory.swap.current").read_text()) != 0:
                    reason = "swap guard"
                if time.monotonic()-start > args.timeout:
                    reason = "wall timeout"
                if reason:
                    break
                time.sleep(0.5)
            if not reason and processes(child.pid):
                reason = "owned descendants remain after command exit"
        except BaseException as err:
            reason = "monitor interrupted: " + type(err).__name__
        finally:
            # Signal the entire OWNED group even if its leader exited already.
            # Never release the writer lock with a live descendant left behind.
            if reason or child.poll() is None:
                try:
                    os.killpg(child.pid, signal.SIGTERM)
                except ProcessLookupError:
                    pass
                time.sleep(0.5)
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            code = child.wait()
            for _ in range(20):
                if not any(rss > 0 for _, _, rss in processes(child.pid)):
                    break
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                time.sleep(0.1)
            while any(rss > 0 for _, _, rss in processes(child.pid)):
                # Retain this process AND flock until every live owned child
                # drains, including an uninterruptible kernel wait. Never raise
                # here: an exception would release the lock too early.
                reason = "waiting for owned process group to drain"
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                time.sleep(1)
    gate_exit = code if code > 0 else (1 if reason or code else 0)
    result = dict(command=command, child_exit=code, gate_exit=gate_exit, status="pass" if gate_exit == 0 else "fail", seconds=round(time.monotonic()-start, 3),
        peak_aggregate_rss_bytes=peak, stop_reason=reason, log=str(logpath),
        resource_flags="LEAN_NUM_THREADS=1; package weakLeanArgs=-j1; RLIMIT_AS=12GiB; VM=16GiB; swap=0; reserve=4GiB",
        config=str(config), log_sha256=hashlib.sha256(logpath.read_bytes()).hexdigest(),
        input_source_sha256=input_hashes, **tool_versions)
    (args.evidence/(args.tag+".json")).write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result))
    raise SystemExit(gate_exit)


if __name__ == "__main__":
    main()
