#!/usr/bin/env python3
"""Run one audit gate with exclusive lock, explicit SDK and serial resource guards.

No systemd-run. Default VM mode retains its 16GiB cgroup and 4GiB reserve.
Explicit host mode requires an existing <=12GiB zero-swap cgroup and preserves
12GiB host MemAvailable. Both modes enforce child RLIMIT_AS=12GiB, continuous
aggregate descendant/argv observations, proof/group deadlines and a 14400s window.
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
import importlib.util

_policy_spec=importlib.util.spec_from_file_location("audit_runtime_policy",Path(__file__).with_name("runtime_policy.py"))
_policy_bytes=Path(_policy_spec.origin).read_bytes()
policy=importlib.util.module_from_spec(_policy_spec)
exec(compile(_policy_bytes,_policy_spec.origin,"exec"),policy.__dict__)

ROOT = Path(__file__).resolve().parents[4]
TOOL = policy.DEFAULT_SDK/"bin"  # Compatibility default; main resolves explicit SDK.
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
    p.add_argument("--mode", choices=["vm", "host"], default="vm")
    p.add_argument("--sdk", type=Path)
    p.add_argument("--proof-timeout", type=int)
    p.add_argument("--evidence", type=Path, required=True)
    p.add_argument("--tag", required=True)
    p.add_argument("--timeout", type=int, default=3600)
    p.add_argument("command", nargs=argparse.REMAINDER)
    args = p.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    policy.require(bool(command), "empty gate command")
    policy.require(0 < args.timeout <= policy.WINDOW, "group deadline exceeds 14400s window")
    proof_timeout=args.proof_timeout if args.proof_timeout is not None else args.timeout
    policy.require(0 < proof_timeout <= args.timeout, "invalid proof deadline")
    if any(Path(x).name == "lean" for x in command):
        policy.require("--version" in command or ("-j1" in command and not any((x.startswith("-j") and x!="-j1") or x.startswith("--threads") for x in command)), "direct Lean requires explicit -j1 only")
    args.evidence.mkdir(parents=True, exist_ok=True)
    lockdir = Path("/tmp/solidity-lean-feature-groups-20261025")
    lockdir.mkdir(exist_ok=True)
    lock = (lockdir/"writer.lock").open("a")
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    status = subprocess.check_output(["git", "status", "--short", "--branch"], cwd=ROOT, text=True)
    runtime_pins={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__).resolve(),Path(policy.__file__).resolve()]}
    runtime_pins[str(Path(policy.__file__).resolve())]=hashlib.sha256(_policy_bytes).hexdigest()
    guards=policy.Guards(args.mode)
    sdk,tool_versions=policy.sdk_configuration(args.mode,args.sdk,ROOT)
    tool=sdk/"bin"
    runtime_pins[str(tool/"lean")]=tool_versions["lean_binary_sha256"]
    runtime_pins[str(tool/"lake")]=tool_versions["lake_binary_sha256"]
    runtime_pins[str(ROOT/"lean-toolchain")]=tool_versions["toolchain_file_sha256"]
    window=policy.AggregateWindow()
    spent=window.spent
    # Alternate TOML changes resource flags only and leaves the tracked lakefile intact.
    config = args.evidence/"bounded-lakefile.toml"
    config.write_text('weakLeanArgs = ["-j1"]\n' + (ROOT/"lakefile.toml").read_text())
    shimdir = args.evidence/"bin"
    shimdir.mkdir(exist_ok=True)
    shim = shimdir/"lake"
    import shlex
    shim.write_text("#!/bin/sh\nexec " + shlex.quote(str(tool/"lake")) +
        " -f " + shlex.quote(str(config)) + ' "$@"\n')
    shim.chmod(0o755)
    env = {k:v for k,v in os.environ.items() if not k.startswith(("LEAN_","ELAN_"))}
    env.update(LEAN_NUM_THREADS="1", LEAN_SYSROOT=str(sdk),
        AUDIT_LEAN_SDK=str(sdk), AUDIT_RESOURCE_MODE=args.mode)
    if args.mode=="vm":
        env.update(XDG_CACHE_HOME="/workspace/.setup/cache",
            SOLKEY_RULES="/workspace/.setup/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key")
    env["PATH"] = str(shimdir)+":"+str(tool)+":"+env["PATH"]
    input_hashes = {str((ROOT/arg).resolve()): hashlib.sha256((ROOT/arg).read_bytes()).hexdigest()
        for arg in command if arg.endswith(".lean") and (ROOT/arg).is_file()}
    def setup():
        os.setsid()
        resource.setrlimit(resource.RLIMIT_AS, (CAP, CAP))
        signal.pthread_sigmask(signal.SIG_SETMASK, launch_mask)
    logpath = args.evidence/(args.tag+".log")
    start = time.monotonic()
    peak = 0
    proof_started={}
    policy.subreaper()
    samples=(args.evidence/(args.tag+"-observations.jsonl")).open("w")
    reason = None
    deadline=window.reserve(args.timeout)
    def interrupted(signum,frame):raise InterruptedError("monitor signal "+str(signum))
    signal.signal(signal.SIGTERM,interrupted)
    signal.signal(signal.SIGHUP,interrupted)
    with logpath.open("w") as log:
        log.write("command="+json.dumps(command)+"\n"+status)
        log.flush()
        launch_mask=signal.pthread_sigmask(signal.SIG_BLOCK,{signal.SIGINT,signal.SIGTERM,signal.SIGHUP})
        try:
            child = subprocess.Popen(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT, preexec_fn=setup)
        except BaseException:
            signal.pthread_sigmask(signal.SIG_SETMASK,launch_mask)
            raise
        tracker=policy.Descendants(child.pid)
        def owned():return tracker.sample()
        def live(rows):return [r for r in rows if r["state"]!="Z"]
        try:
            # Pending launch signals are delivered only inside owned cleanup.
            signal.pthread_sigmask(signal.SIG_SETMASK,launch_mask)
            while child.poll() is None:
                members=owned()
                rss=sum(r["rss"] for r in members);peak=max(peak,rss)
                sample=guards.sample()
                samples.write(json.dumps({"elapsed":time.monotonic()-start,"members":members,"guards":sample})+"\n");samples.flush()
                reason=policy.serial_reason(members,time.monotonic(),proof_started,proof_timeout,tool/"lean")
                if rss>CAP:reason="aggregate descendant RSS cap"
                if time.monotonic()-start>deadline:reason="group/aggregate window deadline"
                if reason:
                    break
                time.sleep(0.5)
            if not reason and live(owned()):
                reason = "owned descendants remain after command exit"
        except BaseException as err:
            reason = "monitor interrupted: " + type(err).__name__ + ": " + str(err)
        finally:
            # Capture the root exit before reaping any adopted orphan.
            if reason or child.poll() is None:
                try:os.killpg(child.pid,signal.SIGTERM)
                except ProcessLookupError:pass
                except BaseException as err:reason="cleanup signal interrupted: "+str(err)
                # SIGKILL/identity cleanup is handled without observation unwind.
                failures=policy.drain_owned(tracker,child.pid,note=lambda msg: log.write(msg+"\n"))
            else:
                failures=policy.drain_owned(tracker,child.pid,note=lambda msg: log.write(msg+"\n"))
            code=child.wait()
            if failures:reason="cleanup observation failures: "+"; ".join(failures)
            while True:
                try:
                    if os.waitpid(-1,os.WNOHANG)[0]==0:break
                except ChildProcessError:break
    samples.close()
    elapsed=time.monotonic()-start
    window.finish(elapsed)
    try:
        for name,pin in runtime_pins.items():
            if hashlib.sha256(Path(name).read_bytes()).hexdigest()!=pin:reason="guard/SDK input changed: "+name
    except OSError as err:reason="guard/SDK input unavailable: "+str(err)
    gate_exit = code if code > 0 else (1 if reason or code else 0)
    result = dict(command=command, child_exit=code, gate_exit=gate_exit, status="pass" if gate_exit == 0 else "fail", seconds=round(time.monotonic()-start, 3),
        peak_aggregate_rss_bytes=peak, stop_reason=reason, log=str(logpath),
        resource_mode=args.mode, initial_guards=guards.initial, aggregate_window_seconds=spent+elapsed, aggregate_window_state=str(window.path), proof_timeout_seconds=proof_timeout,
        resource_flags="LEAN_NUM_THREADS=1; package weakLeanArgs=-j1; RLIMIT_AS=12GiB; swap=0; reserve="+("12GiB host available" if args.mode=="host" else "4GiB VM cgroup"),
        config=str(config), log_sha256=hashlib.sha256(logpath.read_bytes()).hexdigest(),
        input_source_sha256=input_hashes, runtime_input_sha256=runtime_pins, observations_sha256=hashlib.sha256(Path(samples.name).read_bytes()).hexdigest(), observations=str(args.evidence/(args.tag+"-observations.jsonl")), **tool_versions)
    (args.evidence/(args.tag+".json")).write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result))
    raise SystemExit(gate_exit)


if __name__ == "__main__":
    main()
