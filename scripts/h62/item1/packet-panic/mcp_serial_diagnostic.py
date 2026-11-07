#!/usr/bin/env python3
"""Build the staged PanicBytes helper and its closure using the Lean MCP build tool.

The caller holds the repository writer lock. This process imposes a 12 GiB
per-process address-space limit on itself and descendants. The monitored cgroup reserve is sampled, not a hard aggregate cap.
"""
import argparse
import asyncio
import ctypes
import os
import resource
import re
from pathlib import Path
import signal
import sys
import time
from diagnostic_policy import validated_target

root = Path(__file__).resolve().parents[4]
parser = argparse.ArgumentParser()
parser.add_argument("--project", type=Path, default=root / "tests/h62/item1/packet-panic/closure-project-retry")
parser.add_argument("--diagnostic", type=Path, help="optional Lean file for a per-file MCP diagnostic after a successful build")
args = parser.parse_args()
project = args.project.resolve(strict=True)
allowed_projects = {
    root / "tests/h62/item1/packet-panic/closure-project-retry",
    Path("/workspace/h62-packet-panic-overlay-2a18/tests/h62/item1/packet-panic/closure-project-overlay"),
}
if project not in allowed_projects:
    raise SystemExit("project is outside the two authorized isolated diagnostic paths")
target = validated_target(project, args.diagnostic) if args.diagnostic else None
from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import get_default_environment, stdio_client
print(f"isolated project: {project}", flush=True)
if (project / ".lake").exists():
    raise SystemExit("isolated cache already exists; preserve it and use a fresh isolated project")
resource.setrlimit(resource.RLIMIT_AS, (12 * 1024**3, 12 * 1024**3))
shim = Path("/workspace/h62-packet-panic-postmerge-evidence/serial-toolchain")
if not (shim / "bin/lean").is_file():
    raise SystemExit("serial toolchain view is missing")
cap_text = Path("/sys/fs/cgroup/memory.max").read_text().strip()
if cap_text == "max" or len(Path("/proc/swaps").read_text().splitlines()) != 1:
    raise SystemExit("finite cgroup memory cap and zero swap are required")
limit = min(12 * 1024**3, int(cap_text) - 4 * 1024**3)
cgroup = Path("/sys/fs/cgroup/memory.current")
if limit <= 0 or int(cgroup.read_text()) >= limit:
    raise SystemExit("insufficient cgroup headroom")
libc = ctypes.CDLL(None, use_errno=True)
if libc.prctl(36, 1, 0, 0, 0) != 0:
    raise SystemExit(f"cannot enable child subreaper: errno={ctypes.get_errno()}")

env = get_default_environment()
env.update({"PATH": str(root / "scripts/h62/item1/packet-panic/bin") + ":" + str(shim / "bin") + ":" + env.get("PATH", ""),
            "LEAN_SYSROOT": str(shim), "LAKE_OVERRIDE_LEAN": "true", "LAKE_NO_CACHE": "true", "LAKE_CACHE_DIR": "",
            "LEAN_NUM_THREADS": "1", "LEAN_LSP_MAX_OPEN_FILES": "1", "LEAN_REPL": "0", "LEAN_PROJECT_PATH": str(project),
            "LEAN_MCP_DISABLED_TOOLS": "lean_leansearch,lean_loogle,lean_leanfinder,lean_state_search,lean_hammer_premise,lean_get_widgets,lean_get_widget_source"})
peak = int(cgroup.read_text())
observed_lean = set()

def host_available_bytes():
    for line in Path("/proc/meminfo").read_text().splitlines():
        if line.startswith("MemAvailable:"):
            return int(line.split()[1]) * 1024
    raise RuntimeError("host MemAvailable is unavailable")

if host_available_bytes() < 4 * 1024**3:
    raise SystemExit("host available-memory reserve is below 4 GiB")

def live_lean_pids():
    result = []
    for proc in Path("/proc").iterdir():
        if not proc.name.isdigit():
            continue
        try:
            if (proc / "comm").read_text().strip() != "lean":
                continue
            if (proc / "stat").read_text().split()[2] != "Z":
                result.append(int(proc.name))
        except FileNotFoundError:
            continue
    return result

if live_lean_pids():
    raise SystemExit("a live Lean process already exists; do not start another job")

server = StdioServerParameters(command="/workspace/solidity-lean/.venv/bin/python", args=["-m", "lean_lsp_mcp", "--lean-project-path", str(project)], env=env, cwd=str(root))

async def diagnose():
    async with stdio_client(server) as (read, write):
        async with ClientSession(read, write) as session:
            await session.initialize()
            result = await session.call_tool("lean_build", {"lean_project_path": str(project), "clean": False, "fetch_cache": False, "output_lines": 1000000})
            print(result.model_dump_json(indent=2), flush=True)
            payload = result.structuredContent or {}
            build = payload.get("result", payload)
            output = build.get("output", "")
            if (result.isError or not build.get("success") or build.get("errors") or
                    len(output.splitlines()) >= 1000000):
                raise RuntimeError("isolated helper build failed or output may be truncated")
            has_warnings = bool(re.search(r"(?im)(?:\bwarning:|^\s*warn\b|⚠)", output))
            artifact = project / ".lake/build/lib/lean/PanicBytes.olean"
            if not artifact.is_file():
                raise RuntimeError("build reported success but target olean is missing")
            if target is not None:
                diagnostic = await session.call_tool("lean_diagnostic_messages", {"file_path": str(target), "interactive": False, "timeout_s": 120})
                print(diagnostic.model_dump_json(indent=2), flush=True)
                details = (diagnostic.structuredContent or {}).get("result", {})
                problems = [item for item in details.get("items", []) if item.get("severity") in ("error", "warning") or "out of date" in item.get("message", "").lower()]
                if diagnostic.isError or not details.get("success") or details.get("partial") or details.get("timed_out") or details.get("failed_dependencies") or problems:
                    raise RuntimeError("per-file diagnostic failed, was incomplete or reported warnings")
            if has_warnings:
                raise RuntimeError("isolated helper build reported warnings")

async def guard():
    global peak
    while True:
        current = int(cgroup.read_text())
        peak = max(peak, current)
        if current >= limit:
            raise RuntimeError("cgroup headroom guard reached")
        if host_available_bytes() < 4 * 1024**3:
            raise RuntimeError("host available-memory reserve reached")
        if len(Path("/proc/swaps").read_text().splitlines()) != 1:
            raise RuntimeError("swap became available during the build")
        pids = live_lean_pids()
        if len(pids) > 1:
            raise RuntimeError("more than one live Lean process observed")
        for pid in pids:
            try:
                raw = (Path("/proc") / str(pid) / "cmdline").read_bytes()
            except FileNotFoundError:
                continue
            args = [part.decode("utf-8", "replace") for part in raw.split(b"\0") if part]
            if args and "-j1" not in args:
                raise RuntimeError(f"observed Lean process {pid} without explicit -j1")
            if args and len(observed_lean) < 50:
                observed_lean.add(" ".join(args))
        await asyncio.sleep(0.25)

async def main():
    job = asyncio.create_task(diagnose())
    watch = asyncio.create_task(guard())
    try:
        done, _ = await asyncio.wait({job, watch}, timeout=3600, return_when=asyncio.FIRST_COMPLETED)
        if not done:
            raise TimeoutError("diagnostic exceeded one hour")
        for task in done:
            await task
    finally:
        job.cancel()
        watch.cancel()
        await asyncio.gather(job, watch, return_exceptions=True)


def cleanup_adopted():
    """Reap or stop only children adopted by this subreaper, not other sessions."""
    children_file = Path(f"/proc/{os.getpid()}/task/{os.getpid()}/children")
    for sig in (signal.SIGTERM, signal.SIGKILL):
        deadline = time.monotonic() + 5
        while time.monotonic() < deadline:
            try:
                pid, _ = os.waitpid(-1, os.WNOHANG)
            except ChildProcessError:
                return
            if pid:
                continue
            for child in children_file.read_text().split():
                try:
                    os.kill(int(child), sig)
                except ProcessLookupError:
                    pass
            time.sleep(0.05)
    raise RuntimeError("owned child cleanup did not finish; inspect before another Lean job")

try:
    asyncio.run(main())
finally:
    print(f"sampled cgroup peak bytes: {peak}; sampled reserve bytes: {int(cap_text) - peak}", flush=True)
    for command in sorted(observed_lean):
        print(f"sampled Lean command: {command}", flush=True)
    cleanup_adopted()
