#!/usr/bin/env python3
"""One bounded, per-file Lean MCP diagnostic using a private serial launcher.
Run with the repository .venv/bin/python (mcp is installed there).
"""
import argparse
import asyncio
import fcntl
import json
import os
import hashlib
from pathlib import Path
import subprocess
import signal
import sys
from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client

parser = argparse.ArgumentParser()
parser.add_argument("--toolchain", type=Path, required=True)
parser.add_argument("--output", type=Path, required=True)
args = parser.parse_args()
root = Path.cwd()
fixture = "tests/h62/item6/migrate-backend/TernaryDependency.lean"
allowed = [Path("/workspace/migrate-backend-toolchains/lean-4.35.0-linux"),
           Path("/workspace/.setup/tools/lean-4.24.0-linux")]
if args.toolchain.resolve() not in allowed: raise RuntimeError("unapproved toolchain")
lock = Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock").open("a")
fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
subprocess.run(["git", "status", "--short"], check=True)
args.output.mkdir(parents=True, exist_ok=False)
args.output = args.output.resolve()
shimdir = args.output/"bin"
shimdir.mkdir()
lake = str(args.toolchain.resolve()/"bin/lake")
(shimdir/"lake").write_text('#!/bin/bash\nif [ "$1" = serve ]; then\n exec '+lake+' "$@" --tstack=131072 -j1 -M12288\nelse\n exec '+lake+' "$@"\nfi\n')
(shimdir/"lake").chmod(0o700)
env = dict(os.environ, LEAN_NUM_THREADS="1", LEAN_LSP_MAX_OPEN_FILES="1",
           PATH=str(shimdir)+":"+str(args.toolchain.resolve()/"bin")+":"+os.environ["PATH"],
           LEAN_PROJECT_PATH=str(root))
cap = 12*1024**3
reserve = 4*1024**3
limit = int(Path("/sys/fs/cgroup/memory.max").read_text())
if limit < cap+reserve or Path("/proc/swaps").read_text().splitlines()[1:]:
    raise RuntimeError("insufficient memory cap or swap enabled")
peak_cgroup = 0
def guard():
    global peak_cgroup
    current = int(Path("/sys/fs/cgroup/memory.current").read_text())
    peak_cgroup = max(peak_cgroup, current)
    available = int(next(line.split()[1] for line in Path("/proc/meminfo").read_text().splitlines() if line.startswith("MemAvailable:")))*1024
    if current > min(cap,limit-reserve) or available < reserve:
        raise RuntimeError("RESOURCE_STOP")
guard()
async def monitor():
    while True:
        guard()
        await asyncio.sleep(0.25)
versions = {name: subprocess.check_output([str(args.toolchain/"bin"/name),"--version"],text=True).strip() for name in ("lean","lake")}
async def diagnose():
    server = StdioServerParameters(command=sys.executable, args=["-m","lean_lsp_mcp","--lean-project-path",str(root)], cwd=str(root),env=env)
    async with stdio_client(server) as (read, write):
        async with ClientSession(read,write) as session:
            await session.initialize()
            result = await session.call_tool("lean_diagnostic_messages", {"file_path":fixture,"interactive":False,"timeout_s":90})
            data = {"versions":versions,"tool":"lean_diagnostic_messages","file":fixture,
                    "result":result.model_dump(mode="json"),
                    "fixture_sha256":hashlib.sha256((root/fixture).read_bytes()).hexdigest(),
                    "peak_cgroup_bytes":peak_cgroup,"memory_cap_bytes":cap,"reserve_bytes":reserve,
                    "boundary":"per-file fixture check; no runtime or migration gate pass"}
            (args.output/"result.json").write_text(json.dumps(data,indent=2)+"\n")
            print(json.dumps({"versions":versions,"evidence":str(args.output/"result.json")}))
            details = result.structuredContent.get("result", {}) if result.structuredContent else {}
            if result.isError or not details.get("success") or details.get("partial") or details.get("timed_out"):
                raise RuntimeError("MCP diagnostics failed or incomplete")
async def main():
    call = asyncio.create_task(diagnose())
    watch = asyncio.create_task(monitor())
    loop = asyncio.get_running_loop()
    for sig in (signal.SIGTERM, signal.SIGHUP):
        loop.add_signal_handler(sig, call.cancel)
    try:
        async with asyncio.timeout(120):
            done, pending = await asyncio.wait([call,watch], return_when=asyncio.FIRST_COMPLETED)
            if watch in done: await watch
            await call
    finally:
        for task in (call,watch):
            if not task.done(): task.cancel()
        await asyncio.gather(call,watch,return_exceptions=True)
asyncio.run(main())
