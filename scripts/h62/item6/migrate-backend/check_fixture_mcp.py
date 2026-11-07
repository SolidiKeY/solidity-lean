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
import shlex
import sys
from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client
from census import imports, is_toolchain_module

parser = argparse.ArgumentParser()
parser.add_argument("--toolchain", type=Path, required=True)
parser.add_argument("--output", type=Path, required=True)
parser.add_argument("--file", type=Path, default=Path("tests/h62/item6/migrate-backend/TernaryDependency.lean"))
parser.add_argument("--build-dir", type=Path, help="Explicit dependency artifact selection; provenance must be validated separately")
args = parser.parse_args()
root = Path.cwd().resolve()
allowed = [Path("/workspace/migrate-backend-toolchains/lean-4.35.0-linux"),
           Path("/workspace/.setup/tools/lean-4.24.0-linux")]
if args.toolchain.resolve() not in allowed: raise RuntimeError("unapproved toolchain")
lock = Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock").open("a")
fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
subprocess.run(["git", "status", "--short"], check=True)
source = args.file.resolve()
if not source.is_relative_to(root) or source.suffix != ".lean" or not source.is_file():
    raise RuntimeError("diagnostic target must be an existing Lean file inside the checkout")
fixture = str(source.relative_to(root))
project_imports = [module for module in imports(source.read_text()) if not is_toolchain_module(module)]
if project_imports and args.build_dir is None:
    raise RuntimeError("project imports require explicit --build-dir; implicit checkout cache is not accepted")
if args.build_dir is not None:
    args.build_dir = args.build_dir.resolve()
    if not args.build_dir.is_dir(): raise RuntimeError("dependency build directory is absent")
args.output.mkdir(parents=True, exist_ok=False)
args.output = args.output.resolve()
shimdir = args.output/"bin"
shimdir.mkdir()
toolchain = args.toolchain.resolve()
lake = str(toolchain/"bin/lake")
selected_build = args.build_dir if args.build_dir is not None else args.output/"empty-build"
config = (root/"lakefile.toml").read_text().replace("enableArtifactCache = true", "enableArtifactCache = false")
config = "buildDir = "+json.dumps(str(selected_build))+"\nsrcDir = "+json.dumps(str(root))+"\n"+config
config = config.replace('weakLeanArgs = ["--tstack=131072"]', 'weakLeanArgs = ["--tstack=131072", "-j1", "-M8192"]')
config_path = args.output/"lakefile.toml"
config_path.write_text(config)
# --no-build is forwarded even for server-initiated setup-file. A private
# sysroot wrapper restores LAKE after Lake.serve overwrites its environment.
lake_args = ["--no-build", "--no-cache", "-d", str(root), "-f", str(config_path)]
launch = shlex.join([lake, *lake_args])
lake_shim = shimdir/"lake"
lake_shim.write_text('#!/bin/bash\nif [ "$1" = serve ]; then\n exec '+launch+' "$@" --tstack=131072 -j1 -M8192\nelse\n exec '+launch+' "$@"\nfi\n')
lake_shim.chmod(0o700)
sysroot = args.output/"sysroot"
sysroot.mkdir();(sysroot/"bin").mkdir()
for entry in toolchain.iterdir():
    if entry.name != "bin": (sysroot/entry.name).symlink_to(entry,target_is_directory=entry.is_dir())
for entry in (toolchain/"bin").iterdir():
    if entry.name not in ("lean","lake"): (sysroot/"bin"/entry.name).symlink_to(entry)
(sysroot/"bin/lake").symlink_to(lake_shim)
lean_shim = sysroot/"bin/lean"
lean_shim.write_text('#!/bin/bash\nexport LAKE='+shlex.quote(str(lake_shim))+'\nexec '+shlex.quote(str(toolchain/"bin/lean"))+' -j1 "$@" -j1 -M8192\n')
lean_shim.chmod(0o700)
env = dict(os.environ, LEAN_NUM_THREADS="1", LEAN_LSP_MAX_OPEN_FILES="1",
           PATH=str(shimdir)+":"+str(toolchain/"bin")+":"+os.environ["PATH"],
           LEAN_PROJECT_PATH=str(root), LEAN_SYSROOT=str(sysroot), LEAN=str(lean_shim),
           LAKE_OVERRIDE_LEAN="true", LAKE=str(lake_shim), LEAN_PATH="", LEAN_SRC_PATH="",
           LAKE_NO_CACHE="1", LAKE_ARTIFACT_CACHE="0", LAKE_CACHE_DIR=str(args.output/"unused-cache"))
env["ELAN_TOOLCHAIN"] = "leanprover/lean4:v4.35.0" if toolchain.name == "lean-4.35.0-linux" else "leanprover/lean4:v4.24.0"
env.pop("LEAN_GITHASH",None)
env.pop("LAKE_HOME",None)
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
                    "fixture_sha256":hashlib.sha256(source.read_bytes()).hexdigest(),
                    "dependency_build_dir":str(args.build_dir) if args.build_dir is not None else None,
                    "project_imports":project_imports,
                    "dependency_build_policy":"configured: private --no-build --no-cache wrapper; runtime enforcement requires independent verification",
                    "dependency_provenance":"explicit directory selection only; require separate validated source/toolchain/artifact manifest before API or migration acceptance",
                    "peak_cgroup_bytes":peak_cgroup,"memory_cap_bytes":cap,"module_lean_memory_limit_mib":8192,"reserve_bytes":reserve,
                    "boundary":"per-file fixture check; no runtime or migration gate pass"}
            (args.output/"result.json").write_text(json.dumps(data,indent=2)+"\n")
            print(json.dumps({"versions":versions,"evidence":str(args.output/"result.json")}))
            details = result.structuredContent.get("result", {}) if result.structuredContent else {}
            if result.isError or not details.get("success") or details.get("partial") or details.get("timed_out") or details.get("failed_dependencies"):
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
