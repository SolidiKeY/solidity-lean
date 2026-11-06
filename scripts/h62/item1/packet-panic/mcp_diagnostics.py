#!/usr/bin/env python3
"""Run one pinned Lean MCP diagnostic, with a cgroup headroom watchdog."""
import asyncio
import os
from pathlib import Path
import sys
from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import get_default_environment, stdio_client

root = Path(__file__).resolve().parents[4]
target = sys.argv[1]
cgroup = Path("/sys/fs/cgroup/memory.current")
cgroup_max = Path("/sys/fs/cgroup/memory.max").read_text().strip()
if cgroup_max == "max":
    raise SystemExit("memory guard: no finite cgroup memory cap")
limit = min(12 * 1024**3, int(cgroup_max) - 4 * 1024**3)
if limit <= 0 or len(Path("/proc/swaps").read_text().splitlines()) != 1:
    raise SystemExit("memory guard: insufficient cgroup capacity or swap enabled")
if int(cgroup.read_text()) >= limit:
    raise SystemExit("memory guard: less than 4 GiB remains under 16 GiB cgroup cap")
env = get_default_environment()
env.update({"PATH": str(root / "scripts/h62/item1/packet-panic/bin") + ":/workspace/h62-toolchain/lean-4.35.0-linux/bin:" + env.get("PATH", ""),
            "LEAN_NUM_THREADS": "1", "LEAN_LSP_MAX_OPEN_FILES": "1", "LEAN_REPL": "0",
            "LEAN_PROJECT_PATH": str(root),
            "LEAN_MCP_DISABLED_TOOLS": "lean_leansearch,lean_loogle,lean_leanfinder,lean_state_search,lean_hammer_premise,lean_get_widgets,lean_get_widget_source"})
server = StdioServerParameters(command="/workspace/solidity-lean/.venv/bin/python", args=[str(root / "scripts/h62/item1/packet-panic/mcp_no_build_server.py"), "--lean-project-path", str(root)], env=env, cwd=str(root))

async def diagnose():
    async with stdio_client(server) as (read, write):
        async with ClientSession(read, write) as session:
            await session.initialize()
            result = await session.call_tool("lean_diagnostic_messages", {"file_path": target, "interactive": False, "timeout_s": 40})
            print(result.model_dump_json(indent=2))
            diagnostics = (result.structuredContent or {}).get("result", {})
            errors = [item for item in diagnostics.get("items", []) if item.get("severity") in ("error", "warning") or "out of date" in item.get("message", "").lower()]
            if result.isError or not diagnostics.get("success") or diagnostics.get("partial") or diagnostics.get("timed_out") or diagnostics.get("failed_dependencies") or errors:
                raise RuntimeError("diagnostic was incomplete, stale, or reported errors/warnings")

async def guard():
    while True:
        if int(cgroup.read_text()) >= limit:
            raise RuntimeError("memory guard: 4 GiB cgroup reserve reached")
        await asyncio.sleep(0.25)

async def main():
    job = asyncio.create_task(diagnose())
    watch = asyncio.create_task(guard())
    try:
        done, _ = await asyncio.wait({job, watch}, timeout=55, return_when=asyncio.FIRST_COMPLETED)
        if not done:
            raise TimeoutError("diagnostic did not complete within 55 seconds")
        for task in done:
            await task
    finally:
        job.cancel()
        watch.cancel()
        await asyncio.gather(job, watch, return_exceptions=True)

asyncio.run(main())
