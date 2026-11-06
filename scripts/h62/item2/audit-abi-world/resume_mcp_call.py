#!/usr/bin/env python3
"""Separate post-merge diagnostics; never relabel frozen-base receipts.

Pin every upstream Solidity source to the authorized integration commit, retain
the original map/files byte-for-byte, and bind every local audit source.
Caller owns the existing resource guard and writer lock.
"""
import asyncio
import hashlib
import time
import subprocess
import json
import os
from pathlib import Path
import sys
from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client

async def main():
    root = Path(__file__).resolve().parents[4]
    env = dict(os.environ)
    env["PATH"] = str(Path(__file__).with_name("resume-bin").resolve()) + ":/workspace/.setup/tools/lean-4.24.0-linux/bin:" + env["PATH"]
    env["LEAN_NUM_THREADS"] = "1"
    env["LEAN_LSP_MAX_OPEN_FILES"] = "1"
    params = json.loads(sys.argv[2]) if len(sys.argv) > 2 else {}
    file = root / params["file_path"] if "file_path" in params else None
    before_hash = hashlib.sha256(file.read_bytes()).hexdigest() if file else None
    support_paths = ["tests/h62/item2/audit-abi-world/H62AbiWorld/WitnessSchema.lean",
        "tests/h62/item2/audit-abi-world/resume-serial.lakefile.toml",
        "scripts/h62/item2/audit-abi-world/resume_mcp_call.py", "scripts/h62/item2/audit-abi-world/resume-bin/lake",
        "lean-toolchain", "lakefile.toml",
        "scripts/h62/item2/audit-abi-world/resume_sources.py",
        "scripts/h62/item2/audit-abi-world/prepare_resume_config.py",
        "scripts/h62/item2/audit-abi-world/census.py"]
    def support_hashes():
        return {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in support_paths}
    support_before = support_hashes()
    import census
    from resume_sources import snapshot
    from prepare_resume_config import INTEGRATION
    original_base = census.BASE
    base = INTEGRATION
    upstream_before = snapshot()
    def local_sources():
        return {str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest()
                for p in sorted((root/"tests/h62/item2/audit-abi-world/H62AbiWorld").glob("*.lean"))}
    local_before = local_sources()
    assert not subprocess.check_output(["git", "diff", "--name-only", base, "--", "Solidity", "lakefile.toml", "lean-toolchain"], cwd=root).strip()
    version = subprocess.check_output(["/workspace/.setup/tools/lean-4.24.0-linux/bin/lean", "--version"], text=True).strip()
    started = time.monotonic()
    server = StdioServerParameters(command=str(root/".venv/bin/python"), args=["-m", "lean_lsp_mcp", "--lean-project-path", str(root)], cwd=str(root), env=env)
    async with stdio_client(server) as (read, write):
        async with ClientSession(read, write) as session:
            await session.initialize()
            if sys.argv[1] == "tools":
                result = await session.list_tools()
            else:
                result = await session.call_tool(sys.argv[1], json.loads(sys.argv[2]))
            upstream_after = snapshot()
            assert upstream_before == upstream_after, "Upstream inputs changed during diagnostics"
            after_hash = hashlib.sha256(file.read_bytes()).hexdigest() if file else None
            report = result.model_dump(mode="json")
            report["_audit"] = {"file": str(file) if file else None, "source_sha256": before_hash,
                "after_sha256": after_hash, "elapsed_seconds": time.monotonic()-started,
                "tool": sys.argv[1], "arguments": params, "lean_num_threads": 1,
                "support_before": support_before, "support_after": support_hashes(),
                "lean_version": version, "integration_sources_clean": True,
                "base": base, "original_frozen_base": original_base,
                "upstream_before": upstream_before, "upstream_after": upstream_after,
                "frozen_mapped_sources_clean": True, "local_before": local_before,
                "local_after": local_sources()}
            print(json.dumps(report))
            if before_hash != after_hash or support_before != support_hashes() or local_before != local_sources(): raise SystemExit(1)
            if getattr(result, "isError", False): raise SystemExit(1)
            content = getattr(result, "structuredContent", None)
            if sys.argv[1] == "lean_diagnostic_messages":
                data = (content or {}).get("result", {})
                if (data.get("success") is not True or data.get("partial") is not False
                    or data.get("timed_out") is not False or data.get("failed_dependencies")
                    or any(item.get("severity") == "error" for item in data.get("items", []))):
                    raise SystemExit(1)
            elif content:
                data = content.get("result", content)
                if data.get("success") is False or data.get("partial") is True:
                    raise SystemExit(1)

asyncio.run(main())
