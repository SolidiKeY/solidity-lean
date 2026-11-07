#!/usr/bin/env python3
"""Guard regression: per-file checks bypass Lake or rebuild imports in parallel.

This prepares a candidate command only; source, toolchain, cache and execution
still require authentication and independent acceptance.
"""
import hashlib
import os
import pathlib


def tool(path, name, expected):
    path = pathlib.Path(path)
    if (not path.is_absolute() or path.name != name or path.is_symlink() or
            not path.is_file() or not os.access(path, os.X_OK) or path.resolve() != path):
        raise ValueError(f"invalid {name} executable")
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if not isinstance(expected, str) or actual != expected:
        raise ValueError(f"{name} executable hash mismatch")
    return path


def prepare(lake, lake_sha256, lean, lean_sha256, checkout, source, context, env):
    lake = tool(lake, "lake", lake_sha256)
    lean = tool(lean, "lean", lean_sha256)
    if lake.parent != lean.parent:
        raise ValueError("Lake and Lean must share a toolchain directory")
    root = pathlib.Path(checkout)
    if not root.is_absolute() or root.resolve() != root or not root.is_dir():
        raise ValueError("checkout must be absolute and canonical")
    if (not isinstance(source, str) or not source.endswith(".lean") or source.startswith("/")
            or "\\" in source or any(part in ("", ".", "..") for part in source.split("/"))):
        raise ValueError("invalid source path")
    path = root / source
    if not path.is_file() or path.is_symlink() or path.resolve() != path:
        raise ValueError("source missing or reached through symlink")
    if context not in ("root", "bridge") or (source.startswith("Bridge/") != (context == "bridge")):
        raise ValueError("source/context mismatch")
    if not isinstance(env, dict) or any(not isinstance(k, str) or not isinstance(v, str) for k, v in env.items()):
        raise ValueError("invalid environment")
    allowed = {"PATH", "HOME", "TMPDIR", "LANG", "LC_ALL", "TZ", "XDG_CACHE_HOME", "LEAN_NUM_THREADS"}
    if set(env) - allowed:
        raise ValueError("environment contains an unverified override")
    search = env.get("PATH", "").split(":")
    if not search or search[0] != str(lean.parent) or any(not p.startswith("/") for p in search):
        raise ValueError("PATH must start with the pinned toolchain directory")
    cwd = root if context == "root" else root / "Bridge"
    relative = str(path.relative_to(cwd))
    controlled_env = dict(env)
    controlled_env["LEAN_NUM_THREADS"] = "1"
    # --no-build rejects stale build actions; workspace loading and dependency
    # materialization still require separate containment and authentication.
    return {"argv": [str(lake), "--no-build", "lean", relative, "--", "-j1", "--tstack=131072"],
            "cwd": str(cwd), "env": controlled_env,
            "tool_sha256": {"lake": lake_sha256, "lean": lean_sha256}}
