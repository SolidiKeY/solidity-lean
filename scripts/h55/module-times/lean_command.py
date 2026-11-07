#!/usr/bin/env python3
"""Prepare a narrowly shaped Lean invocation; does not authenticate a VM."""
import hashlib
import os
import pathlib


def prepare(binary, expected_sha256, checkout, path, context, env):
    binary = pathlib.Path(binary)
    checkout = pathlib.Path(checkout)
    if (not binary.is_absolute() or binary.name != "lean" or binary.is_symlink()
            or not binary.is_file() or not os.access(binary, os.X_OK)):
        raise ValueError("Lean binary must be an absolute regular file named lean")
    if not isinstance(expected_sha256, str) or hashlib.sha256(binary.read_bytes()).hexdigest() != expected_sha256:
        raise ValueError("Lean executable hash mismatch")
    if not checkout.is_absolute() or not checkout.is_dir():
        raise ValueError("invalid checkout")
    if (not isinstance(path, str) or not path.endswith(".lean") or path.startswith("/")
            or "\\" in path or any(x in ("", ".", "..") for x in path.split("/"))):
        raise ValueError("invalid source path")
    root = checkout.resolve()
    source = root / path
    if source.is_symlink() or not source.is_file() or source.resolve() != source:
        raise ValueError("source is missing or reached via symlink")
    if context not in ("root", "bridge") or (context == "bridge" and not path.startswith("Bridge/")):
        raise ValueError("invalid build context")
    cwd = root if context == "root" else root / "Bridge"
    if context == "root" and path.startswith("Bridge/"):
        raise ValueError("Bridge path requires Bridge context")
    relative = str(source.relative_to(cwd))
    if not isinstance(env, dict) or any(not isinstance(k, str) or not isinstance(v, str) for k, v in env.items()):
        raise ValueError("invalid environment")
    if any(k.startswith("LD_") or k in ("LEAN_OPTS", "LEAN_EXTRA_OPTS") for k in env):
        raise ValueError("environment permits unverified runtime injection")
    # The caller must authenticate LEAN_PATH and other runtime configuration.
    clean_env = dict(env)
    clean_env["LEAN_NUM_THREADS"] = "1"
    return {"argv": [str(binary), "-j1", "--tstack=131072", relative],
            "cwd": str(cwd), "env": clean_env}
