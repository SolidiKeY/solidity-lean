#!/usr/bin/env python3
"""Guard regression: selected Lake workspace state changes go unnoticed.

An observation of selected paths only; it does not discover every input,
prevent materialization, authenticate provenance, or constitute a gate.
"""
import hashlib
import importlib.util
import os
import pathlib
import stat

spec = importlib.util.spec_from_file_location("h55_cache_fingerprint", pathlib.Path(__file__).with_name("cache_fingerprint.py"))
cache = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cache)


def file_snapshot(path):
    path = pathlib.Path(path)
    if not path.is_absolute() or path.resolve() != path:
        raise ValueError("file path must be canonical and absolute")
    before = path.stat(follow_symlinks=False)
    if not stat.S_ISREG(before.st_mode):
        raise ValueError("workspace input must be a regular file")
    fd = os.open(path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW | os.O_NONBLOCK)
    try:
        opened = os.fstat(fd)
        if cache.identity(before) != cache.identity(opened):
            raise ValueError("workspace input replaced")
        digest = hashlib.sha256()
        while True:
            chunk = os.read(fd, 1024 * 1024)
            if not chunk:
                break
            digest.update(chunk)
        if cache.identity(opened) != cache.identity(os.fstat(fd)) or cache.identity(opened) != cache.identity(path.stat(follow_symlinks=False)):
            raise ValueError("workspace input changed")
    finally:
        os.close(fd)
    return {"path": str(path), "sha256": digest.hexdigest(), "size": opened.st_size, "mode": stat.S_IMODE(opened.st_mode),
            "mtime_ns": opened.st_mtime_ns, "links": opened.st_nlink}


def capture(config_files, selected_trees, command):
    if not isinstance(config_files, dict) or not config_files or not isinstance(selected_trees, dict) or not selected_trees:
        raise ValueError("explicit nonempty files and trees required")
    if any(not isinstance(k, str) or not k for k in (*config_files, *selected_trees)):
        raise ValueError("invalid labels")
    if not isinstance(command, dict) or set(command) != {"argv", "cwd", "env", "tool_sha256"}:
        raise ValueError("candidate command required")
    env = command.get("env")
    allowed = {"PATH", "HOME", "TMPDIR", "LANG", "LC_ALL", "TZ", "XDG_CACHE_HOME", "LEAN_NUM_THREADS"}
    if not isinstance(env, dict) or set(env) - allowed or any(not isinstance(v, str) for v in env.values()):
        raise ValueError("command environment is not allowlisted")
    # If supplied, bind this explicit environment location to the selected
    # observation. Lake may nevertheless select a different cache (e.g. Elan).
    if "XDG_CACHE_HOME" in env:
        xdg = pathlib.Path(env["XDG_CACHE_HOME"])
        selected = selected_trees.get("xdg_cache_home")
        if (not xdg.is_absolute() or xdg.resolve() != xdg or
                selected is None or pathlib.Path(selected) != xdg):
            raise ValueError("XDG cache home is not bound to the selected tree")
    # Exact command binding is observation, not validation or attestation.
    import json
    serialized = json.dumps(command, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False)
    files = {label: file_snapshot(path) for label, path in sorted(config_files.items())}
    trees = {label: {"path": str(path), "snapshot": cache.fingerprint(path)} for label, path in sorted(selected_trees.items())}
    if files != {label: file_snapshot(path) for label, path in sorted(config_files.items())}:
        raise ValueError("workspace files changed during observation")
    return {"command_sha256": hashlib.sha256(serialized.encode("ascii")).hexdigest(), "files": files, "trees": trees}


def unchanged(before, after):
    return isinstance(before, dict) and set(before) == {"command_sha256", "files", "trees"} and before == after
