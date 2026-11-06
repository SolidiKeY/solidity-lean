#!/usr/bin/env python3
"""Snapshot source and tool identities for comparison, not VM attestation."""
import hashlib
import pathlib
import re
import subprocess


COMMIT = re.compile(r"[0-9a-f]{40}\Z")


def snapshot(root, expected_head, tool, source):
    root = pathlib.Path(root)
    tool = pathlib.Path(tool)
    if not root.is_absolute() or not root.is_dir() or not tool.is_absolute():
        raise ValueError("invalid root or tool")
    if not isinstance(expected_head, str) or not COMMIT.fullmatch(expected_head):
        raise ValueError("expected full commit required")
    if (not isinstance(source, str) or not source.endswith(".lean") or source.startswith("/")
            or "\\" in source or any(x in ("", ".", "..") for x in source.split("/"))):
        raise ValueError("invalid source path")
    root = root.resolve()
    path = root / source
    if path.is_symlink() or not path.is_file() or path.resolve() != path or tool.is_symlink() or not tool.is_file():
        raise ValueError("missing or symlinked input")
    def git(*args):
        return subprocess.check_output(["git", "-C", str(root), *args]).decode().strip()
    if pathlib.Path(git("rev-parse", "--show-toplevel")).resolve() != root:
        raise ValueError("root is not the git top level")
    if git("rev-parse", "HEAD") != expected_head or git("status", "--porcelain", "--untracked-files=all"):
        raise ValueError("wrong head or dirty checkout")
    if subprocess.run(["git", "-C", str(root), "ls-files", "--error-unmatch", "--", source],
                      stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode:
        raise ValueError("source not tracked")
    digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
    return {"head": expected_head, "tree": git("rev-parse", "HEAD^{tree}"),
            "source": source, "source_sha256": digest(path), "tool_sha256": digest(tool)}


def unchanged(before, after):
    keys = {"head", "tree", "source", "source_sha256", "tool_sha256"}
    if not isinstance(before, dict) or set(before) != keys or before != after:
        return False
    if any(not isinstance(before[k], str) for k in keys):
        return False
    source = before["source"]
    return bool(COMMIT.fullmatch(before["head"]) and COMMIT.fullmatch(before["tree"])
                and re.fullmatch(r"[0-9a-f]{64}", before["source_sha256"])
                and re.fullmatch(r"[0-9a-f]{64}", before["tool_sha256"])
                and source.endswith(".lean") and not source.startswith("/")
                and "\\" not in source and all(p not in ("", ".", "..") for p in source.split("/")))
