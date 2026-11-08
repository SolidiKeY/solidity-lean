"""Regression guard: archived frozen inputs retain exact bytes and fail closed.

The default inputs come from one immutable H145 private Git packet. Supply an
external checkout with SOLIDITY_COORD_EVIDENCE_REPO; no network, local-path
fallback or new evidence is manufactured by this reader. Explicit manifests
remain available for genuine checker fixtures and isolated controls.
"""
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess

REPO = Path(__file__).resolve().parents[4]
ARCHIVE_COMMIT = "74956e3ca554128d499fcd4b921ea67c7634ad17"
ARCHIVE_DIR = "evidence/solidity-h28-sol-20261104/automation-benchmark/evm-try-owner-inputs-v135"


def _git_bytes(repo, revision, relative):
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("archive requires an immutable commit")
    p = PurePosixPath(relative)
    if p.is_absolute() or not p.parts or any(v in (".", "..") for v in p.parts):
        raise ValueError("unsafe archive path")
    args = ["git", "--no-replace-objects", "--no-optional-locks", "-C", str(repo)]
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull, GIT_NO_LAZY_FETCH="1")
    subprocess.check_output(args + ["cat-file", "-e", revision + "^{commit}"], stderr=subprocess.PIPE, env=env)
    tree = subprocess.check_output(args + ["ls-tree", revision, "--", str(p)], stderr=subprocess.PIPE, env=env)
    fields = tree.decode().rstrip("\n").split("\t")
    if len(fields) != 2 or fields[1] != str(p) or not fields[0].startswith("100644 blob "):
        raise ValueError("archive input must be one regular tracked file")
    return subprocess.check_output(args + ["show", revision + ":" + str(p)], stderr=subprocess.PIPE, env=env)


def _checked(data, row, name):
    if len(data) != row["bytes"] or hashlib.sha256(data).hexdigest() != row["sha256"]:
        raise ValueError("bulk input size/checksum mismatch: " + name)
    return data


def bulk_bytes(name, manifest=None):
    if manifest is not None:
        row = json.loads(Path(manifest).read_text())[name]
        path = Path(row["path"])
        if not path.is_absolute() or path.resolve().is_relative_to(REPO):
            raise ValueError("H44: bulk input must be an absolute external path")
        if path.is_symlink():
            raise ValueError("bulk input must not be a symlink")
        return _checked(path.read_bytes(), row, name)
    location = os.environ.get("SOLIDITY_COORD_EVIDENCE_REPO")
    if not location:
        raise FileNotFoundError("set SOLIDITY_COORD_EVIDENCE_REPO to the private archive checkout")
    root = Path(location)
    if not root.is_absolute() or root.is_symlink() or root.resolve().is_relative_to(REPO):
        raise ValueError("private archive checkout must be absolute and external")
    data = _git_bytes(root, ARCHIVE_COMMIT, ARCHIVE_DIR + "/bulk-inputs-manifest.json")
    row = json.loads(data)[name]
    relative = row["path"]
    if not isinstance(relative, str) or not re.fullmatch(r"[A-Za-z0-9_-]+\.json", relative):
        raise ValueError("unsafe archive payload path")
    return _checked(_git_bytes(root, ARCHIVE_COMMIT, ARCHIVE_DIR + "/" + relative), row, name)
