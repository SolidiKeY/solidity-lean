#!/usr/bin/env python3
"""Guard H127 snapshots against live checkout, filters and Git-alternate inputs.

Materializes raw regular Git blobs and a private shallow object database. This
is preparation under exclusive writer control, not an immutable mount, complete
history, toolchain/cache authentication or execution/measurement authorization.
Failures retain an incomplete destination for inspection; never reuse it.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import subprocess

GIT = "/usr/bin/git"
ENV = {"PATH": "/usr/bin:/bin", "LC_ALL": "C", "HOME": "/nonexistent",
       "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": "/dev/null",
       "GIT_NO_REPLACE_OBJECTS": "1", "GIT_NO_LAZY_FETCH": "1",
       "GIT_OPTIONAL_LOCKS": "0", "GIT_TERMINAL_PROMPT": "0"}
MAX_BLOB = 128 * 1024 * 1024
RESERVE = 2_000_000_000


def command(repo, *args, **kw):
    return subprocess.run([GIT, "-c", "core.hooksPath=/dev/null", "-c",
        "core.fsmonitor=false", "-c", "core.attributesFile=/dev/null", "-C",
        str(repo), *args], env=ENV, check=True, **kw)


def output(repo, *args):
    return command(repo, *args, stdout=subprocess.PIPE).stdout


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode() + b"\n"


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(262144), b""):
            h.update(chunk)
    return h.hexdigest()


def safe_path(name):
    parts = name.split("/")
    if any(x in ("", ".", "..") or x.casefold() == ".git" or
           any(ord(c) < 32 or ord(c) == 127 for c in x) for x in parts):
        raise ValueError("unsafe Git path")
    return parts


def entries(repo, commit):
    if not re.fullmatch("[0-9a-f]{40}", commit):
        raise ValueError("exact SHA1 commit required")
    if output(repo, "rev-parse", "--show-object-format").strip() != b"sha1":
        raise ValueError("only SHA1 Git repositories supported")
    if output(repo, "cat-file", "-t", commit).strip() != b"commit":
        raise ValueError("not a commit")
    rows, trees = [], []
    for raw in output(repo, "ls-tree", "-rzt", "-l", "--full-tree", commit).split(b"\0"):
        if not raw:
            continue
        header, rawname = raw.split(b"\t", 1)
        mode, kind, oid, size = header.decode("ascii").split()
        name = rawname.decode("utf-8")
        safe_path(name)
        if kind == "tree" and mode == "040000":
            trees.append(oid)
        elif kind == "blob" and mode in ("100644", "100755"):
            if not size.isdecimal() or int(size) > MAX_BLOB:
                raise ValueError("oversized Git blob")
            rows.append({"path": name, "mode": mode, "oid": oid, "bytes": int(size)})
        else:
            raise ValueError("nonregular Git entry")
    names = [r["path"] for r in rows]
    if len(names) != len(set(names)):
        raise ValueError("duplicate Git path")
    return rows, trees


def verify(directory, expected_manifest_sha):
    directory = Path(directory)
    if directory != directory.resolve(strict=True):
        raise ValueError("snapshot path contains symlink")
    if not stat.S_ISDIR(directory.lstat().st_mode):
        raise ValueError("snapshot envelope is not a directory")
    repo = directory / "repo"
    if not stat.S_ISDIR(repo.lstat().st_mode):
        raise ValueError("snapshot repository is not a real directory")
    manifest = directory / "manifest.json"
    ms = manifest.lstat()
    if not stat.S_ISREG(ms.st_mode) or ms.st_nlink != 1:
        raise ValueError("unsafe snapshot manifest")
    if not re.fullmatch("[0-9a-f]{64}", expected_manifest_sha) or sha(manifest) != expected_manifest_sha:
        raise ValueError("manifest hash mismatch")
    data = json.loads(manifest.read_bytes())
    if sha(Path(GIT)) != data["gitSha256"]:
        raise ValueError("Git executable hash mismatch")
    # All entries, including private Git metadata, must be regular single-link
    # files or directories. No live alternate/common-dir or symlink escapes.
    actual, directories = [], []
    for parent, dirs, files in os.walk(repo, followlinks=False):
        for name in dirs + files:
            p = Path(parent) / name
            s = p.lstat()
            if stat.S_ISDIR(s.st_mode):
                directories.append(p.relative_to(repo).as_posix())
                continue
            if not stat.S_ISREG(s.st_mode) or s.st_nlink != 1:
                raise ValueError("unsafe snapshot entry")
            actual.append({"path": p.relative_to(repo).as_posix(), "bytes": s.st_size,
                           "mode": stat.S_IMODE(s.st_mode), "sha256": sha(p)})
    if sorted(directories) != data["directories"]:
        raise ValueError("snapshot directory inventory mismatch")
    if sorted(actual, key=lambda r:r["path"]) != data["files"]:
        raise ValueError("snapshot inventory mismatch")
    if set(os.listdir(directory)) != {"repo", "manifest.json"}:
        raise ValueError("extra snapshot envelope entry")
    for forbidden in ("objects/info/alternates", "objects/info/http-alternates", "commondir", "config.worktree"):
        if (repo / ".git" / forbidden).exists():
            raise ValueError("external Git metadata")
    if output(repo, "rev-parse", "HEAD").strip().decode() != data["commit"]:
        raise ValueError("private Git head mismatch")
    if output(repo, "rev-parse", "HEAD^{tree}").strip().decode() != data["tree"]:
        raise ValueError("private Git tree mismatch")
    command(repo, "fsck", "--strict", stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if output(repo, "status", "--porcelain=v1", "--untracked-files=all"):
        raise ValueError("private Git working tree differs")
    return {"status": "verified-prepared-source-only", "commit": data["commit"],
            "manifestSha256": expected_manifest_sha, "files": len(data["files"]),
            "immutableMountAuthenticated": False}


def materialize(repository, commit, destination):
    repo, dest = Path(repository), Path(destination)
    if repo != repo.resolve(strict=True) or dest.parent != dest.parent.resolve(strict=True):
        raise ValueError("source or destination parent contains symlink")
    rows, trees = entries(repo, commit)
    total = sum(r["bytes"] for r in rows)
    # Conservative coarse estimate only: raw tree + two pack copies + allowance.
    # Allocation granularity, inodes and concurrent writers are NOT bounded here.
    # Production use requires the future controller capacity monitor/reservation.
    fs = os.statvfs(dest.parent)
    if fs.f_bavail * fs.f_frsize < RESERVE + 3 * total + 64 * 1024 * 1024:
        raise ValueError("insufficient snapshot disk reserve")
    dest.mkdir(mode=0o700)  # exclusive; an incomplete prior attempt is not reused
    work = dest / "repo"
    work.mkdir(mode=0o700)
    batch = subprocess.Popen([GIT, "-C", str(repo), "cat-file", "--batch"],
                             env=ENV, stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    try:
        for row in rows:
            batch.stdin.write((row["oid"] + "\n").encode()); batch.stdin.flush()
            expected = f'{row["oid"]} blob {row["bytes"]}\n'.encode()
            if batch.stdout.readline(256) != expected:
                raise ValueError("Git blob header differs")
            target = work / row["path"]
            target.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
            h = hashlib.sha1(f'blob {row["bytes"]}\0'.encode())
            remaining = row["bytes"]
            with target.open("xb") as f:
                os.fchmod(f.fileno(), int(row["mode"][-3:], 8))
                while remaining:
                    chunk = batch.stdout.read(min(262144, remaining))
                    if not chunk:
                        raise ValueError("truncated Git blob")
                    f.write(chunk); h.update(chunk); remaining -= len(chunk)
            if batch.stdout.read(1) != b"\n" or h.hexdigest() != row["oid"]:
                raise ValueError("Git blob identity differs")
        batch.stdin.close()
        if batch.wait() != 0:
            raise ValueError("Git blob reader failed")
    finally:
        if batch.poll() is None:
            batch.kill(); batch.wait()
        batch.stdout.close()
        if not batch.stdin.closed:
            batch.stdin.close()
    template = dest / "empty-template"
    template.mkdir(mode=0o700)
    command(work, "init", "--quiet", "--template=" + str(template))
    template.rmdir()
    root = output(repo, "rev-parse", commit + "^{tree}").strip().decode()
    objects = sorted({commit, root, *trees, *(r["oid"] for r in rows)})
    pack = dest / "input.pack"
    with pack.open("xb") as f:
        command(repo, "pack-objects", "--stdout", "--threads=1", "--window=0", "--depth=0",
                input=("\n".join(objects) + "\n").encode(), stdout=f)
    with pack.open("rb") as f:
        command(work, "index-pack", "--stdin", stdin=f, stdout=subprocess.PIPE)
    pack.unlink()
    # Only exact commit/tree/blob closure is copied, not parent history.
    (work / ".git/shallow").write_text(commit + "\n")
    command(work, "update-ref", "refs/heads/snapshot", commit)
    command(work, "symbolic-ref", "HEAD", "refs/heads/snapshot")
    command(work, "read-tree", commit)
    # status may refresh index stat metadata; finish that before sealing bytes.
    if output(work, "status", "--porcelain=v1", "--untracked-files=all"):
        raise ValueError("materialized Git working tree differs")
    files, directories = [], []
    for parent, dirs, names in os.walk(work):
        directories.extend((Path(parent) / name).relative_to(work).as_posix() for name in dirs)
        for name in names:
            p = Path(parent) / name
            files.append({"path": p.relative_to(work).as_posix(), "bytes": p.stat().st_size,
                          "mode": stat.S_IMODE(p.stat().st_mode), "sha256": sha(p)})
    data = {"version": 1, "commit": commit, "tree": root, "gitSha256": sha(Path(GIT)),
            "history": "shallow exact commit; no parent objects, remotes or alternates",
            "immutableMountAuthenticated": False,
            "capacityEnforcementAuthenticated": False,
            "directories": sorted(directories),
            "files": sorted(files, key=lambda r:r["path"])}
    manifest = dest / "manifest.json"
    manifest.write_bytes(canonical(data))
    return verify(dest, sha(manifest))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="action", required=True)
    make = sub.add_parser("prepare")
    make.add_argument("repository", type=Path); make.add_argument("commit")
    make.add_argument("destination", type=Path)
    check = sub.add_parser("verify")
    check.add_argument("destination", type=Path); check.add_argument("manifest_sha256")
    a = p.parse_args()
    result = (materialize(a.repository, a.commit, a.destination) if a.action == "prepare"
              else verify(a.destination, a.manifest_sha256))
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
