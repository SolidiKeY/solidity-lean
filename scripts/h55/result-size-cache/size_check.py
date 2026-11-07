#!/usr/bin/env python3
"""Census changed Git content and reject large H44 data; no bypass flags.

Guards parser-limit JSON disguises and additions hidden in merged root history.
This prototype does not establish coordinator base approval or an atomic checkout.
"""
import argparse
import hashlib
import json
import os
import stat
import subprocess
import sys

DATA_LIMIT = 100 * 1024
SOURCE_LIMIT = 1024 * 1024
SOURCE_SUFFIXES = (b".lean", b".py", b".sh", b".js", b".mjs", b".ts", b".c", b".h", b".rs")


def git(*args):
    return subprocess.check_output([b"git", b"--no-replace-objects", *args], env=dict(os.environ, GIT_OPTIONAL_LOCKS="0"))


def changes(*args, root=False):
    command = (b"diff-tree", b"--root", b"--no-commit-id", b"-r") if root else (b"diff",)
    fields = git(*command, b"--name-status", b"-z", b"--no-renames", b"--ignore-submodules=none", *args).split(b"\0")
    return [(fields[i], fields[i + 1]) for i in range(0, len(fields) - 1, 2)]


def classify(path, content, approved):
    size = len(content)
    # UTF-8 source is reviewable only when it is not a binary payload or JSON
    # disguised with a source suffix. No filename-based data exemptions exist.
    source = path.lower().endswith(SOURCE_SUFFIXES) and b"\0" not in content
    if source:
        try:
            decoded = content.decode("utf-8")
        except UnicodeDecodeError:
            source = False
        else:
            if any(ord(c) < 32 and c not in "\n\r\t" for c in decoded):
                source = False
            else:
                try:
                    json.loads(decoded, parse_int=str, parse_float=str)
                except RecursionError:
                    source = False
                except ValueError:
                    pass
                else:
                    source = False
    # Exceptions are bound to a digest in the trusted base, not the lane tree.
    digest = hashlib.sha256(content).hexdigest()
    allowed = source and approved.get(os.fsdecode(path)) == digest
    kind = "approved-source" if allowed else ("source-candidate" if source else "data")
    limit = SOURCE_LIMIT if allowed else DATA_LIMIT
    return kind, size, limit, size <= limit


def fingerprint(path):
    try:
        info = os.lstat(path)
    except FileNotFoundError:
        return None
    return (info.st_dev, info.st_ino, info.st_mode, info.st_size, info.st_mtime_ns, info.st_ctime_ns)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("base", help="base commit against which committed changes are checked")
    args = parser.parse_args()
    metadata = git(b"rev-parse", b"--show-toplevel", b"--is-shallow-repository", b"HEAD").splitlines()
    if len(metadata) != 3:
        raise RuntimeError("ambiguous repository metadata")
    root, shallow, head = metadata
    os.chdir(root)
    if shallow != b"false":
        raise RuntimeError("shallow history cannot establish the full changed-content census")
    if "GIT_GRAFT_FILE" in os.environ or "GIT_SHALLOW_FILE" in os.environ:
        raise RuntimeError("custom graft/shallow history is not supported")
    locations = git(b"rev-parse", b"--git-path", b"index", b"--git-path", b"info/grafts", b"--git-path", b"info/attributes").splitlines()
    if len(locations) != 3:
        raise RuntimeError("ambiguous Git metadata paths")
    index, grafts, info_attributes = locations
    if os.path.lexists(grafts):
        raise RuntimeError("grafted history cannot establish the full changed-content census")
    base = git(b"rev-parse", b"--verify", os.fsencode(args.base) + b"^{commit}").strip()
    merge = git(b"merge-base", base, head).strip()
    if merge != base:
        raise RuntimeError("base must be an ancestor of HEAD")
    approval_spec = base + b":scripts/h55/result-size-cache/approved-source.json"
    found = subprocess.run([b"git", b"--no-replace-objects", b"cat-file", b"-e", approval_spec], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0
    approved = json.loads(git(b"cat-file", b"blob", approval_spec)) if found else {}
    if not isinstance(approved, dict) or any(not isinstance(k, str) or not isinstance(v, str) or len(v) != 64 or any(c not in "0123456789abcdef" for c in v) for k, v in approved.items()):
        raise RuntimeError("invalid trusted source approval list")
    index_state = fingerprint(index)
    info_attributes_state = fingerprint(info_attributes)
    flags = git(b"ls-files", b"-v", b"-z").split(b"\0")
    if any(row and (row[:1] != b"H") for row in flags):
        raise RuntimeError("index contains skip-worktree or assume-unchanged entries")
    paths = [row[2:] for row in flags if row]
    untracked_data = git(b"ls-files", b"--others", b"--exclude-standard", b"-z")
    untracked_paths = [p for p in untracked_data.split(b"\0") if p]
    watched = {path: fingerprint(path) for path in paths + untracked_paths}
    autocrlf = git(b"config", b"--default", b"false", b"--get", b"core.autocrlf").strip().lower()
    if autocrlf not in (b"false", b"no", b"0", b"off", b""):
        raise RuntimeError("raw-byte census refuses core.autocrlf normalization")
    if paths:
        attributes = subprocess.check_output(
            [b"git", b"--no-replace-objects", b"check-attr", b"-z", b"--stdin", b"filter", b"text", b"eol", b"ident", b"working-tree-encoding"],
            input=b"\0".join(paths) + b"\0", env=dict(os.environ, GIT_OPTIONAL_LOCKS="0")).split(b"\0")
        if any(value not in (b"unspecified", b"unset") for value in attributes[2::3]):
            raise RuntimeError("raw-byte census refuses transforming Git attributes")
    snapshots = []
    for commit in git(b"rev-list", b"--reverse", base + b".." + head).splitlines():
        parents = git(b"rev-list", b"--parents", b"-n", b"1", commit).split()[1:]
        if not parents:
            snapshots.append(("commit:" + commit.decode(), changes(commit, root=True), commit, None))
        for parent in parents:
            snapshots.append(("commit:" + commit.decode(), changes(parent, commit), commit, parent))
    snapshots.extend([("committed", changes(merge, head), head, merge),
                      ("staged", changes(b"--cached", head), b":", head),
                      ("tracked", changes(), None, b":")])
    untracked = [(b"A", p) for p in untracked_paths]
    snapshots.append(("untracked", untracked, None, None))
    failures = 0
    for scope, rows, revision, previous in snapshots:
        for status, path in rows:
            display = os.fsdecode(path)
            if status == b"D":
                spec = previous + (b"" if previous == b":" else b":") + path
                prior_type = git(b"cat-file", b"-t", spec).strip().decode()
                prior_size = int(git(b"cat-file", b"-s", spec))
                print(json.dumps(dict(scope=scope, status="D", path=display, prior_type=prior_type, prior_bytes=prior_size), ensure_ascii=True))
                continue
            actual_size = None
            if revision is None:
                try:
                    mode = os.lstat(path).st_mode
                    if stat.S_ISLNK(mode):
                        content = os.fsencode(os.readlink(path))
                    elif stat.S_ISREG(mode):
                        fd = os.open(path, os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW)
                        with os.fdopen(fd, "rb") as f:
                            before = os.fstat(f.fileno())
                            if not stat.S_ISREG(before.st_mode):
                                raise RuntimeError(f"special file refused: {display!r}")
                            actual_size = before.st_size
                            content = f.read(SOURCE_LIMIT + 1)
                            after = os.fstat(f.fileno())
                            if (before.st_size, before.st_mtime_ns, before.st_ctime_ns) != (after.st_size, after.st_mtime_ns, after.st_ctime_ns):
                                raise RuntimeError(f"file changed while reading: {display!r}")
                    else:
                        raise RuntimeError(f"special file refused: {display!r}")
                except OSError as exc:
                    raise RuntimeError(f"cannot read {display!r}: {exc}") from exc
            else:
                spec = revision + (b"" if revision == b":" else b":") + path
                size = int(git(b"cat-file", b"-s", spec))
                if size > SOURCE_LIMIT:
                    print(json.dumps(dict(scope=scope, status=os.fsdecode(status), path=display, kind="oversize", bytes=size, limit=SOURCE_LIMIT, result="fail"), ensure_ascii=True))
                    failures += 1
                    continue
                content = git(b"cat-file", b"blob", spec)
            kind, size, limit, ok = classify(path, content, approved)
            if actual_size is not None:
                size = actual_size
                ok = ok and size <= limit
            failures += not ok
            print(json.dumps(dict(scope=scope, status=os.fsdecode(status), path=display, kind=kind, bytes=size, limit=limit, result="pass" if ok else "fail"), ensure_ascii=True))
    if (git(b"rev-parse", b"HEAD").strip() != head or fingerprint(index) != index_state or
            fingerprint(info_attributes) != info_attributes_state or
            git(b"ls-files", b"--others", b"--exclude-standard", b"-z") != untracked_data or
            any(fingerprint(path) != state for path, state in watched.items()) or
            git(b"config", b"--default", b"false", b"--get", b"core.autocrlf").strip().lower() != autocrlf):
        raise RuntimeError("repository inputs changed during size census")
    print(json.dumps(dict(summary="fail" if failures else "pass", failures=failures)))
    return bool(failures)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, RuntimeError, ValueError, subprocess.CalledProcessError) as exc:
        print(f"size-check: {exc}", file=sys.stderr)
        sys.exit(2)
