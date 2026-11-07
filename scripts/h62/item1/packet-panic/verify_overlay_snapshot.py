#!/usr/bin/env python3
"""Verify a Git archive contains exactly the committed regular-file blobs."""
import argparse, hashlib, json, pathlib, re, subprocess, tarfile

def tree_entries(repo, commit):
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise ValueError("expected a full SHA-1 commit")
    fmt = subprocess.check_output(["git", "rev-parse", "--show-object-format"], cwd=repo, text=True).strip()
    if fmt != "sha1":
        raise ValueError("unsupported Git object format")
    raw = subprocess.check_output(["git", "ls-tree", "-rz", "--full-tree", commit], cwd=repo)
    result = {}
    for item in raw.split(b"\0"):
        if not item:
            continue
        header, raw_path = item.split(b"\t", 1)
        mode, kind, oid = header.decode("ascii").split()
        name = raw_path.decode("utf-8")
        if mode not in ("100644", "100755") or kind != "blob" or name in result:
            raise ValueError("unsupported tree entry or duplicate path")
        result[name] = (mode, oid)
    if not result:
        raise ValueError("empty Git tree")
    return result

def verify_archive(archive, expected):
    seen = set()
    expected_dirs = {str(parent) for name in expected for parent in pathlib.PurePosixPath(name).parents if str(parent) != "."}
    seen_dirs = set()
    opener = tarfile.open(fileobj=archive, mode="r:") if hasattr(archive, "read") else tarfile.open(archive, "r:")
    with opener as stream:
        for member in stream:
            name = member.name
            path = pathlib.PurePosixPath(name)
            if path.is_absolute() or ".." in path.parts or path.as_posix() != name:
                raise ValueError("unsafe archive path")
            if member.isdir():
                if name not in expected_dirs or name in seen_dirs or name in expected:
                    raise ValueError("unexpected or duplicate archive directory")
                if member.mode != 0o755:
                    raise ValueError("archive directory mode differs from expected 0755")
                seen_dirs.add(name)
                continue
            if not member.isfile() or name in seen or name not in expected:
                raise ValueError("unexpected, duplicate or non-regular archive entry")
            mode, oid = expected[name]
            expected_mode = 0o755 if mode == "100755" else 0o644
            if member.mode != expected_mode:
                raise ValueError("archive file mode differs from expected Git mode")
            blob = hashlib.sha1()
            blob.update(f"blob {member.size}\0".encode())
            source = stream.extractfile(member)
            if source is None:
                raise ValueError("archive member has no data")
            with source:
                for chunk in iter(lambda: source.read(1024 * 1024), b""):
                    blob.update(chunk)
            if blob.hexdigest() != oid:
                raise ValueError("archive content differs from Git blob")
            seen.add(name)
    if seen != set(expected) or seen_dirs != expected_dirs:
        raise ValueError("archive omits Git tree files or parent directories")
    return len(seen)

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--repository", type=pathlib.Path, default=pathlib.Path.cwd())
    p.add_argument("--commit", required=True)
    p.add_argument("--archive", type=pathlib.Path, required=True)
    args = p.parse_args()
    expected = tree_entries(args.repository, args.commit)
    count = verify_archive(args.archive, expected)
    h = hashlib.sha256()
    with args.archive.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    print(json.dumps({"commit": args.commit, "files": count, "archive_sha256": h.hexdigest(), "method": "all regular file bytes, file modes and unique parent directory entries match the Git tree under tar.umask=0022; no symlinks or extra entries"}))

if __name__ == "__main__": main()
