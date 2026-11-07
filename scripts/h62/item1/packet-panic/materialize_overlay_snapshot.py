#!/usr/bin/env python3
"""Materialize a verified Git archive without registering a Git worktree."""
import argparse, hashlib, json, os, pathlib, stat, subprocess, tarfile
from verify_overlay_snapshot import tree_entries, verify_archive

def digest_stream(stream):
    h = hashlib.sha256()
    for chunk in iter(lambda: stream.read(1024 * 1024), b""):
        h.update(chunk)
    return h.hexdigest()

def verify_extracted(root, expected):
    if root.is_symlink() or not root.is_dir() or stat.S_IMODE(root.stat().st_mode) != 0o700:
        raise ValueError("snapshot root is not a private directory")
    expected_dirs = {str(parent) for name in expected for parent in pathlib.PurePosixPath(name).parents if str(parent) != "."}
    files, dirs = set(), set()
    for path in root.rglob("*"):
        name = path.relative_to(root).as_posix()
        if path.is_symlink():
            raise ValueError("extracted snapshot contains a symlink")
        if path.is_dir():
            if name not in expected_dirs:
                raise ValueError("extracted snapshot contains an extra directory")
            if stat.S_IMODE(path.stat().st_mode) != 0o700:
                raise ValueError("extracted directory is not private 0700")
            dirs.add(name)
        elif path.is_file():
            if name not in expected:
                raise ValueError("extracted snapshot contains an extra file")
            mode, oid = expected[name]
            expected_mode = 0o755 if mode == "100755" else 0o644
            if stat.S_IMODE(path.stat().st_mode) != expected_mode:
                raise ValueError("extracted file mode differs")
            h = hashlib.sha1()
            h.update(f"blob {path.stat().st_size}\0".encode())
            with path.open("rb") as stream:
                for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                    h.update(chunk)
            if h.hexdigest() != oid:
                raise ValueError("extracted bytes differ from Git blob")
            files.add(name)
        else:
            raise ValueError("extracted snapshot contains a nonregular entry")
    if files != set(expected) or dirs != expected_dirs:
        raise ValueError("extracted snapshot omits files or directories")

def materialize(repo, commit, archive, destination):
    repo = repo.resolve(strict=True)
    archive = archive.absolute()
    destination = destination.absolute()
    if archive.exists() or archive.is_symlink() or destination.exists() or destination.is_symlink():
        raise FileExistsError("snapshot archive or destination already exists; preserve it")
    archive = archive.parent.resolve(strict=True) / archive.name
    destination = destination.parent.resolve(strict=True) / destination.name
    if archive.exists() or archive.is_symlink() or destination.exists() or destination.is_symlink():
        raise FileExistsError("snapshot archive or destination already exists; preserve it")
    if archive.is_relative_to(destination):
        raise ValueError("archive must be outside snapshot destination")
    expected = tree_entries(repo, commit)
    with archive.open("x+b") as source:
        os.fchmod(source.fileno(), 0o600)
        subprocess.run(["git", "-c", "tar.umask=0022", "archive", "--format=tar", commit], cwd=repo, stdout=source, check=True)
        source.flush()
        os.fsync(source.fileno())
        original = os.fstat(source.fileno())
        def check_archive_identity():
            current = os.stat(archive, follow_symlinks=False)
            if not stat.S_ISREG(current.st_mode) or (current.st_dev, current.st_ino) != (original.st_dev, original.st_ino):
                raise ValueError("snapshot archive path no longer names the created file")
        check_archive_identity()
        source.seek(0)
        count = verify_archive(source, expected)
        source.seek(0)
        before = digest_stream(source)
        source.seek(0)
        destination.mkdir(mode=0o700)
        os.chmod(destination, 0o700)
        old_umask = os.umask(0o077)
        try:
            with tarfile.open(fileobj=source, mode="r:") as stream:
                stream.extractall(destination, filter="data")
        finally:
            os.umask(old_umask)
        source.seek(0)
        after = digest_stream(source)
        check_archive_identity()
        if before != after:
            raise ValueError("snapshot archive changed during extraction")
        verify_extracted(destination, expected)

    return {"commit": commit, "files": count, "archive_sha256": before, "destination": str(destination), "method": "fresh private unregistered snapshot, verified against Git blobs before and after extraction"}

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--repository", type=pathlib.Path, default=pathlib.Path.cwd())
    p.add_argument("--commit", required=True)
    p.add_argument("--archive", type=pathlib.Path, required=True)
    p.add_argument("--destination", type=pathlib.Path, required=True)
    args = p.parse_args()
    print(json.dumps(materialize(args.repository, args.commit, args.archive, args.destination)))

if __name__ == "__main__": main()
