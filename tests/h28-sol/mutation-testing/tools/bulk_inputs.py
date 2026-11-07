"""H44: authenticate off-Git bulk inputs through a small committed manifest.

Tracked source files still require exact HEAD bytes. Only explicitly indexed
bulk files may use the external-data path; both mirror and archive-copy bytes
must match the committed index digest and per-file size/hash.
"""
import hashlib
import json
from pathlib import Path
import subprocess

PREFIX = Path("tests/h28-sol/mutation-testing")


def sha(data):
    return hashlib.sha256(data).hexdigest()


def head_bytes(repo, relative):
    return subprocess.check_output(["git", "show", "HEAD:" + str(relative)], cwd=repo, stderr=subprocess.PIPE)


def read(repo, path):
    repo = repo.resolve()
    path = Path(path)
    if path.is_symlink():
        raise ValueError("input must not be a symlink")
    rel = path.resolve().relative_to(repo)
    try:
        blob = head_bytes(repo, rel)
    except subprocess.CalledProcessError:
        blob = None
    if blob is not None:
        if blob != path.read_bytes():
            raise ValueError("committed input differs from working file: " + str(rel))
        return blob
    if not rel.is_relative_to(PREFIX):
        raise ValueError("uncommitted input outside bulk scope")
    manifest_path = PREFIX / "bulk-data.json"
    try:
        pin = head_bytes(repo, manifest_path)
    except subprocess.CalledProcessError as exc:
        raise ValueError("input is neither committed nor registered bulk data") from exc
    if (repo / manifest_path).is_symlink() or (repo / manifest_path).read_bytes() != pin:
        raise ValueError("bulk manifest differs from committed input")
    manifest = json.loads(pin)
    if manifest["schema"] != 1 or manifest["authorization"] != "H44":
        raise ValueError("unsupported bulk manifest")
    index_path = Path(manifest["index"])
    root = Path(manifest["root"])
    if not root.is_absolute() or not index_path.is_absolute() or index_path.is_symlink():
        raise ValueError("unsafe external bulk location")
    index_bytes = index_path.read_bytes()
    if sha(index_bytes) != manifest["index_sha256"]:
        raise ValueError("bulk index identity mismatch")
    index = json.loads(index_bytes)["files"]
    if len(index) != manifest["file_count"] or str(rel) not in index:
        raise ValueError("unregistered bulk input")
    record = index[str(rel)]
    external = root / rel
    if external.is_symlink() or not external.resolve().is_relative_to(root.resolve()):
        raise ValueError("unsafe external bulk file")
    data = external.read_bytes()
    if len(data) != record["bytes"] or sha(data) != record["sha256"]:
        raise ValueError("bulk file identity mismatch")
    if path.read_bytes() != data:
        raise ValueError("bulk mirror differs from authenticated external input")
    return data
