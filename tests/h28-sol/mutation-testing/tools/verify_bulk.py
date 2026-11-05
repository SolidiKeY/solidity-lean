#!/usr/bin/env python3
"""Verify the committed H44 bulk manifest, all external/mirror files and archive."""
from pathlib import Path
import hashlib
import json
import subprocess
import tarfile
import time
import bulk_inputs


def digest(data):
    return hashlib.sha256(data).hexdigest()


def verify(repo):
    t = time.monotonic()
    pin = repo / bulk_inputs.PREFIX / "bulk-data.json"
    m = json.loads(bulk_inputs.read(repo, pin))
    index_bytes = Path(m["index"]).read_bytes()
    assert digest(index_bytes) == m["index_sha256"]
    entries = json.loads(index_bytes)["files"]
    assert len(entries) == m["file_count"]
    total = 0
    for rel, expected in entries.items():
        name = Path(rel)
        assert not name.is_absolute() and ".." not in name.parts and name.is_relative_to(bulk_inputs.PREFIX)
        for path in [Path(m["root"]) / name, repo / name]:
            assert path.is_file() and not path.is_symlink()
            data = path.read_bytes()
            assert len(data) == expected["bytes"] and digest(data) == expected["sha256"], str(path)
        total += expected["bytes"]
    assert total == m["uncompressed_bytes"]
    archive = Path(m["archive"])
    assert archive.stat().st_size == m["archive_bytes"] and digest(archive.read_bytes()) == m["archive_sha256"]
    seen = set()
    with tarfile.open(archive, "r:gz") as tar:
        for member in tar:
            if member.isdir(): continue
            assert member.isfile() and member.name not in seen and not member.name.startswith("/") and ".." not in Path(member.name).parts
            seen.add(member.name)
            if member.name.startswith("files/"):
                rel = member.name[len("files/"):]
                data = tar.extractfile(member).read()
                assert len(data) == entries[rel]["bytes"] and digest(data) == entries[rel]["sha256"]
            elif member.name == "files.json":
                assert tar.extractfile(member).read() == index_bytes
            else:
                assert member.name == "SHA256SUMS"
        assert seen == {"files/" + p for p in entries} | {"files.json", "SHA256SUMS"}
    assert digest(Path(m["backup_bundle"]).read_bytes()) == m["backup_bundle_sha256"]
    subprocess.run(["git", "bundle", "verify", m["backup_bundle"]], cwd=repo, check=True, stdout=subprocess.DEVNULL)
    return {"status": "pass", "command": "python3 -B tests/h28-sol/mutation-testing/tools/verify_bulk.py", "files": len(entries), "uncompressed_bytes": total, "archive": str(archive), "archive_bytes": m["archive_bytes"], "sha256": m["archive_sha256"], "backup_bundle_verified": True, "seconds": time.monotonic() - t}


if __name__ == "__main__":
    repo = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())
    print(json.dumps(verify(repo), indent=2))
