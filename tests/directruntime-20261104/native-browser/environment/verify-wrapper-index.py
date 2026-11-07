"""Guard reviewable wrapper identity without executing historical validation."""

import argparse
import hashlib
import json
from pathlib import Path
import tarfile


def digest(data):
    return hashlib.sha256(data).hexdigest()


def verify(archive=None):
    root = Path(__file__).resolve().parents[4]
    index = json.loads(Path(__file__).with_name("wrapper-index.json").read_text())
    paths = set()
    members = set()
    for entry in index["wrappers"]:
        name = entry["repositoryPath"]
        path = root / name
        if name in paths or path.is_symlink() or not path.resolve().is_relative_to(root):
            raise ValueError(f"Unsafe or duplicate wrapper path: {name}")
        if entry["archiveMember"] in members:
            raise ValueError(f"Duplicate archive member: {entry['archiveMember']}")
        paths.add(name)
        members.add(entry["archiveMember"])
        data = path.read_bytes()
        if len(data) != entry["bytes"] or digest(data) != entry["sha256"]:
            raise ValueError(f"Wrapper identity mismatch: {name}")
    if not paths:
        raise ValueError("Empty wrapper inventory")
    if archive is not None:
        sealed = next(e for e in index["delivery"]["sealedArtifacts"]
                      if e["archiveName"] == "evidence.tar.gz")
        data = Path(archive).read_bytes()
        if len(data) != sealed["bytes"] or digest(data) != sealed["sha256"]:
            raise ValueError("Sealed evidence archive identity mismatch")
        with tarfile.open(archive, "r:gz") as stream:
            all_members = stream.getmembers()
            names = [m.name for m in all_members]
            if len(set(names)) != len(names):
                raise ValueError("Duplicate sealed archive member")
            for entry in index["wrappers"]:
                member = stream.getmember(entry["archiveMember"])
                if not member.isfile():
                    raise ValueError(f"Non-regular wrapper: {member.name}")
                data = stream.extractfile(member).read()
                if len(data) != entry["bytes"] or digest(data) != entry["sha256"]:
                    raise ValueError(f"Sealed wrapper identity mismatch: {member.name}")
    print(f"PASS {len(paths)} wrapper/config snapshots; no wrappers executed")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path)
    verify(parser.parse_args().archive)
