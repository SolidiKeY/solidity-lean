#!/usr/bin/env python3
"""Lane-owned pinned corpus extraction. No legacy generated output is modified."""
import argparse, hashlib, json, tarfile
from pathlib import Path, PurePosixPath
ROOT = Path(__file__).resolve().parents[2]
PIN = "1835d247de183f23e7b0e2bc4a50732af525b77c"
ARCHIVE_SHA = "9200f2a26b08be5b77faf877c44f5cfbf5ea95f1bccc45dae559d2fbc7cefb2d"
PREFIX = "test/libsolidity/semanticTests/inlineAssembly/"
def sha(b): return hashlib.sha256(b).hexdigest()
def inventory(archive, snapshot, destination=None):
    manifest = json.loads(snapshot.read_bytes())
    if manifest.get("commit") != PIN or manifest.get("archiveSha256") != ARCHIVE_SHA:
        raise ValueError("snapshot pin mismatch")
    if sha(archive.read_bytes()) != ARCHIVE_SHA: raise ValueError("archive drift")
    expected = {f["path"]: f for f in manifest["files"] if f["path"].startswith(PREFIX)}
    if not expected: raise ValueError("empty inlineAssembly corpus")
    rows, seen = [], set()
    with tarfile.open(archive) as tar:
        for member in tar:
            name = member.name
            if name.startswith("/") or ".." in PurePosixPath(name).parts:
                raise ValueError("unsafe archive member")
            if not name.startswith(PREFIX): continue
            if not member.isfile():
                if member.isdir(): continue
                raise ValueError("non-regular corpus member")
            if name in seen or name not in expected: raise ValueError("duplicate/unlisted corpus member")
            seen.add(name)
            data = tar.extractfile(member).read()
            row = expected[name]
            if len(data) != row["bytes"] or sha(data) != row["sha256"]:
                raise ValueError("fixture drift: " + name)
            data.decode("utf-8", errors="strict")
            rows.append(dict(row))
            if destination:
                target = destination / name
                # An existing extraction is immutable; never repair it silently.
                if target.exists():
                    if target.read_bytes() != data: raise ValueError("extraction drift: " + name)
                else:
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_bytes(data)
    if seen != set(expected): raise ValueError("missing corpus members")
    return {"schema":1, "commit":PIN, "archiveSha256":ARCHIVE_SHA,
            "snapshotSha256":sha(snapshot.read_bytes()), "files":sorted(rows,key=lambda r:r["path"]),
            "scope":"Inventory only; no execution or Lean correspondence implied."}
def main():
    ap=argparse.ArgumentParser(); ap.add_argument("--extract",type=Path); ap.add_argument("--out",type=Path,required=True)
    a=ap.parse_args(); result=inventory(ROOT/"tests/upstream/solidity-0.8.38.tar.gz",ROOT/"tests/upstream/snapshot.json",a.extract)
    a.out.parent.mkdir(parents=True,exist_ok=True); a.out.write_text(json.dumps(result,indent=2)+"\n")
    print(str(len(result["files"]))+" pinned assembly fixtures verified")
if __name__ == "__main__": main()
