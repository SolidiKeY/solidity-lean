#!/usr/bin/env python3
"""Export every pinned Osaka state-test variant to a deterministic off-Git stream."""
import argparse
import gzip
import hashlib
import io
import json
import tarfile
from pathlib import Path
from pipeline import EEST_SHA, file_sha


def export(root):
    archive = root/"upstream/fixtures_develop-v5.3.0.tar.gz"
    if file_sha(archive) != EEST_SHA: raise ValueError("fixture archive checksum")
    census = json.loads((root/"evidence/eest-census.json").read_text())
    if census["archive_sha256"] != EEST_SHA: raise ValueError("census archive binding")
    by_path = {}
    expected = set()
    for index, row in enumerate(census["cases"]):
        by_path.setdefault(row["path"], []).append((index, row))
        key = (row["path"], row["case"], row["variant"])
        if key in expected: raise ValueError("duplicate census variant")
        expected.add(key)
    if not expected: raise ValueError("empty census")
    destination = root/"eest-inputs.jsonl.gz"
    seen = set()
    with destination.open("wb") as raw, gzip.GzipFile(filename="", fileobj=raw, mode="wb", mtime=0) as zipped:
        with tarfile.open(archive, "r|gz") as tar:
            for member in tar:
                if member.name not in by_path: continue
                data = tar.extractfile(member).read()
                digest = hashlib.sha256(data).hexdigest()
                doc = json.loads(data)
                for index, row in by_path[member.name]:
                    if row["sha256"] != digest: raise ValueError("census fixture bytes changed")
                    fixture = doc[row["case"]]
                    post = fixture["post"]["Osaka"][row["variant"]]
                    if post["indexes"] != row["indexes"]: raise ValueError("census indexes changed")
                    key = (member.name, row["case"], row["variant"])
                    seen.add(key)
                    record = dict(index=index, path=member.name, case=row["case"], variant=row["variant"],
                                  fixture_sha256=digest, env=fixture["env"], pre=fixture["pre"],
                                  config=fixture.get("config", {}), post=post)
                    zipped.write((json.dumps(record, sort_keys=True, separators=(",", ":"))+"\n").encode())
    if seen != expected: raise ValueError("incomplete fixture export")
    receipt = dict(cases=len(seen), archive_sha256=EEST_SHA, census_sha256=file_sha(root/"evidence/eest-census.json"),
                   stream_sha256=file_sha(destination), stream=str(destination), role="reference-input-only")
    (root/"evidence/eest-export.json").write_text(json.dumps(receipt, indent=2)+"\n")
    return receipt

if __name__ == "__main__":
    p = argparse.ArgumentParser(__doc__); p.add_argument("--bulk", type=Path, required=True); a = p.parse_args()
    root=a.bulk.resolve(); repo=Path(__file__).resolve().parents[4]
    if root==repo or repo in root.parents: p.error("bulk must stay outside repository")
    print(json.dumps(export(root)))
