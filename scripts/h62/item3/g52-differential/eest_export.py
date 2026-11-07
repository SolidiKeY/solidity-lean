#!/usr/bin/env python3
"""Guarded regression: wrong-fork or wrong-format fixtures must not enter a pinned deterministic reference-input stream. Exporting inputs is never execution conformance."""
import argparse
import gzip
import hashlib
import io
import json
import tarfile
from pathlib import Path
from pipeline import EEST_SHA, file_sha


def blockchain_record(index, row, fixture, digest):
    if fixture.get("network") != "Osaka" or fixture.get("_info", {}).get("fixture-format") != "blockchain_test":
        raise ValueError("blockchain format/fork mismatch")
    return dict(index=index, path=row["path"], case=row["case"], variant=0,
                fixture_sha256=digest, fixture=fixture, status="input-only-not-executed")


def export(root, kind="state_test"):
    if kind not in ("state_test", "blockchain_test"): raise ValueError("unsupported export format")
    archive = root/"upstream/fixtures_develop-v5.3.0.tar.gz"
    if file_sha(archive) != EEST_SHA: raise ValueError("fixture archive checksum")
    census_path = root/("evidence/eest-census.json" if kind == "state_test" else "evidence/archive-census.json")
    census = json.loads(census_path.read_text())
    if kind == "blockchain_test":
        inventory = root/"archive-inventory.jsonl.gz"
        if file_sha(inventory) != census["inventory_sha256"]: raise ValueError("archive inventory binding mismatch")
        selected = []
        with gzip.open(inventory, "rt") as stream:
            for line in stream:
                row = json.loads(line)
                if row.get("role") == "fixture" and row.get("format") == kind and row.get("selection") == "exact-osaka":
                    if row["variants"] != 1: raise ValueError("unexpected blockchain variants")
                    selected.append(dict(path=row["path"], case=row["case"], variant=0))
        census["cases"] = selected
    if census["archive_sha256"] != EEST_SHA: raise ValueError("census archive binding")
    by_path = {}
    expected = set()
    for index, row in enumerate(census["cases"]):
        by_path.setdefault(row["path"], []).append((index, row))
        key = (row["path"], row["case"], row["variant"])
        if key in expected: raise ValueError("duplicate census variant")
        expected.add(key)
    if not expected: raise ValueError("empty census")
    destination = root/("eest-inputs.jsonl.gz" if kind == "state_test" else "blockchain-inputs.jsonl.gz")
    seen = set()
    temporary = destination.with_name(destination.name + ".partial")
    with temporary.open("wb") as raw, gzip.GzipFile(filename="", fileobj=raw, mode="wb", mtime=0) as zipped:
        with tarfile.open(archive, "r|gz") as tar:
            for member in tar:
                if member.name not in by_path: continue
                data = tar.extractfile(member).read()
                digest = hashlib.sha256(data).hexdigest()
                doc = json.loads(data)
                for index, row in by_path[member.name]:
                    if kind == "state_test" and row["sha256"] != digest: raise ValueError("census fixture bytes changed")
                    fixture = doc[row["case"]]
                    if kind == "blockchain_test":
                        record = blockchain_record(index, row, fixture, digest)
                        seen.add((member.name, row["case"], 0))
                        zipped.write((json.dumps(record, sort_keys=True, separators=(",", ":"))+"\n").encode())
                        continue
                    post = fixture["post"]["Osaka"][row["variant"]]
                    if post["indexes"] != row["indexes"]: raise ValueError("census indexes changed")
                    key = (member.name, row["case"], row["variant"])
                    seen.add(key)
                    record = dict(index=index, path=member.name, case=row["case"], variant=row["variant"],
                                  fixture_sha256=digest, env=fixture["env"], pre=fixture["pre"],
                                  config=fixture.get("config", {}), post=post)
                    zipped.write((json.dumps(record, sort_keys=True, separators=(",", ":"))+"\n").encode())
    if seen != expected: raise ValueError("incomplete fixture export")
    temporary.replace(destination)
    receipt = dict(cases=len(seen), archive_sha256=EEST_SHA, census_sha256=file_sha(census_path),
                   stream_sha256=file_sha(destination), stream=str(destination), role="reference-input-only")
    receipt_path = root/("evidence/eest-export.json" if kind == "state_test" else "evidence/blockchain-export.json")
    receipt_temporary = receipt_path.with_name(receipt_path.name + ".partial")
    receipt_temporary.write_text(json.dumps(receipt, indent=2)+"\n")
    receipt_temporary.replace(receipt_path)
    return receipt

if __name__ == "__main__":
    p = argparse.ArgumentParser(__doc__); p.add_argument("--bulk", type=Path, required=True); p.add_argument("--format", choices=["state_test", "blockchain_test"], default="state_test"); a = p.parse_args()
    root=a.bulk.resolve(); repo=Path(__file__).resolve().parents[4]
    if root==repo or repo in root.parents: p.error("bulk must stay outside repository")
    print(json.dumps(export(root, a.format)))
