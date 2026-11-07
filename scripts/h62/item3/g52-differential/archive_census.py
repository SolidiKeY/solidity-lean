#!/usr/bin/env python3
"""Guarded regression: non-state or transition Osaka fixtures silently disappearing
from coverage accounting. Inventory only: no fixture is an execution pass.
"""
import argparse
import configparser
import gzip
import json
import tarfile
from collections import Counter
from pathlib import Path
from pipeline import EEST_SHA, EEST_COMMIT, file_sha


def inspect_fixture(path, name, fixture):
    fmt = fixture.get("_info", {}).get("fixture-format", "unrecognized")
    post = fixture.get("post")
    if isinstance(post, dict):
        forks = [(fork, len(variants)) for fork, variants in post.items()]
    elif fmt == "transaction_test" and isinstance(fixture.get("result"), dict):
        forks = [(fork, 1) for fork in fixture["result"]]
    elif isinstance(fixture.get("network"), str):
        forks = [(fixture["network"], 1)]
    else:
        forks = [("unresolved", 1)]
    forks = forks or [("unresolved", 1)]
    return [dict(role="fixture", path=path, case=name, format=fmt, fork=fork, variants=count,
                 selection="exact-osaka" if fork == "Osaka" else "osaka-transition-or-related" if "Osaka" in fork else "other-fork" if fork != "unresolved" else "unresolved",
                 status="inventory-only-not-executed") for fork, count in forks]


def inspect_allocation_group(path, doc):
    if not isinstance(doc.get("testIds"), list) or not isinstance(doc.get("network"), str) or not isinstance(doc.get("pre"), dict):
        raise ValueError("malformed allocation group")
    return dict(role="support-allocation-group", path=path, fork=doc["network"], referenced_cases=len(doc["testIds"]), declared_test_count=doc.get("testCount"), variants=0, status="support-data-not-executed")


def census(root):
    archive = root/"upstream/fixtures_develop-v5.3.0.tar.gz"
    if file_sha(archive) != EEST_SHA: raise ValueError("archive checksum mismatch")
    counts = Counter(); totals = Counter(); selections = Counter(); groups = Counter(); metadata = False
    output = root/"archive-inventory.jsonl.gz"
    with output.open("wb") as raw, gzip.GzipFile(filename="", fileobj=raw, mode="wb", mtime=0) as zipped:
        with tarfile.open(archive, "r|gz") as tar:
            for member in tar:
                totals["members"] += 1
                if not member.isfile(): totals["non-files"] += 1; continue
                if member.name == "fixtures/.meta/fixtures.ini":
                    cfg = configparser.ConfigParser();cfg.read_string(tar.extractfile(member).read().decode())
                    if cfg["fixtures"]["commit"] != EEST_COMMIT: raise ValueError("embedded commit mismatch")
                    metadata = True
                if not member.name.endswith(".json"): totals["non-json-files"] += 1; continue
                totals["json-files"] += 1
                if member.name.startswith("fixtures/.meta/"): totals["metadata-json-files"] += 1; continue
                doc = json.load(tar.extractfile(member))
                if not isinstance(doc, dict): raise ValueError("non-object fixture file")
                if member.name.startswith("fixtures/blockchain_tests_engine_x/pre_alloc/"):
                    row = inspect_allocation_group(member.name, doc)
                    totals["support-allocation-group-files"] += 1
                    totals["support-test-references"] += row["referenced_cases"]
                    groups[row["fork"]] += 1
                    zipped.write((json.dumps(row, sort_keys=True)+"\n").encode())
                    continue
                for name, fixture in doc.items():
                    if not isinstance(fixture, dict): raise ValueError("non-object fixture record")
                    totals["fixture-records"] += 1
                    for row in inspect_fixture(member.name, name, fixture):
                        counts[(row["format"], row["fork"], row["selection"])] += row["variants"]
                        selections[row["selection"]] += row["variants"]
                        zipped.write((json.dumps(row, sort_keys=True)+"\n").encode())
    if not metadata or not totals["fixture-records"]: raise ValueError("missing provenance/empty inventory")
    result = dict(archive_sha256=EEST_SHA, upstream_commit=EEST_COMMIT, inventory_sha256=file_sha(output),
                  totals=dict(totals), selections=dict(selections), support_groups_by_fork=dict(groups),
                  by_format_fork=[dict(format=f, fork=k, selection=s, variants=n) for (f,k,s),n in sorted(counts.items())],
                  execution_passes=0, full_differential_complete=False)
    (root/"evidence/archive-census.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    return dict(totals=result["totals"],selections=result["selections"],execution_passes=0)

if __name__ == "__main__":
    p=argparse.ArgumentParser(__doc__);p.add_argument("--bulk",type=Path,required=True);a=p.parse_args();root=a.bulk.resolve();repo=Path(__file__).resolve().parents[4]
    if root==repo or repo in root.parents:p.error("H44 bulk must stay outside Git")
    print(json.dumps(census(root)))
