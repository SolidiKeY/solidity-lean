#!/usr/bin/env python3
"""Guarded regression: wrong-fork or wrong-format fixtures must not enter a pinned deterministic reference-input stream. Unbound Engine-X allocations must not be treated as complete inputs. Exporting inputs is never execution conformance."""
import argparse
import gzip
import hashlib
import io
import json
import tarfile
import tempfile
from functools import lru_cache
from pathlib import Path
from pipeline import EEST_SHA, file_sha


FORMATS = {"state_test": "eest", "blockchain_test": "blockchain",
           "blockchain_test_engine": "engine", "blockchain_test_engine_x": "engine-x",
           "blockchain_test_sync": "sync", "transaction_test": "transaction"}


def blockchain_record(index, row, fixture, digest, kind="blockchain_test"):
    if kind not in FORMATS or kind in ("state_test", "transaction_test") or fixture.get("network") != "Osaka" or fixture.get("_info", {}).get("fixture-format") != kind:
        raise ValueError("blockchain format/fork mismatch")
    return dict(index=index, path=row["path"], case=row["case"], variant=0,
                fixture_sha256=digest, fixture=fixture, status="input-only-not-executed")


def transaction_record(index, row, fixture, digest):
    """Guard wrong-fork transaction expectations being imported as Osaka inputs."""
    results = fixture.get("result")
    if fixture.get("_info", {}).get("fixture-format") != "transaction_test" or not isinstance(results, dict) or not isinstance(results.get("Osaka"), dict):
        raise ValueError("transaction format/fork mismatch")
    if not isinstance(fixture.get("txbytes"), str) or not fixture["txbytes"].startswith("0x"):
        raise ValueError("transaction bytes missing")
    return dict(index=index, path=row["path"], case=row["case"], variant=0,
                fixture_sha256=digest, fixture=fixture, selected_fork="Osaka",
                expected=results["Osaka"], status="input-only-not-executed")


def allocation_inputs(archive, root):
    """Stage canonical, seekable Osaka preallocs with exact archive membership.

    Offsets refer to the staged canonical stream, not an extracted directory.
    No allocation or genesis field is execution evidence.
    """
    destination = root/"engine-x-allocations.jsonl"
    temporary = destination.with_name(destination.name + ".partial")
    index_path = root/"engine-x-allocations-index.json"
    index_temporary = index_path.with_name(index_path.name + ".partial")
    groups = {}
    with temporary.open("wb") as out, tarfile.open(archive, "r|gz") as tar:
        for member in tar:
            if not member.name.startswith("fixtures/blockchain_tests_engine_x/pre_alloc/") or not member.name.endswith(".json"): continue
            raw = tar.extractfile(member).read()
            group = json.loads(raw)
            if group.get("network") != "Osaka": continue
            key = Path(member.name).stem
            if key in groups: raise ValueError("duplicate allocation key")
            ids = group.get("testIds")
            if not isinstance(ids, list) or len(ids) != len(set(ids)) or group.get("testCount") != len(ids): raise ValueError("allocation test count/identity mismatch")
            if not isinstance(group.get("pre"), dict) or group.get("preAccountCount") != len(group["pre"]): raise ValueError("allocation account count mismatch")
            if not isinstance(group.get("environment"), dict) or not isinstance(group.get("genesis"), dict): raise ValueError("allocation environment/genesis missing")
            line = (json.dumps(dict(path=member.name, source_sha256=hashlib.sha256(raw).hexdigest(), allocation=group), sort_keys=True, separators=(",", ":"))+"\n").encode()
            groups[key] = dict(path=member.name, offset=out.tell(), length=len(line), source_sha256=hashlib.sha256(raw).hexdigest(), record_sha256=hashlib.sha256(line).hexdigest())
            out.write(line)
    if not groups: raise ValueError("empty Osaka allocation stream")
    index_temporary.write_text(json.dumps(groups,sort_keys=True,indent=2)+"\n")
    return groups, temporary, destination, index_temporary, index_path


def allocation_reference(fixture, case, groups, stream):
    key = fixture.get("preHash")
    if key not in groups: raise ValueError("missing Engine-X preHash allocation")
    ref = groups[key]
    stream.seek(ref["offset"])
    raw = stream.read(ref["length"])
    if hashlib.sha256(raw).hexdigest() != ref["record_sha256"]: raise ValueError("allocation record digest mismatch")
    decoded = json.loads(raw)
    if decoded["path"] != ref["path"] or decoded["source_sha256"] != ref["source_sha256"]: raise ValueError("allocation index/record provenance mismatch")
    group = decoded["allocation"]
    if group["network"] != fixture["network"] or case not in group["testIds"]: raise ValueError("allocation fork/case membership mismatch")
    return dict(pre_hash=key, stream="engine-x-allocations.jsonl", **ref)


def export(root, kind="state_test"):
    if kind not in FORMATS: raise ValueError("unsupported export format")
    archive = root/"upstream/fixtures_develop-v5.3.0.tar.gz"
    if file_sha(archive) != EEST_SHA: raise ValueError("fixture archive checksum")
    census_path = root/("evidence/eest-census.json" if kind == "state_test" else "evidence/archive-census.json")
    census = json.loads(census_path.read_text())
    if kind != "state_test":
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
    destination = root/(FORMATS[kind]+"-inputs.jsonl.gz")
    allocation = allocation_inputs(archive, root) if kind == "blockchain_test_engine_x" else None
    allocation_stream = allocation[1].open("rb") if allocation else None
    referenced_groups = set()
    seen = set()
    temporary = destination.with_name(destination.name + ".partial")
    try:
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
                        if kind != "state_test":
                            record = transaction_record(index, row, fixture, digest) if kind == "transaction_test" else blockchain_record(index, row, fixture, digest, kind)
                            if allocation:
                                record["allocation_ref"] = allocation_reference(fixture, row["case"], allocation[0], allocation_stream)
                                referenced_groups.add(fixture["preHash"])
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
    finally:
        if allocation_stream: allocation_stream.close()
    if seen != expected: raise ValueError("incomplete fixture export")
    if allocation:
        allocation[1].replace(allocation[2])
        allocation[3].replace(allocation[4])
    temporary.replace(destination)
    receipt = dict(cases=len(seen), archive_sha256=EEST_SHA, census_sha256=file_sha(census_path),
                   stream_sha256=file_sha(destination), stream=str(destination), role="reference-input-only")
    if allocation:
        receipt["allocation"] = dict(groups=len(allocation[0]), referenced_groups=len(referenced_groups), stream="engine-x-allocations.jsonl", stream_sha256=file_sha(allocation[2]), index="engine-x-allocations-index.json", index_sha256=file_sha(allocation[4]))
    receipt_path = root/("evidence/"+FORMATS[kind]+"-export.json")
    receipt_temporary = receipt_path.with_name(receipt_path.name + ".partial")
    receipt_temporary.write_text(json.dumps(receipt, indent=2)+"\n")
    receipt_temporary.replace(receipt_path)
    return receipt


@lru_cache(maxsize=2)
def _archive_input_expectations(archive_name, archive_sha, generator_pins, kind):
    """Regenerate from verified upstream bytes, never a mutable receipt/cache file.

    Guard coordinated input/result/receipt substitution. Reuse the existing
    census/export algorithms and record their per-file source audit. The cache
    is process-local immutable JSON, keyed by archive and generator hashes.
    """
    from archive_census import census
    archive = Path(archive_name)
    if archive_sha != EEST_SHA or file_sha(archive) != EEST_SHA:
        raise ValueError("untrusted fixture archive")
    with tempfile.TemporaryDirectory(prefix="engine-archive-verification-", dir=archive.parent.parent) as tmp:
        root = Path(tmp)
        (root/"upstream").mkdir(); (root/"evidence").mkdir()
        (root/"upstream/fixtures_develop-v5.3.0.tar.gz").symlink_to(archive)
        census(root)
        generated = export(root, kind)
        names = [FORMATS[kind]+"-inputs.jsonl.gz", "archive-inventory.jsonl.gz", "evidence/archive-census.json"]
        sources = {}
        if kind == "blockchain_test_engine_x":
            names += ["engine-x-allocations.jsonl", "engine-x-allocations-index.json"]
            sources = {entry["path"]: entry["source_sha256"] for entry in
                       json.loads((root/"engine-x-allocations-index.json").read_text()).values()}
        with gzip.open(root/(FORMATS[kind]+"-inputs.jsonl.gz"), "rt") as stream:
            for line in stream:
                row = json.loads(line)
                previous = sources.setdefault(row["path"], row["fixture_sha256"])
                if previous != row["fixture_sha256"]:
                    raise ValueError("inconsistent archive source audit")
        proof = dict(algorithm="verify pinned archive SHA256; regenerate existing census/export; compare exact stream/index hashes", format=kind,
                     archive_sha256=EEST_SHA, cases=generated["cases"],
                     files={name: file_sha(root/name) for name in names},
                     generator_sha256=dict(generator_pins), source_files=sources)
    if file_sha(archive) != EEST_SHA:
        raise ValueError("fixture archive changed during regeneration")
    return json.dumps(proof, sort_keys=True)


def verify_archive_inputs(root, kind):
    """Guard coordinated fixture/expectation/receipt substitutions against the archive."""
    if kind not in ("blockchain_test_engine_x", "transaction_test"):
        raise ValueError("unsupported archive verification format")
    archive = (root/"upstream/fixtures_develop-v5.3.0.tar.gz").resolve()
    actual = file_sha(archive)
    if actual != EEST_SHA:
        raise ValueError("untrusted fixture archive")
    directory = Path(__file__).resolve().parent
    pins = tuple((name, file_sha(directory/name)) for name in
                 ("archive_census.py", "eest_export.py", "pipeline.py"))
    proof = json.loads(_archive_input_expectations(str(archive), actual, pins, kind))
    for name, expected in proof["files"].items():
        if file_sha(root/name) != expected:
            raise ValueError("input differs from pinned archive: " + name)
    return proof


def verify_engine_x_inputs(root):
    """Preserve the Engine-X verifier interface and its archive anchor."""
    return verify_archive_inputs(root, "blockchain_test_engine_x")


if __name__ == "__main__":
    p = argparse.ArgumentParser(__doc__); p.add_argument("--verify", action="store_true"); p.add_argument("--bulk", type=Path, required=True); p.add_argument("--format", choices=list(FORMATS), default="state_test"); a = p.parse_args()
    root=a.bulk.resolve(); repo=Path(__file__).resolve().parents[4]
    if root==repo or repo in root.parents: p.error("bulk must stay outside repository")
    print(json.dumps(verify_archive_inputs(root, a.format) if a.verify else export(root, a.format)))
