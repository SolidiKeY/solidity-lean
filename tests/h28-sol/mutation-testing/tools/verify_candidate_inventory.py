#!/usr/bin/env python3
"""Verify the committed pointer to the isolated VM inventory proof world."""
from pathlib import Path
import hashlib
import json
import subprocess
import tarfile
import time
from archive_io import read_json, require
import checked


def sha(stream):
    value = hashlib.sha256()
    for block in iter(lambda: stream.read(1048576), b""): value.update(block)
    return value.hexdigest()


def verify(repo):
    start = time.monotonic()
    pin = read_json(repo / "tests/h28-sol/mutation-testing/bulk-data.json", repo)["candidate_inventory_audit"]
    archive = Path(pin["archive"])
    require(archive.stat().st_size == pin["bytes"], "archive size mismatch")
    with archive.open("rb") as stream: require(sha(stream) == pin["sha256"], "archive hash mismatch")
    with tarfile.open(archive, "r:gz") as tar:
        expected = {}
        for line in tar.extractfile("SHA256SUMS").read().decode().splitlines():
            digest, name = line.split("  ", 1)
            require(name not in expected and not name.startswith("/") and ".." not in Path(name).parts, "invalid archive seal")
            expected[name] = digest
        seen = set()
        for member in tar:
            require(member.isfile() and member.name not in seen and not member.name.startswith("/") and ".." not in Path(member.name).parts, "unsafe archive member")
            seen.add(member.name)
            if member.name != "SHA256SUMS": require(sha(tar.extractfile(member)) == expected[member.name], "member hash mismatch")
        require(seen == set(expected) | {"SHA256SUMS"}, "archive membership mismatch")
        require(sha(tar.extractfile("InventoryAudit.lean")) == pin["positive_source_sha256"], "positive source mismatch")
        require(sha(tar.extractfile("InventoryAudit.olean")) == pin["artifact_sha256"], "positive object mismatch")
        require("InventoryNegative.olean" not in seen, "negative control retained object")
        catalog_bytes = tar.extractfile("catalog.json").read()
        require(hashlib.sha256(catalog_bytes).hexdigest() == pin["catalog_sha256"], "catalog mismatch")
        catalog = json.loads(catalog_bytes); result = json.loads(tar.extractfile("result.json").read())
        negative = result["checks"]["known-bad-table"]
        negative_source = tar.extractfile("InventoryNegative.lean").read().decode()
        line = next(i for i, text in enumerate(negative_source.splitlines(), 1) if text.startswith("theorem accepts_all"))
        errors = [m for m in checked.messages(tar.extractfile("negative.log").read().decode()) if m["severity"] in {"error", "warning"}]
        require(negative["kind"] == "exit" and negative["exit"] == 1 and len(errors) == 1, "negative control outcome changed")
        require(errors[0]["severity"] == "error" and errors[0]["fileName"] == "InventoryNegative.lean" and errors[0]["pos"]["line"] == line and errors[0]["data"].startswith("Tactic `rfl` failed"), "negative control attribution changed")
        names = ["Solidity." + row["id"] for row in catalog["declarations"]] + ["H28.CandidateInventoryAudit." + name for name in ["accepts_all", "compound_all", "numeric_all", "increment_all"]]
        certificate = checked.success(result["checks"]["positive"], tar.extractfile("positive.log").read().decode(), names)
        require(certificate == catalog["kernel_certificate"] and len(names) == 294, "kernel certificate mismatch")
        require(result["audit_complete"] and not result["scope_complete"] and result["score"] is None, "audit boundary changed")
        require(len(catalog["declarations"]) == 290 and sum(len(row["clauses"]) for row in catalog["declarations"]) == 308, "census changed")
        require(len(catalog["fixtures"]) == 30 and len(catalog["frozen_manifests"]) == 9 and len(catalog["case_variants"]) == 17, "fixture inventory changed")
    with open(pin["dependency_pack"]["archive"], "rb") as stream:
        require(sha(stream) == pin["dependency_pack"]["sha256"], "dependency archive mismatch")
    return {"status": "pass", "command": "python3 -B tests/h28-sol/mutation-testing/tools/verify_candidate_inventory.py", "archive": str(archive), "members": len(seen), "checked_exports": len(names), "dependency_hash_verified": True, "seconds": time.monotonic() - start, "scope_complete": False, "score": None, "coordinator_pull_observed": False}


if __name__ == "__main__":
    repo = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())
    print(json.dumps(verify(repo), indent=2))
