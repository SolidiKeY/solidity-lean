#!/usr/bin/env python3
"""Check proposed source identities only; never admission, budgets or U01 acceptance."""
import hashlib
import json
from pathlib import Path
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[2]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    proposal = json.loads((ROOT / "docs/benchmarks/u01-proposal.json").read_text())
    assert proposal["kind"] == "u01-suite-budget-proposal"
    assert proposal["approval"]["status"] == "pending"
    assert proposal["approval"]["implementationAuthorized"] is False
    counts = {}
    for group in proposal["groups"]:
        if "path" in group:
            assert digest((ROOT / group["path"]).read_bytes()) == group["sha256"], group["id"]
        if "adapter" in group:
            assert digest((ROOT / group["adapter"]).read_bytes()) == group["adapterSha256"]
            script = "import {suiteSources} from './scripts/testsuite-performance.mjs'; import fs from 'node:fs'; console.log(suiteSources(fs.readFileSync(process.argv[1], 'utf8')).length)"
            counts[group["id"]] = int(subprocess.check_output(
                ["node", "--input-type=module", "-e", script, group["path"]], cwd=ROOT, text=True))
        if "archive" not in group:
            continue
        archive = ROOT / group["archive"]
        assert digest(archive.read_bytes()) == group["archiveSha256"]
        with tarfile.open(archive, "r:gz") as source:
            if "member" in group:
                data = source.extractfile(group["member"]).read()
                assert digest(data) == group["sha256"]
            else:
                snapshot_bytes = (ROOT / group["snapshot"]).read_bytes()
                assert digest(snapshot_bytes) == group["snapshotSha256"]
                snapshot = json.loads(snapshot_bytes)
                assert snapshot["commit"] == group["upstreamCommit"]
                assert snapshot["archiveSha256"] == group["archiveSha256"]
                selected = {row["path"]: row for row in snapshot["files"]
                            if row["path"].startswith(group["memberPrefix"])
                            and row["path"].endswith(group["memberSuffix"])}
                members = [member for member in source.getmembers()
                           if member.name.startswith(group["memberPrefix"])
                           and member.name.endswith(group["memberSuffix"]) and member.isfile()]
                assert len(members) == len(selected) == group["memberCount"]
                assert {member.name for member in members} == set(selected)
                for member in members:
                    data = source.extractfile(member).read()
                    assert digest(data) == selected[member.name]["sha256"], member.name
                    assert len(data) == selected[member.name]["bytes"], member.name
                counts[group["id"]] = len(members)
    print("PROPOSAL_IDENTITIES_PASS " + json.dumps(counts, sort_keys=True))
    print("Approval, admission, phase telemetry, baseline and CI acceptance remain pending.")


if __name__ == "__main__":
    main()
