"""Guard regression: normalized replay or revalidation is not fresh-build proof.

Check exact published owner metadata against the retained original journal,
source fingerprints and committed harness. Missing remote raw archives remain
explicit; this does not execute a browser, rerun a STOP, or certify semantics.
"""
import hashlib
import json
import pathlib
import subprocess
import sys

if not __debug__:
    raise RuntimeError("Intake checks require ordinary Python")
repo, owner_head, out_arg = sys.argv[1:]
repo = pathlib.Path(repo).resolve()
out = pathlib.Path(out_arg).resolve()
out.mkdir(parents=True, exist_ok=False)
owned = repo/"tests/directruntime-20261104/memory-references"
base = owned/"runtime/master-5f145-validation"

def sha(path):
    with pathlib.Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()

def blob(head, path):
    return subprocess.check_output(["git", "-C", str(repo), "show", head+":"+path])

expected = {"b-original-replay-manifest.json": "b589a6bcd8c3a58413f0f144b7c4879b1ba81d820291505e60691276d6bfa6f3", "b-original-reconciliation-manifest.json": "149dd65a8935547044d41b2e59d52149fa893933a92f2924ec8949fd47b6c4ff"}
metadata = {}
for name, digest in expected.items():
    data = blob(owner_head, "tests/directruntime-20261104/native-browser/"+name)
    assert hashlib.sha256(data).hexdigest() == digest, name
    (out/name).write_bytes(data)
    metadata[name] = json.loads(data)
replay = metadata["b-original-replay-manifest.json"]
reconciliation = metadata["b-original-reconciliation-manifest.json"]
summary = replay["summary"]
assert summary["casesPerBackend"] == 84 and summary["exactRequestObjectsEqual"] == 84
assert summary["exactJournalWireReconstruction"] and summary["exactBackendResultObjectParity"]
assert summary["statusCountsPerBackend"] == {"proved": 64, "refuted": 16, "pending": 4}
assert summary["mandatoryIdentityDiamondBothModesBothBackends"]
assert replay["gate"]["exitCode"] == 0
assert replay["gate"]["scope"] == {"memoryMaxBytes": 12884901888, "memorySwapMaxBytes": 0}
assert not replay["gate"]["resourceStop"]
assert reconciliation["exactRequestObjectsEqual"] == 0  # Earlier field-only stage, not the final replay.
for name, digest in [("browser-handoff.json", "53c9438eb30010736432d9bcde121ef94272efcfa243c25acfc034cb79c4879f"), ("requests.jsonl", "ae658ff7ea04b163a9d3939f58fc4b30acc15cf4cbe5487ca4abf5baddbb7f1d")]:
    assert sha(base/"source-traces"/name) == digest
journal = (base/"source-traces/requests.jsonl").read_bytes()
assert len(journal) == 537822 and len(journal.splitlines()) == 84
for line in journal.splitlines():
    request = json.loads(line)
    assert request["function"] == "identity"
    selected = [n for n in request["contract"]["nodes"] if n.get("nodeType") == "FunctionDefinition" and n.get("name") == "identity"]
    assert len(selected) == 1 and selected[0]["id"] == request["sourceId"]
assert replay["originalJournalSha256"] == sha(base/"source-traces/requests.jsonl")
native = json.loads((base/"native/build.json").read_text())
compatibility = []
for head in [replay["runtimeBuildHead"], owner_head]:
    subprocess.run(["git", "-C", str(repo), "merge-base", "--is-ancestor", "b419c3cf4f642ae519b66bebc26cdf2f7cf93574", head], check=True)
    for source in native["sourceFiles"]:
        path = source["module"].replace(".", "/")+".lean"
        digest = hashlib.sha256(blob(head, path)).hexdigest()
        assert digest == source["sourceSha256"], (head, path)
        compatibility.append({"head": head, "path": path, "sha256": digest})
    for path, key in [("web/browser/direct-bridge.c", "bridgeSha256"), ("scripts/direct-runtime-closure.py", "closureScriptSha256")]:
        assert hashlib.sha256(blob(head, path)).hexdigest() == native[key]
(out/"source-compatibility.json").write_text(json.dumps(compatibility, indent=2)+"\n")
harness = blob(owner_head, "tests/directruntime-20261104/native-browser/h81-memory-controls.mjs")
assert hashlib.sha256(harness).hexdigest() == summary["committedHarnessSha256"]
(out/"committed-harness.mjs").write_bytes(harness)
raw = []
for path, digest, inbox_name in [(".lake/native-browser-b-journal-handoff-cc62220dcf1a/handoff.json", "ce3b211c7482f7c23761032aef098129c97152578eae9a6cb0484ab7ed594fe0", "handoff.json"), (".lake/native-browser-b-original-replay/evidence.tar.gz", "da15f10be44a77b18d488ab63312b40b8d0d9978ceb395cce3b446a73001a0ad", "replay-evidence.tar.gz"), (".lake/native-browser-b-original-reconciliation/evidence.tar.gz", "40436ffb2fb002578dc00da33e3e0a3733a339b82c96f756b44e78a9c2b6859e", "reconciliation-evidence.tar.gz")]:
    inbox_file = base/"browser-cc622-owner-evidence"/inbox_name
    file = inbox_file if inbox_file.is_file() else repo/path
    present = file.is_file()
    if present:
        assert sha(file) == digest, path
    raw.append({"sourcePath": str(repo/path), "path": str(file), "expectedSha256": digest, "locallyPresentAndVerified": present})
handoff_verified = False
if raw[0]["locallyPresentAndVerified"]:
    handoff = json.loads(pathlib.Path(raw[0]["path"]).read_text())
    assert handoff["head"] == owner_head
    assert handoff["sourceBuildHead"] == replay["runtimeBuildHead"]
    assert handoff["gates"][1]["command"] == replay["gate"]["command"]
    assert handoff["gates"][1]["exitCode"] == replay["gate"]["exitCode"]
    assert handoff["gates"][1]["wallSeconds"] == replay["gate"]["wallSeconds"]
    assert handoff["gates"][1]["scope"] == replay["gate"]["scope"]
    decisive = handoff["decisiveOutput"]
    assert decisive["exactRequestObjectsEqual"] == summary["exactRequestObjectsEqual"]
    assert decisive["statusCountsPerBackend"] == summary["statusCountsPerBackend"]
    for key in ["casesPerBackend", "exactJournalWireReconstruction", "exactBackendResultObjectParity", "concreteModelHaltExpectationsPerBackend", "mandatoryIdentityDiamondBothModesBothBackends", "statusesEqualPriorNormalizedRun", "noForbiddenLoadsOrAssetsObserved", "executedHarnessSha256", "committedHarnessSha256"]:
        assert decisive[key] == summary[key]
    assert handoff["runtimeGatePass"] is False
    handoff_verified = True
result = {"ownerHead": owner_head, "runtimeBuildHead": replay["runtimeBuildHead"], "metadataSha256": expected, "originalJournalSha256": replay["originalJournalSha256"], "journalBytes": len(journal), "journalCases": 84, "sourceFingerprintsPerHead": len(native["sourceFiles"]), "headsChecked": 2, "bridgeAndClosureMatch": True, "committedHarnessSha256": summary["committedHarnessSha256"], "executedHarnessSha256Reported": summary["executedHarnessSha256"], "ownerReportedReplay": summary, "ownerReportedGate": replay["gate"], "runtimePolicy": replay["runtimePolicy"], "rawArtifacts": raw, "localRawEvidenceComplete": all(r["locallyPresentAndVerified"] for r in raw), "localHandoffPayloadVerified": handoff_verified, "limitations": ["Local verification covers Git metadata/source compatibility and retained journal, not an independent browser execution.", "A verified handoff payload is not verification of executed harness bytes or actual wire/results inside undelivered archives.", "Owner used revalidated prior fresh H81 binaries, not a new build for this replay; no unchanged STOP rerun requested.", "Four diamonds pending; no source/compiler preservation, universal machine correctness or RUNTIME_GATE_PASS."]}
(out/"intake.json").write_text(json.dumps(result, indent=2)+"\n")
print(json.dumps({k:v for k,v in result.items() if k not in ["ownerReportedReplay", "ownerReportedGate"]}))
