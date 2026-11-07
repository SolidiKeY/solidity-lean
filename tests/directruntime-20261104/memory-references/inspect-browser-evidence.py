"""Guard regression: exact raw replay evidence must not be replaced by metadata.

Verify every requested archive member, original wire bytes and saved replies.
Reuse the authenticated owner reconciliation helpers; never run its harness,
a browser, a build or a STOP benchmark. Observed parity is not semantic proof.
"""
import collections
import difflib
import gzip
import hashlib
import importlib.util
import json
import pathlib
import resource
import subprocess
import sys
import tarfile

if not __debug__:
    raise RuntimeError("Archive inspection requires ordinary Python")
repo, inbox, out = [pathlib.Path(p).resolve() for p in sys.argv[1:]]
out.mkdir(parents=True, exist_ok=False)
owner = "cc62220dcf1a47771536d75599b0ef588d143d62"
base = repo/"tests/directruntime-20261104/memory-references/runtime/master-5f145-validation"
sha = lambda data: hashlib.sha256(data).hexdigest()

def unpack(name, expected, count, folder):
    archive = inbox/name
    assert sha(archive.read_bytes()) == expected
    folder.mkdir()
    with tarfile.open(archive, "r:gz") as tar:
        members = tar.getmembers()
        names = [m.name for m in members]
        assert len(names) == len(set(names)) == count
        for member in members:
            path = pathlib.PurePosixPath(member.name)
            assert member.isfile() and not path.is_absolute() and ".." not in path.parts
        manifest = json.loads(tar.extractfile("files.json").read())
        wanted = {row["path"].lstrip("/"): row for row in manifest}
        assert len(wanted) == len(manifest) == count-1
        assert set(names) == set(wanted) | {"files.json"}
        for member in members:
            data = tar.extractfile(member).read()
            if member.name in wanted:
                assert len(data) == wanted[member.name]["bytes"]
                assert sha(data) == wanted[member.name]["sha256"]
            destination = folder/member.name
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(data)
    return {"archive": str(archive), "sha256": expected, "members": count, "payloadFiles": len(manifest), "allMemberHashesVerified": True}

a = unpack("replay-evidence.tar.gz", "da15f10be44a77b18d488ab63312b40b8d0d9978ceb395cce3b446a73001a0ad", 180, out/"replay")
b = unpack("reconciliation-evidence.tar.gz", "40436ffb2fb002578dc00da33e3e0a3733a339b82c96f756b44e78a9c2b6859e", 17, out/"reconciliation")
replay = out/"replay/workspace/scratch/browser-chain/b-original-replay"
recon = out/"reconciliation/workspace/scratch/browser-chain/b-original-reconciliation"
controls = replay/"controls"
original = base/"source-traces"
journal = (original/"requests.jsonl").read_bytes()
assert len(journal) == 537822 and sha(journal) == "ae658ff7ea04b163a9d3939f58fc4b30acc15cf4cbe5487ca4abf5baddbb7f1d"
archived_inbox = out/"reconciliation/workspace/h62-coordinator-inputs/router-20261106T200314Z"
assert (archived_inbox/"requests.jsonl").read_bytes() == journal
assert (archived_inbox/"browser-handoff.json").read_bytes() == (original/"browser-handoff.json").read_bytes()
handoff = json.loads((inbox/"handoff.json").read_text())
assert sha((inbox/"handoff.json").read_bytes()) == "ce3b211c7482f7c23761032aef098129c97152578eae9a6cb0484ab7ed594fe0"
summary = json.loads((replay/"summary.json").read_text())
assert summary == handoff["decisiveOutput"]
checker_path = out/"replay/workspace/solidity-lean/tests/directruntime-20261104/native-browser/reconcile-b-journal.py"
checker = checker_path.read_bytes()
assert checker == subprocess.check_output(["git", "-C", str(repo), "show", owner+":tests/directruntime-20261104/native-browser/reconcile-b-journal.py"])
spec = importlib.util.spec_from_file_location("owner_reconciliation", checker_path)
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
committed = (out/"replay/workspace/solidity-lean/tests/directruntime-20261104/native-browser/h81-memory-controls.mjs").read_bytes()
executed = gzip.decompress((replay/"executed-harness.mjs.gz").read_bytes())
assert sha(committed) == summary["committedHarnessSha256"]
assert sha(executed) == summary["executedHarnessSha256"]
assert committed == subprocess.check_output(["git", "-C", str(repo), "show", owner+":tests/directruntime-20261104/native-browser/h81-memory-controls.mjs"])
old, new = executed.decode().splitlines(True), committed.decode().splitlines(True)
assert len(old) == len(new)
changes = [(a,b) for a,b in zip(old,new) if a != b]
assert len(changes) == 1
before, after = changes[0]
assert before.startswith("const report={") and after.startswith("const report={")
assert before.partition("boundary:")[0] == after.partition("boundary:")[0]
assert before.endswith("};\n") and after.endswith("};\n")
(out/"harness-boundary.diff").write_text("".join(difflib.unified_diff(old,new)))
(out/"executed-harness.mjs").write_bytes(executed)
inv = json.loads((controls/"control-inventory-with-guard.json").read_text())
wires = [json.loads(line) for line in (controls/"browser-attempts-with-guard.jsonl").read_text().splitlines()]
requests = [json.loads(line) for line in journal.splitlines()]
cases = json.loads((original/"browser-handoff.json").read_text())["cases"]
native_stream = [json.loads(line) for line in (controls/"native-replies-with-guard.jsonl").read_text().splitlines()]
assert native_stream.pop(0) == {"ready": True}
assert len(requests) == len(wires) == len(cases) == len(inv["requests"]) == len(inv["native"]) == len(inv["browser"]) == len(native_stream) == 84
assert "".join(row["wire"]+"\n" for row in wires).encode() == journal
assert inv["requestMode"] == "exact-delivered-B-journal" and inv["identityNonVacuityComplete"]
assert not inv["semanticAcceptanceComplete"]
for key in ["errors", "forbiddenNativeLoads", "forbiddenBrowserAssets", "externalRequests", "requiredControlFailures"]: assert inv[key] == []
rows = []
counts = collections.Counter()
for i,(case,request,wire,meta,native,browser) in enumerate(zip(cases,requests,wires,inv["requests"],inv["native"],inv["browser"])):
    key = case["id"]+"."+case["modality"]+(".ir" if case["viaIR"] else ".non-ir")
    assert key == meta["caseKey"] == native["caseKey"] == browser["caseKey"]
    parsed = json.loads(wire["wire"])
    assert not helper.compare(request,parsed) and request == parsed
    helper.selector(parsed)
    assert sha(wire["wire"].encode()) == wire["wireSha256"] == meta["wireSha256"] == native["wireSha256"] == browser["wireSha256"]
    assert native_stream[i] == native["reply"]
    assert native["reply"]["results"] == browser["reply"]["results"] and not helper.compare(native["reply"]["results"],browser["reply"]["results"])
    assert len(native["reply"]["results"]) == 1
    reply = native["reply"]["results"][0]
    assert reply["sourceId"] == request["sourceId"] and reply["tag"] == case["modality"]
    status = reply["status"]
    assert case["requiredProven"] == (status == "proved")
    assert browser["boot"]["kind"] == "generated-c-wasm"
    assert browser["boot"]["build"] == inv["freshness"]["wasm"]["binarySha256"]
    assert browser["reply"]["timings"]["backend"] == "generated-c-wasm"
    assert browser["reply"]["timings"]["checkSequence"] == 1
    assert browser["reply"]["timings"]["environmentImports"] == 0
    assert case["sourceSha256"] == meta["sourceHash"] == sha((repo/meta["original"]).read_bytes())
    fixture = out/"replay"/meta["fixture"].lstrip("/")
    assert sha(fixture.read_bytes()) == meta["fixtureSha256"]
    assert json.loads(fixture.read_text())["header"] == meta["compilerHeader"]
    companion = fixture.with_name(fixture.name.removesuffix(".ast.json")+".sol")
    assert sha(companion.read_bytes()) == case["sourceSha256"]
    counts[status] += 1
    rows.append({"caseKey": key, "status": status, "wireSha256": wire["wireSha256"], "exactRequestEqual": True, "backendResultsEqual": True})
assert counts == {"proved":64,"refuted":16,"pending":4}
identity = [r for r in rows if r["caseKey"].startswith("identity.diamond.")]
assert len(identity) == 2 and all(r["status"] == "proved" for r in identity)
halt_kinds = collections.Counter(r["modelHalt"] for r in inv["requests"])
assert halt_kinds == {"success":48,"revert":16,"panic":8,"conditionalSuccessOrRevert":8,"successOrExhausted":4}
assert sum(halt_kinds[k] for k in ["success","revert","panic"]) == summary["concreteModelHaltExpectationsPerBackend"] == 72
wire_report = json.loads((replay/"wire-reconciliation.json").read_text())
assert wire_report["exactRequestObjectsEqual"] == 84 and wire_report["commonValueDifferences"] == 0
assert all(r["exactRequestObjectEqual"] for r in wire_report["cases"])
assert json.loads((recon/"accepted-reconciliation.json").read_text())["exactRequestObjectsEqual"] == 0
(out/"case-results.json").write_text(json.dumps(rows,indent=2)+"\n")
result = {"archives":[a,b],"ownerHead":owner,"exactJournalSha256":sha(journal),"casesPerBackend":84,"statusCountsPerBackend":dict(counts),"mandatoryIdentityDiamondBothSettings":True,"archivedExecutedHarnessSha256":sha(executed),"archivedCommittedHarnessSha256":sha(committed),"harnessDelta":"One report-boundary initializer line; all other bytes/lines unchanged.","checkerSha256":sha(checker),"fixtureModelHaltExpectations":72,"fixtureHaltKinds":dict(halt_kinds),"separateRuntimeHaltFieldClaimed":False,"localReplayPerformed":False,"selfMaxRssKiB":resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,"childMaxRssKiB":resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,"limitations":["Read-only verification of retained owner observations;no new execution/build/STOP rerun.","72 model-halt expectations are fixture metadata,not72 separately observed runtime halt fields.","Four diamonds pending;no compiler preservation,universal machine correctness or semantic absence certification."]}
(out/"inspection.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result))
