#!/usr/bin/env python3
"""H279 additive mixed-pin compatibility; never accepts the V1 global audit.

The V1 ledger, exact pins, revision checks and validator remain available unchanged.
V2 applies an explicit before/after delta, binds exact checked source bytes, and
uses the original statement/closure/trust validators. This supplies scoped audit
compatibility only; global accounting, producer adequacy and review remain OPEN.
"""
import argparse, hashlib, importlib.util, io, json, pathlib, re, subprocess, sys, tarfile
sys.dont_write_bytecode = True
ROOT = pathlib.Path(__file__).resolve().parents[1]
POLICY = "tests/roadmap-v16/mixed-premises.json"
DESCRIPTOR = "tests/roadmap-v16/mixed-premises-v2.json"
BASELINE = "f71b010fd1a9c60ee0dad03b3c43edb4ed44a148"
PUBLIC = "099bfbe185731c354b12a40f28ccf5d98534c779"
sp = importlib.util.spec_from_file_location("mixed_v1", ROOT/"scripts/roadmap-v16-mixed-audit.py")
v1 = importlib.util.module_from_spec(sp); sp.loader.exec_module(v1)
core = v1.core

def digest(data): return hashlib.sha256(data).hexdigest()
def git_bytes(rev, name):
    return subprocess.check_output(["git", "show", rev+":"+name], cwd=ROOT)
def production_identity(root=ROOT):
    names = subprocess.check_output(["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard", "*.lean"], cwd=root).decode().split("\0")
    h = hashlib.sha256()
    for name in sorted(set(n for n in names if n.startswith("Solidity/") or n == "Solidity.lean")):
        h.update(name.encode()+b"\0"+(root/name).read_bytes()+b"\0")
    return h.hexdigest()
def lean_tree_identity(root=ROOT):
    names=subprocess.check_output(["git","ls-files","-z","--cached","--others","--exclude-standard","*.lean"],cwd=root).decode().split("\0")
    h=hashlib.sha256()
    for name in sorted(set(n for n in names if n)): h.update(name.encode()+b"\0"+(root/name).read_bytes()+b"\0")
    return h.hexdigest()
def published_production_identity(revision):
    archive=subprocess.check_output(["git","archive",revision,"--","Solidity","Solidity.lean"],cwd=ROOT)
    with tarfile.open(fileobj=io.BytesIO(archive),mode="r:") as tar:
        files={member.name:tar.extractfile(member).read() for member in tar if member.isfile() and member.name.endswith(".lean")}
    h=hashlib.sha256()
    for name in sorted(files): h.update(name.encode()+b"\0"+files[name]+b"\0")
    return h.hexdigest()
def rename_private(value, relocations):
    if isinstance(value, str):
        for old, new in relocations.items(): value=value.replace(old, new)
        return value
    if isinstance(value, list): return [rename_private(v, relocations) for v in value]
    if isinstance(value, dict): return {rename_private(k, relocations): rename_private(v, relocations) for k,v in value.items()}
    return value

def validate_descriptor(d, root=ROOT):
    core.require(set(d) == {"version", "authority", "baselinePolicySha256", "originalLedgerSha256", "checkedLedgerSha256", "productionRevision", "productionLeanTreeSha256", "toolchainSha256", "lakefileSha256", "extractors", "producers", "privateModuleRelocations", "pinDelta"}, "unexpected/missing compatibility field")
    core.require(d["version"] == 2 and d["authority"] == "H279", "wrong compatibility version/authority")
    frozen = git_bytes(BASELINE, POLICY)
    core.require((root/POLICY).read_bytes() == frozen, "original exact V1 policy changed")
    core.require(d["baselinePolicySha256"] == digest(frozen), "wrong original policy identity")
    original_ledger = git_bytes(PUBLIC, core.LEDGER)
    core.require(d["originalLedgerSha256"] == digest(original_ledger), "wrong original ledger identity")
    core.require(d["checkedLedgerSha256"] == digest((root/core.LEDGER).read_bytes()), "checked ledger drift")
    core.require(d["productionLeanTreeSha256"] == production_identity(root), "checked production tree drift")
    core.require(re.fullmatch("[0-9a-f]{40}", d["productionRevision"]) is not None, "production revision is not full immutable SHA")
    resolved=subprocess.run(["git","rev-parse",d["productionRevision"]+"^{commit}"],cwd=root,text=True,capture_output=True)
    core.require(resolved.returncode == 0 and resolved.stdout.strip() == d["productionRevision"], "production identity is not exact commit")
    core.require(subprocess.run(["git", "merge-base", "--is-ancestor", d["productionRevision"], "HEAD"], cwd=root, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0, "unknown production revision")
    core.require(d["productionLeanTreeSha256"] == published_production_identity(d["productionRevision"]), "production revision does not identify checked bytes")
    core.require(digest((root/"lean-toolchain").read_bytes()) == d["toolchainSha256"], "changed pinned toolchain")
    core.require(digest((root/"lakefile.toml").read_bytes()) == d["lakefileSha256"], "checked Lake configuration drift")
    for name, sha in d["extractors"].items():
        core.require(name in {"tests/roadmap-v16/Inventory.lean", "tests/roadmap-v16/MixedMemoryControls.lean"}, "unexpected extractor")
        core.require(digest((root/name).read_bytes()) == sha, "checked extractor drift")
    core.require(len(d["extractors"]) == 2, "missing actual extractor")
    expected_producers = ["Solidity/Evm/"+f+".lean" for f in ["Compiler", "MemoryCompile", "MemoryGrowResult", "MemorySource", "MemoryStructAlloc", "MemoryAllocSourceExamples", "MemoryCompileExamples"]]+["Solidity/Semantics/Run.lean", "Solidity/Calculus/Correct.lean"]
    core.require(set(d["producers"]) == set(expected_producers), "producer source omitted")
    for name, pair in d["producers"].items():
        core.require(pair["original"] == digest(git_bytes(PUBLIC, name)), "wrong original producer identity")
        core.require(pair["checked"] == digest((root/name).read_bytes()), "checked producer drift")
    original = json.loads(frozen)
    relocations = d["privateModuleRelocations"]
    for old, new in relocations.items():
        stem = old.removeprefix("_private.Solidity.Roadmap.V16.").removesuffix(".")
        core.require(old == "_private.Solidity.Roadmap.V16."+stem+"." and new == "_private.Solidity.Examples.Roadmap.V16."+stem+".", "not a private module relocation")
        core.require((root/"Solidity/Examples/Roadmap/V16"/(stem+".lean")).is_file() and not (root/"Solidity/Roadmap/V16"/(stem+".lean")).exists(), "incorrect module relocation")
    effective = rename_private(original, relocations)
    core.require(set(d["pinDelta"]) == {"axiomPins", "dependencyPins"}, "unexpected policy delta")
    for field, changes in d["pinDelta"].items():
        for name, pair in changes.items():
            core.require(set(pair) == {"before", "after"}, "malformed exact delta")
            core.require(effective[field].get(name) == pair["before"], "delta does not preserve original pins")
            core.require(isinstance(pair["after"], list) and len(pair["after"]) == len(set(pair["after"])), "invalid exact pins")
            core.require(pair["after"] == sorted(pair["after"]), "noncanonical exact pins")
            if field == "axiomPins": core.require(set(pair["after"]) <= core.AXIOMS, "trust expansion")
            effective[field][name] = pair["after"]
    # All original public statements, observations and obligation IDs are kept.
    for field in original.keys()-{"axiomPins", "dependencyPins"}:
        core.require(effective[field] == original[field], "public statement/obligation changed")
    core.require(set(effective["axiomPins"]) == set(effective["dependencyPins"]), "missing paired exact pins")
    for name in effective["dependencyPins"]:
        core.require(not any(x == "sorryAx" or "ofReduceBool" in x or "native_decide" in x for x in effective["dependencyPins"][name]), "forbidden trust shortcut")
    return effective

def capture_binding(root=ROOT):
    d=json.loads((root/DESCRIPTOR).read_text()); validate_descriptor(d, root)
    scripts=["scripts/roadmap-v16-accounting.py", "scripts/roadmap-v16-check.py", "scripts/roadmap-v16-mixed-audit.py", "scripts/roadmap-v16-heap-audit.py", "scripts/roadmap-v16-mixed-compatibility-v2.py", DESCRIPTOR]
    return {"version": 2, "scope": "SCOPED_COMPATIBILITY_ONLY_GLOBAL_AUDIT_OPEN", "head": subprocess.check_output(["git","rev-parse","HEAD"],cwd=root,text=True).strip(), "productionLeanTreeSha256": production_identity(root), "leanTreeSha256": lean_tree_identity(root), "lakefileSha256": digest((root/"lakefile.toml").read_bytes()), "lakeManifestSha256": digest((root/"lake-manifest.json").read_bytes()) if (root/"lake-manifest.json").exists() else None, "checkedLedgerSha256": digest((root/core.LEDGER).read_bytes()), "extractors": d["extractors"], "validatorSources": {name:digest((root/name).read_bytes()) for name in scripts}}

def snapshot(path, root=ROOT):
    text=pathlib.Path(path).read_text();core.require(text.rstrip().endswith("exit=0"), "compatibility command did not pass")
    def marker(prefix):
        lines=[s[len(prefix):] for s in text.splitlines() if s.startswith(prefix)]
        core.require(len(lines)==1, "missing/duplicate V2 metadata/binding: "+prefix)
        return json.loads(lines[0])
    before=marker("V16-COMPAT-V2-BINDING-BEFORE ");after=marker("V16-COMPAT-V2-BINDING-AFTER ")
    core.require(before==after==capture_binding(root), "stale/changed V2 execution source binding")
    return marker("V16-INVENTORY ")

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("inventory");ap.add_argument("controls");ap.add_argument("report");a=ap.parse_args()
    d=json.loads((ROOT/DESCRIPTOR).read_text());policy=validate_descriptor(d)
    inventory=snapshot(a.inventory);meta=snapshot(a.controls)
    core.validate_owned_imports({"sources":core.sources(ROOT),"modules":inventory["modules"]})
    v1.statements({r["name"]:r for r in inventory["theorems"]},policy)
    nodes=v1.h.merged([meta]);reached=v1.controls(nodes,policy)
    report={"version":2,"scopedPinsAndStatements":"PASS_PENDING_REVIEW","strictV1GlobalMixedAudit":"PENDING","allGlobalObligations":"OPEN","laneComplete":False,"originalLedgerAndGuards":"RETAINED; not replaced or waived","baselineObligationIds":policy["baselineObligationIds"],"binding":capture_binding(),"exactDelta":d["pinDelta"],"productionIdentity":{k:d[k] for k in ["productionRevision","productionLeanTreeSha256","producers"]},"reachedNodes":len(reached),"logs":{str(p):digest(pathlib.Path(p).read_bytes()) for p in [a.inventory,a.controls]},"boundary":"Scoped versioned compatibility only. No global G03 closure, Source/native correspondence, producer adequacy or physical/EVM acceptance. Original byte-equality guards still govern V1."}
    pathlib.Path(a.report).write_text(json.dumps(report,indent=2)+"\n")
    print("PASS V2 scoped exact pins/statements; review and full strict audit remain OPEN")
if __name__ == "__main__": main()
