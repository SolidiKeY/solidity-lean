#!/usr/bin/env python3
"""Guard conditional G49 interface exports from becoming discharged producer facts.

Reuse the H55 sealed census and H62 type graph. Generic constructor contexts are
retained without pretending that their slots are atomic or instantiated proofs.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[4]
PACKET_COMMIT = "356fc3995378fb21a44e7c14ff9768e4d7cfefef"
SOURCE_COMMIT = "4a0b111282472d79f9aefe546c2e24ae85f4e855"
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
EXPORT_SHA = "021e1f89d7dcb0e70e0668efc83c3fe7176c1556c42f8cb3790acd690a3495a4"
RESULTS_SHA = "3f43e77b76874ad621c27518b0d50f191c6c63b0ff0414966a1774b0461fea6e"
P = "Solidity.Roadmap."
PUBLIC = P + "G49Final.PublicObligations"
THEOREM = P + "G49Final.g49_g50_of_fold"
SELECTION = {P+"Lowering": ("interface.lowering", "P8b"),
             P+"Compilation": ("interface.compilation", "G49.01"),
             P+"Execution": ("interface.execution", "G49.02"),
             P+"Pass": ("interface.pass", "G49.01"),
             P+"Cert": ("interface.cert", "G49.01"),
             PUBLIC: ("interface.public", "G49.01"),
             THEOREM: ("interface.fold", "G49.01")}


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


GRAPH = module("h62_graph", Path(__file__).with_name("graph.py"))
H55 = module("h55_census", ROOT / "scripts/h55/g49-final-theorem/constructor-slots.py")
require = GRAPH.require


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def git(*args):
    # Never use a replacement object as the authenticated source snapshot.
    env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
    env.update(GIT_NO_REPLACE_OBJECTS="1", GIT_NO_LAZY_FETCH="1", GIT_OPTIONAL_LOCKS="0")
    return subprocess.check_output(["git", "--no-replace-objects", *args], cwd=ROOT, env=env)


def checked_export(run):
    """Pin the authenticated exports and verify the entire checked source closure."""
    require(sha((run / "results.json").read_bytes()) == RESULTS_SHA, "unrecognized checked run")
    for name in ("constructor-contracts.json", "constructor-contracts-repeat.json"):
        require(sha((run / name).read_bytes()) == EXPORT_SHA, "unrecognized constructor export")
    require(git("rev-parse", "--is-shallow-repository").strip() == b"false", "shallow source history")
    grafts = Path(git("rev-parse", "--git-path", "info/grafts").decode().strip())
    require(not (grafts if grafts.is_absolute() else ROOT/grafts).exists(), "grafted source history")
    git("merge-base", "--is-ancestor", BASE, SOURCE_COMMIT)
    snapshot, status = H55.load_run(run)
    records = H55.decode((run / "results.json").read_bytes())
    ordered, seen = [], set()

    def visit(name):
        if name in seen:
            return
        seen.add(name)
        path = name.replace(".", "/") + ".lean"
        raw = git("show", SOURCE_COMMIT + ":" + path)
        for line in raw.decode().splitlines():
            if line.startswith("import "):
                match = re.fullmatch(r"import (Solidity\.[A-Za-z0-9_.]+)\s*", line)
                require(match is not None, "changed source import policy")
                visit(match.group(1))
        ordered.append((name, path))

    visit("Solidity.KeySort")
    visit("Solidity.Roadmap.G49Final.FoldedPublic")
    ordered += [("tests.h62.item5.statement-graph.Exporter", "tests/h62/item5/statement-graph/Exporter.lean"),
                ("H55ConstructorCensus", "tests/h55/g49-final-theorem/ConstructorCensus.lean")]
    require([r["module"] for r in records] == [n for n, _ in ordered], "incomplete/reordered checked closure")
    for row, (_, path) in zip(records, ordered):
        require(row["command"][-1] == path and "--tstack=131072" in row["command"], "changed checked command")
        require(sha(git("show", SOURCE_COMMIT + ":" + path)) == row["source_sha256"], "source snapshot mismatch")
    for path in ("scripts/h55/g49-final-theorem/check-pass-correct.py",
                 "scripts/h55/g49-final-theorem/constructor-slots.py",
                 "scripts/h55/g49-final-theorem/premise-tools.py",
                 "tests/h55/g49-final-theorem/h64-shapes.json"):
        require((ROOT/path).read_bytes() == git("show", SOURCE_COMMIT + ":" + path), "intake policy source drift")
    require(set(SELECTION) == {row["declaration"] for row in snapshot["declarations"]}, "changed declaration selection")
    require(all("witness" not in b for r in snapshot["declarations"] for b in r["binders"]+r["fields"]),
            "conditional census cannot register witnesses")
    return snapshot, status


def catalog_for(snapshot, registry, ownership, original_pending):
    """Classify all selected telescope entries conservatively as open conditions."""
    H55.census(snapshot, registry, "solidity-h62-3-20261106/g52-differential")
    require(GRAPH.validate_source_snapshot(original_pending) is not None, "missing original source snapshot")
    expected_roots = {"G49": ["G49.01", "G49.02", "G49.03"], "G50": ["G50.01", "G50.02"]}
    require(original_pending.get("roots") == expected_roots, "changed representative roots")
    owner_rows = {row["id"]: row for row in ownership["items"]}
    owners = {key: row.get("owner") for key, row in owner_rows.items()}
    require(len(owners) == len(ownership["items"]), "duplicate owner reference")
    def assignment(ref, basis="adapter generic-interface accounting default"):
        owner = owners.get(ref)
        require(isinstance(owner, str) and owner == owner.strip() and
                owner.lower() not in ("", "-", "unknown", "unowned", "pending", "later"),
                "missing logical owner: " + ref)
        return dict(kind="premise", ownerReference=ref, owner=owner, basis=basis)
    nodes = []
    for row in snapshot["declarations"]:
        node_id, ref = SELECTION[row["declaration"]]
        roles = {}
        for i, binder in enumerate(row["binders"]):
            roles[str(i)] = assignment(registry["owners"].get(binder["name"], ref),
                "frozen H55 logical-input reference" if binder["name"] in registry["owners"] else
                "adapter generic-interface accounting default")
        for i, field in enumerate(row["fields"]):
            roles["field:"+str(i)] = assignment(registry["owners"][field["name"]] if row["declaration"] == PUBLIC else ref,
                "frozen H55 public-field reference" if row["declaration"] == PUBLIC else
                "adapter field inherits stage/interface accounting reference")
        nodes.append(dict(id=node_id, declaration=row["declaration"],
                          kind="statement" if row["declaration"] == THEOREM else "premise",
                          area="G49-interface", ownerReference=ref, owner=assignment(ref)["owner"], binderRoles=roles))
    pending = []
    for row in original_pending["pendingInputs"]:
        entry = {key: row[key] for key in ("id", "area", "owner", "ownerReference")}
        entry.update(inputArtifact="Concrete producer/factory bindings and compatibility acceptance",
                     reason="Selected conditional interfaces are typed; this production view remains unproved.",
                     source="Original representative logical-owner view; no live delivery-owner inference")
        pending.append(entry)
    return dict(nodes=nodes, pendingInputs=pending,
                roots={name: list(ids)+["interface.fold"] for name, ids in original_pending["roots"].items()})


def collect(run, ownership):
    snapshot, status = checked_export(run)
    registry = H55.decode((ROOT / "tests/h55/g49-final-theorem/h64-shapes.json").read_bytes())
    pending = GRAPH.read(ROOT / "tests/h62/item5/statement-graph/pending-inputs.json")
    catalog = catalog_for(snapshot, registry, ownership, pending)
    tree = git("rev-parse", SOURCE_COMMIT + "^{tree}").decode().strip()
    graph = GRAPH.build(snapshot, catalog, BASE, tree, ownership)
    require(graph["counts"]["done"] == 0 and graph["counts"]["dischargedPremises"] == 0,
            "conditional intake cannot discharge premises")
    require(graph["counts"]["typedDeclarations"] == 7 and graph["counts"]["pendingInputs"] == 5 and
            all(node["status"] == "blocked" for node in graph["nodes"]), "conditional graph lost an open view")
    return dict(schema="h62-conditional-census-v1", graph=graph, catalog=catalog,
                sourceCommit=SOURCE_COMMIT, privatePacketCommit=PACKET_COMMIT,
                intakePolicySha256=sha(Path(__file__).read_bytes()),
                originalPendingCatalogSha256=sha((ROOT / "tests/h62/item5/statement-graph/pending-inputs.json").read_bytes()),
                deliveryOwnerAgreement=False,
                checkedExportSha256=EXPORT_SHA, checkedResultsSha256=status["resultsSha256"],
                constructorSlots=H55.census(snapshot, registry, "solidity-h62-3-20261106/g52-differential"),
                countingScope="Selected generic telescopes/fields; overlapping root closures and slots are not atomic logical premises.",
                atomicOpenPremises=None, productionSelectionComplete=False, freshLocalLeanRun=False,
                toolchainEvidence="Producer reports Lean4.24.0/Lake5.0.0-src+797c613; binary/archive identity is not sealed by this run.",
                migrationOrRuntimeAcceptance=False)


def write_new(path, data):
    """Publish complete private output once, without replacing even identical bytes."""
    require(not path.is_symlink(), "output symlink refused")
    path = path.resolve()
    require(not path.is_relative_to(ROOT), "bulk output must remain outside the repository")
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix="."+path.name+".", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        os.link(temporary, path)  # Atomic no-replace publication, including races.
        parent = os.open(path.parent, os.O_RDONLY)
        try:
            os.fsync(parent)
        finally:
            os.close(parent)
    finally:
        os.unlink(temporary)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", type=Path, required=True)
    parser.add_argument("--ownership", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = collect(args.run, GRAPH.read(args.ownership))
    write_new(args.output, GRAPH.canonical(result))
    print(json.dumps(result["graph"]["counts"], sort_keys=True))


if __name__ == "__main__":
    main()
