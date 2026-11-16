#!/usr/bin/env python3
"""Count supplied constructor-field slots, not logical atoms or proved producers.

Reads actual H62 constructor exports from a hash-bound successful H55 run.
Expands only Lowering/Compilation/Execution through Pass and Cert; interface
contexts and named public predicates remain opaque. Generic constructor types
retain their original telescope context; they are not instantiated path types.
"""
import argparse
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
SPEC = importlib.util.spec_from_file_location("h55_premises", ROOT / "scripts/h55/g49-final-theorem/premise-tools.py")
BASE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BASE)
require, decode, digest = BASE.require, BASE.decode, BASE.digest
P = "Solidity.Roadmap."
PUBLIC = P + "G49Final.PublicObligations"
THEOREM = P + "G49Final.g49_g50_of_fold"
PACKAGES = {"lowering": P + "Lowering", "backend": P + "Compilation", "execution": P + "Execution"}
FIELDS = {
    P + "Lowering": {"lower": False, "pass": False, "dom": True, "agrees": True, "cert": False},
    P + "Compilation": {"compile": False, "pass": False, "dom": True, "agrees": True, "cert": False},
    P + "Execution": {"assemble": False, "pass": False, "dom": True, "agrees": True, "cert": False},
    P + "Pass": {"Dom": False, "run": False, "envAbs": False},
    P + "Cert": {"envSound": True, "envOnto": True, "need": False, "need_ok": True, "back": True},
}
INPUTS = ["S", "I", "Asm", "V", "lowering", "backend", "execution", "compiler", "decode"]


def load_run(run):
    require(not run.resolve().is_relative_to(ROOT), "checked evidence must be outside repository")
    status = decode((run / "run-status.json").read_bytes())
    raw = (run / "results.json").read_bytes()
    require(status["status"] == "pass" and digest(raw) == status["resultsSha256"], "failed or changed run")
    records = decode(raw)
    require(records and records[0]["module"] == "Solidity.KeySort", "missing KeySort prerequisite")
    require(records[-1]["command"][-1] == "tests/h55/g49-final-theorem/ConstructorCensus.lean", "wrong checked driver")
    require(sum(r["module"] == "tests.h62.item5.statement-graph.Exporter" for r in records) == 1, "missing exporter check")
    for row in records:
        require(row["exit_code"] == 0 and row["stop_reason"] is None, "failed or stopped check")
        require("-j1" in row["command"], "unbounded Lean thread count")
        source = (ROOT / row["command"][-1]).resolve()
        require(source.is_relative_to(ROOT) and digest(source.read_bytes()) == row["source_sha256"], "checked source drift")
        log = run / Path(row["log"]).name
        require(digest(log.read_bytes()) == row["log_sha256"], "checked log drift")
    snapshots = ["constructor-contracts.json", "constructor-contracts-repeat.json"]
    require(set(status["outputs"]) == set(snapshots), "missing or extra checked output")
    for name in snapshots:
        require(digest((run / name).read_bytes()) == status["outputs"][name], "changed constructor export")
    require(status["outputs"][snapshots[0]] == status["outputs"][snapshots[1]], "nondeterministic export")
    return decode((run / snapshots[0]).read_bytes()), status


def census(snapshot, registry, collector):
    require(isinstance(collector, str) and collector.strip() == collector and (collector == "coordinator" or "/" in collector), "named delivery lane required")
    require(snapshot["schema"] == 1 and snapshot["source"] == "Lean.ConstantInfo.type", "wrong export schema")
    rows = {r["declaration"]: r for r in snapshot["declarations"]}
    require(len(rows) == len(snapshot["declarations"]) and set(rows) == set(FIELDS) | {PUBLIC, THEOREM}, "missing or duplicate typed declaration")
    require([b["name"] for b in rows[THEOREM]["binders"]] == INPUTS + ["obligations"], "aggregate telescope changed")
    require([b["name"] for b in rows[PUBLIC]["binders"]] == INPUTS, "public interface telescope changed")
    require([b["isProp"] for b in rows[THEOREM]["binders"]] == [False] * 9 + [True], "aggregate binder role drift")
    for left, right in zip(rows[PUBLIC]["binders"], rows[THEOREM]["binders"]):
        require(left["typeExpr"] == right["typeExpr"] and left["isProp"] == right["isProp"],
                "public/theorem input type disagreement")
    require(set(rows[THEOREM]["axioms"]) <= {"propext", "Quot.sound"}, "aggregate axiom drift")
    require(rows[THEOREM]["isTheorem"] and rows[THEOREM]["exists"], "aggregate is not an exported theorem")
    public_names = registry["binderOrder"][9:]
    require(registry["binderOrder"][:9] == INPUTS and len(public_names) == 15
            and len(set(public_names)) == 15, "public registry telescope drift")
    require(set(registry["owners"]) == set(INPUTS + public_names), "missing or extra logical owner ID")
    require(all(isinstance(x, str) and x.strip() not in ("", "-", "unknown")
                for x in registry["owners"].values()), "unnamed logical obligation")
    expected = dict(FIELDS, **{PUBLIC: {name: True for name in public_names}})
    field_maps = {}
    for name, kinds in expected.items():
        row = rows[name]
        fs = {f["name"]: f for f in row["fields"]}
        require(row["exists"] and len(fs) == len(row["fields"]) and set(fs) == set(kinds), "field schema drift: " + name)
        require(set(row["fieldDeclarations"]) == {name + "." + f for f in fs}, "projection declaration drift")
        for index, (key, field) in enumerate(fs.items()):
            require(field["contextSize"] == len(row["binders"]) + index, "constructor context order drift")
            require(field["isProp"] is kinds[key], "field Prop/data drift: " + name + "." + key)
            require(isinstance(field["typeExpr"], str) and field["typeExpr"], "missing actual field type")
        field_maps[name] = fs
    leaves = []

    def expand(structure, prefix, logical, trail):
        for name, field in field_maps[structure].items():
            projection = structure + "." + name
            step = dict(structure=structure, projection=projection, field=field)
            child = {"pass": P + "Pass", "cert": P + "Cert"}.get(name) if structure in PACKAGES.values() else None
            if child:
                require(child in field["references"], "nested package type drift")
                expand(child, prefix + "." + name, logical, trail + [step])
            else:
                leaves.append(dict(path=prefix + "." + name, isProp=field["isProp"],
                                   constructorContexts=trail + [step], logicalObligation=logical,
                                   deliveryLane=collector, concreteProducerSupplied=False))

    for parameter, structure in PACKAGES.items():
        expand(structure, parameter, registry["owners"][parameter], [])
    packages = list(leaves)
    expand(PUBLIC, "obligations", "public-field", [])
    for row in leaves[len(packages):]:
        row["logicalObligation"] = registry["owners"][row["path"].rsplit(".", 1)[1]]
    # Retain all six opaque inputs with their actual aggregate telescope types.
    fields = leaves
    leaves = []
    for binder in rows[THEOREM]["binders"][:9]:
        name = binder["name"]
        if name in PACKAGES:
            leaves.extend(row for row in packages if row["path"].startswith(name + "."))
        else:
            leaves.append(dict(path=name, isProp=binder["isProp"], constructorContexts=[],
                               theoremContext=dict(declaration=THEOREM, binder=binder),
                               logicalObligation=registry["owners"][name], deliveryLane=collector,
                               concreteProducerSupplied=False))
    leaves.extend(fields[len(packages):])
    return dict(schema="h55-constructor-slots-v1", accountingLane="solidity-h55-sol-20261106/g49-final-theorem",
                deliveryLane=collector, countingPolicy="Three stage packages through Pass/Cert; public predicates and interfaces opaque. Generic field contexts retained, not instantiated nested-path types.",
                publicConstructor=PUBLIC + ".mk", aggregateTheorem=THEOREM,
                aggregateTheoremBinders=len(rows[THEOREM]["binders"]),
                ownershipBoundary="Logical IDs from the fixture policy; delivery lane explicitly supplied by operator, not a proof of owner agreement.",
                topLevelConstructorBinders=len(INPUTS) + len(public_names), contextParameters=4,
                implementationFunctions=2, packageLeafSlots=len(packages),
                packagePropSlots=sum(x["isProp"] for x in packages),
                packageDataSlots=sum(not x["isProp"] for x in packages),
                namedPublicPropFields=len(public_names), totalSuppliedSlots=len(leaves),
                suppliedSlots=leaves, atomicOpenPremises=None, productionSelectionComplete=False,
                premiseDischargeClaim=False, newSemanticAdapter=False)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--run", type=Path, required=True)
    ap.add_argument("--collector", required=True)
    ap.add_argument("--output", type=Path, required=True)
    a = ap.parse_args()
    snapshot, status = load_run(a.run)
    registry = decode((ROOT / "tests/h55/g49-final-theorem/h64-shapes.json").read_bytes())
    result = census(snapshot, registry, a.collector)
    result.update(checkedResultsSha256=status["resultsSha256"], checkedExportSha256=status["outputs"]["constructor-contracts.json"])
    require(not a.output.exists(), "refusing to replace existing evidence")
    BASE.external_write(a.output, (json.dumps(result, indent=2) + "\n").encode())
    print(json.dumps({k: result[k] for k in ("packageLeafSlots", "packagePropSlots", "packageDataSlots", "namedPublicPropFields", "totalSuppliedSlots", "atomicOpenPremises")}))


if __name__ == "__main__":
    main()
