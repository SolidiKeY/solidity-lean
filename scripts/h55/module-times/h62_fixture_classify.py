#!/usr/bin/env python3
"""Guard regression: standalone audit rows lose driver and I/O distinctions.

Static classification of reviewed groups; never an execution acceptance.
"""
import hashlib
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
G25 = "tests/h62/item2/audit-g25-scalar-lowering/"
YUL = "tests/h62/item6/migrate-yul/"
TYPING = "tests/h62/item2/audit-typing/"
CALCULUS = "tests/h62/item2/audit-calculus/"
ABI = "tests/h62/item2/audit-abi-world/H62AbiWorld/"
TYPING_FILES = {"ClosureCensus", "ClosureFidelity", "ClosureWitnesses", "DeclarationCensus",
                "ProvisionedCensus", "UnitsSuccess", "UnitsSuccessFidelity",
                "ValuesDefaultsFidelity", "ValuesDefaultsWitnesses", "ValuesHeredFidelity",
                "ValuesHeredWitnesses", "ValuesListsFidelity", "ValuesListsWitnesses",
                "ValuesOpsFidelity", "ValuesOpsWitnesses"}
CALCULUS_FILES = {"ChunkCensus", "CreationAdditionalWitnesses", "CreationWitnesses", "DagJoint",
                  "DagJointChecks", "ExprDagCensus", "ExprDagChecks", "FailureAdditionalWitnesses",
                  "FailureWitnesses", "JoinWalkWitnesses", "KernelCensus", "PrivateCommands",
                  "ScopeWitnesses", "StaticTransportWitnesses"}
ABI_FILES = {"BasicWitnesses", "CodecWitnesses", "ControlWitnesses", "Fidelity", "RepresentationWitnesses",
             "RuntimeVectors", "SuccessContracts", "WindowWitnesses", "WitnessSchema"}
G25_SPECIAL = {"AllWitnesses": "witness-aggregator", "BoundaryVectors": "external-vector-export",
               "ClosedTotality": "totality-control", "EnvironmentTotality": "totality-control",
               "Fixtures": "shared-fixture", "KernelCensus": "kernel-census-export",
               "ScalarTotality": "totality-control", "SuccessAxioms": "axiom-report",
               "SuccessControls": "success-control", "WitnessCommand": "command-support",
               "WitnessCommandChecks": "command-control"}
YUL_ROLES = {"ExportInterfaces": "interface-exporter", "InterfaceFixture": "interface-fixture",
             "LegacyStringCases": "legacy-string-fixture", "NewStringCases": "new-string-fixture",
             "ReservedNamesCandidate": "candidate-reserved-names", "ReservedNamesOriginalAxioms": "original-axiom-report"}


def classify(root, manifest):
    if not isinstance(manifest, dict) or not isinstance(manifest.get("rows"), list):
        raise ValueError("invalid census")
    root = pathlib.Path(root)
    rows, seen = [], set()
    for entry in manifest["rows"]:
        if not isinstance(entry, dict) or not isinstance(entry.get("path"), str):
            raise ValueError("invalid census entry")
        path = entry["path"]
        groups = ((G25, "g25"), (YUL, "yul"), (TYPING, "typing"), (CALCULUS, "calculus"), (ABI, "abi"))
        found = [(prefix, group) for prefix, group in groups if path.startswith(prefix)]
        if not found:
            continue
        prefix, group = found[0]
        if (path in seen or not path.endswith(".lean") or "/" in path[len(prefix):]
                or "\\" in path or any(p in ("", ".", "..") for p in path.split("/"))):
            raise ValueError("invalid selected path")
        seen.add(path)
        source = root / path
        if source.is_symlink() or not source.is_file() or source.resolve() != source:
            raise ValueError("invalid source")
        raw = source.read_bytes()
        if hashlib.sha256(raw).hexdigest() != entry.get("sha256"):
            raise ValueError("source differs from census")
        stem = source.stem
        if group == "g25":
            role = G25_SPECIAL.get(stem)
            if role is None and re.fullmatch(r"(?:Scalar|Environment)[A-Za-z0-9]*Witnesses|SliceWitnesses", stem):
                role = "witness-module"
            if role is None:
                raise ValueError("unreviewed G25 file")
            driver = "scripts/h62/item2/audit-g25-scalar-lowering/bounded_lean.py"
            outcome = "selected checks expect successful elaboration; exact invocation unverified"
            effects = {"BoundaryVectors": "writes fixed external-vector JSON",
                       "KernelCensus": "writes /workspace/h62-audit-g25-artifacts/evidence/kernel-census-v424.json and /workspace/h62-audit-g25-artifacts/evidence/premise-structures-v424.json",
                       "AllWitnesses": "writes fixed witness-verification JSON",
                       "WitnessCommand": "defines I/O-writing commands; invocation effects depend on caller"}.get(stem, "private olean/receipt outputs; other effects unverified")
        elif group == "yul":
            role = YUL_ROLES.get(stem)
            if role is None:
                raise ValueError("unreviewed Yul file")
            driver = "scripts/h62/item6/migrate-yul/interfaces.py" if stem == "ExportInterfaces" else "unresolved"
            outcome = "phase and current invocation unverified"
            effects = "--run MODULE OUTPUT writes/truncates output; --self-test does not export" if stem == "ExportInterfaces" else "unverified"
        elif group == "typing":
            if stem not in TYPING_FILES:
                raise ValueError("unreviewed typing file")
            role = "fidelity" if stem.endswith("Fidelity") else "witness" if stem.endswith("Witnesses") else "census-or-success"
            driver = "scripts/h62/item2/audit-typing/check_closure.py"
            outcome = "driver sequence requires successful checks; current invocation unverified"
            effects = "driver may write private oleans, logs, receipts and census reports; prerequisites unverified"
        elif group == "calculus":
            if stem not in CALCULUS_FILES:
                raise ValueError("unreviewed calculus file")
            role = "closed-telescope-check" if stem == "JoinWalkWitnesses" else "witness" if stem.endswith("Witnesses") else "command-or-audit-control"
            driver = "scripts/h62/item2/audit-calculus/bounded_lean.py"
            outcome = "selected checks expect success including guarded refusals; current invocation unverified"
            effects = "private oleans, logs, receipts and optional generated probes; mode unverified"
        else:
            if stem not in ABI_FILES:
                raise ValueError("unreviewed ABI file")
            role = "vector-output" if stem == "RuntimeVectors" else "fidelity" if stem == "Fidelity" else "success-control" if stem == "SuccessContracts" else "schema-or-witness"
            driver = ("scripts/h62/item2/audit-abi-world/vectors_call.py" if stem == "RuntimeVectors" else
                      "scripts/h62/item2/audit-abi-world/fidelity_call.py" if stem == "Fidelity" else "unresolved")
            outcome = "expected-success control; current invocation unverified"
            effects = "prints H62_VECTORS; external extractor writes JSON/provenance" if stem == "RuntimeVectors" else "unverified per invocation"
        imports = [{"line": n, "text": line} for n, line in enumerate(raw.decode("utf8").splitlines(), 1)
                   if re.match(r"^import\s", line)]
        rows.append({"candidate": entry, "group": group, "role": role, "driver_reference": driver,
                     "expected_outcome": outcome, "auxiliary_inputs": "unresolved per invocation",
                     "side_effects": effects, "lexical_import_lines": imports,
                     "status": "static-reference-not-execution-acceptance"})
    return rows


def main():
    if len(sys.argv) != 2:
        print("usage: h62_fixture_classify.py CENSUS.json", file=sys.stderr)
        return 2
    try:
        data = pathlib.Path(sys.argv[1]).read_bytes()
        out = {"status": "partial-static-classification-not-acceptance", "coverage": "unverified-subsets-accepted",
               "census_sha256": hashlib.sha256(data).hexdigest(), "rows": classify(ROOT, json.loads(data))}
        print(json.dumps(out, indent=2, sort_keys=True))
        return 0
    except (OSError, UnicodeError, ValueError) as exc:
        print(f"fixture classification unavailable: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
