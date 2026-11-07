#!/usr/bin/env python3
"""Guard regression: standalone controls silently execute file-writing probes.

Partial static source references only; no execution or acceptance is inferred.
"""
import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
SHARED = "tests/directruntime-20261104/shared-translator/"
VT = "tests/fullscope-20261104/vt1/"
VO = "tests/fullscope-20261104/vo1/"
PRE = "tests/h62/item2/audit-precompiles/"
BIND = "tests/h62/item1/readonly-bind/"
ROADMAP = "tests/h62/item2/audit-roadmap/"
GRAPH = "tests/h62/item5/statement-graph/"
FILES = {
    "shared": {"AdmissionControls", "ApiSignatures", "AxiomInventory", "ComposedControls", "ConstructReaderControls",
               "DirectResultControls", "FixtureControls", "IntrinsicControls", "MetadataBench", "ModalityControls",
               "ParityControls", "ReaderControls", "RequestControls", "SelectionControls", "YulJsonControls"},
    "vt": {"DialectChecks", "ImportFollowup/ParserChecks", "ImportFollowup/Signatures", "IrCensusGen", "IrEvalChecks",
           "IrHelperChecks", "IrImportChecks", "IrLeanGen", "IrParseChecks", "ObjectDataChecks"},
    "vo": {"O02Controls", "O03Controls", "PipelineControls", "ValueValidatorControls", "X06Controls", "YulValidatorControls"},
    "precompiles": {"BasicWitnesses", "CoreSignatures", "CoreWitnesses", "DataWitnesses", "JointPremiseFixture", "StipendControl", "TypeFidelity"},
    "bind": {"BindControls", "PhaseControls", "overlay/Solidity/Lowering/Readonly/CaptureFailures",
             "overlay/Solidity/Lowering/Readonly/CapturePhases", "overlay/Solidity/Lowering/Readonly/EnvironmentCredit"},
    "roadmap": {"ContextWitnesses", "CreationWitnesses", "EvmWitnesses", "FrontendWitnesses", "WitnessObstruction"},
    "graph": {"Census", "EvmCensus", "Exporter", "Fixture", "Pending", "WitnessFixture"},
}


def classify(root, manifest):
    if not isinstance(manifest, dict) or not isinstance(manifest.get("rows"), list):
        raise ValueError("invalid census")
    root = pathlib.Path(root)
    out, seen = [], set()
    groups = ((SHARED, "shared"), (VT, "vt"), (VO, "vo"), (PRE, "precompiles"),
              (BIND, "bind"), (ROADMAP, "roadmap"), (GRAPH, "graph"))
    for row in manifest["rows"]:
        if not isinstance(row, dict) or not isinstance(row.get("path"), str):
            raise ValueError("invalid candidate")
        path = row["path"]
        match = [(prefix, name) for prefix, name in groups if path.startswith(prefix)]
        if not match:
            continue
        prefix, group = match[0]
        rel = path[len(prefix):]
        if (not rel.endswith(".lean") or rel[:-5] not in FILES[group] or path in seen
                or "\\" in path or any(x in ("", ".", "..") for x in path.split("/"))):
            raise ValueError("unreviewed or invalid file")
        seen.add(path)
        source = root / path
        if source.is_symlink() or not source.is_file() or source.resolve() != source:
            raise ValueError("invalid source")
        raw = source.read_bytes()
        if hashlib.sha256(raw).hexdigest() != row.get("sha256"):
            raise ValueError("source differs from census")
        name = rel[:-5]
        driver, inputs, effects = "unresolved", "unresolved per invocation", "unverified per invocation"
        if group == "shared":
            driver = "candidate tests/directruntime-20261104/shared-translator/bounded.sh; applicability unverified"
            if name in ("FixtureControls", "DirectResultControls", "MetadataBench"):
                inputs = "reads bulk AST fixture; exact availability and hashes unverified"
            if name == "DirectResultControls":
                effects = "capture environment option can overwrite observation JSON"
            elif name == "MetadataBench":
                effects = "writes fixed metadata-component-bench.json"
        elif group == "vt":
            if name == "DialectChecks":
                driver = "tests/fullscope-20261104/vt1/check-dialect.sh"
            elif name in ("IrCensusGen", "IrParseChecks", "IrEvalChecks", "IrHelperChecks"):
                driver = "tests/fullscope-20261104/vt1/check-ir.sh; VT1_SKIP_LEAN=1 skips Lean"
            elif name in ("IrImportChecks", "ObjectDataChecks"):
                driver = "tests/fullscope-20261104/vt1/measured-checks.py"
            if name in ("IrCensusGen", "IrLeanGen", "IrParseChecks", "IrEvalChecks", "IrHelperChecks"):
                inputs = "reads fixture data relative to checkout; exact bytes unverified"
            if name == "IrCensusGen":
                effects = "writes fixtures/census-tree.txt"
            elif name == "IrLeanGen":
                effects = "writes fixture .term outputs"
        elif group == "vo":
            driver = "candidate tests/fullscope-20261104/vo1/bounded.py; applicability unverified"
        elif group == "precompiles":
            driver = "candidate scripts/h62/item2/audit-precompiles/bounded.py; applicability unverified"
        elif group == "bind":
            driver = "unresolved Lean driver; scripts/h62/item1/readonly-bind/overlay.py generates overlay copies"
            if name.startswith("overlay/"):
                inputs = "isolated overlay source and matching private oleans; exact current inputs unverified"
                effects = "overlay.py writes copies by default; --check is comparison only"
        elif group == "roadmap":
            driver = "scripts/h62/item2/audit-roadmap/serial_checks.py; current applicability unverified"
            effects = "driver may write private oleans, logs and receipts"
        else:
            driver = ("scripts/h62/item5/statement-graph/verify.py; current applicability unverified"
                      if name in ("Exporter", "Fixture", "WitnessFixture", "Pending") else "unresolved")
            inputs = "H62_GRAPH_OUTPUT_DIR and pinned archive/oleans as applicable; current inputs unverified"
            effects = "graph commands write JSON into H62_GRAPH_OUTPUT_DIR; exact invocation unverified"
        role = ("historically-unchecked-pending" if group == "precompiles" and name == "StipendControl" else
                "intentional-contradiction-and-toy-control" if group == "roadmap" and name == "WitnessObstruction" else
                "overlay-copy" if group == "bind" and name.startswith("overlay/") else "static-fixture")
        out.append({"candidate": row, "group": group, "role": role, "driver_reference": driver,
                    "expected_outcome": "unresolved per current invocation", "auxiliary_inputs": inputs,
                    "side_effects": effects, "status": "static-reference-not-execution-acceptance"})
    return out


def main():
    if len(sys.argv) != 2:
        print("usage: fixture_effects.py CENSUS.json", file=sys.stderr)
        return 2
    try:
        raw = pathlib.Path(sys.argv[1]).read_bytes()
        print(json.dumps({"status": "partial-static-classification-not-acceptance", "coverage": "unverified-subsets-accepted",
                          "census_sha256": hashlib.sha256(raw).hexdigest(), "rows": classify(ROOT, json.loads(raw))}, indent=2, sort_keys=True))
        return 0
    except (OSError, UnicodeError, ValueError) as exc:
        print(f"fixture classification unavailable: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
