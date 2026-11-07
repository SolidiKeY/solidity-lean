#!/usr/bin/env python3
"""Owner-complete H64 typed inventory from a hash-bound successful VM check.

This counts named conditional obligations, not proved concrete producers.
The representative shape registry is explicitly not exhaustive lane coverage.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
SPEC = importlib.util.spec_from_file_location("g49_premises", ROOT / "scripts/h55/g49-final-theorem/premise-tools.py")
BASE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BASE)
require, digest, decode = BASE.require, BASE.digest, BASE.decode
REGISTRY = ROOT / "tests/h55/g49-final-theorem/h64-shapes.json"


def load_inventory(run):
    status = decode((run / "run-status.json").read_bytes())
    results_bytes = (run / "results.json").read_bytes()
    require(status["status"] == "pass" and digest(results_bytes) == status["resultsSha256"], "unverified or failed run")
    records = decode(results_bytes)
    require(records and records[-1]["module"] == "H64Controls", "missing checked controls")
    for row in records:
        require(row["exit_code"] == 0 and row["stop_reason"] is None, "failed/resource-stopped check")
        source = (ROOT / row["command"][-1]).resolve()
        require(source.is_relative_to(ROOT), "source outside repository")
        require(digest(source.read_bytes()) == row["source_sha256"], "source drift after check")
        require(digest(Path(row["log"]).read_bytes()) == row["log_sha256"], "changed checked-run log")
    lines = Path(records[-1]["log"]).read_text().splitlines()
    inventory = [line.removeprefix("H64-INVENTORY ") for line in lines if line.startswith("H64-INVENTORY ")]
    require(len(inventory) == 1, "ambiguous typed inventory")
    return decode(inventory[0]), status["resultsSha256"]


def account(inventory, registry, ownership):
    declarations = {row["name"]: row for row in inventory["declarations"]}
    require(len(declarations) == len(inventory["declarations"]), "duplicate declaration")
    require(set(declarations) == set(registry["checkedDeclarations"]), "missing/extra checked declaration")
    for row in declarations.values():
        require(set(row["axioms"]) <= {"propext", "Quot.sound"}, "unexpected axiom")
    ctor = declarations["Solidity.Roadmap.G49Final.PublicObligations.mk"]["binders"]
    require(len(ctor) == 24 and {row["name"] for row in ctor} == set(registry["owners"]), "missing/extra named premise")
    owners = {}
    for item in ownership["items"]:
        require(item["id"] not in owners, "duplicate ownership ID")
        owners[item["id"]] = item
    report = []
    for index, row in enumerate(ctor):
        require(row["index"] == index and row["name"] == registry["binderOrder"][index]
                and isinstance(row["isProp"], bool) and row["isProp"] == (index >= 9), "binder order/kind drift")
        obligation = registry["owners"][row["name"]]
        require(obligation in owners, "unknown owner obligation")
        owner = owners[obligation]
        require(isinstance(owner["owner"], str) and owner["owner"].strip() not in {"", "-", "unowned"}, "unassigned premise")
        role = "open-public-obligation" if index >= 9 else (
            "interface-parameter" if index < 4 else "full-certificate-package" if index < 7 else "implementation-parameter")
        report.append(dict(row, role=role, obligation=obligation, owner=owner["owner"], ownerStatus=owner["status"], discharged=False))
    adapters = registry["carrierAdapters"]
    require(len(adapters) == len(set(adapters)) == 5 and all(name in declarations for name in adapters), "missing/duplicate adapter")
    implementation = registry["semanticImplementation"]
    def reaches(name, seen):
        if name == implementation:
            return True
        if name in seen:
            return False
        return any(reaches(dep, seen | {name}) for dep in declarations[name]["dependencies"] if dep in declarations)
    require(all(reaches(name, set()) for name in adapters), "adapter bypasses common implementation")
    families = registry["families"]
    require({f["id"] for f in families} == {"full-cert", "bare-refinement", "compiler-agreement",
            "frame-claim", "world-phase", "opcode-local"} and len(families) == 6, "shape registry drift")
    require(all(isinstance(f["supported"], bool) for f in families)
            and {f["id"] for f in families if f["supported"]} == {"full-cert"}
            and registry["exhaustiveLaneCoverage"] is False, "false adapter completeness")
    return dict(publicObligationFields=15, fullCertificatePackages=3, implementationParameters=2,
                interfaceParameters=4, totalConstructorBinders=24, premises=report,
                implementedSemanticShapes=1, carrierAdapterEntrypoints=5,
                representativeShapeFamilies=6, unresolvedRepresentativeFamilies=5,
                exhaustiveLaneCoverage=False, concretePublicObligationsDischarged=False,
                families=families, declarations=inventory["declarations"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", type=Path, required=True)
    parser.add_argument("--ownership", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    registry = decode(REGISTRY.read_bytes())
    manifest = decode(BASE.MANIFEST.read_bytes())
    owner_bytes = args.ownership.read_bytes()
    require(digest(owner_bytes) == manifest["ownershipSnapshot"]["sha256"], "wrong ownership snapshot")
    for path, sha in registry["sourceHashes"].items():
        require(digest((ROOT/path).read_bytes()) == sha, "lane source drift")
    inventory, run_sha = load_inventory(args.run)
    result = account(inventory, registry, decode(owner_bytes))
    result.update(runResultsSha256=run_sha, ownershipSha256=digest(owner_bytes), registrySha256=digest(REGISTRY.read_bytes()))
    BASE.external_write(args.output, (json.dumps(result,indent=2,ensure_ascii=False)+"\n").encode())
    print("H64_ACCOUNT_PASS: 15 open public fields; 3 certificate packages; 2 implementation parameters; 1 adapted semantic shape / 5 carriers; 5 representative shape gaps")


if __name__ == "__main__":
    main()
