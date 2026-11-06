#!/usr/bin/env python3
"""Enumerate every direct edge in the saved selected export; expose missing types.

No Lean invocation or source parsing. The selected graph is deliberately partial:
frontier names have no exported type/body, so no atomic-premise total is inferred.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("h64_account", HERE / "h64-account.py")
account = importlib.util.module_from_spec(spec)
spec.loader.exec_module(account)


def census(run, ownership):
    registry = account.decode(account.REGISTRY.read_bytes())
    manifest = account.decode(account.BASE.MANIFEST.read_bytes())
    owner_bytes = ownership.read_bytes()
    account.require(account.digest(owner_bytes) == manifest["ownershipSnapshot"]["sha256"],
                    "wrong ownership snapshot")
    for path, sha in registry["sourceHashes"].items():
        account.require(account.digest((account.ROOT / path).read_bytes()) == sha,
                        "lane source drift")
    inventory, results_hash = account.load_inventory(run)
    checked = account.account(inventory, registry, account.decode(owner_bytes))
    rows = {row["name"]: row for row in inventory["declarations"]}
    edges = sorted({(name, dep) for name, row in rows.items() for dep in row["dependencies"]})
    frontier = sorted({dep for _, dep in edges} - rows.keys())
    reached = {}
    for root in sorted(rows):
        seen, missing, pending = set(), set(), [root]
        while pending:
            name = pending.pop()
            if name in seen:
                continue
            seen.add(name)
            for dep in rows[name]["dependencies"]:
                if dep in rows:
                    pending.append(dep)
                else:
                    missing.add(dep)
        reached[root] = {"selectedReachable": sorted(seen), "unexportedFrontier": sorted(missing),
                         "typedTransitiveClosureComplete": not missing}
    binders = checked["premises"]
    return {"schema": "g49-selected-dependency-frontier-v1",
            "boundary": "All edges of the selected saved export, not all repository or production declarations. Dependency edges do not imply open premises. No unexported dependency type/body is invented.",
            "validatedResultsSha256": results_hash,
            "ownershipSha256": hashlib.sha256(ownership.read_bytes()).hexdigest(),
            "selectedDeclarationCount": len(rows), "directEdgeCount": len(edges),
            "directEdges": [{"from": a, "to": b, "targetHasSelectedTypedRow": b in rows} for a, b in edges],
            "unexportedDependencyCount": len(frontier), "unexportedDependencies": frontier,
            "perRoot": reached,
            "publicConstructorBinders": binders,
            "publicProofFieldCount": sum(x["role"] == "open-public-obligation" for x in binders),
            "certificatePackageCount": sum(x["role"] == "full-certificate-package" for x in binders),
            "expandedAtomicOpenPremises": None, "expandedAtomicInventoryComplete": False,
            "productionDeclarationSelectionComplete": False, "newLeanRun": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", type=Path, required=True)
    parser.add_argument("--ownership", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = census(args.run, args.ownership)
    account.require(not args.output.exists(), "refusing to replace existing evidence")
    account.BASE.external_write(args.output, (json.dumps(result, indent=2) + "\n").encode())
    print(json.dumps({key: result[key] for key in ("selectedDeclarationCount", "directEdgeCount", "unexportedDependencyCount", "publicProofFieldCount", "certificatePackageCount", "expandedAtomicOpenPremises")}))


if __name__ == "__main__":
    main()
