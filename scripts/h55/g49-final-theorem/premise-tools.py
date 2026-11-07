#!/usr/bin/env python3
"""H44 payload regeneration and type-pinned, owner-complete premise accounting.

Metadata checks supplement Lean; they never prove or discharge a premise.
The final public theorem is outside the currently inventoried backfill scope.
"""
import argparse
import hashlib
import io
import json
from pathlib import Path
import tarfile

ROOT = Path(__file__).resolve().parents[3]
MANIFEST = ROOT / "tests/h55/g49-final-theorem/staging-manifest.json"
POLICY = ROOT / "tests/h55/g49-final-theorem/pass-chain-premises.json"
PAYLOAD = "tests/roadmap-v16/parallel-premises.json"


class Invalid(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise Invalid(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON key: " + key)
        result[key] = value
    return result


def decode(data):
    return json.loads(data, object_pairs_hook=unique_object)


def payload_bytes(archive, manifest):
    require(digest(archive) == manifest["archiveSha256"], "wrong staging archive hash")
    with tarfile.open(fileobj=io.BytesIO(archive)) as bundle:
        members = bundle.getmembers()
        require(len(members) == len(manifest["files"]), "wrong staging member count")
        require({m.name for m in members} == set(manifest["files"]), "wrong staging member set")
        payload = None
        for member in members:
            require(member.isfile() and not Path(member.name).is_absolute()
                    and ".." not in Path(member.name).parts, "unsafe staging member")
            data = bundle.extractfile(member).read()
            require(digest(data) == manifest["files"][member.name], "changed staging source: " + member.name)
            if member.name == PAYLOAD:
                payload = data
        require(payload is not None, "missing premise payload")
        return payload


def external_write(path, data):
    path = path.resolve()
    require(not path.is_relative_to(ROOT), "bulk output must remain outside the repository")
    path.parent.mkdir(parents=True, exist_ok=True)
    require(not path.exists() or path.read_bytes() == data, "refusing to replace different evidence")
    path.write_bytes(data)


def read_inventory(log):
    rows = [line.removeprefix("G49-PREMISES ") for line in log.splitlines()
            if line.startswith("G49-PREMISES ")]
    require(len(rows) == 1, "exactly one actual Lean inventory required")
    return decode(rows[0])


def account(inventory, policy, ownership):
    require(inventory["name"] == policy["theorem"], "wrong theorem")
    require(digest(inventory["type"].encode()) == policy["theoremTypeSha256"], "full theorem statement drift")
    require(sorted(set(inventory["dependencies"])) == policy["dependencies"], "proof dependency drift")
    require(sorted(inventory["axioms"]) == sorted(policy["axioms"]), "axiom drift")
    require("sorryAx" not in inventory["axioms"], "unproved theorem")
    bindings = policy["bindings"]
    require(len(inventory["premises"]) == len(bindings), "missing/extra binder")
    owners = {}
    for item in ownership["items"]:
        require(item["id"] not in owners, "duplicate owner obligation ID")
        owners[item["id"]] = item
    rows, counts = [], {"producer": 0, "condition": 0, "parameter": 0}
    for index, (actual, expected) in enumerate(zip(inventory["premises"], bindings)):
        require(set(actual) == {"index", "name", "type", "isProp", "closedExpr", "constants"},
                "unknown/missing binder metadata")
        require(actual["index"] == expected["index"] == index, "binder order/index drift")
        require(actual["name"] == expected["name"], "binder name drift")
        require(digest(actual["closedExpr"].encode()) == expected["typeSha256"], "dependent binder type drift")
        require(digest(actual["type"].encode()) == expected["readableTypeSha256"], "readable binder type drift")
        require(sorted(actual["constants"]) == expected["constants"], "binder constant drift")
        require(isinstance(actual["isProp"], bool) and actual["isProp"] == expected["isProp"],
                "proposition flag drift")
        role = expected["role"]
        require(role in counts, "unknown binder role")
        require(not actual["isProp"] or role != "parameter", "proposition hidden as parameter")
        certificates = {"Solidity.Roadmap.Lowering", "Solidity.Roadmap.Compilation", "Solidity.Roadmap.Execution"}
        require(not certificates.intersection(actual["constants"]) or role == "producer",
                "typed certificate hidden from producer count")
        row = dict(actual, role=role)
        if role == "parameter":
            require(expected["obligation"] is None, "parameter mislabeled with an owner obligation")
            row.update(owner=None, obligation=None)
        else:
            obligation = expected["obligation"]
            require(obligation in owners, "missing current owner: " + str(obligation))
            owner = owners[obligation]
            require(isinstance(owner["owner"], str) and owner["owner"].strip() not in {"", "-", "unowned"},
                    "unassigned premise owner")
            row.update(owner=owner["owner"], obligation=obligation,
                       ownerStatus=owner["status"], discharged=False)
        counts[role] += 1
        rows.append(row)
    return dict(theorem=inventory["name"], totalBinders=len(rows),
                openProducerPremises=counts["producer"], callerProofConditions=counts["condition"],
                allConditionalPremises=counts["producer"]+counts["condition"],
                quantifiedParameters=counts["parameter"], premises=rows,
                countBoundary=policy["countBoundary"], finalPublicTheoremComplete=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    regen = sub.add_parser("regenerate")
    regen.add_argument("--archive", type=Path, required=True)
    regen.add_argument("--output", type=Path, required=True)
    census = sub.add_parser("count")
    census.add_argument("--inventory-log", type=Path, required=True)
    census.add_argument("--ownership", type=Path, required=True)
    census.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    manifest = decode(MANIFEST.read_bytes())
    if args.command == "regenerate":
        data = payload_bytes(args.archive.read_bytes(), manifest)
        external_write(args.output, data)
        print("PAYLOAD_REGENERATION_PASS " + digest(data))
    else:
        policy = decode(POLICY.read_bytes())
        require(digest((ROOT/policy["source"]).read_bytes()) == policy["sourceSha256"], "proof source drift")
        require(digest((ROOT/"tests/h55/g49-final-theorem/PremiseInventory.lean").read_bytes()) == policy["inventorySourceSha256"], "inventory source drift")
        owner_bytes = args.ownership.read_bytes()
        require(digest(owner_bytes) == manifest["ownershipSnapshot"]["sha256"], "wrong ownership snapshot")
        report = account(read_inventory(args.inventory_log.read_text()), policy, decode(owner_bytes))
        report["ownershipSha256"] = digest(owner_bytes)
        report["inventoryLogSha256"] = digest(args.inventory_log.read_bytes())
        report["proofSourceSha256"] = policy["sourceSha256"]
        external_write(args.output, (json.dumps(report, indent=2, ensure_ascii=False)+"\n").encode())
        print("PREMISE_ACCOUNTING_PASS " + json.dumps({k:v for k,v in report.items() if isinstance(v,int)}))


if __name__ == "__main__":
    main()
