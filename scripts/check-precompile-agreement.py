#!/usr/bin/env python3
"""Pinned source-inventory gate. Final theorem/kernel acceptance is pending.

Default mode deliberately fails closed until the proof gate is implemented.
--inventory-only checks source coverage and hashes; it is not B16 acceptance.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
INVENTORY = ROOT / "Bridge/tests/precompile-agreement/inventory.json"
BASE = "b6ba0696102a7a038afe2ed333c09dff397cc5b2"
CLASSIFICATIONS = {
    "common-gas-external-output", "identity-candidate", "fork-mismatch",
    "header-domain-mismatch", "unsupported-vendor",
}


def validate(data):
    errors = []
    if data.get("schema") != 1 or data.get("base") != BASE:
        errors.append("wrong schema or base")
    source = (ROOT / "Solidity/Roadmap/Evm.lean").read_text()
    address_part = source.split("def Precompile.address", 1)[1].split("def Precompile.all", 1)[0]
    actual = {name: int(address, 16) for name, address in
              re.findall(r"\| \.(\w+) => (0x[0-9a-f]+)", address_part)}
    rows = data.get("rows", [])
    if len(actual) != 18 or len(rows) != 18:
        errors.append("expected exactly 18 addresses")
    if len({r["name"] for r in rows}) != len(rows) or len({r["address"] for r in rows}) != len(rows):
        errors.append("duplicate name/address")
    if {r["name"]: r["address"] for r in rows} != actual:
        errors.append("source address coverage mismatch")
    required_pins = {"Solidity/Roadmap/Evm.lean", "Bridge/lake-manifest.json",
                     "Bridge/vendor/EvmYul/EVM/PrecompiledContracts.lean",
                     "Bridge/vendor/EvmYul/EVM/Semantics.lean",
                     "Bridge/vendor/EvmYul/FFI/ffi.lean", "Bridge/lean-toolchain"}
    required_pins.update(str(p.relative_to(ROOT)) for p in
                         (ROOT / "Solidity/Precompiles").glob("*.lean"))
    for directory in ("Bridge/vendor/EvmYul", "Bridge/vendor/Conform"):
        required_pins.update(str(p.relative_to(ROOT)) for p in
                             (ROOT / directory).rglob("*.lean"))
    required_pins.update("Bridge/vendor/EvmYul/" + name for name in
                         ("VENDOR.md", "SHA256SUMS", "UPSTREAM_SHA256SUMS",
                          "h7-bounded-scanner-padding-pin.json"))
    pins = data.get("pins", {})
    if not required_pins <= pins.keys():
        errors.append("missing required input pins")
    for name, expected in pins.items():
        path = ROOT / name
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            errors.append("hash mismatch: " + name)
    vendor = (ROOT / "Bridge/vendor/EvmYul/EVM/PrecompiledContracts.lean").read_text()
    dispatch = (ROOT / "Bridge/vendor/EvmYul/EVM/Semantics.lean").read_text()
    dispatch_pairs = {int(address): definition for address, definition in re.findall(
        r"\| (\d+)\s*=> \.ok <\| \(∅, (Ξ_\w+)", dispatch)}
    if set(dispatch_pairs) != set(range(1, 11)):
        errors.append("vendor dispatch coverage changed")
    modules = {1: "Basic", 2: "Basic", 3: "Basic", 4: "Basic", 5: "Modexp",
               6: "Bn254", 7: "Bn254", 8: "Bn254", 9: "Blake2f", 10: "PointEval",
               **{address: "Bls12381" for address in range(11, 18)}, 256: "P256"}
    classes = {**{address: "common-gas-external-output" for address in (1, 2, 3, 6, 7, 8, 10)},
               4: "identity-candidate", 5: "fork-mismatch", 9: "header-domain-mismatch",
               **{address: "unsupported-vendor" for address in (*range(11, 18), 256)}}
    for row in rows:
        expected_module = "Solidity/Precompiles/" + modules.get(row["address"], "MISSING") + ".lean"
        if row.get("core_module") != expected_module or expected_module not in pins:
            errors.append(row["name"] + ": wrong/unpinned core module")
        if row.get("classification") != classes.get(row["address"]):
            errors.append(row["name"] + ": changed source classification")
        for field in ("core_module", "core_gas", "length", "malformed", "vendor_behavior", "controls"):
            if not row.get(field):
                errors.append(row["name"] + ": missing " + field)
        if row.get("classification") not in CLASSIFICATIONS:
            errors.append(row["name"] + ": bad classification")
        if row["address"] <= 10:
            definition = row.get("vendor_definition")
            if (definition != dispatch_pairs.get(row["address"]) or not definition or
                    "def " + definition + "\n" not in vendor or not row.get("vendor_gas")):
                errors.append(row["name"] + ": missing actual vendor definition")
        elif row.get("vendor_definition") is not None or row["classification"] != "unsupported-vendor":
            errors.append(row["name"] + ": unsupported row misclassified")
        if row.get("proof_status") != "pending" or row.get("proofs") != []:
            errors.append(row["name"] + ": inventory checkpoint cannot claim checked proofs")
    if data.get("status") != "source-inventory-only":
        errors.append("inventory checkpoint cannot claim final acceptance")
    return errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory-only", action="store_true")
    args = parser.parse_args()
    errors = validate(json.loads(INVENTORY.read_text()))
    if errors:
        print("FAIL: " + "\nFAIL: ".join(errors))
        return 1
    print("PASS source inventory: 18 unique addresses, actual vendor dispatch/definitions, exact input hashes")
    if not args.inventory_only:
        print("BLOCKED final acceptance: theorem/fixture mapping, kernel proofs, axiom pins and final gates pending")
        return 1
    print("Source inventory only; no kernel or cryptographic equality claim")
    return 0


if __name__ == "__main__":
    sys.exit(main())
