#!/usr/bin/env python3
"""Read-only accounting inventory; no opcode semantics or completion verdicts."""
import json
import re
from pathlib import Path

root = Path(__file__).resolve().parents[1]
source = (root / "Solidity/Backend/Opcode.lean").read_text()
code = source.split("def code : Op → UInt8", 1)[1].split("def name : Op → String", 1)[0]
ops = [(int(byte, 16), name) for name, byte in
       re.findall(r"\| \.([A-Z0-9]+) => (0x[0-9a-f]+)", code)]
for prefix, base, count, first in [("PUSH", 0x5f, 33, 0), ("DUP", 0x80, 16, 1),
                                   ("SWAP", 0x90, 16, 1), ("LOG", 0xa0, 5, 0)]:
    ops.extend((base + n, prefix + str(n + first)) for n in range(count))
assert len(ops) == 150 and len({b for b, _ in ops}) == 150
rows = []
for byte, name in sorted(ops):
    if name in {"MLOAD", "MSTORE", "MSTORE8", "MCOPY", "CALLDATALOAD", "CALLDATACOPY", "MSIZE"}:
        group = "G46.02"
    elif name in {"SLOAD", "SSTORE", "TLOAD", "TSTORE"}:
        group = "G46.03"
    elif name in {"KECCAK256", "EXTCODEHASH"}:
        group = "G46.05"
    elif name in {"CREATE", "CREATE2", "CALL", "CALLCODE", "DELEGATECALL", "STATICCALL", "RETURN", "REVERT", "STOP", "INVALID", "SELFDESTRUCT"} or name.startswith("LOG"):
        group = "G47"
    elif 0x30 <= byte <= 0x4a or name in {"PC", "GAS"}:
        group = "G46.04"
    else:
        group = "G46.01"
    rows.append(dict(byte=f"0x{byte:02x}", opcode=name, primaryAccountingArea=group,
                     composition="G46.06", v15Status="open", dischargedByV15=[]))
manifest = json.loads((root / "Bridge/lake-manifest.json").read_text())
packages = []
for p in manifest["packages"]:
    if p["name"] in {"mathlib", "cslib", "auto"}:
        directory = root / "Bridge/.lake/packages" / p["name"]
        packages.append(dict(name=p["name"], revision=p.get("rev"),
                             sourcePresent=directory.exists(),
                             oleanCount=len(list(directory.glob(".lake/build/lib/lean/**/*.olean")))))
ledger = json.loads((root / "docs/feature-work/roadmap-g03-ledger.json").read_text())
features = [r["id"] for r in ledger["features"]
            if any(g in {"G46.01", "G46.02", "G46.03", "G46.04", "G46.05", "G46.06", "G47"}
                   for g in r.get("owners", {}).get("evm", []))]
print(json.dumps(dict(note="Accounting only; component proofs are read-only prerequisites. No new exclusion or coverage status is assigned.",
                      opcodes=rows, packages=packages, coordinatorFeatureIds=features), indent=2))
