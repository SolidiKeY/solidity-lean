#!/usr/bin/env python3
"""Derive artifact facts for IrEvalChecks.lean from the saved solc 0.8.38 output.

No compiler is run: everything is read from fixtures/output.json.
- creation/deployed bytecode, with each library placeholder `__$…$__` replaced
  by 20 zero bytes and its byte offsets recorded (`links`);
- the deployed object's offset inside the creation bytecode;
- immutable positions: operands of PUSH32 instructions whose 32 bytes are all
  zero, found by disassembling the deployed code before its CBOR metadata
  (solc emits immutables as zero PUSH32 placeholders in `deployedBytecode`).

Usage: generate-artifacts.py [--check]   (--check compares with the saved file)
"""
import json, re, sys, pathlib

here = pathlib.Path(__file__).resolve().parent
out = json.loads((here / "fixtures/output.json").read_text())
PLACEHOLDER = re.compile(r"__\$[0-9a-f]{34}\$__")


def unlink(code):
    links = sorted({m.start() // 2 for m in PLACEHOLDER.finditer(code)})
    return PLACEHOLDER.sub("0" * 40, code), links


def zero_push32(code):
    raw = bytes.fromhex(code)
    meta = int.from_bytes(raw[-2:], "big") + 2
    end, i, found = len(raw) - meta, 0, []
    while i < end:
        op = raw[i]
        if 0x60 <= op <= 0x7F:
            n = op - 0x5F
            if n == 32 and raw[i + 1:i + 33] == bytes(32):
                found.append(i + 1)
            i += 1 + n
        else:
            i += 1
    return found


rows = []
for name in ["Census", "LinkedMath"]:
    evm = out["contracts"]["Census.sol"][name]["evm"]
    creation, creation_links = unlink(evm["bytecode"]["object"])
    deployed, deployed_links = unlink(evm["deployedBytecode"]["object"])
    offset = creation.find(deployed)
    positions = zero_push32(deployed)
    # Independent of the zero-PUSH32 scan: the creation code pushes each
    # immutable position (PUSH2 <pos>) to add it to the copy buffer.
    for p in positions:
        assert ("61%04x" % p) in creation[:2 * offset], f"{name}: no PUSH2 {p} in creation code"
    assert offset >= 0 and offset % 2 == 0 and creation.count(deployed) == 1
    rows.append({
        "contract": name,
        "creation": creation,
        "deployed": deployed,
        "deployedOffset": offset // 2,
        "creationLinks": creation_links,
        "deployedLinks": deployed_links,
        "immutablePositions": positions,
    })

text = json.dumps(rows, indent=1) + "\n"
target = here / "fixtures/artifacts.json"
if "--check" in sys.argv:
    if target.read_text() != text:
        sys.exit("artifacts.json differs from fixtures/output.json")
    print("ARTIFACTS_CHECK_PASS")
else:
    target.write_text(text)
    for r in rows:
        print(r["contract"], len(r["creation"]) // 2, r["deployedOffset"], r["creationLinks"], r["deployedLinks"], r["immutablePositions"])
