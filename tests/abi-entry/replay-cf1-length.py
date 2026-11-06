#!/usr/bin/env python3
"""Generate decoder-only length checks from the immutable first cf1 fixture.
Includes exact empty-revert controls for one-byte-truncated uint256 arrays.
No body execution, return-byte equality, or full-fixture replay is claimed.
"""
import hashlib, json, pathlib, sys
root = pathlib.Path(__file__).resolve().parents[2]
source = root / "tests/upstream/cf1-abi-entry-results.json"
fixture = json.loads(source.read_text())["fixtures"][0]
def require(condition, message):
    if not condition:
        raise ValueError(message)
require(fixture["path"].endswith("/calldata_array_length_v2.sol"), "wrong fixture")
shapes = {
    "f(uint256[])": ".array (.word (.uint 256))",
    "f(uint256[2])": ".fixed (.word (.uint 256)) 2",
    "f(uint256[][])": ".array (.array (.word (.uint 256)))",
}
rows = []
for variant in fixture["after"]["result"]["variants"]:
    for observed in variant["observed"]:
        require(not observed["failed"], "failure needs a separately specified decoder expectation")
        shape = shapes[observed["signature"]]  # refuse an unsupported signature
        raw = bytes.fromhex(observed["calldataBytes"].removeprefix("0x"))
        returned = observed["returnBytes"]
        require(returned.startswith("0x") and len(returned) >= 66, "short return word")
        require((len(returned) - 2) % 64 == 0, "partial return word")
        bytes.fromhex(returned[2:])  # validate the complete saved word sequence
        expected = int(returned[2:66], 16)
        rows.append((variant["pipeline"], shape, list(bytes(4) + raw), expected))
require(bool(rows), "no observations")
header = """import Solidity.Semantics.AbiEntry
open Solidity.AbiEntry
-- Runtime regression only: actual entry acceptance and outer calldata length.
-- Selector bytes are irrelevant to entry; the saved calldata omits them.
def replay (shape : Shape) (bytes : List UInt8) : Except String Nat := do
  let entries ← (entry ⟨bytes, 128⟩ 1000 [⟨shape, .calldata, true⟩]).mapError reprStr
  match entries with
  | .cons (.ref _ length) .nil =>
    match shape with
    | .fixed _ count => pure count
    | _ => pure length
  | .cons (.val _) .nil => throw "unexpected value entry for a calldata parameter"
def uintArrayEmptyRevert (bytes : List UInt8) : Bool :=
  match entry ⟨bytes, 128⟩ 1000 [⟨.array (.word (.uint 256)), .calldata, true⟩] with
  | .error .revert => true
  | _ => false
#eval do
"""
body = []
truncated = 0
for index, (pipeline, shape, raw, expected) in enumerate(rows):
    body.append(f"  let result{index} := replay ({shape}) {raw}")
    body.append(f'  unless result{index}.toOption == some {expected} do throw (IO.userError "vector {index} {pipeline} mismatch")')
    if shape == shapes["f(uint256[])"]:
        require(len(raw) > 4, "cannot truncate an absent argument")
        body.append(f'  unless uintArrayEmptyRevert {raw[:-1]} do throw (IO.userError "truncated vector {index} {pipeline}: expected exact empty revert")')
        truncated += 1
require(truncated == 8, "unexpected single-dimensional vector inventory")
body.append(f'  IO.println "PASS: {len(rows)} saved pipeline observations; entry accepted and dynamic outer / declared fixed lengths match; {truncated} one-byte truncations empty-revert"')
pathlib.Path(sys.argv[1]).write_text(header + "\n".join(body) + "\n")
print("fixture_sha256=" + hashlib.sha256(source.read_bytes()).hexdigest())
print("vectors=" + str(len(rows)))
print("truncated_controls=" + str(truncated))
