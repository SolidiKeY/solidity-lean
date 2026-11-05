import Solidity.Tools.Upstream

open Solidity Solidity.Frontend Solidity.Tools.Upstream Lean

/- Enums nested in ABI types at the external entry and in `abi.decode`
   (lane FU2-D): `tests/abi-0.8.38/EnumArrays.sol`, replayed on the raw
   calldata of `tests/abi-0.8.38/EnumArrays.vectors.json`, whose expectations
   are EVM observations (`scripts/enum-abi-probe.mjs`, four configurations
   agreeing). Each sequence runs from a fresh deployment. `working` is
   agreement with the EVM; a refusal names its boundary. -/
solc_import "../abi-0.8.38/EnumArrays.ast.json" hash 0x52222d48809b5290 as AbiEnum.EnumArrays testing entrypoints

/-- The bytes a `0x…` hex string spells. -/
private def hexToBytes (s : String) : List Nat :=
  let ds := (s.drop 2).toList.map fun c =>
    if '0' ≤ c && c ≤ '9' then c.toNat - 48 else if 'a' ≤ c && c ≤ 'f' then c.toNat - 87 else c.toNat - 55
  let rec go : List Nat → List Nat
    | a :: b :: rest => (16 * a + b) :: go rest
    | _ => []
  go ds

/-- The parameter types of a signature, split at its top-level commas. -/
private def paramTypes (sig : String) : List String :=
  let inner := ((sig.splitOn "(").drop 1 |> "(".intercalate).dropRight 1
  if inner.isEmpty then [] else Id.run do
    let mut out : List String := []
    let mut cur := ""
    let mut depth := 0
    for c in inner.toList do
      if c == ',' && depth == 0 then
        out := out ++ [cur]; cur := ""
      else
        if c == '(' then depth := depth + 1
        if c == ')' then depth := depth - 1
        cur := cur.push c
    return out ++ [cur]

/-- The return types of the probe's functions. -/
private def returnTypes (sig : String) : List String :=
  if sig.startsWith "setStored" then [] else if sig.startsWith "stored" then ["uint8"] else ["uint256"]

/-- Each sequence's replay status and reason; with `flip`, every expected
outcome inverted (a negative control: no sequence may then agree). -/
private def replayAll (flip : Bool := false) : IO Unit := do
  let text ← IO.FS.readFile "tests/abi-0.8.38/EnumArrays.vectors.json"
  let .ok spec := Json.parse text | throw (IO.userError "invalid vectors JSON")
  let .ok seqs := spec.getObjValAs? (List Json) "sequences" | throw (IO.userError "no sequences")
  for seq in seqs do
    let label := (seq.getObjValAs? String "label").toOption.getD ""
    let calls := (seq.getObjValAs? (List Json) "calls").toOption.getD []
    let vectors := calls.map fun c =>
      let sig := (c.getObjValAs? String "signature").toOption.getD ""
      let expect := (c.getObjVal? "expect").toOption.getD Json.null
      let failed := (expect.getObjValAs? Bool "failed").toOption.getD false != flip
      let data := hexToBytes ((expect.getObjValAs? String "data").toOption.getD "0x")
      let args : List Nat := match (c.getObjValAs? String "raw").toOption with
        | some raw => hexToBytes raw
        | none =>
          -- the probe's `args` are words (or one word array, `entryArr`, or
          -- one word tuple, `entryStruct`), encoded as the ABI encodes them
          let vs := (c.getObjValAs? (List Json) "args").toOption.getD []
          let word (n : Nat) : List Nat := (Semantics.wordBytes n).map UInt8.toNat
          let nat (j : Json) : Nat := (j.getNat?).toOption.getD 0
          match vs with
          | [.arr xs] =>
            if sig.startsWith "entryArr" then word 32 ++ word xs.size ++ xs.toList.flatMap (word ∘ nat)
            else xs.toList.flatMap (word ∘ nat)
          | _ => vs.flatMap (word ∘ nat)
      Json.mkObj [("signature", toJson sig), ("calldata", toJson args),
        ("inputTypes", toJson (paramTypes sig)), ("outputTypes", toJson (returnTypes sig)),
        ("expectedBytes", toJson data), ("failure", toJson failed)]
    let report := replay AbiEnum.EnumArrays AbiEnum.EnumArrays.report
      (Json.mkObj [("vectors", toJson vectors)])
    let status := (report.getObjValAs? String "status").toOption.getD "?"
    let reason := (report.getObjValAs? String "reason").toOption.getD ""
    IO.println s!"{label}: {status}{if reason.isEmpty then "" else ": " ++ reason}"

/--
info: abi.decode of E[]: working: all supported runtime vectors match
abi.decode of E[2]: working: all supported runtime vectors match
E[] at the external entry: working: all supported runtime vectors match
struct with an enum member at the external entry: working: all supported runtime vectors match
public enum getter: working: all supported runtime vectors match
-/
#guard_msgs in #eval replayAll

/--
info: abi.decode of E[]: broken: runtime expectation mismatch: decodeArr(uint256,uint256)
abi.decode of E[2]: broken: runtime expectation mismatch: decodeFixed(uint256,uint256)
E[] at the external entry: broken: runtime expectation mismatch: entryArr(uint8[])
struct with an enum member at the external entry: broken: runtime expectation mismatch: entryStruct((uint8,uint256))
public enum getter: broken: runtime expectation mismatch: stored()
-/
#guard_msgs in #eval replayAll (flip := true)
