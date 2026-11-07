import Solidity.Tools.DirectRuntime
import Solidity.Semantics.RunFuel
/-! Guards H90 fixed-byte local spelling/marker and tuple/bitwise regressions.
Finite intrinsic/checker observations are not source/ABI/native proofs. Parameter,
storage, dynamic-byte/string and malformed fixed-byte refusals remain explicit.
The positive length checker path refuses with a uint32 range-literal diagnostic;
the false length assertion refutes. That proof/backend gap remains explicit. -/
open Lean Solidity Solidity.Frontend Solidity.Frontend.ExecutableAst.Shared
private def elementary (name : String) : Json := Json.mkObj [("nodeType", "ElementaryTypeName"),("name",name)]
#guard (List.range 32).all fun i =>
  let name := s!"bytes{i+1}"
  match localTypeName (elementary name), elabTyW ({ vars := [] } : Contract) (.named name) with
  | .ok (.prim .uint, .named spelling), .ok (.prim .uint, rows) =>
    spelling == name && rows == (if i+1 < 32 then [("",8*(i+1))] else []) ++ [("#bytes",i+1)]
  | _, _ => false
#guard ["bytes0","bytes33","bytes01","bytes","string","address"].all fun name => !(localTypeName (elementary name)).isOk
#guard !(typeName (elementary "bytes4")).isOk
private def checked {α : Type} : Except String α → IO α
  | .ok a => pure a | .error e => throw (IO.userError e)
#eval show IO Unit from do
  let packet ← checked (Json.parse (← IO.FS.readFile "tests/directruntime-20261104/shared-translator/artifacts/fixed-bytes/FixedByteLocals.ast.json"))
  let some source := (J.nodes packet).find? (fun j => J.str? j "name" == some "FixedByteLocals") |
    throw (IO.userError "missing fixed-byte source")
  for (name,expected) in [("zero","proved"),("complement","proved"),("wideComplement","proved"),
      ("tupleSwap","proved"),("repeated","proved"),("wrong","refuted"),("length","unsupported"),("wrongLength","refuted"),("widening","proved"),("parameter","unsupported")] do
    for box in [false,true] do
      let nodes := (J.arrD source "nodes").map fun n =>
        if box && J.str? n "name" == some name then
          n.setObjVal! "documentation" (Json.mkObj [("nodeType",toJson "StructuredDocumentation"),("text",toJson "@custom:key box")]) else n
      let selectedSource := source.setObjVal! "nodes" (toJson nodes)
      let rows ← checked (Tools.DirectRuntime.check (Json.mkObj [("contract",selectedSource),("function",toJson name)]))
      let rows ← checked rows.getArr?
      unless rows.size == 1 do throw (IO.userError "fixed-byte row count")
      unless (rows[0]!.getObjValAs? String "tag").toOption == some (if box then "box" else "diamond") do
        throw (IO.userError s!"{name} box={box}: modality changed {rows[0]!}")
      let status ← checked (rows[0]!.getObjValAs? String "status")
      unless status == expected do throw (IO.userError s!"{name}: {rows[0]!}")
      if name == "parameter" then
        unless (rows[0]!.getObjValAs? String "reason").toOption == some "compact verifier: unsupported type bytes4" do
          throw (IO.userError "fixed-byte parameter diagnostic changed")
      if name == "length" then
        unless (rows[0]!.getObjValAs? String "reason").toOption == some "4294967296 does not fit uint32" do
          throw (IO.userError "fixed-byte length lowering gap changed")
      IO.println s!"FIXED_BYTE_LOCAL {name} box={box}: {status}"
#print axioms localTypeName_of_fixedBytes
