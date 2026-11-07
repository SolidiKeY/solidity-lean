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

#check localTypeName_of_narrow
#check localTypeName_of_fixedBytes
#print axioms localTypeName_of_narrow
#print axioms localTypeName_of_fixedBytes
