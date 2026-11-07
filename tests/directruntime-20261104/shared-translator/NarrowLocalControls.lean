import Solidity.Frontend.ExecutableAst.Shared.Compose
import Solidity.Frontend.ExecutableAst.Shared.Intrinsic

/-! Guards H90 regression: canonical solc-AST admission previously refused
primitive narrow locals accepted by solc_import. Preserve exact width spelling,
reject malformed widths and retain parameter/storage refusal boundaries.
The pinned CR witness checks admission and intrinsic obligation construction;
these are not source-equivalence or native/WASM closure proofs. -/

open Lean Solidity Solidity.Frontend Solidity.Frontend.ExecutableAst.Shared
private def elementary (name : String) : Json := Json.mkObj [
  ("nodeType", "ElementaryTypeName"), ("name", name)]
private def preserves (name : String) (p : PrimTy) : Bool :=
  match localTypeName (elementary name) with
  | .ok (.prim q, .named spelling) => q == p && spelling == name
  | _ => false
#guard preserves "uint8" .uint
#guard preserves "int248" .int
#guard ((List.range 256).filter (fun n => 8 ≤ n && n < 256 && n % 8 == 0)).all
  (fun n => preserves s!"uint{n}" .uint && preserves s!"int{n}" .int)
#guard ["uint0", "uint7", "uint08", "int264", "address", "string"].all
  (fun n => !(localTypeName (elementary n)).isOk)
-- The storage/type boundary has not silently lost narrow metadata.
#guard !(typeName (elementary "uint8")).isOk
#guard match localTypeName (elementary "uint256") with
  | .ok (.prim .uint, .named "uint") => true | _ => false
private def emptyC : Contract := { vars := [] }
-- The existing intrinsic local-type elaborator retains the eight-bit width.
#guard match elabTyW emptyC (.named "uint8") with
  | .ok (_, rows) => rows == [("", 8)] | _ => false
#print axioms localTypeName
#print axioms localPrim
#print axioms localTypeName_of_narrow

-- Exact CR H90 witness, copied byte-for-byte from the pinned owner head.
-- This guard must pass before any admission or parity improvement is reported.
#eval show IO Unit from do
  let path := "tests/directruntime-20261104/shared-translator/artifacts/h90/CanonicalReaderContract.ast.json"
  let .ok packet := Json.parse (← IO.FS.readFile path) | throw (IO.userError "H90 JSON")
  let some contract := (J.nodes packet).find? (fun j => J.kind j == "ContractDefinition") |
    throw (IO.userError "H90 contract")
  for name in ["wide", "narrowLocal", "signedWide", "flag", "memoryArray"] do
    let some ast := (J.arrD contract "nodes").toList.find? (fun j => J.str? j "name" == some name) |
      throw (IO.userError s!"H90 missing {name}")
    let .ok (_, d) := function executableReader ast contract.compress |
      throw (IO.userError s!"H90 admission {name}")
    if name == "narrowLocal" then
      unless d.body.any (fun s => match s with
          | .decl (.named "uint8") "y" _ => true | _ => false) do
        throw (IO.userError "H90 narrow local spelling lost")
      let C : Contract := { vars := [], funs := [(name, d)] }
      unless (specObligation C name).isOk do
        throw (IO.userError "H90 narrow local intrinsic obligation")
  let some param := (J.arrD contract "nodes").toList.find? (fun j => J.str? j "name" == some "narrowParam") |
    throw (IO.userError "H90 parameter witness")
  if (function executableReader param contract.compress).isOk then
    throw (IO.userError "H90 narrow parameter unexpectedly admitted")
  IO.println "H90 exact six-function probe: expected five admitted, narrow parameter refused; narrowLocal obligation constructed"
