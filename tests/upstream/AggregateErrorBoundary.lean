import Solidity.Tools.Upstream
open Solidity Solidity.Frontend Solidity.Tools Solidity.Tools.Upstream Lean
solc_import "AggregateErrorControls.legacy.ast.json" hash 0x323ea6f54c3796de as Group10.AggregateLegacy.AggregateErrorControls testing
solc_import "AggregateErrorControls.viaIR.ast.json" hash 0x4e0b11581b66a097 as Group10.AggregateIR.AggregateErrorControls testing


#eval (do
  for report in [Group10.AggregateLegacy.AggregateErrorControls.report,Group10.AggregateIR.AggregateErrorControls.report] do
    let refused := report.filter (fun r => r.status == .unsupported)
    unless refused.length == 2 && refused.all (fun r =>
        (r.reason.splitOn "a calldata slice ordinary alias without a known calldata origin").length > 1) do
      throw (IO.userError "exact calldata provenance refusals changed")
  for C in [Group10.AggregateLegacy.AggregateErrorControls,Group10.AggregateIR.AggregateErrorControls] do
    let some d := Semantics.lookupBy "PairError" C.errors | throw (IO.userError "missing PairError")
    let parameter : Option (Solidity.Name × Ty) := d.params[1]?
    let some (_,T) := parameter | throw (IO.userError "missing struct parameter")
    let Ty.ref (RefTy.struct original) := T | throw (IO.userError "not a struct parameter")
    let other := original.replace "ErrorPair" "OtherPair"
    unless other != original && !(Semantics.structDef original).isEmpty && Semantics.structDef original == Semantics.structDef other do
      throw (IO.userError "distinct same-layout nominal control is malformed")
    let declared : Contract := {C with structs := ("OtherPair",other) :: C.structs}
    let bad : Contract := {declared with errors := C.errors.map fun (e,d) => if e == "PairError" then
        (e,{d with params := d.params.map fun (n,T) =>
          match T with | .ref (.struct _) => (n,.ref (.struct other)) | _ => (n,T)}) else (e,d)}
    unless bad.structName? "OtherPair" == some other do throw (IO.userError "other struct not declared")
    let program : Except String (Blk bad []) := do Solidity.Tools.Upstream.entryProg bad [← Solidity.Tools.runStmt bad "pairMemory" []]
    if program.isOk then throw (IO.userError "same-layout wrong nominal struct admitted")
  unless errorAbiHasEnum (.array (.array .uint)) [("[][]#enum",1)] "" do
    throw (IO.userError "nested aggregate enum refusal missing")
  : IO Unit)
