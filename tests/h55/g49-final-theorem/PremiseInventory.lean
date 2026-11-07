import Solidity.Roadmap.G49Final.PassChain
import Lean

/-! External inventory of the checked backfill's actual kernel declaration.
No inventory row or ownership label proves or discharges a producer premise.
The bulk output is retained outside Git by the bounded check runner. -/
open Lean Elab Command in
run_cmd do
  let name := `Solidity.Roadmap.G49Final.pass_chain
  let info ← getConstInfo name
  let premises ← liftTermElabM do
    Meta.forallBoundedTelescope info.type (some info.type.getNumHeadForalls) fun xs _ => do
      let mut rows : Array Json := #[]
      let mut rawType := info.type
      for x in xs do
        let decl ← x.fvarId!.getDecl
        let ty ← Meta.ppExpr decl.type
        let rawDomain := rawType.consumeMData.bindingDomain!
        rawType := rawType.consumeMData.bindingBody!
        rows := rows.push (Json.mkObj [
          ("index", toJson rows.size), ("name", toJson decl.userName.toString),
          ("type", toJson ty.pretty), ("isProp", toJson (← Meta.isProp decl.type)),
          ("closedExpr", toJson (reprStr rawDomain)),
          ("constants", toJson (decl.type.getUsedConstants.toList.map Name.toString))])
      return rows
  let ty ← liftTermElabM do return (← Meta.ppExpr info.type).pretty
  let axioms ← collectAxioms name
  logInfo m!"G49-PREMISES {(Json.mkObj [
    ("name", toJson name.toString), ("type", toJson ty), ("premises", .arr premises),
    ("dependencies", toJson (info.getUsedConstantsAsSet.toList.map Name.toString)),
    ("axioms", toJson (axioms.toList.map Name.toString))]).compress}"

#print axioms Solidity.Roadmap.G49Final.pass_chain
