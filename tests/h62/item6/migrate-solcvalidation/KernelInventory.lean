import Lean
import Solidity.SolcValidation.DataResolution

/-! Test-only inventory of actual imported kernel declarations, including
private helpers and generated constructors, recursors and equation lemmas.
Types use Expr representation, independently of pretty-printer field notation.
Raw cross-version differences require classification, not automatic acceptance.
-/
open Lean Elab Command

elab "#migration_kernel_inventory " moduleName:str : command => do
  let env ← getEnv
  let constants := env.constants.toList.toArray.qsort (fun a b => Name.lt a.1 b.1)
  let mut count : Nat := 0
  for (name, ci) in constants do
    let some index := env.getModuleIdxFor? name | continue
    let some owner := env.header.moduleNames[index.toNat]? | continue
    unless owner.toString == moduleName.getString do continue
    let axioms ← collectAxioms name
    unless axioms.all (fun n => n == ``propext || n == ``Classical.choice || n == ``Quot.sound) do
      throwError "unexpected axiom in migration declaration {name}"
    let kind := match ci with
      | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor" | .inductInfo _ => "inductive"
    let row := Json.mkObj [
      ("module", Json.str owner.toString), ("name", Json.str name.toString),
      ("kind", Json.str kind), ("type_expr", Json.str (reprStr ci.type)),
      ("level_params", Json.arr (ci.levelParams.toArray.map (fun n => Json.str n.toString))),
      ("axioms", Json.arr ((axioms.qsort Name.lt).map (fun n => Json.str n.toString)))]
    logInfo m!"MIGRATION_KERNEL {row.compress}"
    count := count + 1
  if count == 0 then throwError "migration module has no imported declarations"
  logInfo m!"MIGRATION_KERNEL_COUNT {moduleName.getString} {count}"

#migration_kernel_inventory "Solidity.SolcValidation.Dialect"
#migration_kernel_inventory "Solidity.SolcValidation.DataLayout"
#migration_kernel_inventory "Solidity.SolcValidation.DataResolution"
