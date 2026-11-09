import Lean

/-! Build a joint existential from every outer binder of an unchanged theorem.
Each supplied term is checked against its dependent domain in order. The final
conclusion is proved by applying the original theorem to exactly those terms.
Head normalization exposes aliases and lets hiding further binders. The ordinary
kernel checks the resulting theorem; errors and unresolved terms are rejected.
Transitive proof dependencies are restricted to the standard three-axiom set. This command adds no assumption or axiom to the imported statement.
-/
namespace Solidity.H62.ExactAudit
open Lean Meta Elab Term Command

private partial def jointType (type : Expr) : MetaM Expr := do
  let type ← whnf type
  match type with
  | .forallE name domain body _ =>
    withLocalDeclD name domain fun x => do
      let tail ← jointType (body.instantiate1 x)
      mkAppM ``Exists #[← mkLambdaFVars #[x] tail]
  | _ => pure type

private partial def packWitness (target : Expr) (values : List Expr)
    (conclusion : Expr) : MetaM Expr := do
  match values with
  | [] => pure conclusion
  | value :: tail =>
    let head := target.getAppFn
    let args := target.getAppArgs
    let .const ``Exists levels := head
      | throwError "joint existential shape mismatch"
    if args.size != 2 then throwError "joint existential arity mismatch"
    let domain := args[0]!
    let predicate := args[1]!
    let rest ← packWitness (predicate.beta #[value]) tail conclusion
    pure (mkApp4 (Lean.mkConst ``Exists.intro levels) domain predicate value rest)

syntax (name := jointInputs) "#joint_inputs " ident " for " ident " :=" "[" term,* "]" : command

@[command_elab jointInputs]
def elabJointInputs : CommandElab := fun stx => do
  let helper := (← getCurrNamespace) ++ stx[1].getId
  let original := stx[3].getId
  let terms := stx[6].getSepArgs
  liftTermElabM <| Term.withoutErrToSorry do
    let info ← getConstInfo original
    unless info.isTheorem do throwError "expected an existing theorem: {original}"
    let levels ← info.levelParams.mapM fun _ => mkFreshLevelMVar
    let mut applied := Lean.mkConst original levels
    let sourceType ← inferType applied
    let target ← jointType sourceType
    let mut rest := sourceType
    let mut values : Array Expr := #[]
    for term in terms do
      rest ← whnf rest
      let .forallE _ domain body _ := rest
        | throwError "too many witness terms for {original}"
      let value ← Term.elabTermEnsuringType term (some domain)
      Term.synthesizeSyntheticMVarsNoPostponing
      let value ← instantiateMVars value
      values := values.push value
      applied := mkApp applied value
      rest := body.instantiate1 value
    rest ← whnf rest
    if rest.isForall then throwError "missing witness binder(s) for {original}: {rest}"
    let proof ← packWitness target values.toList applied
    unless (← isDefEq (← inferType proof) target) do
      throwError "joint witness does not have its derived target type"
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars proof
    let target ← instantiateMVars target
    if proof.hasMVar || target.hasMVar || proof.hasFVar || target.hasFVar || proof.hasSorry then
      throwError "joint witness is not a closed, fully checked proof"
    let saved ← getEnv
    addDecl <| .thmDecl {name := helper, levelParams := [], type := target, value := proof}
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    unless (← collectAxioms helper).all (allowed.contains ·) do
      setEnv saved
      throwError "joint witness depends on a nonstandard axiom"
    logInfo m!"JOINT_INPUTS original={original} helper={helper} binders={values.size}"
    logInfo m!"FROZEN_TYPE {original}: {← instantiateMVars sourceType}"
    logInfo m!"FROZEN_EXPR {original}: {repr (← instantiateMVars sourceType)}"
    logInfo m!"JOINT_TYPE {helper}: {target}"

end Solidity.H62.ExactAudit

namespace Solidity.H62.ExactAudit
open Lean Elab Command

/-- Emit all compiler theorem declarations attributed to one imported module,
including generated/private declarations. Classification is left explicit. -/
syntax (name := auditModuleTheorems) "#audit_module_theorems " ident : command

@[command_elab auditModuleTheorems]
def elabAuditModuleTheorems : CommandElab := fun stx => do
  let module := stx[1].getId
  let env ← getEnv
  let mut entries : Array Json := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if env.header.moduleNames[idx.toNat]! == module && info.isTheorem then
        let signature ← liftTermElabM do
          withOptions (fun opts => (opts.setBool `pp.proofs true).setBool `pp.universes true) do
            pure (toString (← Lean.Meta.ppExpr info.type))
        entries := entries.push (Json.mkObj [
          ("name", toJson name.toString), ("module", toJson module.toString),
          ("signature", toJson signature), ("kernel_type_expr", toJson (reprStr info.type)),
          ("levels", toJson (info.levelParams.map Name.toString)),
          ("axioms", toJson ((← Lean.collectAxioms name).map Name.toString).toList)])
  logInfo s!"MODULE_THEOREMS_JSON {Json.compress (Json.mkObj [("module", toJson module.toString), ("theorems", Json.arr entries)])}"

end Solidity.H62.ExactAudit
