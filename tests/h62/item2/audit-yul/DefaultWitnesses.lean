import Lean
/-! Bounded construction of complete joint witnesses, never assumed premises.
The target is the existential closure of every exposed outer binder in the exact
imported theorem type, ending in True. Universe parameters are retained. A
candidate is reported covered only after Lean's normal kernel accepts its
closed proof. Failed construction emits an explicit uncovered record and no
declaration. No source theorem, option budget or interface is changed. -/
open Lean Meta Elab Command

register_option h62.auditOutput : String := {
  defValue := ""
  descr := "Off-Git JSONL output for H62 joint-witness attempts" }

namespace H62.AuditYul.Defaults

private partial def jointType (type : Expr) : MetaM Expr := do
  let type ← whnf type
  match type with
  | .forallE name domain body info =>
    withLocalDecl name info domain fun x => do
      let rest ← jointType (body.instantiate1 x)
      mkAppM ``Exists #[← mkLambdaFVars #[x] rest]
  | _ => pure (mkConst ``True)

private partial def construct (type : Expr) : MetaM (Expr × Array String) := do
  let type ← whnf type
  match type with
  | .forallE name domain body info =>
    let value ← if ← isProp domain then
        try
          let decided ← mkDecide domain
          -- mkDecideProof contains an expected-type hint; do not use that
          -- hint as evidence that the decision actually reduced to true.
          unless ← isDefEq decided (mkConst ``Bool.true) do
            throwError "decidable hypothesis is false"
          mkDecideProof domain
        catch _ => mkDefault domain
      else mkDefault domain
    let value ← instantiateMVars value
    let value ← withTransparency .all (whnf value)
    if value.hasMVar || value.hasFVar then throwError "nonclosed witness at {name}"
    let (rest, values) ← construct (body.instantiate1 value)
    let predicate ← withLocalDecl name info domain fun x => do
      mkLambdaFVars #[x] (← jointType (body.instantiate1 x))
    let proof ← mkAppOptM ``Exists.intro #[some domain, some predicate, some value, some rest]
    return (proof, #[reprStr value] ++ values)
  | _ => pure (mkConst ``True.intro, #[])

private def expectedJoint (type : Expr) : MetaM (Expr × Nat) :=
  forallTelescopeReducing type fun xs _ => do
    let mut result := mkConst ``True
    for x in xs.reverse do
      result ← mkAppM ``Exists #[← mkLambdaFVars #[x] result]
    return (result, xs.size)

private def emit (row : Json) : CommandElabM Unit := do
  let path := h62.auditOutput.get (← getOptions)
  if path.isEmpty then throwError "h62.auditOutput must name an audit artifact"
  let output ← IO.FS.Handle.mk path .append
  output.putStrLn row.compress
  output.flush

elab "audit_joint_defaults " source:str " as " target:ident : command => do
  let sourceText := source.getString
  let env ← getEnv
  let sourceName? := env.constants.fold (init := none) fun found n _ =>
    if n.toString == sourceText then some n else found
  let some sourceName := sourceName? | throwError "missing frozen theorem {sourceText}"
  unless wasOriginallyTheorem env sourceName do throwError "not a theorem: {sourceText}"
  let ci ← getConstInfo sourceName
  let targetName := target.getId
  if env.contains targetName then throwError "duplicate audit declaration {targetName}"
  let attempt ← liftTermElabM do
    try
      let (expected, count) ← expectedJoint ci.type
      let type ← jointType ci.type
      unless ← isDefEq type expected do throwError "joint telescope shape drift"
      let (proof, values) ← construct ci.type
      if values.size != count then throwError "joint telescope arity drift"
      let type ← instantiateMVars expected
      let proof ← instantiateMVars proof
      if type.hasMVar || proof.hasMVar || type.hasFVar || proof.hasFVar then
        throwError "open witness term"
      unless ← isDefEq (← inferType proof) type do throwError "witness type mismatch"
      pure (Except.ok (type, proof, values))
    catch ex =>
      pure (Except.error (← ex.toMessageData.toString))
  match attempt with
  | .error reason =>
    emit <| Json.mkObj [("theorem", toJson sourceText),
      ("status", toJson "uncovered"), ("reason", toJson reason)]
  | .ok (type, proof, values) =>
    -- This is ordinary declaration checking, not an unsafe environment update.
    -- Kernel rejection is a hard compilation error, never an uncovered record.
    liftCoreM <| addAndCompile <| .thmDecl {
      name := targetName, levelParams := ci.levelParams, type := type, value := proof }
    let checkedEnv ← getEnv
    unless (checkedEnv.checked.get.find? targetName).isSome do
      throwError "audit theorem not present in checked kernel environment"
    let axioms ← liftTermElabM (collectAxioms targetName)
    unless axioms.all (fun n => [``propext, ``Classical.choice, ``Quot.sound].contains n) do
      throwError "unapproved witness axioms {axioms}"
    emit <| Json.mkObj [("theorem", toJson sourceText),
      ("status", toJson "joint_witness_proved"), ("proof", toJson targetName.toString),
      ("level_parameters", toJson (ci.levelParams.map Name.toString)),
      ("frozen_type_repr", toJson (reprStr ci.type)),
      ("joint_type_repr", toJson (reprStr type)), ("values_repr", toJson values),
      ("axioms", toJson (axioms.toList.map Name.toString))]
end H62.AuditYul.Defaults
