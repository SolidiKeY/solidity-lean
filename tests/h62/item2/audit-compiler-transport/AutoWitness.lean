import Lean.Util.Heartbeats
import tests.h62.item2.«audit-compiler-transport».JointHypotheses
import tests.h62.item2.«audit-compiler-transport».NilFixture
import tests.h62.item2.«audit-compiler-transport».OptimizerFixture
import tests.h62.item2.«audit-compiler-transport».ExplicitCases

/-! Bounded constructive witness search over fixed, independently proved points.
An unsolved case produces no theorem. Successful values are checked by Lean as
ordinary theorem declarations. No source statement is changed or used as an
extra premise, and no missing premise is assumed. -/
namespace H62.CompilerTransport.AutoWitness
open Lean Meta Elab Command

private def auditName (text : String) : Name :=
  (text.splitOn ".").foldl (fun accumulated part =>
    match part.toNat? with
    | some number => .num accumulated number
    | none => .str accumulated part) .anonymous

private def proofNames : Array Name := #[
  ``True.intro, ``ExplicitCases.accepted, ``ExplicitCases.rejected,
  ``ExplicitCases.distinct, ``ExplicitCases.preserves, ``ExplicitCases.reflexive,
  ``ExplicitCases.transitive, ``ExplicitCases.nonempty_each,
  ``NilFixture.input, ``NilFixture.source_run, ``NilFixture.target_run,
  ``NilFixture.mapped, ``NilFixture.represented, ``NilFixture.recognized,
  ``NilFixture.payment_free, ``NilFixture.push_free, ``NilFixture.capacity,
  ``NilFixture.link, ``NilFixture.mapped_link, ``NilFixture.reframed_link,
  ``NilFixture.overbudget, ``OptimizerFixture.accepted,
  ``OptimizerFixture.distinct, ``OptimizerFixture.rejected,
  ``OptimizerFixture.preserves, ``OptimizerFixture.reflexive,
  ``OptimizerFixture.transitive, ``OptimizerFixture.each]

private def dataNames : Array Name := #[
  ``ExplicitCases.validator, ``ExplicitCases.Carrier, ``ExplicitCases.relation,
  ``ExplicitCases.identity, ``ExplicitCases.nonemptyPasses,
  ``ExplicitCases.input37, ``ExplicitCases.input38,
  ``NilFixture.compiled, ``OptimizerFixture.validator,
  ``NilFixture.program, ``NilFixture.fragment, ``NilFixture.output,
  ``Solidity.Backend.Passes.MemoryCallControls.initial,
  ``Solidity.Backend.Passes.MemoryCallControls.machine,
  ``Solidity.Backend.Passes.MemoryCallControls.base,
  ``Solidity.Backend.Passes.MemoryCallControls.C,
  ``OptimizerFixture.relation, ``OptimizerFixture.identity,
  ``OptimizerFixture.passes, ``OptimizerFixture.yulIdentity,
  ``Nat, ``Bool, ``NilFixture.context, ``NilFixture.tail,
  ``NilFixture.zero, ``NilFixture.one, ``NilFixture.frame,
  ``Bool.false, ``Bool.true, ``PUnit, ``PUnit.unit]

private def tryConstant (goal : Expr) (names : Array Name) : MetaM Bool := do
  if (← goal.mvarId!.isAssigned) then return true
  let expected ← instantiateMVars (← inferType goal)
  for name in names do
    let remaining ← getRemainingHeartbeats
    if remaining < 20000000 then throwError "bounded search stopped with heartbeat reserve intact"
    let saved ← saveState
    try
      let candidate ← mkConstWithFreshMVarLevels name
      let candidateType ← inferType candidate
      -- Limit search to 2,000 user heartbeats per candidate inside the original
      -- declaration budget; never increase a proof or kernel-checking limit.
      let compatible ← tryCatchRuntimeEx
        (withCurrHeartbeats <|
          withTheReader Core.Context (fun context =>
            { context with maxHeartbeats := min remaining 2000000 }) do
              isDefEq expected candidateType)
        (fun error => do
          if error.isMaxHeartbeat || error.isMaxRecDepth then return false
          throw error)
      if compatible then
        goal.mvarId!.assign candidate
        return true
    catch _ => pure ()
    saved.restore
  return false

private def premiseType (type : Expr) : MetaM Expr :=
  forallTelescope type fun xs _ => do
    let mut body := Lean.mkConst ``True
    for x in xs.reverse do
      body ← mkAppM ``Exists #[← mkLambdaFVars #[x] body]
    return body

private partial def pack (type : Expr) (values : List Expr) : MetaM Expr := do
  match type.consumeMData, values with
  | .forallE name domain body _, value :: rest =>
    let predicate ← withLocalDeclD name domain fun localValue => do
      mkLambdaFVars #[localValue] (← premiseType (body.instantiate1 localValue))
    let inner ← pack (body.instantiate1 value) rest
    mkAppOptM ``Exists.intro #[some domain, some predicate, some value, some inner]
  | .forallE .., [] => throwError "missing original parameter"
  | _, [] => pure (Lean.mkConst ``True.intro)
  | _, _ => throwError "unexpected additional parameter"

private def construct (name : Name) : MetaM (Expr × Expr × Array Json × List Name) := do
  let sourceInfo ← getConstInfo name
  let constant := Lean.mkConst name (sourceInfo.levelParams.map Level.param)
  let original ← inferType constant
  let (parameters, _, _) ← forallMetaTelescope original
  -- Constrain proof-carrying certificate families before solving acceptance or
  -- execution premises; otherwise a free relation could be fixed arbitrarily.
  for parameter in parameters do
    unless ← parameter.mvarId!.isAssigned do
      let type ← instantiateMVars (← inferType parameter)
      let head := type.getAppFn.constName?.getD .anonymous
      if head == ``Solidity.Evm.Compiler.Compilation || head == ``Solidity.Optimizer.Validator then
        discard <| tryConstant parameter dataNames
  for _ in [:2] do
    for parameter in parameters do
      unless ← parameter.mvarId!.isAssigned do
        if ← isProp (← inferType parameter) then
          discard <| tryConstant parameter proofNames
    for parameter in parameters do
      unless ← parameter.mvarId!.isAssigned do
        unless ← isProp (← inferType parameter) do
          discard <| tryConstant parameter dataNames
  let mut values : Array Expr := #[]
  let mut bindings : Array Json := #[]
  for parameter in parameters do
    let value ← instantiateMVars parameter
    if value.hasMVar then throwError "original parameter or universe remains uninstantiated"
    values := values.push value
    bindings := bindings.push (Json.mkObj [
      ("value",toJson (← ppExpr value).pretty),
      ("type",toJson (← ppExpr (← inferType value)).pretty)])
  let expected ← instantiateMVars (← premiseType original)
  let proof ← instantiateMVars (← pack original values.toList)
  unless ← isDefEq (← inferType proof) expected do
    throwError "constructed tuple does not match the original complete telescope"
  if expected.hasMVar || proof.hasMVar then
    throwError "constructed tuple retains unresolved metavariables"
  return (expected,proof,bindings,sourceInfo.levelParams)

elab "#audit_joint " source:str " as " outputName:ident " into " file:str : command => do
  let found ← liftTermElabM do
    try
      let (type, proof, bindings, levels) ← construct (auditName source.getString)
      return Except.ok (type, proof, bindings, levels)
    catch error => return Except.error (← error.toMessageData.toString)
  match found with
  | .error message =>
    liftIO <| IO.FS.writeFile file.getString (Json.pretty (Json.mkObj [
      ("source",toJson source.getString),("status",toJson "unresolved"),
      ("reason",toJson message)]) ++ "\n")
  | .ok (type,proof,bindings,levels) =>
    -- Normal checked declaration path. Kernel rejection is fatal and is never
    -- converted into an unresolved row.
    liftCoreM <| addDecl (.thmDecl { name := outputName.getId, levelParams := levels, type, value := proof })
    let axioms ← collectAxioms outputName.getId
    for axiomName in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unexpected axiom dependency {axiomName}"
    liftIO <| IO.FS.writeFile file.getString (Json.pretty (Json.mkObj [
      ("source",toJson source.getString),("status",toJson "checked-declaration"),
      ("axioms",toJson (axioms.map Name.toString)),
      ("universe_parameters",toJson (levels.map Name.toString)),
      ("proof",toJson outputName.getId.toString),("bindings",toJson bindings)]) ++ "\n")
end H62.CompilerTransport.AutoWitness
