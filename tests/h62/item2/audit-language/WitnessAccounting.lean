import tests.h62.item2.«audit-language».FullTelescopeWitness

/-!
Guarded regression: source association counts are not kernel certification, and
closed schemas must not earn input-tuple credit. This diagnostic checks the
existing full leading-telescope schema, kernel theorem status and axiom policy.
Raw leading binders are counted; semantic interface classification, historical
ownership replay and dependent-definition meaning audits remain separate.
-/
open Lean Meta Elab Term

private partial def leadingKinds (type : Expr) : MetaM (Nat × Nat) := do
  match type with
  | .forallE name domain body info =>
    let premise ← isProp domain
    withLocalDecl name info domain fun x => do
      let (inputs, premises) ← leadingKinds (body.instantiate1 x)
      pure (inputs + 1, premises + if premise then 1 else 0)
  | _ => pure (0, 0)

elab "#audit_witness " witness:ident " for " target:ident : command => do
  Lean.Elab.Command.liftTermElabM do
    let w ← realizeGlobalConstNoOverloadWithInfo witness
    let t ← realizeGlobalConstNoOverloadWithInfo target
    let env ← getEnv
    let some (.thmInfo wi) := env.checked.get.find? w | throwError "witness is not a kernel theorem"
    let some (.thmInfo ti) := env.checked.get.find? t | throwError "target is not a kernel theorem"
    unless wi.levelParams.isEmpty && ti.levelParams.isEmpty do
      throwError "polymorphic schema needs explicit level handling"
    let expected ← elabTerm (← `(hypotheses_of% $target)) none
    let expected ← instantiateMVars expected
    if expected.hasMVar then throwError "unresolved witness schema"
    unless (← isDefEq wi.type expected) do throwError "hypothesis telescope mismatch"
    let axioms ← Lean.collectAxioms w
    let targetAxioms ← Lean.collectAxioms t
    for axiomName in axioms ++ targetAxioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unapproved witness axiom: {axiomName}"
    let (inputs, premises) ← leadingKinds ti.type
    let kind := if inputs == 0 then "no-input-tuple"
      else if premises == 0 then "inputs-without-premises" else "joint-premises"
    let row := Json.mkObj [("witness", toJson w.toString), ("target", toJson t.toString),
      ("leading_binders", toJson inputs), ("prop_binders", toJson premises),
      ("kind", toJson kind), ("witness_axioms", toJson (axioms.map Name.toString)),
      ("target_axioms", toJson (targetAxioms.map Name.toString))]
    logInfo m!"H62_WITNESS_AUDIT {row.compress}"
