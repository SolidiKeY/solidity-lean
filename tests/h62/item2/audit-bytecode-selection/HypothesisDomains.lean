import Lean
import Solidity.Backend.Selection.InterfaceV2Controls
import tests.h62.item2.«audit-bytecode-selection».RuntimePremiseWitness

/-! Exact explicit-hypothesis domains derived from frozen theorem kernel types.
This audit-only elaborator packages every syntactic forall binder as a dependent
existential, including implicit parameters, record self, and proof arguments.
Only the conclusion is replaced by True: this proves hypothesis feasibility,
not the original conclusion. Original interfaces remain unchanged.

No universe instantiation is guessed. Hidden function binders under reducible
results are rejected. Not/Ne conclusions are kept as conclusions, never added
as false extra preconditions. Parent subobjects remain explicit self parameters.
This module imports Lean only in tests and must not enter the intrinsic core.
-/
namespace Solidity.H62.BytecodeSelection.HypothesisAudit
open Lean Meta Elab Term

private partial def explicitDomain (type : Expr) : MetaM Expr := do
  match type.consumeMData with
  | .forallE name domain body _ =>
    withLocalDecl name .default domain fun value => do
      let rest ← explicitDomain (body.instantiate1 value)
      let predicate ← mkLambdaFVars #[value] rest
      mkAppM ``Exists #[predicate]
  | .letE _ _ value body _ => explicitDomain (body.instantiate1 value)
  | conclusion =>
    let head := conclusion.getAppFn.constName?
    if head == some ``Not || head == some ``Ne then
      return mkConst ``True
    match ← whnf conclusion with
    | .forallE .. => throwError "hypothesis audit: hidden binders under reducible result"
    | _ => return mkConst ``True

elab "hypotheses_of% " id:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo id
  let info ← getConstInfo name
  unless wasOriginallyTheorem (← getEnv) name do
    throwError "hypothesis audit: target is not a theorem"
  unless info.levelParams.isEmpty do
    throwError "hypothesis audit: universe-polymorphic target needs explicit review"
  explicitDomain info.type

private theorem dependentToy (n : Nat) (_proof : n = 0) : True := True.intro
example : hypotheses_of% dependentToy := ⟨0, rfl, True.intro⟩

private theorem negativeToy (n : Nat) : 0 ≠ n + 1 := by
  intro impossible
  cases impossible
example : hypotheses_of% negativeToy := ⟨0, True.intro⟩

private def hidden : Prop := ∀ (n : Nat), n = 0 → True
private theorem hiddenToy : hidden := by intro _ _; exact True.intro
/-- error: hypothesis audit: hidden binders under reducible result -/
#guard_msgs in
#check hypotheses_of% hiddenToy

private theorem letToy : let n := 0; ∀ (m : Nat), m = n → True := by
  intro _ _ _
  exact True.intro
example : hypotheses_of% letToy := ⟨0, rfl, True.intro⟩

universe u
private theorem polymorphicToy (_type : Type u) : True := True.intro
/-- error: hypothesis audit: universe-polymorphic target needs explicit review -/
#guard_msgs in
#check hypotheses_of% polymorphicToy

private def datum : Nat := 0
/-- error: hypothesis audit: target is not a theorem -/
#guard_msgs in
#check hypotheses_of% datum

open Backend Backend.Selection

/-- The full frozen RuntimeConsumer.consume binder list is derived, not copied. -/
theorem runtime_consume_domain :
    hypotheses_of% Solidity.Backend.Selection.V2.RuntimeConsumer.consume := by
  exact ⟨Unit, (fun _ => ()), MixedControls.sampleIR, RuntimeFixture.relation,
    .code CompositionControls.code.instructions, 1, 2, CompositionControls.composition,
    LabelExec.step (encode CompositionControls.composition.assembled.code),
    (fun count => LabelExec.advance count (encode CompositionControls.composition.assembled.code)),
    (fun _ => True), RuntimeFixture.consumer, RuntimeFixture.compiler,
    CompositionControls.identityDecoder, 0, RuntimeFixture.initial, [23], [5,23],
    rfl, rfl, ⟨rfl, rfl⟩, True.intro⟩

/-- Inhabited DUP capacity with a populated protected suffix. -/
theorem capacity_domain :
    hypotheses_of% Solidity.Backend.Selection.V2.FrameCertificate.capacity := by
  exact ⟨[7], [7,7], V2.duplicateHead 7, [11,99], by decide, True.intro⟩

/-- The actual nonempty prefix, split, run and room premises coexist. -/
theorem prefixes_domain :
    hypotheses_of% Solidity.Backend.Selection.V2.FrameCertificate.prefixes := by
  exact ⟨[7], [7,7], V2.duplicateHead 7, [11,99], by decide,
    (V2.duplicateHead 7).code, [], [7,7,11,99], rfl,
    (V2.duplicateHead 7).frame [11,99], True.intro⟩

/-- A negative conclusion adds no fictitious Nonempty-certificate premise. -/
theorem no_overfull_domain :
    hypotheses_of% Solidity.Backend.Selection.V2.no_overfull_output := by
  exact ⟨[], List.replicate 1025 0,
    by simp only [List.length_replicate]; decide, True.intro⟩

/-- Intentional negative control: its derived hypothesis domain is impossible.
This is not recorded as a positive witness or a repaired interface. -/
theorem reject_push_domain_impossible :
    ¬ (hypotheses_of% Solidity.Backend.Selection.V2.Controls.reject_push_program) := by
  rintro ⟨_, _, certificate, bad, _⟩
  exact V2.Controls.reject_push_program certificate bad

#print axioms runtime_consume_domain
#print axioms capacity_domain
#print axioms prefixes_domain
#print axioms no_overfull_domain
#print axioms reject_push_domain_impossible
end Solidity.H62.BytecodeSelection.HypothesisAudit
