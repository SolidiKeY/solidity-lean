import Solidity.Correctness.Lowering.Total.Production
import Solidity.Correctness.Lowering.Loops.Correct

/-!
# Loop lowering: what the contract still asks (e2b-loops-producer)

`Total.LowerLoopsCorrectContract b i decode` composed with the two theorems that
exist: the production theorem `universalProducerCorrect` (e2d) and the family
theorem `lowerLoopsFamily_correct` (e1). Both hold at every boundary, so:

* `contract_iff_coverage`: the contract is exactly its coverage conjunct.
* `contract_iff`: the interpretation `i` adds nothing beyond `Faithful b i`
  (its four agreement fields); what remains is `Residual b decode`, stated
  against the boundary's own reference interpretation.
* `normalCompatibility_iff`, `returnCompatibility_iff`: the e1 endpoints are
  theorems, so the two compatibility fields say only that `relates` holds of
  every family pair.
* `production_correct`: the consumer whose only premise on the request is its
  successful pipeline; admission comes from `FullDomain b` (the boundary
  admits every request whose pipeline succeeds). The raw `LowersTo` conjunct
  is for top-level requests only: nothing is stated of the `lowerLoops` run
  inside `calleeBody`.
* `Residual.of_empty`: a boundary admitting nothing, whose `relates` holds of
  the e1 families, satisfies the residual. So the contract alone does not rule
  out input exclusion, and `FullDomain` is a separate obligation.
The concrete boundary built on this reduction is in `Total.Decode` (the
raw-to-Source decoder), `Total.Spells` (the spelling relation) and
`Total.Boundary` (policies, simulation, allocation trace, state relation and
what is left). `Solidity.Goals.lowerLoopsCorrect` stays unstated.
-/
namespace Solidity.Correctness.Lowering.Total

open Solidity.Roadmap.G49Final

/-- `relates` holds of every pair of the e1 normal-outcome family. -/
def RelatesNormalFamily (b : SemanticBoundary) : Prop :=
  ∀ k {E srcΓ returns M l u C Γ} (m : Lowering.V07.ContextMap srcΓ Γ) (pair : Loops.Pair m)
    (extra : Loops.Shape.Extra E returns M u srcΓ C Γ k) names,
    b.relates (SourceProgram.ofStmt (Loops.Shape.source (l := l) k pair extra))
      (k.lowered pair extra names)

/-- `relates` holds of every pair of the e1 return family. -/
def RelatesReturnFamily (b : SemanticBoundary) : Prop :=
  ∀ k {E srcΓ M l u C Γ} (m : Lowering.V07.ContextMap srcΓ Γ) (pair : Loops.Pair m)
    (extra : Loops.RetShape.Extra E srcΓ C Γ k) names,
    b.relates (SourceProgram.ofStmt (Loops.RetShape.source (M := M) (l := l) (u := u) k pair extra))
      ⟨_, k.program pair extra names⟩

/-- The e1 normal endpoint is a theorem, so compatibility is membership. -/
theorem normalCompatibility_iff (b : SemanticBoundary) :
    NormalCompatibility b ↔ RelatesNormalFamily b := by
  constructor
  · intro h k E srcΓ returns M l u C Γ m pair extra names
    exact (h k m pair extra names).mpr (normalFamily_correct k m pair extra names _ rfl)
  · intro h k E srcΓ returns M l u C Γ m pair extra names
    exact ⟨fun _ => normalFamily_correct k m pair extra names _ rfl,
      fun _ => h k m pair extra names⟩

/-- The e1 return endpoint is a theorem, so compatibility is membership. -/
theorem returnCompatibility_iff (b : SemanticBoundary) :
    ReturnCompatibility b ↔ RelatesReturnFamily b := by
  constructor
  · intro h k E srcΓ M l u C Γ m pair extra names
    exact (h k m pair extra names).mpr (returnFamily_correct k m pair extra names)
  · intro h k E srcΓ M l u C Γ m pair extra names
    exact ⟨fun _ => returnFamily_correct k m pair extra names, fun _ => h k m pair extra names⟩

/-- The production and family conjuncts hold at every boundary. -/
theorem contract_iff_coverage (b : SemanticBoundary) (i : RawSourceInterpretation)
    (decode : Request → Option SourceProgram) :
    LowerLoopsCorrectContract b i decode ↔ CoverageObligations b i decode :=
  ⟨fun h => h.2.1, fun h => ⟨universalProducerCorrect, h, lowerLoopsFamily_correct⟩⟩

/-- The interpretation agrees with the boundary's reference. -/
structure Faithful (b : SemanticBoundary) (i : RawSourceInterpretation) : Prop where
  admitted : ∀ r, i.entry r ↔ b.reference.entry r
  association : ∀ r s, i.associated r s ↔ b.reference.associated r s
  source : ∀ s, (i.source s).behaviour = (b.reference.source s).behaviour
  target : ∀ {C Γ} (p : Blk C Γ), (i.target p).behaviour = (b.reference.target p).behaviour

theorem Faithful.refl (b : SemanticBoundary) : Faithful b b.reference :=
  ⟨fun _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ => rfl, fun _ => rfl⟩

/-- What the contract asks of a boundary and a decoder, with no interpretation
left: every admitted request decodes, to its one associated Source program;
every successful pipeline of an admitted request has a safe allocation trace,
is related to that program and refines it; and the e1 families are related. -/
structure Residual (b : SemanticBoundary) (decode : Request → Option SourceProgram) : Prop where
  total : ∀ r, b.reference.entry r → ∃ s, decode r = some s
  decoder : ∀ r s, b.reference.entry r → (decode r = some s ↔ b.reference.associated r s)
  allocation : ∀ r o after parts program, b.reference.entry r →
    r.pipeline o after parts program →
    ∃ scopes, b.allocations r o after parts program scopes ∧
      ∀ scope ∈ scopes, SafeSpellings r.input.names scope.protectedNames scope.generated
  pipeline : ∀ r o after parts program s, b.reference.entry r → decode r = some s →
    r.pipeline o after parts program →
    b.relates s program ∧
      Nonempty (PassCorrect (b.reference.source s).behaviour (b.reference.target program).behaviour)
  normal : RelatesNormalFamily b
  returns : RelatesReturnFamily b

/-- Coverage is faithfulness of the interpretation together with the residual. -/
theorem coverage_iff (b : SemanticBoundary) (i : RawSourceInterpretation)
    (decode : Request → Option SourceProgram) :
    CoverageObligations b i decode ↔ Faithful b i ∧ Residual b decode := by
  constructor
  · intro h
    refine ⟨⟨h.admitted, h.association, h.sourceFaithful, h.targetFaithful⟩, ?_, ?_, ?_, ?_,
      (normalCompatibility_iff b).mp h.normal, (returnCompatibility_iff b).mp h.returns⟩
    · intro r e
      obtain ⟨s, a⟩ := h.source r ((h.admitted r).mpr e)
      exact ⟨s, (h.decoder r s ((h.admitted r).mpr e)).mpr a⟩
    · intro r s e
      exact (h.decoder r s ((h.admitted r).mpr e)).trans (h.association r s)
    · intro r o after parts program e run
      exact h.allocation r o after parts program ((h.admitted r).mpr e) run
    · intro r o after parts program s e d run
      have p : b.relates s program ∧
          Nonempty (PassCorrect (i.source s).behaviour (i.target program).behaviour) :=
        h.pipeline r o after parts program s ((h.admitted r).mpr e) d run
      exact ⟨p.1, h.sourceFaithful s ▸ h.targetFaithful program ▸ p.2⟩
  · intro ⟨f, h⟩
    refine ⟨f.admitted, f.association, f.source, f.target, ?_, ?_, ?_, ?_,
      (normalCompatibility_iff b).mpr h.normal, (returnCompatibility_iff b).mpr h.returns⟩
    · intro r o after parts program e run
      exact h.allocation r o after parts program ((f.admitted r).mp e) run
    · intro r e
      obtain ⟨s, d⟩ := h.total r ((f.admitted r).mp e)
      exact ⟨s, (f.association r s).mpr ((h.decoder r s ((f.admitted r).mp e)).mp d)⟩
    · intro r s e
      exact (h.decoder r s ((f.admitted r).mp e)).trans (f.association r s).symm
    · intro r o after parts program s e d run
      have p : b.relates s program ∧ Nonempty (PassCorrect (b.reference.source s).behaviour
          (b.reference.target program).behaviour) :=
        h.pipeline r o after parts program s ((f.admitted r).mp e) d run
      exact ⟨p.1, (f.source s).symm ▸ (f.target program).symm ▸ p.2⟩

/-- **The contract, composed with e2d and e1**: at every boundary,
interpretation and decoder it is faithfulness and the residual. -/
theorem contract_iff (b : SemanticBoundary) (i : RawSourceInterpretation)
    (decode : Request → Option SourceProgram) :
    LowerLoopsCorrectContract b i decode ↔ Faithful b i ∧ Residual b decode :=
  (contract_iff_coverage b i decode).trans (coverage_iff b i decode)

/-- At the reference interpretation the contract is the residual. -/
theorem contract_reference_iff (b : SemanticBoundary) (decode : Request → Option SourceProgram) :
    LowerLoopsCorrectContract b b.reference decode ↔ Residual b decode :=
  (contract_iff b b.reference decode).trans ⟨fun h => h.2, fun h => ⟨Faithful.refl b, h⟩⟩

/-- An admitted request has one associated Source program: the decoded one. -/
theorem Residual.associated_unique {b : SemanticBoundary}
    {decode : Request → Option SourceProgram} (h : Residual b decode) {r : Request}
    {s s' : SourceProgram} (e : b.reference.entry r) (a : b.reference.associated r s)
    (a' : b.reference.associated r s') : s = s' :=
  Option.some.inj (((h.decoder r s e).mpr a).symm.trans ((h.decoder r s' e).mpr a'))

/-- The request's whole pipeline succeeds: lowering (for a callee, the callee
body pass) and then intrinsic elaboration and placement. -/
def Request.Succeeds (r : Request) : Prop :=
  ∃ o after parts program, r.pipeline o after parts program

/-- Every request whose whole pipeline succeeds is admitted. A lowering whose
elaboration or placement then fails is outside this statement. -/
def FullDomain (b : SemanticBoundary) : Prop :=
  ∀ r, r.Succeeds → b.reference.entry r

/-- A successful top-level run is in the relation; no admission is used. -/
theorem Request.lowers (r : Request) (o : ProductionOutput) (top : r.callee = none)
    (run : r.success o) :
    @LowersTo r.input.names r.input.returnSlots r.input.raw o.raw r.input.scope r.input.before
      o.after := by
  obtain ⟨C, input, callee⟩ := r
  cases top
  exact universalProducerCorrect input o run

/-- **Production correctness from the residual and `FullDomain`**: the only
premise on the request is its own successful pipeline. The `LowersTo` conjunct
is for top-level requests; for a callee only the semantic conjuncts are stated.
The pipeline premise runs the `partial` elaborator, so this cannot yet be
applied to a concrete run. -/
theorem production_correct {b : SemanticBoundary} {decode : Request → Option SourceProgram}
    (h : Residual b decode) (full : FullDomain b) (r : Request) (o : ProductionOutput)
    (after : Checker.Snapshot) (parts : SProg r.contract) (program : Blk r.contract r.context.ctx)
    (run : r.pipeline o after parts program) :
    (r.callee = none →
      @LowersTo r.input.names r.input.returnSlots r.input.raw o.raw r.input.scope r.input.before
        o.after) ∧
    (∃ scopes, b.allocations r o after parts program scopes ∧
      ∀ scope ∈ scopes, SafeSpellings r.input.names scope.protectedNames scope.generated) ∧
    ∃ s, decode r = some s ∧ b.reference.associated r s ∧ b.relates s program ∧
      Nonempty (PassCorrect (b.reference.source s).behaviour
        (b.reference.target program).behaviour) := by
  have e : b.reference.entry r := full r ⟨o, after, parts, program, run⟩
  obtain ⟨s, d⟩ := h.total r e
  exact ⟨fun top => r.lowers o top run.1, h.allocation r o after parts program e run,
    s, d, (h.decoder r s e).mp d, h.pipeline r o after parts program s e d run⟩

/-- Negative control: a boundary that admits nothing satisfies the residual at
every decoder once `relates` holds of the families. So the contract does not
exclude an empty admission by itself; `FullDomain` is a separate obligation. -/
theorem Residual.of_empty (b : SemanticBoundary) (decode : Request → Option SourceProgram)
    (empty : ∀ r, ¬ b.reference.entry r) (normal : RelatesNormalFamily b)
    (returns : RelatesReturnFamily b) : Residual b decode :=
  ⟨fun r e => absurd e (empty r), fun r _ e => absurd e (empty r),
    fun r _ _ _ _ e => absurd e (empty r), fun r _ _ _ _ _ e => absurd e (empty r),
    normal, returns⟩

end Solidity.Correctness.Lowering.Total
