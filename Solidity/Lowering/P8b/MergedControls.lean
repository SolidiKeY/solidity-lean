import Solidity.Lowering.P8.PlanWitness
import Solidity.Lowering.P8.ResourceContractLaw1
import Solidity.Lowering.P8b.Merged

/-!
# Witness and negative controls for the merged Producer (H57, H60)

Positive: the merged Producer is inhabited by `planProducer` and
`planLowering` (`P8/PlanWitness.lean`); its frontend issues a checked receipt
for a concrete input, the realization runs a concrete program under the
model reference, a failing plan really reverts, and the P8b certificate
carries a concrete source success to the lowered program.

Negative: G07's original toy source (resources in `Nat`) admits no failure
projection, hence no frozen Producer (P8-SPEC-LAW1); a wrong reference admits
no realization; a source admitting nothing admits no Producer; a wrong
emitter admits no P8b certificate. These show the witness is not obtained by
weakening any field.
-/
namespace Solidity.Lowering.P8b.MergedControls
open Solidity.Roadmap Solidity.Roadmap.Controls Solidity.Lowering.P8 P8a PlanWitness

/-! ## Witness controls -/

/-- **The merged Producer is inhabited.** -/
def planMerged :
    Merged.Producer planSource planReference planOrigins planRoots planIntrinsic :=
  Merged.Producer.ofPair planProducer ⟨planLowering⟩

theorem merged_inhabited :
    Nonempty (Merged.Producer planSource planReference planOrigins planRoots planIntrinsic) :=
  ⟨planMerged⟩

/-- The concrete input `3 1` (succeed with `[1]`, hashing nothing). -/
def quietInput : ToyInput := { text := [3, 1] }

def quietResolved : ToyRes := ⟨.quiet [1], .legacy, .v2⟩

/-- The frozen admission accepts it, with exactly its resolution. -/
theorem quiet_admitted : planMerged.toP8a.admission.frontend quietInput = some quietResolved :=
  rfl

/-- A checked frontend receipt (the frozen P8b `CertifiedInput`) at the
merged producer: the certificate is checked by `check` in the kernel. -/
def quietReceipt : Merged.CertifiedInput planMerged quietInput where
  resolved := quietResolved
  certificate := Toy.quiet [1]
  produced := rfl

theorem quiet_receipt_checks :
    planMerged.toP8a.checkedFrontend.check quietInput quietReceipt.resolved
      quietReceipt.certificate = true := by decide

/-- Malformed text is refused by the same frontend. -/
theorem bad_tag_refused : planMerged.toP8a.admission.frontend { text := [4] } = none := rfl

/-- The realization maps the admitted meaning to an actual intrinsic Source
program, which the model reference executes to the source's success. -/
theorem quiet_executes :
    planReference.Executes
      (planMerged.toP8a.realization.program (.quiet [1])) quietEnv ⟨0, quietPlan⟩
      ⟨[], some (.success [1])⟩ := rfl

/-- A plan with a failure point at the first frame reverts the same program:
the plan in the resource is read by the semantics, not ignored. -/
def failingPlan : Evm.FailurePoints := ⟨fun _ => .runs 0 none, fun k => if k = 0 then some 0 else none⟩

theorem failing_plan_reverts :
    (planSource.lang.sem (.quiet [1]) quietEnv ⟨0, failingPlan⟩).final = some (.revert []) := rfl

theorem failing_plan_not_noFail : ¬ planSource.NoFail failingPlan := fun h => by
  have := h.2 0
  simp only [failingPlan, if_true, reduceCtorEq] at this

/-- The failure projection covers every EVM plan, including the failing one. -/
theorem covers_failing_plan :
    planMerged.toP8a.failures.points (planMerged.toP8a.failures.ofPoints failingPlan) = failingPlan :=
  rfl

/-- The P8b certificate of the merged producer carries the concrete source
success of `3 1` to the lowered program. -/
theorem lowered_success : ∃ rt, planIntrinsic.lang.Admissible rt ∧
    (planIntrinsic.lang.sem (.quiet [1]) quietEnv rt).final = some (.success [1]) := by
  obtain ⟨rt, ha, ho, _⟩ := (planMerged.toLowering.cert.refines (.quiet [1])
    (planMerged.toLowering.dom quietResolved trivial trivial ⟨[], 0⟩) quietEnv quietEnv_allowed).completes
      trivial (plan_forward (.quiet [1]) quietEnv 0).1 (plan_forward (.quiet [1]) quietEnv 0).2 rfl
  exact ⟨rt, ha, ho⟩

/-! ## Negative controls -/

/-- G07's original toy source has `Nat`-encodable resources, so P8-SPEC-LAW1
refutes every failure projection for it: the obstruction the witness avoids
is real, and the frozen contract still enforces it. -/
theorem toySource_no_projection : ¬ Nonempty (FailureProjection toySource) := by
  rintro ⟨F⟩
  apply ResourceContractLaw1.nat_encodable_resource_impossible toySource F
    (fun r => 2 * r.horizon + (if r.exhausted then 1 else 0))
    (fun n => ⟨n / 2, n % 2 == 1⟩)
  intro r
  rcases r with ⟨h, b⟩
  cases b
  · show (⟨(2 * h + 0) / 2, (2 * h + 0) % 2 == 1⟩ : Bound) = ⟨h, false⟩
    have h1 : (2 * h + 0) / 2 = h := by omega
    have h2 : (2 * h + 0) % 2 = 0 := by omega
    rw [h1, h2]
    rfl
  · show (⟨(2 * h + 1) / 2, (2 * h + 1) % 2 == 1⟩ : Bound) = ⟨h, true⟩
    have h1 : (2 * h + 1) / 2 = h := by omega
    have h2 : (2 * h + 1) % 2 = 1 := by omega
    rw [h1, h2]
    rfl

theorem toySource_no_producer (reference : OperationalReference)
    (origins : SourceOrigins toySource) (roots : RootModel toySource) :
    ¬ Nonempty (Producer toySource reference origins roots) :=
  fun ⟨p⟩ => toySource_no_projection ⟨p.failures⟩

/-- A reference that always reports success admits no realization: `exact`
is checked against the source's revert. -/
def alwaysSucceeds : OperationalReference where
  Resource := PlanBound
  points := PlanBound.plan
  Executes := fun _ _ _ out => out = ⟨[], some (.success [1])⟩

theorem wrong_reference_no_realization :
    ¬ Nonempty (SourceRealization alwaysSucceeds planOrigins planFailures) := by
  rintro ⟨R⟩
  have h := (R.exact (.fail [7]) quietEnv ⟨0, quietPlan⟩ _).2 rfl
  have h3 : (some (Outcome.revert [7]) : Option Outcome) = some (.success [1]) :=
    congrArg Prefix.final h
  cases h3

/-- A reference that ignores the plan (always the unexhausted run) admits no
realization: `exact` is checked at the failing plan. -/
def ignoresPlan : OperationalReference where
  Resource := PlanBound
  points := PlanBound.plan
  Executes := fun sp _ _ out => Toy.run (decode (bytesOf sp.2.main)) false = out

theorem plan_ignoring_reference_no_realization :
    ¬ Nonempty (SourceRealization ignoresPlan planOrigins planFailures) := by
  rintro ⟨R⟩
  have h1 := (R.exact (.quiet [1]) quietEnv ⟨0, quietPlan⟩ _).2 rfl
  have h2 := (R.exact (.quiet [1]) quietEnv ⟨0, failingPlan⟩ _).2 rfl
  have h3 : (some (Outcome.success [1]) : Option Outcome) = some (.revert []) :=
    congrArg Prefix.final (h1.symm.trans h2)
  cases h3

/-- A source that parses nothing is vacuous, so it admits no Producer. -/
def emptyPlanSource : SourceSpec := { planSource with Parses := fun _ _ => False }

theorem empty_no_producer (reference : OperationalReference)
    (origins : SourceOrigins emptyPlanSource) (roots : RootModel emptyPlanSource) :
    ¬ Nonempty (Producer emptyPlanSource reference origins roots) :=
  fun ⟨p⟩ => SourceSpec.not_nonVacuous_of_no_parse (fun _ _ h => h) p.nonVacuous

/-- A wrong emitter (every program fails) admits no P8b certificate. -/
def badEmit : planSource.lang.Prog → planIntrinsic.World := fun _ => .fail []

theorem bad_emit_no_certificate :
    ¬ Nonempty (Cert (P8b.pass planSource planIntrinsic badEmit)) := by
  apply P8b.no_certificate_of_wrong_completion planSource planIntrinsic badEmit
    quietResolved trivial trivial ⟨[], 0⟩ quietEnv ⟨0, quietPlan⟩ quietEnv_allowed trivial
    (plan_forward (.quiet [1]) quietEnv 0).1 (plan_forward (.quiet [1]) quietEnv 0).2
    (.success [1]) rfl
  intro rt _
  show (Toy.run (.fail []) rt.exhausted).final ≠ _
  cases rt.exhausted <;> intro h <;> cases h

/-- info: 'Solidity.Lowering.P8b.MergedControls.merged_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms merged_inhabited
/-- info: 'Solidity.Lowering.P8b.MergedControls.toySource_no_producer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms toySource_no_producer
/-- info: 'Solidity.Lowering.P8b.MergedControls.wrong_reference_no_realization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_reference_no_realization
/-- info: 'Solidity.Lowering.P8b.MergedControls.plan_ignoring_reference_no_realization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms plan_ignoring_reference_no_realization

end Solidity.Lowering.P8b.MergedControls
