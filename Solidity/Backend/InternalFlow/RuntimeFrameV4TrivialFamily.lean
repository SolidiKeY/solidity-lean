import Solidity.Backend.InternalFlow.RuntimeFrameV4Migration
import Solidity.Backend.InternalFlow.RuntimeFrameV3FixedThunkProducer

/-! A V4 recursive producer for a family that has no V3 producer.

The family is degenerate: `trivialStep` ignores its continuation, so no index
makes a recursive call and every positive index is the same empty-body call.
It shows that V4 admits a never-reverting family V3 rejects; it is not a
producer for a genuinely recursive never-reverting family.

The family is `V3GeneralBoundary.trivialStep` (empty body, no arguments, void
return) over the populated `CompileExamples` caller. Index 0 exhausts, every
positive index succeeds and no index bare-reverts, so V3 is empty for it
(`v3_empty`). Here the publicly selected void-call image
(`Mutation.compileCall`, `NoneProducer.plan`) serves every index: the return
claim is `NoneProducer.returns` at positive indices and vacuous at the
exhausted index 0; the bare-revert claim is vacuous at every index (the source
never bare-reverts), discharged via `NoneProducer.bare_revert`; coherence is derived from the
source; coverage is `V3FixedThunkProducer.coverage`; the successful witness is
a real admitted caller at index 1.

`producer` keeps the approved-domain agreement external, as V3 does.
`satisfiable` instantiates it with `approved := domain` only to show that the
V4 fields are jointly satisfiable; that is not approved-profile provenance. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.V4TrivialFamily
open Evm Evm.Memory V3GeneralBoundary

namespace P
abbrev C := V3FixedThunkProducer.Witness.P.C
abbrev Γ := V3FixedThunkProducer.Witness.P.Γ
abbrev base := V3FixedThunkProducer.Witness.P.base
end P
abbrev F := V3FixedThunkProducer.Witness.F
abbrev caller0 := V3FixedThunkProducer.Witness.caller0
abbrev machine0 := V3FixedThunkProducer.Witness.machine0
abbrev represented0 := V3FixedThunkProducer.Witness.represented0

def thunk (_ : Unit) : Prog P.C [] [] := .nil

def call : Stmt P.C P.Γ P.Γ := .call "trivial" .nil .none (thunk ())

def statement : Composition.Statement 0 F call :=
  (Mutation.compileCall 0 F "trivial" .nil .none (thunk ())).get
    (by first | rfl | decide | omega | decide +kernel)

def selected : Composition.Program 0 F (.cons call .nil) :=
  Composition.cons statement (Composition.nil 0 statement.checked.frag)

theorem room : 0 + selected.checked.need ≤ 8 := by
  first | rfl | decide | omega | decide +kernel

theorem nonallocating : selected.checked.allocates = false := by
  first | rfl | decide | omega | decide +kernel

/-- The one emitted image, the same at every index. -/
def image : InterfaceV1.Emission P.C P.Γ P.Γ := NoneProducer.plan selected 8 8

def plan : InterfaceV1.RecursiveEmission P.C P.Γ P.Γ :=
  ⟨image.code, fun _ => image.frag, fun _ => image.need, image.localLimit, image.pointerCell,
    fun _ => image.arenaWords, fun _ => image.heapCost⟩

theorem plan_at (n : Nat) : plan.at n = image := rfl

/-- Physical admission only: no source outcome, index or plan Entry. -/
def domain : Nat → InterfaceV3.Admission P.C P.Γ :=
  fun _ => V3FixedThunkProducer.admitted 0 F selected.checked.need 8 8

theorem no_index_filter (left right : Nat) : domain left = domain right := rfl

abbrev source (n : Nat) : Stmt P.C P.Γ P.Γ :=
  InterfaceV1.recursiveSource "trivial" .nil .none trivialStep n

theorem source_succ (n : Nat) (σ : State P.C P.Γ) : (source (n + 1)).run σ = call.run σ := rfl

theorem source_zero (σ : State P.C P.Γ) : (source 0).run σ = .error .exhausted := rfl

theorem coverage : InterfaceV3.FamilyEntryCoverage 0 F domain plan := fun _ =>
  V3FixedThunkProducer.coverage thunk selected 8 8 nonallocating

theorem returns (n : Nat) : InterfaceV1.ReturnClaim 0 F (source n) (plan.at n) := by
  intro L frame caller base machine start entry out run
  cases n with
  | zero => rw [source_zero] at run; exact nomatch run
  | succ n =>
    rw [source_succ] at run
    exact NoneProducer.returns selected 8 8 (NoneProducer.init_flags selected.checked.frag .refl)
      L frame caller base machine start entry out run

theorem bare_revert (n : Nat) : InterfaceV1.BareRevertClaim 0 F (source n) (plan.at n) := by
  intro L frame caller base machine start entry run
  cases n with
  | zero => rw [source_zero] at run; exact nomatch run
  | succ n =>
    rw [source_succ] at run
    exact NoneProducer.bare_revert selected 8 8 L frame caller base machine start entry run

theorem coherent :
    InterfaceV1.RecursiveReturnCoherence "trivial" (.nil : Args P.C P.Γ []) .none trivialStep := by
  intro caller n k left right hl hr
  cases n with
  | zero => change (source 0).run caller = _ at hl; rw [source_zero] at hl; exact nomatch hl
  | succ n =>
    cases k with
    | zero => change (source 0).run caller = _ at hr; rw [source_zero] at hr; exact nomatch hr
    | succ k =>
      change (source (n + 1)).run caller = _ at hl
      change (source (k + 1)).run caller = _ at hr
      rw [source_succ] at hl hr
      exact Except.ok.inj (hl.symm.trans hr)

theorem member : domain 1 1 16 caller0 P.base machine0 10 :=
  ⟨represented0, by decide, room, by decide, by decide, by decide, by decide,
    .inl (by decide), by decide, by rfl⟩

theorem source_one : ∃ out, (source 1).run caller0 = .ok out := ⟨_, rfl⟩

theorem successful : ∃ n, InterfaceV3.SuccessfulEntry 0 F (domain n) (source n) (plan.at n) := by
  obtain ⟨out, run⟩ := source_one
  exact ⟨1, 1, 16, caller0, P.base, machine0, 10, out, member,
    coverage 1 1 16 caller0 P.base machine0 10 member, run⟩

/-- The V4 producer; only the approved-domain agreement is external. -/
def producer (approved : Nat → InterfaceV3.Admission P.C P.Γ)
    (hprof : InterfaceV3.FamilyAdmissionAgreement approved domain) :
    InterfaceV4.PendingRecursiveReturns 0 F approved domain "trivial" .nil .none trivialStep where
  plan := plan
  required_profile := hprof
  required_coverage := coverage
  required_successful_entry := successful
  required_source_coherence := coherent
  required_return := returns
  required_bare_revert := bare_revert

/-- Joint satisfiability of every V4 field (not approved-profile provenance). -/
theorem satisfiable :
    Nonempty (InterfaceV4.PendingRecursiveReturns 0 F domain domain "trivial" .nil .none
      trivialStep) :=
  ⟨producer domain fun _ _ _ _ _ _ _ => Iff.rfl⟩

/-! ## Negative controls -/

/-- V3 is empty for this family at the same domain: V4 strictly extends it. -/
theorem v3_empty (approved : Nat → InterfaceV3.Admission P.C P.Γ) :
    ¬ Nonempty (InterfaceV3.PendingRecursiveReturns 0 F approved domain "trivial" .nil .none
      trivialStep) :=
  no_recursive_producer (trivial_never_reverts "trivial")

/-- The always-exhausting family stays empty under V4 (at every domain; shown
here at this one). It is a different family and does not test `producer`. -/
theorem exhausting_empty (approved : Nat → InterfaceV3.Admission P.C P.Γ) :
    ¬ Nonempty (InterfaceV4.PendingRecursiveReturns 0 F approved domain "trivial" .nil .none
      V4Migration.exhaustingStep) :=
  V4Migration.exhausting_empty 0 F approved domain "trivial"

/-- Index 0 is admitted and has an Entry, yet exhausts: coverage is not success. -/
theorem exhausted_is_covered :
    domain 0 1 16 caller0 P.base machine0 10 ∧
    InterfaceV1.Entry (plan.at 0) 1 0 16 F caller0 P.base machine0 10 ∧
    (source 0).run caller0 = .error .exhausted :=
  ⟨member, coverage 0 1 16 caller0 P.base machine0 10 member, source_zero caller0⟩

/-- A changed frame is refused by the physical domain (as the V3
`insufficient_frame_refused`; not specific to V4). -/
theorem wrong_frame : ¬ domain 1 1 14 caller0 P.base machine0 10 := by
  intro h
  have := h.2.2.2.2.2.2.1
  simp only [P.Γ, Solidity.Evm.Memory.CompileExamples.Γ, List.length_cons, List.length_nil] at this
  omega

end Solidity.Backend.InternalFlow.RuntimeFrame.V4TrivialFamily

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.V4TrivialFamily.producer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V4TrivialFamily.producer
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.V4TrivialFamily.satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V4TrivialFamily.satisfiable
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.V4TrivialFamily.v3_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V4TrivialFamily.v3_empty
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.V4TrivialFamily.exhausting_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V4TrivialFamily.exhausting_empty
