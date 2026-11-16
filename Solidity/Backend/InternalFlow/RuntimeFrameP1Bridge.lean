import Solidity.Backend.InternalFlow.RuntimeFrameP1Lang
import Solidity.Backend.InternalFlow.RuntimeFrameV4TrivialFamily

/-! H68 family 3 (`p1_frame_bridge`) for the V4 trivial recursive family.

This is a type-inhabitation and plumbing check of the requested shape, not
evidence of P1 adequacy. The family is degenerate (its step ignores its
continuation: no recursion, empty body, never reverts or panics), the
observation is the coarse frame-boundary one of `P1Lang`, and the content of
the `PassCorrect` is only: the source is unfinished at depth 0 and succeeds at
every positive depth; the target always succeeds.

* Native context: the external approved family `approved`; `Approved` is the
  unchanged family agreement with the producer's admitted domain
  `V4TrivialFamily.domain` (no index or outcome filter; its provenance is not
  established). The languages are built from that domain, not from
  `approved`; the agreement is a pointwise iff, so this changes no membership.
* `beta := id` and `nu := fun _ _ => ()` follow from the joint `Input`
  environment and the `Unit` target resource. Neither is shown uniform with
  the single public G49 environment map, and the pass's `Input` environment
  does not match neighbouring G49 passes, so it folds only as a singleton.
* `Local` carries the actual V4 producer with this plan (not a restatement):
  universal return and bare-revert claims (the latter vacuous here), coverage,
  coherence, the successful witness and the agreement.

General families are not delivered: see `docs/feature-work/runtime-frame-p1.md`. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.P1Bridge
open Evm Evm.Memory P1Lang V4TrivialFamily
open Solidity.Roadmap (Event Outcome Prefix Lang Prefixes)
open Solidity.Roadmap.G49Final (BridgeGoal PassCorrect Behaviour)

/-- The admitted physical domain (index-free). -/
abbrev allowed : InterfaceV3.Admission P.C P.Γ := domain 0

theorem call_ok (σ : State P.C P.Γ) : ∃ out, call.run σ = .ok out := ⟨_, rfl⟩

theorem prefix_zero (e : Input P.C P.Γ) : sourceSem source e 0 = ⟨[], none⟩ := by
  simp only [sourceSem, source_zero, sourcePrefix]

theorem prefix_succ (e : Input P.C P.Γ) (n : Nat) :
    sourceSem source e (n + 1) = ⟨[], some (.success [])⟩ := by
  obtain ⟨out, h⟩ := call_ok e.caller
  simp only [sourceSem, source_succ, h, sourcePrefix]

theorem consistent (e : Input P.C P.Γ) : Prefixes.Consistent (sourceSem source e) := by
  intro r r' le
  cases r with
  | zero => rw [prefix_zero]; exact ⟨List.nil_prefix, .inl rfl⟩
  | succ r =>
    cases r' with
    | zero => omega
    | succ r' => rw [prefix_succ, prefix_succ]; exact Prefix.Le.refl _

/-- The canonical source language of the family. -/
def A : Lang Event Outcome := sourceLang source allowed consistent

/-- The canonical target language of the one emitted image. -/
def B : Lang Event Outcome := targetLang image.code allowed

/-- Every admitted input's target run returns: `ReturnClaim` at depth 1. -/
theorem target_ok (e : Input P.C P.Γ) (h : e.In allowed) :
    ∃ m, Evm.run image.code e.machine = .ok m 0 := by
  obtain ⟨out, run⟩ := call_ok e.caller
  have entry := coverage 1 e.L e.frame e.caller e.base e.machine e.start h
  obtain ⟨target, _, exec, _⟩ :=
    returns 1 e.L e.frame e.caller e.base e.machine e.start entry out ((source_succ 0 e.caller).trans run)
  exact ⟨target, exec⟩

theorem target_prefix (e : Input P.C P.Γ) (h : e.In allowed) :
    targetPrefix (Evm.run image.code e.machine) = ⟨[], some (.success [])⟩ := by
  obtain ⟨m, run⟩ := target_ok e h
  rw [run]
  rfl

/-- The entire original V4 conclusion: the actual producer, with this plan. -/
def Local (approved : Nat → InterfaceV3.Admission P.C P.Γ) : Prop :=
  Nonempty { p : InterfaceV4.PendingRecursiveReturns 0 F approved domain "trivial" .nil .none
      V3GeneralBoundary.trivialStep // p.plan = plan }

/-- The full refinement between the canonical languages. -/
def pass : PassCorrect (Behaviour.ofLang A ()) (Behaviour.ofLang B ()) where
  envAbs := id
  envSound := fun _ h => h
  envOnto := fun e h => ⟨e, h, rfl⟩
  need := fun _ _ => ()
  need_ok e r h _ := by
    refine ⟨⟨trivial, trivial, trivial⟩, ?_⟩
    change (sourceSem source e r).Le (targetPrefix (Evm.run image.code e.machine))
    rw [target_prefix e h]
    cases r with
    | zero => rw [prefix_zero]; exact ⟨List.nil_prefix, .inl rfl⟩
    | succ r => rw [prefix_succ]; exact Prefix.Le.refl _
  back e _ h _ _ := by
    refine ⟨(1 : Nat), trivial, trivial, ?_⟩
    change (targetPrefix (Evm.run image.code e.machine)).Le (sourceSem source e 1)
    rw [target_prefix e h, prefix_succ e 0]
    exact Prefix.Le.refl _

/-- H68 `p1_frame_bridge` for this family: the native context is the
external approved family, `Approved` its unchanged agreement. -/
def p1_frame_bridge (approved : Nat → InterfaceV3.Admission P.C P.Γ)
    (agreement : InterfaceV3.FamilyAdmissionAgreement approved domain) :
    BridgeGoal A B () () id (fun _ _ => ()) (Local approved) :=
  ⟨pass, rfl, rfl, ⟨⟨producer approved agreement, rfl⟩⟩⟩

/-- `BridgeGoal.pass`; it folds only as a singleton (its `Input` environment
matches no neighbouring G49 pass). -/
def fold_entry (approved : Nat → InterfaceV3.Admission P.C P.Γ)
    (agreement : InterfaceV3.FamilyAdmissionAgreement approved domain) :
    PassCorrect (Behaviour.ofLang A ()) (Behaviour.ofLang B ()) :=
  (p1_frame_bridge approved agreement).pass

/-! ## Controls -/

/-- Joint satisfiability (with `approved := domain`; not provenance). -/
theorem satisfiable : Nonempty (BridgeGoal A B () () id (fun _ _ => ()) (Local domain)) :=
  ⟨p1_frame_bridge domain fun _ _ _ _ _ _ _ => Iff.rfl⟩

/-- The source language is not success-only: depth 0 is unfinished. -/
theorem source_unfinished_at_zero (e : Input P.C P.Γ) : (sourceSem source e 0).final = none := by
  rw [prefix_zero]

/-- The populated caller is allowed in both languages. -/
theorem allowed_member : A.Allowed ⟨1, 16, caller0, P.base, machine0, 10⟩ ∧
    B.Allowed ⟨1, 16, caller0, P.base, machine0, 10⟩ := ⟨member, member⟩

/-- Panics are observed as completed reverts, not erased. -/
theorem panic_observed {Δ : Ctx} {H : HTy} :
    sourcePrefix (.error .panic : TRes (Solidity.Out P.C H Δ)) = ⟨[], some (.revert [])⟩ := rfl

/-- A pending jump is not a frame exit. -/
theorem pending_jump_unfinished (m : Machine) :
    (targetPrefix (.ok m 1)).final = none := rfl

/-- The producer's domain rejects a frame too small for its arena. -/
theorem refused_frame : ¬ B.Allowed ⟨1, 14, caller0, P.base, machine0, 10⟩ := wrong_frame

end Solidity.Backend.InternalFlow.RuntimeFrame.P1Bridge

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.P1Bridge.p1_frame_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.P1Bridge.p1_frame_bridge
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.P1Bridge.satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.P1Bridge.satisfiable
