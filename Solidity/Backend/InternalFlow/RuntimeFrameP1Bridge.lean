import Solidity.Backend.InternalFlow.RuntimeFrameP1Lang
import Solidity.Backend.InternalFlow.RuntimeFrameV4TrivialFamily

/-! H68 family 3 (`p1_frame_bridge`) for the V4 trivial recursive family.

Native context: the external approved family `approved`; `Approved` is the
unchanged V3/V4 family agreement with the admitted physical domain
`V4TrivialFamily.domain`, which has no index or outcome filter. The canonical
languages are `P1Lang.sourceLang`/`targetLang` of the actual family
`V4TrivialFamily.source` and the actual emitted image
`V4TrivialFamily.image.code`, with prescribed `beta := id` and
`nu := fun _ _ => ()`. `Local` is the entire V4 producer conclusion: the
universal return and bare-revert claims, universal family coverage, source
coherence, the admitted successful witness and the agreement itself.

Every `PassCorrect` field is proved: forward at every depth (the exhausted
depth 0 is an unfinished prefix below the target's), backward for every
target prefix (the target always succeeds, as `ReturnClaim` at depth 1 shows
for every admitted input). Nothing is assumed beyond the agreement.

Scope: this is the bridge for one degenerate family whose outcomes are all
known (success at positive depth, exhaustion at 0, never a revert or panic).
A bridge for general P1 families needs, per family, depth consistency of the
source language and backward transport of EVERY target outcome, i.e. the
panic/payload/exhaustion/divergence transports of G37.02/G38. -/
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

/-- The entire original V4 conclusion for this family and agreement. -/
def Local (approved : Nat → InterfaceV3.Admission P.C P.Γ) : Prop :=
  InterfaceV3.FamilyAdmissionAgreement approved domain ∧
  InterfaceV3.FamilyEntryCoverage 0 F domain plan ∧
  (∃ n, InterfaceV3.SuccessfulEntry 0 F (domain n) (source n) (plan.at n)) ∧
  InterfaceV1.RecursiveReturnCoherence "trivial" (.nil : Args P.C P.Γ []) .none
    V3GeneralBoundary.trivialStep ∧
  (∀ n, InterfaceV1.ReturnClaim 0 F (source n) (plan.at n)) ∧
  (∀ n, InterfaceV1.BareRevertClaim 0 F (source n) (plan.at n))

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
  ⟨pass, rfl, rfl, agreement, coverage, successful, coherent, returns, bare_revert⟩

/-- The bridge enters the G49 fold as an ordinary pass. -/
def fold_entry (approved : Nat → InterfaceV3.Admission P.C P.Γ)
    (agreement : InterfaceV3.FamilyAdmissionAgreement approved domain) :
    PassCorrect (Behaviour.ofLang A ()) (Behaviour.ofLang B ()) :=
  (p1_frame_bridge approved agreement).pass

/-! ## Controls -/

/-- The bridge is inhabited (with `approved := domain`; not provenance). -/
theorem inhabited : Nonempty (BridgeGoal A B () () id (fun _ _ => ()) (Local domain)) :=
  ⟨p1_frame_bridge domain fun _ _ _ _ _ _ _ => Iff.rfl⟩

/-- The source language is not success-only: depth 0 is unfinished. -/
theorem source_unfinished_at_zero (e : Input P.C P.Γ) : (sourceSem source e 0).final = none := by
  rw [prefix_zero]

/-- The populated caller is allowed in both languages. -/
theorem allowed_member : A.Allowed ⟨1, 16, caller0, P.base, machine0, 10⟩ := member

/-- A narrowed frame is not allowed: the domain is the physical one. -/
theorem refused_frame : ¬ B.Allowed ⟨1, 14, caller0, P.base, machine0, 10⟩ := wrong_frame

end Solidity.Backend.InternalFlow.RuntimeFrame.P1Bridge

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.P1Bridge.p1_frame_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.P1Bridge.p1_frame_bridge
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.P1Bridge.inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.P1Bridge.inhabited
