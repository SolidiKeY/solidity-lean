import SolidityBridge.WeakestPre
import Solidity.Calculus.Sound
import Solidity.Calculus.CloseLemmas
import Solidity.Syntax.Elab

/-!
The actual box reading rejects panic. The closer's `Modality.wp` is a
separate, simpler helper: it treats every error as `onHalt`. Both are
analysed here; preservation of top for that helper must not be transferred
to the actual box.
-/
namespace Solidity.Bridge

variable {α β γ : Type}

theorem wp_inf (m : Modality) (run : α → TRes β) (p q : Set β) :
    wp m run (p ⊓ q) = wp m run p ⊓ wp m run q := by
  ext s
  cases h : run s <;>
    simp only [wp, Set.mem_setOf_eq, Set.inf_eq_inter, Set.mem_inter_iff, Modality.afterRunTR, h,
      ne_eq, reduceCtorEq, not_false_eq_true, and_true, and_self, iff_self]

/-- Sequencing of arbitrary result-valued functions uses the actual halt policy. -/
theorem wp_comp (m : Modality) (run : α → TRes β) (next : β → TRes γ) (q : Set γ) :
    wp m (fun s => run s >>= next) q = wp m run (wp m next q) := by
  ext s
  cases h : run s <;>
    simp only [wp, Set.mem_setOf_eq, h, bind, Except.bind, Modality.afterRunTR,
      Except.error.injEq, ne_eq, reduceCtorEq, not_false_eq_true, and_true, iff_self]

/-- This classifies precisely why the requested unconditional top law fails. -/
theorem wp_box_top_iff (run : α → TRes β) :
    wp .box run ⊤ = ⊤ ↔ ∀ s, run s ≠ .error .panic := by
  simp only [Set.top_eq_univ, wp_box_univ, Set.eq_univ_iff_forall, Set.mem_setOf_eq]

/-- Predicate transformer of a real typed step, observing its returned state. -/
def stepWp {C : Contract} {Γ Δ : Ctx} (m : Modality) (run : TStep C Γ Δ)
    (q : Set (State C Δ)) : Set (State C Γ) :=
  wp m (fun σ => (run σ).map Out.st) q

theorem stepWp_mono {C : Contract} {Γ Δ : Ctx} (m : Modality) (run : TStep C Γ Δ) :
    Monotone (stepWp m run) := wp_mono m _

theorem stepWp_inf {C : Contract} {Γ Δ : Ctx} (m : Modality) (run : TStep C Γ Δ)
    (p q : Set (State C Δ)) :
    stepWp m run (p ⊓ q) = stepWp m run p ⊓ stepWp m run q := wp_inf m _ p q

/-- The real sequencing function retains heap-extension evidence internally. -/
theorem stepWp_seq {C : Contract} {Γ Δ Ε : Ctx} (m : Modality)
    (first : TStep C Γ Δ) (next : TStep C Δ Ε) (q : Set (State C Ε)) :
    stepWp m (TRun.seq first next) q = stepWp m first (stepWp m next q) := by
  ext σ
  cases h : first σ with
  | error e =>
    simp only [stepWp, wp, Set.mem_setOf_eq, TRun.seq, h, Except.map,
      Modality.afterRunTR, ne_eq, Except.error.injEq, iff_self]
  | ok o =>
    cases hn : next o.st <;>
      simp only [stepWp, wp, Set.mem_setOf_eq, TRun.seq, h, hn, Except.map,
        Modality.afterRunTR, ne_eq, reduceCtorEq, not_false_eq_true, and_true, iff_self]

/-- In particular, the core program cons constructor composes transformers. -/
theorem stepWp_prog_cons {C : Contract} {Γ Δ Ε : Ctx} (m : Modality)
    (first : Stmt C Γ Δ) (next : Prog C Δ Ε) (q : Set (State C Ε)) :
    stepWp m (fun σ => Prog.run σ (.cons first next)) q =
      stepWp m first.run (stepWp m (fun σ => Prog.run σ next) q) :=
  stepWp_seq m first.run (fun σ => Prog.run σ next) q

/-- Formula validity is the top element of the same predicate lattice. -/
theorem valid_modal_iff_wp_top {C : Contract} {Δ Ε : Ctx} (m : Modality)
    (P : Prog C [] Δ) (κ : Frames C Δ Ε) (φ : Fml C Ε) :
    Fml.Valid (.modal m P κ φ) ↔
      wp m (fun σ => Prog.runFrames σ P κ) {σ | holds σ φ} = ⊤ := by
  rw [Set.top_eq_univ, Set.eq_univ_iff_forall]
  rfl

theorem proves_modal_wp_top {C : Contract} {R : RuleSet} {Δ Ε : Ctx} (m : Modality)
    (P : Prog C [] Δ) (κ : Frames C Δ Ε) (φ : Fml C Ε)
    (d : Proves C R [] .nil (.modal m P κ φ)) :
    wp m (fun σ => Prog.runFrames σ P κ) {σ | holds σ φ} = ⊤ :=
  (valid_modal_iff_wp_top m P κ φ).mp d.fmlValid

/-- This direct connection uses Proves.valid at its actual Spec type. -/
theorem proves_spec_box_wp_top {C : Contract} {R : RuleSet} {Δ : Ctx}
    (P : Prog C [] Δ) (φ : Spec C Δ)
    (d : Proves C R [] .nil (Spec.box P φ).toFml) :
    wp .box (fun σ => Prog.runFrames σ P .nil) {σ | holds σ φ.toFml} = ⊤ :=
  (valid_modal_iff_wp_top .box P .nil φ.toFml).mp
    ((Spec.valid_iff (.box P φ)).mp d.valid)

/-! The closer's simpler wp helper, without the actual box's panic check. -/

def rawWp (m : Modality) (run : α → TRes β) (q : Set β) : Set α :=
  {s | m.wp (run s) (· ∈ q)}

theorem rawWp_mono (m : Modality) (run : α → TRes β) : Monotone (rawWp m run) := by
  intro p q hpq s hs
  cases h : run s with
  | ok v =>
    simp only [rawWp, Set.mem_setOf_eq, Modality.wp, h] at hs ⊢
    exact hpq hs
  | error e => simpa only [rawWp, Set.mem_setOf_eq, Modality.wp, h] using hs

def rawWpOrderHom (m : Modality) (run : α → TRes β) : Set β →o Set α :=
  ⟨rawWp m run, rawWp_mono m run⟩

theorem rawWp_inf (m : Modality) (run : α → TRes β) (p q : Set β) :
    rawWp m run (p ⊓ q) = rawWp m run p ⊓ rawWp m run q := by
  ext s
  cases h : run s <;>
    simp only [rawWp, Set.mem_setOf_eq, Set.inf_eq_inter, Set.mem_inter_iff, Modality.wp, h, and_self, iff_self]

theorem rawWp_box_top (run : α → TRes β) : rawWp .box run ⊤ = ⊤ := by
  ext s
  cases h : run s <;>
    simp only [rawWp, Set.mem_setOf_eq, Modality.wp, h, Modality.onHalt,
      Set.top_eq_univ, Set.mem_univ]

theorem rawWp_comp (m : Modality) (run : α → TRes β) (next : β → TRes γ) (q : Set γ) :
    rawWp m (fun s => run s >>= next) q = rawWp m run (rawWp m next q) := by
  ext s
  exact Modality.wp_bind

/-- Exact relation between the two core readings, including both exceptional boundaries. -/
theorem wp_eq_rawWp (m : Modality) (run : α → TRes β) (q : Set β) :
    wp m run q = {s | (s ∈ rawWp m run q ∨ run s = .error .exhausted) ∧
      run s ≠ .error .panic} := by
  ext s
  cases h : run s with
  | ok v =>
    simp only [wp, rawWp, Set.mem_setOf_eq, h, Modality.afterRunTR, Modality.wp,
      reduceCtorEq, ne_eq, not_false_eq_true, and_true, or_false]
  | error e =>
    cases m <;> cases e <;>
      simp only [wp, rawWp, Set.mem_setOf_eq, h, Modality.afterRunTR, Modality.wp,
        Modality.onHalt, Modality.onTHalt, Except.error.injEq, reduceCtorEq,
        ne_eq, not_false_eq_true, not_true_eq_false, and_true,
        true_or, false_or, and_false, or_self, and_self, iff_self]

/-- Minimal nonempty counterexample: actual box of top rejects panic. -/
example : wp .box (fun _ : Unit => (.error .panic : TRes Unit)) ⊤ ≠ ⊤ := by
  intro h
  have ht : () ∈ wp .box (fun _ : Unit => (.error .panic : TRes Unit)) ⊤ := by
    rw [h]
    trivial
  exact ht.2 rfl

/-- The same failure is exhibited by an actual, closed Solidity program. -/
theorem assert_false_box_not_valid :
    ¬ Fml.Valid (Fml.modal .box (sol[StandardExample]{ assert(false); }) .nil .tt) := by
  intro h
  exact (h (State.init StandardExample)).2 rfl

example : ¬ Fml.Valid (Fml.modal .box (sol[StandardExample]{ assert(false); }) .nil .tt) :=
  assert_false_box_not_valid

end Solidity.Bridge

#print axioms Solidity.Bridge.wp_mono
#print axioms Solidity.Bridge.wp_inf
#print axioms Solidity.Bridge.wp_comp
#print axioms Solidity.Bridge.wp_box_top_iff
#print axioms Solidity.Bridge.stepWp_mono
#print axioms Solidity.Bridge.stepWp_inf
#print axioms Solidity.Bridge.stepWp_seq
#print axioms Solidity.Bridge.stepWp_prog_cons
#print axioms Solidity.Bridge.valid_modal_iff_wp_top
#print axioms Solidity.Bridge.proves_modal_wp_top
#print axioms Solidity.Bridge.proves_spec_box_wp_top
#print axioms Solidity.Bridge.rawWp_mono
#print axioms Solidity.Bridge.rawWp_inf
#print axioms Solidity.Bridge.rawWp_box_top
#print axioms Solidity.Bridge.rawWp_comp
#print axioms Solidity.Bridge.assert_false_box_not_valid

#print axioms Solidity.Bridge.wp_eq_rawWp
