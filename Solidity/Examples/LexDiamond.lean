import Solidity.Calculus.Sound.LoopLexDiamond
import Solidity.Examples.LexMetrics

/-!
# Local lexicographic diamond VC regressions

The prospective rule retains the source tuple, leaves break/quantified clauses
pending, and proves only the ordinary modality. Its stronger final-turn
decrease requirement is tested separately from successful termination.
-/
namespace Solidity.Examples.LexDiamond

open LoopLex
open Examples.Termination

private def yes : Val C Γ .bool := .simple (.bool true)
private def constants : LoopMetrics C Γ 2 :=
  .cons (.simple (.lit 0 (by decide))) (.cons (.simple (.lit 0 (by decide))) .nil)
private def zeroes : UIntTuple 2 :=
  (PrimTy.ofLit .uint 0 (by decide), PrimTy.ofLit .uint 0 (by decide), ())

theorem break_pending (k : Nat) (body : Prog C Γ Δ) (frame) :
    diamondStep k yes yes constants true [] body frame = .done false := rfl

theorem quantified_pending (k : Nat) (body : Prog C Γ Δ) (frame) :
    diamondStep k yes yes constants false [.all (.user "q") .uint (.val yes)] body frame =
      .done false := rfl

theorem missing_frame_pending (k : Nat) (body : Prog C Γ Δ) :
    diamondStep k yes yes constants false [] body none = .done false := rfl

/-- The generated initial VC cannot pass an undefined component. -/
theorem undefined_head_vc_rejected (σ : State Flags FlagCtx) (k : Nat) :
    ¬ holds σ ((diamondPremise k yes yes Examples.LexMetrics.undefinedMetrics
      (.nil : Prog Flags FlagCtx FlagCtx) [] (some [])).fml .diamond .nil .nil .tt) := by
  intro h
  have hY := h.2 (fun x => TEnv.get x.2 σ.env) rfl
  have hfail : ((snapshot k Examples.LexMetrics.undefinedMetrics).decl
      (fse (k + 2)) (.val (yes : Val Flags FlagCtx .bool).lower)).globT
      (σ.anon [] (fun x => TEnv.get x.2 σ.env)) = none := by
    change ((snapshot k Examples.LexMetrics.undefinedMetrics).globT
      (σ.anon [] (fun x => TEnv.get x.2 σ.env))).bind (fun g => some g) = none
    rw [snapshot_fails_of_undefined _ _ _ (e := .revert) rfl]
    rfl
  have hfree : ((snapshot k Examples.LexMetrics.undefinedMetrics).decl
      (fse (k + 2)) (.val (yes : Val Flags FlagCtx .bool).lower)).pushFree = true := by
    simp only [Upd.pushFree, snapshot_pushFree, Rhs.pushFree, Val.lower_pushFree, Bool.and_self]
  exact hY.of_noExh hfail (Upd.exh_of_pushFree hfree)

/-- The existing source phase loop uses the new bridge with its exact tuple. -/
theorem source_phase_rule (k : Nat) (σ : State Flags FlagCtx) :
    Premise.Runs .diamond
      (.loop (.invLex yes Examples.LexMetrics.metrics false []) guard body)
      (diamondStep k yes guard Examples.LexMetrics.metrics false [] body body.frame) σ :=
  diamondStep_sound k yes guard Examples.LexMetrics.metrics false [] body σ

/-- The printed old/new capture ranges do not overlap. -/
example : (snapshot (C := Flags) (Γ := FlagCtx) 0 constants).names [] =
    [.fresh "variant" 0, .fresh "variant" 1] := rfl
example : (snapshot 3 ((constants : LoopMetrics Flags FlagCtx 2).wk
    (.ofExt (savedExt FlagCtx 2)))).names [.fresh "variant" 0, .fresh "variant" 1] =
    [.fresh "variant" 3, .fresh "variant" 4, .fresh "variant" 0, .fresh "variant" 1] := rfl

private theorem after_capture {U : Upd C Γ Δ} {σ : State C Γ} {g : GlobT C σ.H}
    {τ : State C Δ} {p : State C Δ → Prop} (hL : U.Lands σ g τ) (hp : p τ) :
    U.afterT .diamond σ p :=
  Upd.afterT_intro
    (fun hnone => by rw [hL.1] at hnone; cases hnone)
    (fun _ τ' hL' => (hL'.eq hL).symm ▸ hp)

/-- A successful source-shaped reset checks the full generated postcondition,
using its actual typed body and exact declared metrics. -/
theorem source_phase_post (σ : State Flags FlagCtx) (k : Nat) (before : UIntTuple 2)
    (hbefore : readMetrics σ Examples.LexMetrics.metrics = some before)
    (hc : guard.evalT σ = .ok true) :
    holds (saveState (next σ) before) (diamondPost k yes Examples.LexMetrics.metrics) := by
  constructor
  · rfl
  · have hev := metrics_eval_saved (next σ) Examples.LexMetrics.metrics before
    rw [Examples.LexMetrics.metrics_eval] at hev
    obtain ⟨savedAfter, hs, hseq⟩ := readMetrics_of_eval (saveState (next σ) before)
      (Examples.LexMetrics.metrics.wk (.ofExt (savedExt FlagCtx 2))) hev
    change (snapshot (k + 2 + 1) (Examples.LexMetrics.metrics.wk
      (.ofExt (savedExt FlagCtx 2)))).afterT .diamond (saveState (next σ) before) _
    refine after_capture (p := fun st => holds st _) (snapshot_lands _ _ _ savedAfter hs) ?_
    apply (snapshotsDecrease_holds (next σ) before savedAfter).2
    have hdecrease := Examples.LexMetrics.phase_certificate.decreases σ
      ⟨next σ, List.prefix_refl _⟩ before.toNat savedAfter.toNat trivial hc
      (body_run σ) (eval_of_readMetrics σ _ before hbefore)
    apply hdecrease
    change LoopMetrics.eval (next σ) Examples.LexMetrics.metrics = _
    rw [Examples.LexMetrics.metrics_eval, hseq]

/-- A constant tuple cannot establish the generated postcondition. This also
explains why a return-flag turn that leaves the tuple unchanged remains pending
under this conservative rule, even when it makes the guard false. -/
theorem unchanged_final_turn_rejected (σ : State C Γ) (k : Nat) :
    ¬ holds (saveState σ zeroes) (diamondPost k yes constants) := by
  intro h
  have hdec := h.2.of_lands (snapshot_lands (saveState σ zeroes) (k + 2 + 1)
    ((constants : LoopMetrics C Γ 2).wk (.ofExt (savedExt Γ 2))) zeroes rfl)
  have hlt := (snapshotsDecrease_holds σ zeroes zeroes).1 hdec
  exact LoopMetrics.NatTuple.irrefl _ hlt

/-- This is a genuine generated VC that closes for an exhausting body even
with a false postcondition. Ordinary diamonds deliberately accept exhaustion. -/
theorem exhausting_vc (σ : State C Γ) (k : Nat) :
    holds σ ((diamondPremise k yes yes constants
      (.cons .assumeFalse (.nil : Prog C Γ Γ)) [] (some [])).fml .diamond .nil .nil .ff) := by
  constructor
  · rfl
  · intro bindings hI
    let τ := σ.anon [] bindings
    have hL := Upd.lands_decl (snapshot_lands τ k constants zeroes rfl)
      (fse (k + 2)) (r := Rhs.val (yes : Val C Γ .bool).lower) (v := true) rfl
    change ((snapshot k constants).decl (fse (k + 2)) (.val (yes : Val C Γ .bool).lower)).afterT .diamond τ _
    refine after_capture (p := fun st => holds st _) hL ?_
    constructor
    · intro _
      change (Upd.nil.pop (.push .refl)).afterT .diamond _ _
      refine after_capture (p := fun st => holds st _)
        (Upd.lands_pop_nil (.push .refl) ((saveState τ zeroes).push (t := .val .bool) true)) ?_
      exact ⟨rfl, nofun⟩
    · intro hfalse
      have h := (holds_eq_pvV_lit _ _ _).1 hfalse
      cases h

/-- A non-exhausting VC closes for a loop whose condition is already false. -/
theorem exiting_vc (σ : State C Γ) (k : Nat) :
    holds σ ((diamondPremise k yes (.simple (.bool false)) constants
      (.nil : Prog C Γ Γ) [] (some [])).fml .diamond .nil .nil .tt) := by
  constructor
  · rfl
  · intro bindings hI
    let τ := σ.anon [] bindings
    have hL := Upd.lands_decl (snapshot_lands τ k constants zeroes rfl)
      (fse (k + 2)) (r := Rhs.val (Val.simple (.bool false) : Val C Γ .bool).lower)
      (v := false) rfl
    change ((snapshot k constants).decl (fse (k + 2))
      (.val (Val.simple (.bool false) : Val C Γ .bool).lower)).afterT .diamond τ _
    refine after_capture (p := fun st => holds st _) hL ?_
    constructor
    · intro htrue
      have h := (holds_eq_pvV_lit _ _ _).1 htrue
      cases h
    · intro _
      change (Upd.nil.pop ((savedExt Γ 2).trans (.push .refl))).afterT .diamond _ _
      refine after_capture (p := fun st => holds st _)
        (Upd.lands_pop_nil _ ((saveState τ zeroes).push (t := .val .bool) false)) ?_
      trivial

theorem exiting_source_diamond (σ : State C Γ) (k : Nat) :
    holds σ (.modal .diamond
      (.cons (.loop (.invLex yes constants false []) (.simple (.bool false))
        (.nil : Prog C Γ Γ)) .nil) .nil .tt) :=
  (diamondPremise_sound k yes (.simple (.bool false)) constants .nil rfl σ)
    .nil .nil .tt (exiting_vc σ k)

private def returnGuard : Val Flags [.val .bool] .bool :=
  .unop .not rfl rfl (.simple (.local .here))
private def returnBody : Prog Flags [.val .bool] [.val .bool] :=
  .cons (.assignLocal .here (.simple (.bool true))) .nil
private def returnInitial : State Flags [.val .bool] :=
  (State.init Flags).push (t := .val .bool) false
private def returnFinal : State Flags [.val .bool] :=
  (State.init Flags).push (t := .val .bool) true

/-- A successful return-flag turn makes its guard false without changing a
constant metric. Source returns use this flag mechanism. The strengthened VC
still rejects its unchanged tuple via `unchanged_final_turn_rejected`. -/
theorem return_flag_loop_succeeds :
    Stmt.run returnInitial (.loop (.invLex yes constants false []) returnGuard returnBody) =
      .ok ⟨returnFinal, List.prefix_refl _⟩ := by
  rw [Stmt.run_loop, TLoop.run_unfold]
  change TLoop.run _ _ (⟨returnFinal, List.prefix_refl _⟩ : Out Flags returnInitial.H [.val .bool]) = _
  rw [TLoop.run_unfold]
  rfl

/-- The exhausting VC feeds the actual soundness theorem, not a toy order. -/
theorem exhausting_source_diamond (σ : State C Γ) (k : Nat) :
    holds σ (.modal .diamond
      (.cons (.loop (.invLex yes constants false []) yes
        (.cons .assumeFalse (.nil : Prog C Γ Γ))) .nil) .nil .ff) :=
  (diamondPremise_sound k yes yes constants (.cons .assumeFalse .nil) rfl σ)
    .nil .nil .ff (exhausting_vc σ k)

/-- The same source loop cannot satisfy a strict successful-run certificate. -/
theorem exhausting_not_strict : ¬ LoopMetrics.Certificate
    (constants : LoopMetrics Flags FlagCtx 2) yes (.cons .assumeFalse .nil)
    (fun _ => True) (fun _ => True) :=
  LoopMetrics.no_certificate_of_body_halt (σ := Examples.LexMetrics.initial) trivial rfl
    (error := .exhausted) rfl

end Solidity.Examples.LexDiamond
