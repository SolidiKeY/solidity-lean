import Solidity.Calculus.Core.TSoundArms
import Solidity.Calculus.Core.TSoundCalls

/-!
# The rules of loops are sound over the typed state

`Calculus/Core/Blocks.lean`'s `loopStep` against the typed run
(`TRun.loop`, `TLoop.run`), in the shape of `Calculus/Core/TSoundKit.lean`:
`Calculus/Core/SoundBlocks.lean`'s and `SoundLoops.lean`'s loop arms read
over `TState`.

* `whileUnwind` is one turn of the loop (`TLoop.run_unfold`,
  `Stmt.trunSt_loop_unfold`), `loopExit` its exit; `whileClose` and
  `whileNoVariantDiamond` close to `false`.
* The invariant rules: every loop head is a state the body's frame allows
  from the first (`Prog.trun_frame`), so the premise read under
  `{anon(xs)}` holds there (`tholds_anonHavoc`, from
  `TState.eq_anonHavoc`); the invariant holds at every head by induction on
  the iterations (`TLoop.run_induct`).  Under the diamond the body is read
  under the variant's local (`Prog.wk up`), which it keeps
  (`Prog.trun_wk`), and the variant bounds the iterations left
  (`TLoop.run_variant`).  A condition is a `bool` of the typed state, so it
  is `true` or `false` wherever it is read; what the rule's terms read on
  the erasure is the typed value (`tholds_isBoolD_lower`, from
  `Val.evalT_erase` and `Val.evalT_nd`).
-/

namespace Solidity.Core

open Semantics (Value)
open Solidity (Modality Mutability)

variable {C : Contract}

/-! ## A condition read on the erasure -/

section Cond

variable {Γ : Ctx}

/-- `t ≐ b` holds over the typed state where `t` returns `b` on the
erasure. -/
theorem tholds_isBoolD (t : Tm C Γ .val) (σ : TState C Γ) (b : Bool) :
    tholds σ (Fml.isBoolD t b) ↔ t.eval σ.erase = .ok (.bool b) :=
  (tholds_iff_holds _ rfl σ).trans (holds_isBoolD t σ.erase b)

/-- A value that returns over the typed state reads its erasure on the
erased state. -/
theorem Val.eval_erase_ok {p : PrimTy} (v : Val C Γ p) (σ : TState C Γ) {x : p.Denote}
    (h : v.evalT σ = .ok x) : v.eval σ.erase = .ok (PrimTy.erase x) := by
  have ha := Val.evalT_erase σ v
  rw [h] at ha
  exact ha

/-- What a value reads on the erased state, where the typed one halts: a
halt too, for it never diverges. -/
theorem Val.eval_erase_error {p : PrimTy} (v : Val C Γ p) (σ : TState C Γ) {e : THalt}
    (h : v.evalT σ = .error e) : ∃ e', v.eval σ.erase = .error e' := by
  have ha := Val.evalT_erase σ v
  have hnd := Val.evalT_nd σ v
  rw [h] at ha hnd
  cases e with
  | revert => exact ⟨_, ha⟩
  | panic => exact ⟨_, ha⟩
  | diverge => exact absurd rfl hnd

/-- **A lowered condition** holds `b` over the typed state where it
evaluates to `b`. -/
theorem tholds_isBoolD_lower (c : Val C Γ .bool) (σ : TState C Γ) (b : Bool) :
    tholds σ (Fml.isBoolD c.lower b) ↔ c.evalT σ = .ok b := by
  rw [tholds_isBoolD, Val.eval_lower]
  cases h : c.evalT σ with
  | ok v =>
    rw [Val.eval_erase_ok c σ h]
    constructor
    · intro h'
      have : v = b := Semantics.PrimVal.bool.inj (Except.ok.inj h')
      rw [this]
    · intro h'
      rw [show v = b from Except.ok.inj h']
      rfl
  | error e =>
    obtain ⟨e', he'⟩ := Val.eval_erase_error c σ h
    rw [he']
    exact ⟨nofun, nofun⟩

end Cond

/-! ## The loop, one turn -/

section Turn

variable {Γ Γ₁ : Ctx}

/-- A loop started from an outcome runs, read through its states, as the
loop from that outcome's state: the heap's extension it carries plays no
part. -/
theorem Stmt.trun_loop_from (σ : TState C Γ) (a : LoopAnn C Γ) (c : Val C Γ .bool)
    (body : Prog C Γ Γ₁) (τ : Out C σ.H Γ) :
    (TLoop.run (fun o : Out C σ.H Γ => (Prog.trun o.st body).map
          fun o' => ⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩)
        (fun o => c.evalT o.st) τ).map (·.st) =
      (Stmt.trun τ.st (.loop a c body)).map (·.st) := by
  rw [Stmt.trun_loop]
  have hm := TLoop.run_map (body := fun o : Out C τ.st.H Γ => (Prog.trun o.st body).map
          fun o' => ⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩)
    (c := fun o => c.evalT o.st)
    (body' := fun o : Out C σ.H Γ => (Prog.trun o.st body).map
          fun o' => ⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩)
    (c' := fun o => c.evalT o.st)
    (fun o : Out C τ.st.H Γ => (⟨o.st, τ.ext.trans o.ext⟩ : Out C σ.H Γ)) (fun _ => rfl)
    (fun a => by dsimp only; cases Prog.trun a.st body <;> rfl) ⟨τ.st, List.prefix_refl _⟩
  rw [show (⟨τ.st, τ.ext.trans (List.prefix_refl _)⟩ : Out C σ.H Γ) = τ from rfl] at hm
  rw [hm]
  cases TLoop.run _ _ (⟨τ.st, List.prefix_refl _⟩ : Out C τ.st.H Γ) <;> rfl

/-- **One turn of a loop**, read through its states: the condition, then the
body, its locals popped, and the loop again. -/
theorem Stmt.trunSt_loop_unfold (σ : TState C Γ) (a : LoopAnn C Γ) (c : Val C Γ .bool)
    (body : Prog C Γ Γ₁) :
    Stmt.trunSt σ (.loop a c body) =
      (c.evalT σ).bind fun v => if boolT v then
        ((Prog.trunSt σ body).map (TState.drop body.ext)).bind fun τ =>
          Stmt.trunSt τ (.loop a c body)
      else .ok σ := by
  unfold Stmt.trunSt
  rw [Stmt.trun_loop, TLoop.run_unfold]
  unfold TLoop.step
  dsimp only
  cases c.evalT σ with
  | error => rfl
  | ok v =>
    cases v with
    | false => rfl
    | true =>
      show _ = ((Prog.trunSt σ body).map _).bind _
      unfold Prog.trunSt
      cases Prog.trun σ body with
      | error => rfl
      | ok o => exact Stmt.trun_loop_from σ a c body _

/-- A block, read through its states: the body, its locals popped. -/
theorem Stmt.trunSt_block (σ : TState C Γ) (P : Prog C Γ Γ₁) :
    Stmt.trunSt σ (.block P) = (Prog.trunSt σ P).map (TState.drop P.ext) :=
  TRes.map_st _ _ _ fun _ => rfl

/-- An `if`, read through its states. -/
theorem Stmt.trunSt_ite {Γ₂ : Ctx} (σ : TState C Γ) (c : Val C Γ .bool) (thn : Prog C Γ Γ₁)
    (els : Prog C Γ Γ₂) :
    Stmt.trunSt σ (.ite c thn els) =
      (c.evalT σ).bind fun v => if boolT v then (Prog.trunSt σ thn).map (TState.drop thn.ext)
        else (Prog.trunSt σ els).map (TState.drop els.ext) := by
  unfold Stmt.trunSt
  show (TRun.ite c thn.ext thn.trunR els.ext els.trunR σ).map _ = _
  unfold TRun.ite
  cases c.evalT σ with
  | error => rfl
  | ok v => cases v <;> exact TRes.map_st _ _ _ fun _ => rfl

/-- **A block** is its statements, its locals popped after it. -/
theorem Stmt.tsound_block {m : Modality} (body : Prog C Γ Γ₁) (σ : TState C Γ) :
    Premise.TSound m (.block body) (.unfold body body.ext) σ :=
  Premise.tsound_unfold σ (Stmt.trunSt_block σ body).symm

/-- The loop's annotation plays no part in its run. -/
theorem Stmt.trunSt_loop_ann (σ : TState C Γ) (a a' : LoopAnn C Γ) (c : Val C Γ .bool)
    (body : Prog C Γ Γ₁) : Stmt.trunSt σ (.loop a c body) = Stmt.trunSt σ (.loop a' c body) :=
  rfl

/-- `whileUnwind`: `⟨[ while (nse) body ]⟩ ⇝ ⟨[ if (nse) { { body } while (nse) body } ]⟩`. -/
theorem Premise.tsound_whileUnwind {m : Modality} (n : Nat) (c : Val C Γ .bool)
    (body : Prog C Γ Γ₁) (σ : TState C Γ) :
    Premise.TSound m (.loop (.unwind (n + 1)) c body)
      (.unfold (.cons (.ite c (.cons (.block body) (.cons (.loop (.unwind n) c body) .nil)) .nil)
        .nil) .refl) σ := by
  refine Premise.tsound_unfold σ ?_
  rw [Prog.trunSt_single, Stmt.trunSt_ite, Stmt.trunSt_loop_unfold]
  cases c.evalT σ with
  | error => rfl
  | ok v =>
    cases v with
    | false => rfl
    | true =>
      show ((Prog.trunSt σ (.cons (.block body) (.cons (.loop (.unwind n) c body) .nil))).map
        (TState.drop (Ext.refl (Γ := Γ)))).map (TState.drop .refl) = _
      rw [Prog.trunSt_cons, Stmt.trunSt_block]
      cases (Prog.trunSt σ body).map (TState.drop body.ext) with
      | error => rfl
      | ok τ =>
        show ((Prog.trunSt τ (.cons (.loop (.unwind n) c body) .nil)).map _).map _ = _
        rw [Prog.trunSt_single, Stmt.trunSt_loop_ann τ (.unwind n) (.unwind (n + 1))]
        show _ = Stmt.trunSt τ (.loop (.unwind (n + 1)) c body)
        cases Stmt.trunSt τ (.loop (.unwind (n + 1)) c body) <;> rfl

/-- `loopExit`: `⟨[ while (nse) body ]⟩ ⇝ nse = FALSE ⟹ ⟨[ ]⟩ ; nse = FALSE`. -/
theorem Premise.tsound_loopExit {m : Modality} (c : Val C Γ .bool) (body : Prog C Γ Γ₁)
    (σ : TState C Γ) :
    Premise.TSound m (.loop (.unwind 0) c body) (.check (Fml.isBoolD c.lower false)) σ :=
  Premise.tsound_check σ fun h => by
    rw [Stmt.trunSt_loop_unfold, (tholds_isBoolD_lower c σ false).1 h]
    rfl

end Turn

/-! ## The invariant rules -/

section Inv

variable {Γ Γ₁ : Ctx}

/-- **A state in a loop body's frame is one its anonymised premise covers**
(`holds_anonHavoc`, over the typed state): `{anon(xs)}` (`{havoc}` when
`hv`) of the loop's first state reaches every state that agrees with it but
where the body may write. -/
theorem tholds_anonHavoc {σ τ : TState C Γ} {xs : List ((t : LTy) × Idx Γ t)} {hv : Bool}
    {W : List (LTy × Nat)}
    (hxs : ∀ t (i : Idx Γ t), (t, i.toNat) ∈ W → (⟨t, i⟩ : (t : LTy) × Idx Γ t) ∈ xs)
    (hg : TGFrame (frameMut hv) σ τ) (ha : TLocAgree 0 W σ.env τ.env) {ψ : Fml C Γ}
    (h : tholds σ (Fml.anonHavoc xs hv ψ)) : tholds τ ψ := by
  obtain ⟨b, hb⟩ := TState.eq_anonHavoc hxs hg ha
  cases hv with
  | false =>
    have hk := hg.keeps (by simp only [frameMut]; decide)
    have hτ : τ = σ.anon xs b := by rw [hb, hk.1, hk.2]; rfl
    rw [hτ]
    exact h b
  | true =>
    rw [hb]
    exact h b τ.storage τ.net

/-- The loop's run from `σ`, read through its states, then the rest. -/
abbrev loopThen {Γ₂ Γ₀ : Ctx} (σ : TState C Γ) (ω : Prog C Γ Γ₂) (κ : Frames C Γ₂ Γ₀)
    (r : TRes (Out C σ.H Γ)) : TRes (TState C Γ₀) :=
  (r.map (·.st)).bind fun τ => (Prog.trunSt τ ω).bind (Frames.trunSt · κ)

/-- **`whileInvariantBox` is sound** over the typed state. -/
theorem Premise.tsound_whileInvBox (k : Nat) (I c : Val C Γ .bool)
    (dec : Option (Val C Γ .uint)) (body : Prog C Γ Γ₁) {xs : List ((t : LTy) × Idx Γ t)}
    {hv : Bool} (hf : body.frame = some (xs, hv)) (σ : TState C Γ) :
    Premise.TSound .box (.loop (.inv I dec) c body)
      (.inv (.isBoolD I.lower true) xs hv (Upd.nil.decl (fse k) (.val (p := .bool) c.lower))
        (.isBoolD (.pvV (p := .bool) .here) true) (.isBoolD (.pvV (p := .bool) .here) false)
        .refl (.push .refl) body (.isBoolD I.lower true)) σ := by
  intro _ _ ω κ φ hp
  obtain ⟨hI0, hA⟩ := hp
  obtain ⟨hwμ, hxs⟩ := Prog.frame_some hf
  rw [tholds_modal_iff, trunSt_cons_frames]
  show Modality.afterRunTR .box _ (loopThen σ ω κ (TLoop.run
    (fun o : Out C σ.H Γ => (Prog.trun o.st body).map
      fun o' => ⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩)
    (fun o => c.evalT o.st) ⟨σ, List.prefix_refl _⟩))
  refine TLoop.run_induct
    (P := fun a : Out C σ.H Γ => TGFrame (frameMut hv) σ a.st ∧
      TLocAgree 0 (Prog.writesAt 0 body) σ.env a.st.env ∧ tholds a.st (Fml.isBoolD I.lower true))
    (Q := fun r => Modality.afterRunTR .box (tholds · φ) (loopThen σ ω κ r))
    ⟨TGFrame.refl σ, TLocAgree.refl _, hI0⟩ (fun a ha => ?_) ⟨trivial, nofun⟩
  obtain ⟨hg, hag, hI⟩ := ha
  have hY := tholds_anonHavoc hxs hg hag hA hI
  unfold TLoop.step
  dsimp only
  cases hc : c.evalT a.st with
  | error e =>
    refine ⟨trivial, fun h => ?_⟩
    cases h
    exact Val.evalT_noPanic a.st c hc
  | ok v =>
    have hU : (Upd.nil.decl (fse k) (.val (p := .bool) c.lower)).apply a.st.erase =
        .ok (a.st.push (t := .val .bool) v).erase := by
      show (do let τ₀ ← pure a.st.erase
               pure (τ₀.push (t := .val .bool) (← c.lower.eval a.st.erase))) = _
      rw [Val.eval_lower, Val.eval_erase_ok c a.st hc]
      rfl
    change Modality.afterC .box _ (Upd.apply _ _) at hY
    rw [hU] at hY
    obtain ⟨hT, hF⟩ := hY _ rfl
    cases v with
    | false =>
      have hF' := hF ((tholds_isBoolD _ _ _).2 rfl) a.st rfl
      exact (tholds_modal_iff a.st ω κ φ).1 (tholds_modalK a.st ω κ φ hF')
    | true =>
      have hT' := hT ((tholds_isBoolD _ _ _).2 rfl) a.st rfl
      have h' := (tholds_modal_iff a.st body _ _).1 (tholds_modalK a.st body _ _ hT')
      unfold Prog.trunSt at h'
      dsimp only
      cases hb : Prog.trun a.st body with
      | error e =>
        rw [hb] at h'
        exact ⟨trivial, fun h => h'.2 (by cases h; rfl)⟩
      | ok o =>
        rw [hb] at h'
        obtain ⟨hg', ha'⟩ := Prog.trun_frame body hwμ 0 hb
        exact ⟨hg.trans (hg'.withEnv _), hag.trans ha', h'.1⟩

/-- A block's run, its frame popped with nothing after it, read through
its states. -/
theorem frames_pop_nil_trun {H : HTy} {Γ' : Ctx} (b : BlockKind) (X : TRes (Out C H Γ₁))
    (h : Ext Γ' Γ₁) :
    (X.map (·.st)).bind (Frames.trunSt · (.pop b h .nil)) = (X.map (Out.drop h)).map (·.st) := by
  cases X <;> rfl

/-- **`whileInvariantDiamond` is sound** over the typed state: the variant
bounds the iterations left. -/
theorem Premise.tsound_whileInvDiamond (k : Nat) (I c : Val C Γ .bool) (d : Val C Γ .uint)
    (body : Prog C Γ Γ₁) {xs : List ((t : LTy) × Idx Γ t)} {hv : Bool}
    (hf : body.frame = some (xs, hv)) (σ : TState C Γ) {p : Premise C Γ Γ}
    (hp : loopStep k .diamond (.inv I (some d)) c body = some p) :
    Premise.TSound .diamond (.loop (.inv I (some d)) c body) p σ := by
  unfold loopStep at hp
  rw [hf] at hp
  dsimp only at hp
  cases hp
  intro _ _ ω κ φ hp
  obtain ⟨hI0, hA⟩ := hp
  obtain ⟨hwμ, hxs⟩ := Prog.frame_some hf
  rw [tholds_modal_iff, trunSt_cons_frames]
  show Modality.afterRunTR .diamond _ (loopThen σ ω κ (TLoop.run
    (fun o : Out C σ.H Γ => (Prog.trun o.st body).map
      fun o' => ⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩)
    (fun o => c.evalT o.st) ⟨σ, List.prefix_refl _⟩))
  suffices key : ∃ τ, TLoop.run
      (fun o : Out C σ.H Γ => (Prog.trun o.st body).map
        fun o' => (⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩ : Out C σ.H Γ))
      (fun o => c.evalT o.st) ⟨σ, List.prefix_refl _⟩ = .ok τ ∧
        tholds τ.st (Fml.modalK .diamond ω κ φ) by
    obtain ⟨τf, hrun, hG⟩ := key
    rw [hrun]
    exact (tholds_modal_iff τf.st ω κ φ).1 (tholds_modalK τf.st ω κ φ hG)
  refine TLoop.run_variant
    (H := fun a : Out C σ.H Γ => TGFrame (frameMut hv) σ a.st ∧
      TLocAgree 0 (Prog.writesAt 0 body) σ.env a.st.env ∧ tholds a.st (Fml.isBoolD I.lower true))
    (D := fun a : Out C σ.H Γ => (d.evalT a.st).map (·.1)) ?_
    ⟨TGFrame.refl σ, TLocAgree.refl _, hI0⟩
  rintro a ⟨hg, hag, hI⟩
  have hY := tholds_anonHavoc hxs hg hag hA hI
  change Modality.afterC .diamond _ (Upd.apply _ _) at hY
  have hUe : ((Upd.nil.decl (fie k) (.val (p := .uint) d.lower)).decl (fse k)
      (.val (p := .bool) c.lower)).apply a.st.erase =
      (d.eval a.st.erase >>= fun dv => c.eval a.st.erase >>= fun cv =>
        pure ((a.st.erase.push (t := .val .uint) dv).push (t := .val .bool) cv)) := by
    show (do
      let τ₁ ← (do
        let τ₀ ← pure a.st.erase
        pure (τ₀.push (t := .val .uint) (← d.lower.eval a.st.erase)))
      pure (τ₁.push (t := .val .bool) (← c.lower.eval a.st.erase))) = _
    rw [Val.eval_lower, Val.eval_lower]
    cases d.eval a.st.erase <;> cases c.eval a.st.erase <;> rfl
  rw [hUe] at hY
  cases hd : d.evalT a.st with
  | error e =>
    obtain ⟨e', he'⟩ := Val.eval_erase_error d a.st hd
    rw [he'] at hY
    exact hY.elim
  | ok dv =>
  cases hc : c.evalT a.st with
  | error e =>
    obtain ⟨e', he'⟩ := Val.eval_erase_error c a.st hc
    rw [Val.eval_erase_ok d a.st hd, he'] at hY
    exact hY.elim
  | ok cv =>
  rw [Val.eval_erase_ok d a.st hd, Val.eval_erase_ok c a.st hc] at hY
  obtain ⟨hT, hF⟩ := hY ((a.st.push (t := .val .uint) dv).push (t := .val .bool) cv) rfl
  refine ⟨dv.1, by show (d.evalT a.st).map _ = _; rw [hd]; rfl, ?_, fun hc' => ?_, fun hc' => ?_⟩
  · cases cv
    · exact .inr rfl
    · exact .inl rfl
  · have hcv : cv = false := Except.ok.inj hc'
    subst hcv
    have hF' := hF ((tholds_isBoolD _ _ _).2 rfl) a.st rfl
    exact hF'
  · have hcv : cv = true := Except.ok.inj hc'
    subst hcv
    have hT' := hT ((tholds_isBoolD _ _ _).2 rfl) (a.st.push (t := .val .uint) dv) rfl
    have h' := (tholds_modal_iff _ _ _ _).1 (tholds_modalK _ _ _ _ hT')
    unfold Prog.trunSt at h'
    rw [frames_pop_nil_trun, TState.push_lift,
      (TWkRel.drop (Prog.wk_over body Core.up)
        (Prog.trun_wk body Core.up a.st
          ((dv, a.st.env) : TEnv C a.st.H (.val .uint :: Γ)))).eq_lifted] at h'
    cases hb : Prog.trun a.st body with
    | error e =>
      rw [hb] at h'
      exact h'.1.elim
    | ok o =>
      rw [hb] at h'
      obtain ⟨hg', ha'⟩ := Prog.trun_frame body hwμ 0 hb
      obtain ⟨hI₁, hdec⟩ := h'.1
      let τ₀ : TState C Γ := o.st.drop body.ext
      change tholds (τ₀.push (t := .val .uint) dv) _ at hI₁ hdec
      refine ⟨⟨τ₀, a.ext.trans o.ext⟩, rfl, ⟨hg.trans (hg'.withEnv _), hag.trans ha', ?_⟩,
        fun hc₁ => ?_⟩
      · have hI' := (tholds_isBoolD_lower I.up (τ₀.push (t := .val .uint) dv) true).1 hI₁
        rw [Val.evalT_up] at hI'
        exact (tholds_isBoolD_lower I τ₀ true).2 hI'
      · change c.evalT τ₀ = _ at hc₁
        have hcu : c.up.evalT (τ₀.push (t := .val .uint) dv) = .ok true := by
          rw [Val.evalT_up]; exact hc₁
        change Modality.afterC .diamond _ (Upd.apply _ _) at hdec
        have hU₁ : (Upd.nil.decl (fse k) (.val (p := .bool) c.up.lower)).apply
            (τ₀.push (t := .val .uint) dv).erase =
            .ok ((τ₀.push (t := .val .uint) dv).push (t := .val .bool) true).erase := by
          show (do
            let υ ← pure (τ₀.push (t := .val .uint) dv).erase
            pure (υ.push (t := .val .bool)
              (← c.up.lower.eval (τ₀.push (t := .val .uint) dv).erase))) = _
          rw [Val.eval_lower, Val.eval_erase_ok _ _ hcu]
          rfl
        rw [hU₁] at hdec
        obtain ⟨hle, hlt⟩ := hdec _ rfl ((tholds_isBoolD _ _ _).2 rfl)
        rw [tholds_isBoolD] at hle hlt
        change evalBinop .le .uint (.int 0) (d.up.up.lower.eval _) = _ at hle
        change (d.up.up.lower.eval _ >>= fun a => evalBinop .lt .uint a (pure (.int dv.1))) = _
          at hlt
        rw [Val.eval_lower] at hle hlt
        cases hdx : d.evalT τ₀ with
        | error e =>
          have hd₂ : (d.up.up (t := .val .bool)).evalT
              ((τ₀.push (t := .val .uint) dv).push (t := .val .bool) true) = .error e := by
            rw [Val.evalT_up, Val.evalT_up]; exact hdx
          obtain ⟨e', he'⟩ := Val.eval_erase_error _ _ hd₂
          rw [he'] at hle
          obtain ⟨_, _, -, hy, -, -⟩ := evalBinop_cmp_true (.inr rfl) hle
          cases hy
        | ok x =>
          have hd₂ : (d.up.up (t := .val .bool)).evalT
              ((τ₀.push (t := .val .uint) dv).push (t := .val .bool) true) = .ok x := by
            rw [Val.evalT_up, Val.evalT_up]; exact hdx
          rw [Val.eval_erase_ok _ _ hd₂] at hle hlt
          obtain ⟨_, y, hx0, hy, -, hle'⟩ := evalBinop_cmp_true (.inr rfl) hle
          cases hx0
          cases hy
          change evalBinop .lt .uint (.int x.1) (pure (.int dv.1)) = _ at hlt
          obtain ⟨x', z, hx', hz, hlt', -⟩ := evalBinop_cmp_true (.inl rfl) hlt
          cases hx'
          cases hz
          exact ⟨x.1, by show (d.evalT τ₀).map _ = _; rw [hdx]; rfl, hle' rfl, hlt' rfl⟩

end Inv

/-! ## The rule of a loop -/

/-- **The rule of a loop is sound** over the typed state: unwound, ended, by
its invariant, or closed to `false`. -/
theorem Stmt.tsound_loop (k : Nat) (m : Modality) {Γ Γ₁ : Ctx} (a : LoopAnn C Γ)
    (c : Val C Γ .bool) (body : Prog C Γ Γ₁) (σ : TState C Γ) (p : Premise C Γ Γ)
    (hp : Stmt.step k m (.loop a c body) = some p) :
    Premise.TSound m (.loop a c body) p σ := by
  change loopStep k m a c body = some p at hp
  cases a with
  | unwind n =>
    cases n with
    | zero =>
      unfold loopStep at hp
      cases hp
      exact Premise.tsound_loopExit c body σ
    | succ n =>
      unfold loopStep at hp
      cases hp
      exact Premise.tsound_whileUnwind n c body σ
  | inv I dec =>
    cases hf : body.frame with
    | none =>
      unfold loopStep at hp
      rw [hf] at hp
      cases hp
      exact Premise.tsound_done σ false nofun
    | some f =>
      obtain ⟨xs, hv⟩ := f
      cases m with
      | box =>
        unfold loopStep at hp
        rw [hf] at hp
        dsimp only at hp
        cases hp
        exact Premise.tsound_whileInvBox k I c dec body hf σ
      | diamond =>
        cases dec with
        | none =>
          unfold loopStep at hp
          rw [hf] at hp
          dsimp only at hp
          cases hp
          exact Premise.tsound_done σ false nofun
        | some d => exact Premise.tsound_whileInvDiamond k I c d body hf σ hp

end Solidity.Core
