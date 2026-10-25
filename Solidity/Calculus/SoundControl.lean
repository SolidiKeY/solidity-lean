import Solidity.Calculus.SoundLocal

/-!
# Soundness of payments, control flow, declarations

`transferStep`, `sendStep`, `iteStep`, `requireStep`, `assertStep`, the
declarations with an initializer (`Premise.bind`), `revert` and a block,
each `Premise.Sound`.  A `bool` value is a `bool` here, so a split on a
simple condition covers every state (`holds_isBool`), with no stuck case; a
captured `if` condition reads its branches weakened under the captured
local, which run as before by `Semantics/RunWk.lean`'s
`Prog.run_wk` (`Prog.run_wk_up`).

Every hidden binder ranges over a type with a value (`LTy.tdenote_nonempty`):
`memoryLocalDeclInitDrop`'s over the references the heap typing gives the
local's type and an unset local (decision 17'), from which the premise's
`mv = r;` runs as the declaration does, whatever `r` allocates
(`sound_declMemInit`, an alias initializer included).
-/

namespace Solidity
open Solidity (Modality Srt Op0 Op1 Op2 Op3)
open Semantics (Selector)

variable {C : Contract}

open Solidity (Modality)

section Control

variable {Γ : Ctx} {m : Modality} (σ : State C Γ)

/-! ### Payments -/

/-- `transfer_unfold_rightSndArgument`: the amount captured. -/
theorem sound_transferRight (sadr : Simple C Γ .uint) (a : Val C Γ .uint) (x : Var) :
    Premise.Runs m (.transfer (.simple sadr) a)
      (.capture .uint x a (.transfer (.simple sadr.up) (.simple (.local .here)))) σ := by
  refine Premise.sound_capturePushed σ (fun v hv => TRun.transfer_pushT σ (t := .val .uint) v
      (.simple sadr.up) (.simple (.local .here)) (.simple sadr) a
      (by simp only [Val.evalT, Simple.evalT_up]) (by rw [hv]; rfl)) (fun h hh => ?_)
  show (TRun.transfer _ a σ).map _ = _
  simp only [TRun.transfer, Val.evalT, ok_bind, hh]; rfl

/-- `transfer_unfold_leftFstReceiver`: the receiver captured. -/
theorem sound_transferLeft (r a : Val C Γ .uint) (x : Var) :
    Premise.Runs m (.transfer r a)
      (.capture .uint x r (.transfer (.simple (.local .here)) a.up)) σ := by
  refine Premise.sound_capturePushed σ (fun v hv => TRun.transfer_pushT σ (t := .val .uint) v
      (.simple (.local .here)) a.up r a (by rw [hv]; rfl) (Val.evalT_up σ (t := .val .uint) v a))
    (fun h hh => ?_)
  show (TRun.transfer r a σ).map _ = _
  simp only [TRun.transfer, hh]; rfl

/-- **A transfer** (`transferStep`). -/
theorem transferStep_sound (k : Nat) (r a : Val C Γ .uint) (q : Premise C Γ Γ)
    (hs : transferStep k m r a = q) : Premise.Runs m (.transfer r a) q σ := by
  cases r with
  | simple sadr =>
    cases a with
    | simple se =>
      cases m with
      | box => cases hs; exact sound_transferBox σ sadr se
      | diamond => cases hs; exact sound_done_false (m := .diamond) σ _
    | _ => cases hs; exact sound_transferRight σ sadr _ _
  | _ => cases hs; exact sound_transferLeft σ _ a _

/-- `send_unfold_rightSndArgument`: the amount captured. -/
theorem sound_sendRight (pv : Idx Γ (.val .bool)) (sadr : Simple C Γ .uint) (a : Val C Γ .uint)
    (x : Var) (full : Bool) :
    Premise.Runs m (.send pv (.simple sadr) a full)
      (.capture .uint x a (.send pv.there (.simple sadr.up) (.simple (.local .here)) full)) σ := by
  refine Premise.sound_capturePushed σ (fun v hv => TRun.send_pushT σ (t := .val .uint) v pv
      (.simple sadr.up) (.simple (.local .here)) (.simple sadr) a
      (by simp only [Val.evalT, Simple.evalT_up]) (by rw [hv]; rfl)) (fun h hh => ?_)
  show (TRun.send pv _ a σ).map _ = _
  simp only [TRun.send, Val.evalT, ok_bind, hh]; rfl

/-- `send_unfold_leftFstReceiver`: the receiver captured. -/
theorem sound_sendLeft (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) (x : Var) (full : Bool) :
    Premise.Runs m (.send pv r a full)
      (.capture .uint x r (.send pv.there (.simple (.local .here)) a.up full)) σ := by
  refine Premise.sound_capturePushed σ (fun v hv => TRun.send_pushT σ (t := .val .uint) v pv
      (.simple (.local .here)) a.up r a (by rw [hv]; rfl) (Val.evalT_up σ (t := .val .uint) v a))
    (fun h hh => ?_)
  show (TRun.send pv r a σ).map _ = _
  simp only [TRun.send, hh]; rfl

/-- **A send** (`sendStep`). -/
theorem sendStep_sound (k : Nat) (pv : Idx Γ (.val .bool)) (full : Bool) (r a : Val C Γ .uint)
    (q : Premise C Γ Γ) (hs : sendStep k m pv full r a = q) :
    Premise.Runs m (.send pv r a full) q σ := by
  cases r with
  | simple sadr =>
    cases a with
    | simple se =>
      cases m with
      | box => cases hs; exact sound_send (m := .box) σ pv sadr se full _
      | diamond => cases hs; exact sound_send (m := .diamond) σ pv sadr se full _
    | _ => cases hs; exact sound_sendRight σ pv sadr _ _ full
  | _ => cases hs; exact sound_sendLeft σ pv _ a _ full

/-! ### `if`, `require`, `assert` -/

/-- `se = b` holds where `se` is `b`: the condition read on the typed state. -/
theorem holds_isBool (se : Simple C Γ .bool) (b : Bool) :
    holds σ (Fml.isBool se.lower b) ↔ se.evalT σ = b := by
  show holds σ (.eq _ _) ↔ _
  rw [holds_eq, Simple.denote_lowerT σ se]
  show some _ = some b ↔ _
  rw [Option.some.injEq]

/-- A block weakened under one local runs as before, lifted, its locals
popped (`Prog.run_wk` at `up`). -/
theorem Prog.run_wk_up {t : LTy} {Δ : Ctx} (P : Prog C Γ Δ) (w : t.TDenote C σ.H) :
    ((P.wk (Solidity.up (t := t))).2.2.run (σ.push w)).map (Out.drop (P.wk Solidity.up).2.2.ext) =
      pushedT σ w ((P.run σ).map (Out.drop P.ext)) :=
  TWkRel.eq_lifted (TWkRel.drop (Prog.wk_over P Solidity.up) (Prog.run_wk P Solidity.up σ (w, σ.env)))

/-- `ifElseUnfold`: the condition captured, the branches weakened under it. -/
theorem sound_iteCapture {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (thn : Prog C Γ Γ₁)
    (els : Prog C Γ Γ₂) (x : Var) :
    Premise.Runs m (.ite c thn els)
      (.capture .bool x c (.ite (.simple (.local .here)) (thn.wk up).2.2 (els.wk up).2.2)) σ := by
  refine Premise.sound_capturePushed σ (fun v hv => ?_) (fun h hh => ?_)
  · show TRun.ite (.simple (.local .here)) _ ((thn.wk up).2.2.runR) _ ((els.wk up).2.2.runR)
      (σ.push v) = pushedT σ v (TRun.ite c thn.ext thn.runR els.ext els.runR σ)
    simp only [TRun.ite, Val.evalT, ok_bind, hv]
    cases v
    · exact Prog.run_wk_up σ els _
    · exact Prog.run_wk_up σ thn _
  · show (TRun.ite c _ _ _ _ σ).map _ = _
    simp only [TRun.ite, hh]; rfl

/-- What a joinable branch runs as. -/
def JoinArm.runSt : JoinArm C Γ → TRes (State C Γ)
  | none => .ok σ
  | some ⟨_, i, r⟩ => (r.evalT σ).map fun x => σ.setLocal i x

/-- A joinable branch runs as what it assigns: `{ x = x + 1; }` as
`x = x + 1;`, `{ }` as nothing, its scope's end popping nothing. -/
theorem Prog.joinArm?_runSt {Γ₁ : Ctx} (P : Prog C Γ Γ₁) {a : JoinArm C Γ}
    (h : P.joinArm? = some a) : (Prog.runSt σ P).map (State.drop P.ext) = a.runSt σ := by
  cases P with
  | nil =>
    cases h
    rfl
  | cons s ω =>
    cases s <;> try cases h
    rename_i i r
    cases ω with
    | nil =>
      cases h
      rw [Prog.runSt_single, Stmt.runSt_assignLocal]
      show _ = (r.evalT σ).map _
      cases r.evalT σ <;> rfl
    | cons _ _ => exact nomatch h


/-- A local set to the value it has (`x := x`) leaves the locals as they are. -/
theorem LocsV.set_getV {t : LTy} (i : Idx Γ t) : σ.locV.set i (σ.getV i) = σ.locV := by
  funext u j
  by_cases h : i.toNat = j.toNat
  · obtain rfl := Idx.ty_eq_of_toNat h
    obtain rfl := Idx.toNat_inj i j h
    exact LocsV.set_same _ _ _
  · exact LocsV.set_ne _ i j h _

/-- `v := t` sets `v` to what `t` reads. -/
theorem Rhs.eval_val {p : PrimTy} (t : Tm C Γ (.val p)) : Rhs.eval σ (.val t) = t.eval σ := rfl

/-- `c ? t : e` read where `c` is `bv`: `true ? 1 : x` is `1`. -/
theorem Tm.eval_ite {p : PrimTy} (c : Tm C Γ (.val .bool)) (t e : Tm C Γ (.val p)) {bv : Bool}
    (hc : c.eval σ = some bv) :
    (Tm.app3 .ite c t e).eval σ = cond bv (t.eval σ) (e.eval σ) := by
  show (c.eval σ).bind (fun cv => cond cv (t.eval σ) (e.eval σ)) = _
  rw [hc]; rfl

/-- One branch's assignment (`x = x + 1;`) against an update that sets its
local to the value's term (`{x := x + 1}`). -/
theorem joinArm_agrees_one {p : PrimTy} (i : Idx Γ (.val p)) (r : Val C Γ p)
    {X : Option (State C [] × LocsV C Γ)}
    (hX : X = (r.lower.eval σ).map fun v => (σ.glob, σ.locV.set i v)) :
    TRes.AgreesO (fun τ : State C Γ => (τ.glob, τ.locV))
      (JoinArm.runSt σ (some ⟨p, i, r⟩)) X := by
  subst hX
  refine TRes.AgreesO.map (Val.lower_evalT σ r) fun x => ?_
  show (σ.glob, σ.locV.set i x) = ((σ.setLocal i x).glob, (σ.setLocal i x).locV)
  rw [State.locV_setLocal]
  rfl

/-- An empty branch (`{ }`) against an update that changes nothing. -/
theorem joinArm_agrees_none {X : Option (State C [] × LocsV C Γ)}
    (hX : X = some (σ.glob, σ.locV)) :
    TRes.AgreesO (fun τ : State C Γ => (τ.glob, τ.locV)) (JoinArm.runSt σ none) X := hX

/-- Two branches assigning different locals, `if (c) { x = 1; } else { y = 2; }`
against `{x := c ? 1 : x ‖ y := c ? y : 2}`. -/
theorem ifJoin_agrees_two (c : Tm C Γ (.val .bool)) {bv : Bool} (hc : c.eval σ = some bv)
    {p q : PrimTy} (i : Idx Γ (.val p)) (ra : Val C Γ p) (j : Idx Γ (.val q)) (rb : Val C Γ q)
    (hij : i.toNat ≠ j.toNat) :
    TRes.AgreesO (fun τ : State C Γ => (τ.glob, τ.locV))
      (if bv then JoinArm.runSt σ (some ⟨p, i, ra⟩) else JoinArm.runSt σ (some ⟨q, j, rb⟩))
      (((Upd.nil.snoc (UpdElem.joinThen c i ra.lower)).snoc
        (UpdElem.joinElse c j rb.lower)).applyP σ) := by
  rw [applyP_snoc]
  have h1 : Upd.applyV σ (Upd.nil.snoc (UpdElem.joinThen c i ra.lower)) =
      ((Tm.app3 .ite c ra.lower (.pvV i)).eval σ).map fun v => (σ.globG, σ.locV.set i v) := by
    rw [Upd.applyV_eq_applyVM]
    show (some (σ.globG, σ.locV)).bind (fun p => UpdElem.applyV σ _ p.1 p.2) = _
    rw [Option.bind_some, UpdElem.applyV_local]
    rfl
  rw [h1, Tm.eval_ite σ _ _ _ hc]
  cases bv
  · show TRes.AgreesO _ _ ((some (σ.globG, σ.locV.set i (σ.getV i))).bind _)
    rw [LocsV.set_getV, Option.bind_some, UpdElem.applyV_local]
    refine joinArm_agrees_one σ j rb ?_
    rw [Rhs.eval_val, Tm.eval_ite σ _ _ _ hc]
    cases rb.lower.eval σ <;> rfl
  · refine joinArm_agrees_one σ i ra ?_
    show Option.bind (Option.map _ (ra.lower.eval σ)) _ = _
    cases ra.lower.eval σ with
    | none => rfl
    | some v =>
      rw [Option.map_some, Option.bind_some, UpdElem.applyV_local, Rhs.eval_val,
        Tm.eval_ite σ _ _ _ hc]
      show some (σ.glob, (σ.locV.set i v).set j (σ.getV j)) = some (σ.glob, σ.locV.set i v)
      have e : σ.locV.set i v = (σ.setLocal i v).locV := (State.locV_setLocal σ i v).symm
      rw [e, ← State.getV_setLocal_ne σ i j hij v, LocsV.set_getV]

/-- **The joined update computes what the branch the condition picks runs
as**: `if (c) { x = x + 1; }` as `{x := c ? x + 1 : x}`. -/
theorem ifJoin_agrees (c : Tm C Γ (.val .bool)) {bv : Bool} (hc : c.eval σ = some bv)
    (a b : JoinArm C Γ) :
    TRes.AgreesO (fun τ : State C Γ => (τ.glob, τ.locV))
      (if bv then a.runSt σ else b.runSt σ) ((Upd.ifJoin c a b).applyP σ) := by
  rcases a with _ | ⟨p, i, ra⟩ <;> rcases b with _ | ⟨q, j, rb⟩
  · cases bv <;> exact joinArm_agrees_none σ rfl
  · simp only [Upd.ifJoin]
    rw [applyP_local1]
    cases bv
    · refine joinArm_agrees_one σ j rb ?_
      show Option.map _ ((Tm.app3 .ite c (.pvV j) rb.lower).eval σ) = _
      rw [Tm.eval_ite σ _ _ _ hc]; rfl
    · refine joinArm_agrees_none σ ?_
      show Option.map _ ((Tm.app3 .ite c (.pvV j) rb.lower).eval σ) = _
      rw [Tm.eval_ite σ _ _ _ hc]
      show some (σ.glob, σ.locV.set j (σ.getV j)) = _
      rw [LocsV.set_getV]
  · simp only [Upd.ifJoin]
    rw [applyP_local1]
    cases bv
    · refine joinArm_agrees_none σ ?_
      show Option.map _ ((Tm.app3 .ite c ra.lower (.pvV i)).eval σ) = _
      rw [Tm.eval_ite σ _ _ _ hc]
      show some (σ.glob, σ.locV.set i (σ.getV i)) = _
      rw [LocsV.set_getV]
    · refine joinArm_agrees_one σ i ra ?_
      show Option.map _ ((Tm.app3 .ite c ra.lower (.pvV i)).eval σ) = _
      rw [Tm.eval_ite σ _ _ _ hc]; rfl
  · simp only [Upd.ifJoin]
    by_cases hpq : p = q
    · subst hpq
      rw [dif_pos rfl]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, applyP_local1]
        cases bv
        · refine joinArm_agrees_one σ _ rb ?_
          show Option.map _ ((Tm.app3 .ite c ra.lower rb.lower).eval σ) = _
          rw [Tm.eval_ite σ _ _ _ hc]; rfl
        · refine joinArm_agrees_one σ _ ra ?_
          show Option.map _ ((Tm.app3 .ite c ra.lower rb.lower).eval σ) = _
          rw [Tm.eval_ite σ _ _ _ hc]; rfl
      · rw [if_neg hij]
        exact ifJoin_agrees_two σ c hc i ra j rb (fun h => hij (Idx.toNat_inj _ _ h))
    · rw [dif_neg hpq]
      exact ifJoin_agrees_two σ c hc i ra j rb fun h => hpq (LTy.val.inj (Idx.ty_eq_of_toNat h))

/-- A joinable branch (`{ x = x + 1; }`) never diverges. -/
theorem JoinArm.runSt_noDiv (a : JoinArm C Γ) : (a.runSt σ).NoDiv := by
  rcases a with _ | ⟨p, i, r⟩
  · exact TRes.NoDiv.ok _
  · exact ((Val.evalT_ends σ r).map _).1

/-- A joined update (`{x := c ? x + 1 : x}`) pushes nothing: it is never out
of gas. -/
theorem Upd.ifJoin_pushFree (c : Tm C Γ (.val .bool)) (hc : c.pushFree = true)
    (a b : JoinArm C Γ) : (Upd.ifJoin c a b).pushFree = true := by
  rcases a with _ | ⟨p, i, ra⟩ <;> rcases b with _ | ⟨q, j, rb⟩ <;> simp only [Upd.ifJoin]
  all_goals (repeat' split) <;> simp only [Upd.pushFree, UpdElem.pushFree, Rhs.pushFree,
    Tm.pushFree, Op3.pushFree, hc, Val.lower_pushFree, Tm.castV_pushFree, Bool.and_self]

/-- **`ifElseJoin`**: an `if` whose branches are joinable runs as the joined
update; `if (se) { x = x + 1; }` as `{x := se ? x + 1 : x}`. -/
theorem sound_iteJoin (se : Simple C Γ .bool) {Γ₁ Γ₂ : Ctx} (thn : Prog C Γ Γ₁)
    (els : Prog C Γ Γ₂) {U : Upd C Γ Γ} (h : Upd.ifJoin? se.lower thn els = some U) :
    Premise.Runs m (.ite (.simple se) thn els) (.update U) σ := by
  unfold Upd.ifJoin? at h
  split at h
  next a b ha hb =>
    cases h
    have hr : Stmt.runSt σ (.ite (.simple se) thn els) =
        if boolT (se.evalT σ) then a.runSt σ else b.runSt σ := by
      rw [Stmt.runSt_ite_simple, Prog.joinArm?_runSt σ thn ha, Prog.joinArm?_runSt σ els hb]
    have hag := ifJoin_agrees σ se.lower (Simple.lower_evalT σ se) a b
    have hnd : (if boolT (se.evalT σ) then a.runSt σ else b.runSt σ).NoDiv := by
      split
      · exact JoinArm.runSt_noDiv σ a
      · exact JoinArm.runSt_noDiv σ b
    apply Premise.sound_update σ
    · intro τ hτ
      rw [hr] at hτ
      rw [hτ] at hag
      exact hag
    · intro e he
      rw [hr] at he
      rw [he] at hag hnd
      cases e with
      | revert =>
        refine ⟨nofun, fun _ _ => ⟨?_, Upd.exh_of_pushFree
          (Upd.ifJoin_pushFree _ (Simple.lower_pushFree se) a b)⟩⟩
        have hag' : (Upd.ifJoin se.lower a b).applyP σ = none := hag
        exact Option.map_eq_none_iff.1 hag'
      | panic => exact hag.elim
      | revertWith _ => exact hag.elim
      | diverge => exact absurd rfl hnd
      | exhausted => exact ⟨nofun, fun _ hx => absurd rfl hx⟩
  next => cases h

/-- **An `if`** (`iteStep`). -/
theorem iteStep_sound (k : Nat) {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (thn : Prog C Γ Γ₁)
    (els : Prog C Γ Γ₂) (q : Premise C Γ Γ) (hs : iteStep k c thn els = q) :
    Premise.Runs m (.ite c thn els) q σ := by
  cases c with
  | simple se =>
    simp only [iteStep] at hs
    split at hs
    next U hj => cases hs; exact sound_iteJoin σ se thn els hj
    cases hs
    refine Premise.sound_split σ (fun h => ?_) (fun h => ?_) ?_ (fun h J o he => ?_)
      (fun h J o he => ?_)
    · rw [Stmt.runSt_ite_simple, (holds_isBool σ se true).1 h]; rfl
    · rw [Stmt.runSt_ite_simple, (holds_isBool σ se false).1 h]; rfl
    · cases hv : se.evalT σ
      · exact .inr ((holds_isBool σ se false).2 hv)
      · exact .inl ((holds_isBool σ se true).2 hv)
    · have hv := (holds_isBool σ se true).1 h
      cases he with
      | det hf => nomatch hf
      | iteHalt hc => nomatch hc
      | iteThen _ hP => exact ⟨_, hP, rfl⟩
      | iteElse hc _ =>
        have hc : se.evalT σ = false := Except.ok.inj hc
        rw [hv] at hc; nomatch hc
    · have hv := (holds_isBool σ se false).1 h
      cases he with
      | det hf => nomatch hf
      | iteHalt hc => nomatch hc
      | iteThen hc _ =>
        have hc : se.evalT σ = true := Except.ok.inj hc
        rw [hv] at hc; nomatch hc
      | iteElse _ hP => exact ⟨_, hP, rfl⟩
  | _ => cases hs; exact sound_iteCapture σ _ thn els _

/-- `requireConditionCapture`: `⟨[ require(nse); ]⟩ ⇝ ⟨[ bool se = nse; require(se); ]⟩`. -/
theorem sound_requireCapture (c : Val C Γ .bool) (x : Var) :
    Premise.Runs m (.require c) (.capture .bool x c (.require (.simple (.local .here)))) σ := by
  refine Premise.sound_capturePushed σ
    (fun v hv => TRun.require_pushT σ (t := .val .bool) v _ c (by rw [hv]; rfl)) (fun h hh => ?_)
  show (TRun.require c σ).map _ = _
  simp only [TRun.require, hh]; rfl

/-- **A `require`** (`requireStep`): `requireSimple`, or the condition
captured. -/
theorem requireStep_sound (k : Nat) (c : Val C Γ .bool) (q : Premise C Γ Γ)
    (hs : requireStep k c = q) : Premise.Runs m (.require c) q σ := by
  cases c with
  | simple se =>
    cases hs
    refine Premise.sound_split σ (fun h => ?_) (fun h => ?_) ?_
      (fun h => ExecS.split_det σ rfl rfl ?_) (fun h => ExecS.split_det σ rfl rfl ?_)
    · show (Prog.runSt σ .nil).map _ = (TRun.require (.simple se) σ).map _
      simp only [TRun.require, Val.evalT, ok_bind, (holds_isBool σ se true).1 h]; rfl
    · show (Prog.runSt σ (.cons .revert .nil)).map _ = (TRun.require (.simple se) σ).map _
      simp only [TRun.require, Val.evalT, ok_bind, (holds_isBool σ se false).1 h]; rfl
    · cases hv : se.evalT σ
      · exact .inr ((holds_isBool σ se false).2 hv)
      · exact .inl ((holds_isBool σ se true).2 hv)
    · show (Prog.runSt σ .nil).map _ = (TRun.require (.simple se) σ).map _
      simp only [TRun.require, Val.evalT, ok_bind, (holds_isBool σ se true).1 h]; rfl
    · show (Prog.runSt σ (.cons .revert .nil)).map _ = (TRun.require (.simple se) σ).map _
      simp only [TRun.require, Val.evalT, ok_bind, (holds_isBool σ se false).1 h]; rfl
  | _ => cases hs; exact sound_requireCapture σ _ _

/-- `assertConditionCapture`: `⟨[ assert(nse); ]⟩ ⇝ ⟨[ bool se = nse; assert(se); ]⟩`. -/
theorem sound_assertCapture (c : Val C Γ .bool) (x : Var) :
    Premise.Runs m (.assert c) (.capture .bool x c (.assert (.simple (.local .here)))) σ := by
  refine Premise.sound_capturePushed σ
    (fun v hv => TRun.assert_pushT σ (t := .val .bool) v _ c (by rw [hv]; rfl)) (fun h hh => ?_)
  show (TRun.assert c σ).map _ = _
  simp only [TRun.assert, hh]; rfl

/-- **An `assert`** (`assertStep`): `assertSimple`, or the condition
captured. -/
theorem assertStep_sound (k : Nat) (c : Val C Γ .bool) (q : Premise C Γ Γ)
    (hs : assertStep k c = q) : Premise.Runs m (.assert c) q σ := by
  cases c with
  | simple se =>
    cases hs
    refine Premise.sound_check σ fun h => ?_
    show (TRun.assert (.simple se) σ).map _ = _
    simp only [TRun.assert, Val.evalT, ok_bind, (holds_isBool σ se true).1 h]; rfl
  | _ => cases hs; exact sound_assertCapture σ _ _

/-! ### Declarations, `revert`, blocks -/

/-- `localValueDeclInitDrop`: `⟨[ T v = e; ]⟩ ⇝ ⟨[ v = e; ]⟩`, `v` bound by
the hidden binder. -/
theorem sound_localValueDeclInitDrop {p : PrimTy} (x : Var) (e : Val C Γ p) :
    Premise.Runs m (.declLocal p x (some e))
      (.bind x (.val p) (.cons (.assignLocal .here e.up) .nil)) σ := by
  refine Premise.sound_bind_all σ fun v => ?_
  rw [Prog.runSt_single, Stmt.runSt_assignLocal, Stmt.runSt_declLocal, Val.evalT_up]
  cases e.evalT σ <;> rfl

/-- `storageLocalDeclInitDrop`: `⟨[ T storage lsv = r; ]⟩ ⇝ ⟨[ lsv = r; ]⟩`. -/
theorem sound_declStorageInit {R : RefTy} (x : Var) (r : ARhs C Γ R) :
    Premise.Runs m (.declStorage R x (some r))
      (.bind x (.alias R) (.cons (.rebind .here r.up) .nil)) σ := by
  refine Premise.sound_bind_all σ fun v => ?_
  rw [Prog.runSt_single]
  show (TRun.rebind .here r.up (σ.push v)).map _ = (TRun.declStorage R (some r) σ).map _
  simp only [TRun.rebind, TRun.declStorage, ARhs.evalT_up]
  cases r.evalT σ <;> rfl

/-- `memoryLocalDeclInitDrop`: `⟨[ T memory mv = r; ]⟩ ⇝ ⟨[ mv = r; ]⟩`.  The
premise's run from any value of `mv`, an unset one among them (decision
17'), is the statement's: `mv = r;` reads nothing of `mv` before it sets it.
An alias `T memory mv = mp;` is the same rule. -/
theorem sound_declMemInit {R : RefTy} (x : Var) (r : MRhs C Γ R)
    (hd : ((some r).isSome || (Ty.ref R).defaultOkS) = true) (hm : (Ty.ref R).mapFree = true) :
    Premise.Runs m (.declMem R x (some r) hd hm)
      (.bind x (.mem R) (.cons (.rebindMem .here r.up) .nil)) σ := by
  refine Premise.sound_bind_all σ fun v => ?_
  rw [Prog.runSt_single]
  show (TRun.rebindMem .here r.up (σ.push v)).map _ = (TRun.declMem R (some r) hm σ).map _
  simp only [TRun.rebindMem, TRun.declMem, MRhs.evalT_up]
  cases r.evalT σ <;> rfl

/-- A block, its locals popped after it: `⟨[ { body } ]⟩ ⇝ ⟨[ body ]⟩`. -/
theorem sound_block {Γ₂ : Ctx} (body : Prog C Γ Γ₂) :
    Premise.Runs m (.block body) (.unfold body body.ext) σ :=
  Premise.sound_unfold σ (Stmt.runSt_block σ body).symm

/-- `recursiveCallUnfold` (Lean only): a recursive call runs as the call of
its body (`Stmt.run_callRec`). -/
theorem sound_recursiveCallUnfold {ps rs : Ctx} (f : Name) (d : Nat) (args : Args C Γ ps)
    (ret : CallRet Γ rs Γ') (body : Unit → Prog C (rs ++ ps) (rs ++ ps)) :
    Premise.Runs m (.callRec f d args ret body)
      (.unfold (.cons (.call f args ret (body ())) .nil) .refl) σ :=
  Premise.sound_unfold σ (by
    rw [Prog.runSt_single]
    show (Stmt.runSt σ (.call f args ret (body ()))).map _ = Stmt.runSt σ (.call f args ret (body ()))
    cases Stmt.runSt σ (.call f args ret (body ())) <;> rfl)

end Control

end Solidity
