import Solidity.Calculus.Core.SoundArms
import Solidity.Calculus.Core.SoundCapture
import Solidity.Calculus.Core.SoundKit

/-!
# The rules of calls and `try` are sound

`Calculus/Core/Blocks.lean`'s `callStep` and `tryStep` against the typed run
(`Stmt.trun`, `TRun.call`, `TRun.tryCall`), in the shape of
`Calculus/Core/SoundKit.lean` (`Premise.Sound`).

* **`expand_function_body`.**  The parameters declared with the arguments
  (`Args.trunSt_declsThen`), the return variables at their defaults
  (`Binders.trunSt_declsThen`), the body weakened by `Thin.atop` run as the
  body in its own frame (`Stmt.trun_block_wk`, from `Prog.trun_wk`): the
  frame's state lifted is the caller's with the frame pushed
  (`TEnv.put_atop`), and the caller's locals come out weakened along the
  heap the body grew, as `TRun.call` gives them back.
* **`functionCallArgCapture`.**  The arguments with one captured read as
  before (`Args.evalT_capture`).
* **`try`** under the box: each clause's goal, for every typed value its
  outcome binds (`holds_binders_all`), is the run of that clause.
-/

namespace Solidity.Core
open Semantics (Value Res Halt)
open Solidity (Modality)

variable {C : Contract}

/-! ## The arguments -/

section Args

variable {Γ : Ctx}

theorem Args.capture_snoc {ps : Ctx} (as : Args C Γ ps) (p : PrimTy) (x : Var) (e : Val C Γ p) :
    (Args.snoc as p x e).capture = match as.capture with
      | some ⟨p', v, as'⟩ => some ⟨p', v, .snoc as' p x e.up⟩
      | none => if e.isSimple then none else
          some ⟨p, e, .snoc as.up p x (.simple (.local .here))⟩ := rfl

end Args

/-! ## A body run in its frame -/

theorem Res.ok_bind {α β : Type} (a : α) (f : α → Res β) : (Except.ok a : Res α) >>= f = f a := rfl

theorem Res.ok_bind' {α β : Type} (a : α) (f : α → Res β) :
    Except.bind (Except.ok a : Res α) f = f a := rfl

open Semantics (lookupBy)
open Solidity (Modality)

/-! ## Environments of a frame -/

namespace TEnv

variable {H : HTy}

theorem put_nilTo : (Γ : Ctx) → (x : TEnv C H []) → (d : TEnv C H Γ) →
    TEnv.put (Thin.nilTo Γ) x d = d
  | [], _, _ => rfl
  | _ :: Γ, x, d => congrArg (Prod.mk d.1) (put_nilTo Γ x d.2)

/-- A frame's locals put over the caller's: the frame on top. -/
theorem put_atop {Γ : Ctx} : (ps : Ctx) → (x : TEnv C H ps) → (d : TEnv C H (ps ++ Γ)) →
    TEnv.put (Thin.atop ps Γ) x d = TEnv.append ps x (TEnv.drop (Ext.append Γ ps) d)
  | [], x, d => put_nilTo Γ x d
  | _ :: ps, x, d => congrArg (Prod.mk x.1) (put_atop ps x.2 d.2)

theorem append_take_drop {Γ : Ctx} : (ρ : Ctx) → (e : TEnv C H (ρ ++ Γ)) →
    TEnv.append ρ (TEnv.take ρ e) (TEnv.drop (Ext.append Γ ρ) e) = e
  | [], _ => rfl
  | _ :: ρ, e => congrArg (Prod.mk e.1) (append_take_drop ρ e.2)

theorem thin_ofExt {Γ : Ctx} : {Δ : Ctx} → (h : Ext Γ Δ) → (e : TEnv C H Δ) →
    TEnv.thin (Thin.ofExt h) e = TEnv.drop h e
  | _, .refl, _ => rfl
  | _, .push h, e => thin_ofExt h e.2

theorem thin_keepAll {Γ Δ : Ctx} (h : Thin Γ Δ) : (ρ : Ctx) → (r : TEnv C H ρ) →
    (e : TEnv C H Δ) → TEnv.thin (Thin.keepAll ρ h) (TEnv.append ρ r e) =
      TEnv.append ρ r (TEnv.thin h e)
  | [], _, _ => rfl
  | _ :: ρ, r, e => congrArg (Prod.mk r.1) (thin_keepAll h ρ r.2 e)

theorem drop_set_under {Γ : Ctx} {t : LTy} (j : Idx Γ t) (v : t.TDenote C H) :
    (ρ : Ctx) → (e : TEnv C H (ρ ++ Γ)) →
      TEnv.drop (Ext.append Γ ρ) (TEnv.set (j.under ρ) v e) =
        TEnv.set j v (TEnv.drop (Ext.append Γ ρ) e)
  | [], _ => rfl
  | _ :: ρ, e => drop_set_under j v ρ e.2

/-- The caller's locals under a frame put on top, over a grown heap. -/
theorem drop_put_atop_wk {Γ : Ctx} {H' : HTy} (e : H <+: H') (ρ : Ctx) (x : TEnv C H' ρ)
    (a : TEnv C H ρ) (g : TEnv C H Γ) :
    TEnv.drop (Ext.append Γ ρ)
        (TEnv.put (Thin.atop ρ Γ) x (TEnv.wk e (ρ ++ Γ) (TEnv.append ρ a g))) =
      TEnv.wk e Γ g := by
  rw [put_atop, drop_append, append_wk, drop_append]

/-- The frame dropped from under the return variables it leaves, over a
grown heap. -/
theorem thin_put_keepAllAtop {Γ : Ctx} {rs ps : Ctx} {H' : HTy} (e : H <+: H')
    (x : TEnv C H' (rs ++ ps)) (r : TEnv C H rs) (a : TEnv C H ps) (g : TEnv C H Γ) :
    TEnv.thin (Thin.keepAll rs (Thin.ofExt (Ext.append Γ ps)))
        (TEnv.put (Thin.keepAll rs (Thin.atop ps Γ)) x
          (TEnv.wk e (rs ++ (ps ++ Γ)) (TEnv.append rs r (TEnv.append ps a g)))) =
      TEnv.append rs (TEnv.take rs x) (TEnv.wk e Γ g) := by
  conv => lhs; rw [← append_take_drop rs x]
  rw [append_wk, put_keepAll, put_atop, append_wk, drop_append, thin_keepAll, thin_ofExt,
    drop_append]

/-- The frame dropped from under a memory return, over a heap grown twice
(the object, then the body). -/
theorem thin_keep_put_atop {Γ ps : Ctx} {t : LTy} {H₂ H₃ : HTy} (e₁ : H <+: H₂)
    (e₂ : H₂ <+: H₃) (x : TEnv C H₃ (t :: ps)) (w : t.TDenote C H₂) (a : TEnv C H ps)
    (g : TEnv C H Γ) :
    TEnv.thin (Thin.keep (Thin.ofExt (Ext.append Γ ps)))
        (TEnv.put (Thin.atop (t :: ps) Γ) x
          (TEnv.wk e₂ (t :: (ps ++ Γ)) (w, TEnv.wk e₁ (ps ++ Γ) (TEnv.append ps a g)))) =
      (x.1, TEnv.wk (e₁.trans e₂) Γ g) := by
  show (x.1, TEnv.thin (Thin.ofExt (Ext.append Γ ps))
    (TEnv.put (Thin.atop ps Γ) x.2 (TEnv.wk e₂ _ (TEnv.wk e₁ _ (TEnv.append ps a g))))) = _
  rw [thin_ofExt, wk_trans, drop_put_atop_wk]

end TEnv

/-! ## Runs of the pieces an inlined call is made of -/

section Pieces

variable {Γ : Ctx}

theorem TState.withEnv_self (σ : TState C Γ) : σ.withEnv σ.env = σ := rfl

theorem Val.evalT_unders {p : PrimTy} (v : Val C Γ p) (σ : TState C Γ) :
    (ρ : Ctx) → (r : TEnv C σ.H ρ) →
      (v.unders ρ).evalT (σ.withEnv (TEnv.append ρ r σ.env)) = v.evalT σ
  | [], _ => rfl
  | _ :: ρ, r => by
    show ((v.unders ρ).up).evalT ((σ.withEnv (TEnv.append ρ r.2 σ.env)).push r.1) = _
    rw [Val.evalT_up, Val.evalT_unders v σ ρ r.2]

theorem Stmt.trunSt_declLocal_none (p : PrimTy) (x : Var) (σ : TState C Γ) :
    Stmt.trunSt σ (.declLocal p x none) = .ok (σ.push (t := .val p) (PrimTy.dflt p)) := rfl

theorem Args.evalT_snoc (σ : TState C Γ) {ps : Ctx} (as : Args C Γ ps) (p : PrimTy) (x : Var)
    (e : Val C Γ p) :
    (Args.snoc as p x e).evalT σ = as.evalT σ >>= fun r => e.evalT σ >>= fun v => pure (v, r) :=
  rfl

theorem Args.evalT_up {t : LTy} (σ : TState C Γ) (w : t.TDenote C σ.H) : {ps : Ctx} →
    (as : Args C Γ ps) → (as.up (t := t)).evalT (σ.push w) = as.evalT σ
  | _, .nil => rfl
  | _, .snoc as p x e => by
    show (Args.snoc (as.up (t := t)) p x e.up).evalT (σ.push w) = _
    rw [Args.evalT_snoc, Args.evalT_snoc, Args.evalT_up σ w as, Val.evalT_up]
    rfl

/-- Arguments that are all simple read without halting. -/
theorem Args.evalT_ok (σ : TState C Γ) : {ps : Ctx} → (as : Args C Γ ps) → as.capture = none →
    ∃ a, as.evalT σ = .ok a
  | _, .nil, _ => ⟨(), rfl⟩
  | _, .snoc as p x e, h => by
    rw [Args.capture_snoc] at h
    cases hc : as.capture with
    | some q => rw [hc] at h; cases h
    | none =>
      rw [hc] at h
      obtain ⟨a, ha⟩ := Args.evalT_ok σ as hc
      cases e with
      | simple s =>
        refine ⟨(s.evalT σ, a), ?_⟩
        rw [Args.evalT_snoc, ha]
        rfl
      | _ => simp only [Val.isSimple, Bool.false_eq_true, if_false, reduceCtorEq] at h

/-- **The arguments with one captured** read as the captured value, then the
arguments over it. -/
theorem Args.evalT_capture (σ : TState C Γ) : {ps : Ctx} → (as : Args C Γ ps) →
    ∀ {p : PrimTy} {v : Val C Γ p} {as' : Args C (.val p :: Γ) ps},
      as.capture = some ⟨p, v, as'⟩ →
        as.evalT σ = v.evalT σ >>= fun w => as'.evalT (σ.push (t := .val p) w)
  | _, .nil, _, _, _, h => by cases h
  | _, .snoc as p' x e, p, v, as', h => by
    rw [Args.capture_snoc] at h
    cases hc : as.capture with
    | some q =>
      obtain ⟨p₀, v₀, as₀⟩ := q
      rw [hc] at h
      dsimp only at h
      cases h
      rw [Args.evalT_snoc, Args.evalT_capture σ as hc]
      cases v.evalT σ with
      | error => rfl
      | ok w =>
        show _ = Args.evalT (σ.push (t := .val p) w) (Args.snoc as₀ p' x e.up)
        rw [Args.evalT_snoc, Val.evalT_up]
        rfl
    | none =>
      rw [hc] at h
      dsimp only at h
      split at h
      · cases h
      · cases h
        obtain ⟨a, ha⟩ := Args.evalT_ok σ as hc
        rw [Args.evalT_snoc, ha]
        cases e.evalT σ with
        | error => rfl
        | ok w =>
          show _ = (Args.snoc (as.up (t := .val p')) p' x (.simple (.local .here))).evalT
            (σ.push (t := .val p') w)
          rw [Args.evalT_snoc, Args.evalT_up, ha]
          rfl

/-- **The parameters declared** with the arguments: the arguments read, then
the rest with them on top. -/
theorem Args.trunSt_declsThen {Δ : Ctx} (σ : TState C Γ) : {ps : Ctx} → (as : Args C Γ ps) →
    (rest : Prog C (ps ++ Γ) Δ) →
      Prog.trunSt σ (as.declsThen rest) =
        (as.evalT σ).bind fun a => Prog.trunSt (σ.withEnv (TEnv.append ps a σ.env)) rest
  | _, .nil, rest => rfl
  | _, .snoc (ps := ps') as p x e, rest => by
    show Prog.trunSt σ (as.declsThen (.cons (.declLocal p x (some (e.unders ps'))) rest)) = _
    rw [Args.trunSt_declsThen σ as]
    show _ = (Args.evalT σ as >>= fun r => e.evalT σ >>= fun v => pure (v, r)).bind _
    cases as.evalT σ with
    | error => rfl
    | ok a =>
      show Prog.trunSt _ (.cons _ rest) = (e.evalT σ >>= fun v => pure (v, a)).bind _
      rw [Prog.trunSt_cons, Stmt.trunSt_declLocal, Val.evalT_unders]
      cases e.evalT σ <;> rfl

/-- **The return variables declared** at their defaults. -/
theorem Binders.trunSt_declsThen {Δ : Ctx} (σ : TState C Γ) : {ρ : Ctx} → (bs : Binders ρ) →
    (rest : Prog C (ρ ++ Γ) Δ) →
      Prog.trunSt σ (bs.declsThen rest) =
        Prog.trunSt (σ.withEnv (TEnv.append ρ (bs.defaultsT (C := C)) σ.env)) rest
  | _, .nil, rest => rfl
  | _, .snoc (ρ := ρ') bs p x, rest => by
    show Prog.trunSt σ (bs.declsThen (.cons (.declLocal p x none) rest)) = _
    rw [Binders.trunSt_declsThen σ bs, Prog.trunSt_cons]
    rfl

/-- **A weakened body run as a block** runs as the body, lifted, its locals
popped. -/
theorem Stmt.trun_block_wk {ρ Δ Γf : Ctx} (body : Prog C ρ Γf) (h : Thin ρ Δ) (τ : TState C ρ)
    (d : TEnv C τ.H Δ) :
    Stmt.trun (τ.lift h d) (.block (body.wk h).2.2) =
      liftedT h d ((Prog.trun τ body).map (Out.drop body.ext)) :=
  (TWkRel.drop (Prog.wk_over body h) (Prog.trun_wk body h τ d)).eq_lifted

/-- The caller's state with a frame's locals pushed, read as the frame's state
lifted (`Thin.atop`). -/
theorem TState.withEnv_append_lift {ps : Ctx} (σ : TState C Γ) (a : TEnv C σ.H ps) :
    σ.withEnv (TEnv.append ps a σ.env) =
      (σ.withEnv a).lift (Thin.atop ps Γ) (TEnv.append ps a σ.env) := by
  simp only [TState.lift, TState.withEnv, TEnv.put_atop, TEnv.drop_append]

end Pieces

/-! ## `expand_function_body` -/

section Calls

variable {Γ : Ctx} {m : Modality}

/-- `internalCallExpand` of a call with no result. -/
theorem Premise.sound_callNone {ps Γf : Ctx} (f : Name) (args : Args C Γ ps)
    (body : Prog C ([] ++ ps) Γf) (σ : TState C Γ) :
    Premise.Runs m (.call f args .none body)
      (.unfold (args.declsThen (.cons (.block (body.wk (Thin.atop ps Γ)).2.2) .nil))
        (Ext.append Γ ps)) σ := by
  refine Premise.sound_unfold σ ?_
  rw [Args.trunSt_declsThen]
  show _ = (TRun.call args .none body.ext body.trunR σ).map (·.st)
  rw [TRun.call_eq]
  cases args.evalT σ with
  | error => rfl
  | ok a =>
    show (Prog.trunSt _ _).map _ =
      (TRun.callFrom .none body.ext body.trunR σ ⟨σ.withEnv a, List.prefix_refl _⟩).map _
    rw [Prog.trunSt_single, TState.withEnv_append_lift, Stmt.trunSt, Stmt.trun_block_wk]
    unfold TRun.callFrom Prog.trun
    dsimp only
    cases Prog.trunR body (σ.withEnv a) with
    | error => rfl
    | ok o =>
      exact congrArg Except.ok (by
        simp only [Out.drop, Out.lift, TState.lift, TState.drop, TState.withEnv, TEnv.put_atop,
          TEnv.drop_append, TEnv.drop_wk, CallRet.leaveT])

theorem TRes.ok_bind {α β : Type} (a : α) (f : α → TRes β) : (Except.ok a : TRes α).bind f = f a :=
  rfl

theorem TRes.ok_bind' {α β : Type} (a : α) (f : α → TRes β) : (Except.ok a : TRes α) >>= f = f a :=
  rfl

/-- `functionBodyExpand` of a call whose result lands in `res`. -/
theorem Premise.sound_callVal {ps Γf : Ctx} (f : Name) (args : Args C Γ ps) (p : PrimTy)
    (r : Var) (res : Option (Idx Γ (.val p))) (body : Prog C ([.val p] ++ ps) Γf)
    (σ : TState C Γ) :
    Premise.Runs m (.call f args (.val p r res) body)
      (.unfold (args.declsThen (.cons (.declLocal p r none)
        (.cons (.block (body.wk (Thin.atop (.val p :: ps) Γ)).2.2) (match res with
          | none => .nil
          | some j => .cons (.assignLocal (j.under ps).there (.simple (.local .here))) .nil))))
        (.push (Ext.append Γ ps))) σ := by
  refine Premise.sound_unfold σ ?_
  rw [Args.trunSt_declsThen]
  show _ = (TRun.call args (.val p r res) body.ext body.trunR σ).map (·.st)
  rw [TRun.call_eq]
  cases args.evalT σ with
  | error => rfl
  | ok a =>
    show (Prog.trunSt _ _).map _ = (TRun.callFrom (.val p r res) body.ext body.trunR σ
      ⟨σ.withEnv ((PrimTy.dflt p, a) : TEnv C σ.H (.val p :: ps)), List.prefix_refl _⟩).map _
    rw [Prog.trunSt_cons, Stmt.trunSt_declLocal_none, TRes.ok_bind, Prog.trunSt_cons,
      show (σ.withEnv (TEnv.append ps a σ.env)).push (t := .val p) (PrimTy.dflt p) =
        σ.withEnv (TEnv.append (.val p :: ps) (PrimTy.dflt p, a) σ.env) from rfl,
      TState.withEnv_append_lift (ps := .val p :: ps) σ (PrimTy.dflt p, a), Stmt.trunSt,
      Stmt.trun_block_wk]
    unfold TRun.callFrom Prog.trun
    dsimp only
    cases Prog.trunR body (σ.withEnv ((PrimTy.dflt p, a) : TEnv C σ.H (.val p :: ps))) with
    | error => rfl
    | ok o =>
      rw [show (Ext.append Γ ps).push = Ext.append Γ (LTy.val p :: ps) from rfl]
      cases res with
      | none =>
        exact congrArg Except.ok (by
          simp only [Out.drop, Out.lift, TState.lift, TState.drop, TState.withEnv, CallRet.leaveT]
          erw [TEnv.drop_put_atop_wk (Γ := Γ) _ (LTy.val p :: ps)])
      | some j =>
        exact congrArg Except.ok (by
          simp only [Out.drop, Out.lift, TState.lift, TState.drop, TState.withEnv, TState.setLocal,
            show (j.under ps).there = j.under (LTy.val p :: ps) from rfl, TEnv.drop_set_under,
            CallRet.leaveT]
          erw [TEnv.drop_put_atop_wk (Γ := Γ) _ (LTy.val p :: ps)]
          rfl)

/-- `internalCallExpand` of a call that leaves its return variables
(`CallRet.rets`): the frame dropped from under them. -/
theorem Premise.sound_callRets {ps rs Γf : Ctx} (f : Name) (args : Args C Γ ps)
    (bs : Binders rs) (body : Prog C (rs ++ ps) Γf) (σ : TState C Γ) :
    Premise.Runs m (.call f args (.rets bs) body)
      (.inline (args.declsThen (bs.declsThen
          (.cons (.block (body.wk (Thin.keepAll rs (Thin.atop ps Γ))).2.2) .nil)))
        (Thin.keepAll rs (Thin.ofExt (Ext.append Γ ps)))) σ := by
  refine Premise.sound_inline σ ?_
  rw [Args.trunSt_declsThen]
  show _ = (TRun.call args (.rets bs) body.ext body.trunR σ).map (·.st)
  rw [TRun.call_eq]
  cases args.evalT σ with
  | error => rfl
  | ok a =>
    show (Prog.trunSt _ _).map _ = (TRun.callFrom (.rets bs) body.ext body.trunR σ
      ⟨σ.withEnv (TEnv.append rs (bs.defaultsT (C := C)) a), List.prefix_refl _⟩).map _
    have hs : (σ.withEnv (TEnv.append ps a σ.env)).withEnv
        (TEnv.append rs (bs.defaultsT (C := C)) (σ.withEnv (TEnv.append ps a σ.env)).env) =
        (σ.withEnv (TEnv.append rs (bs.defaultsT (C := C)) a)).lift
          (Thin.keepAll rs (Thin.atop ps Γ))
          (TEnv.append rs (bs.defaultsT (C := C)) (TEnv.append ps a σ.env)) := by
      simp only [TState.lift, TState.withEnv, TEnv.put_keepAll, TEnv.put_atop, TEnv.drop_append]
    rw [Binders.trunSt_declsThen, hs, Prog.trunSt_single, Stmt.trunSt, Stmt.trun_block_wk]
    unfold TRun.callFrom Prog.trun
    dsimp only
    cases Prog.trunR body (σ.withEnv (TEnv.append rs (bs.defaultsT (C := C)) a)) with
    | error => rfl
    | ok o =>
      exact congrArg Except.ok (by
        simp only [Out.drop, Out.lift, TState.lift, TState.drop, TState.thin, TState.withEnv,
          CallRet.leaveT]
        erw [TEnv.thin_put_keepAllAtop])

theorem Stmt.trunSt_declMem_none {Γ : Ctx} (R : RefTy) (x : Var) (hd : (Ty.ref R).defaultOkS = true)
    (hm : (Ty.ref R).mapFree = true) (σ : TState C Γ) :
    Stmt.trunSt σ (.declMem R x none hd hm) =
      .ok ((σ.allocDefaultG R hm).st.push (t := .mem R) (some (σ.allocDefaultG R hm).val)) := rfl

/-- `internalCallExpand` of a call with a memory return: the frame dropped
from under the object. -/
theorem Premise.sound_callMem {ps Γf : Ctx} (f : Name) (args : Args C Γ ps) (R : RefTy)
    (r : Var) (hd : (Ty.ref R).defaultOkS = true) (hm : (Ty.ref R).mapFree = true)
    (body : Prog C ([.mem R] ++ ps) Γf) (σ : TState C Γ) :
    Premise.Runs m (.call f args (.mem R r hd hm) body)
      (.inline (args.declsThen (.cons (.declMem R r none hd hm)
          (.cons (.block (body.wk (Thin.atop (.mem R :: ps) Γ)).2.2) .nil)))
        (.keep (Thin.ofExt (Ext.append Γ ps)))) σ := by
  refine Premise.sound_inline σ ?_
  rw [Args.trunSt_declsThen]
  show _ = (TRun.call args (.mem R r hd hm) body.ext body.trunR σ).map (·.st)
  rw [TRun.call_eq]
  cases args.evalT σ with
  | error => rfl
  | ok a =>
    let g := (σ.withEnv a).allocDefaultG R hm
    show (Prog.trunSt _ _).map _ = (TRun.callFrom (.mem R r hd hm) body.ext body.trunR σ
      ⟨g.st.push (t := .mem R) (some g.val), g.ext⟩).map _
    rw [Prog.trunSt_cons, Stmt.trunSt_declMem_none, TRes.ok_bind, TState.withEnv_append_lift,
      TState.allocDefaultG_lift, Prog.trunSt_single]
    show (Stmt.trunSt ((g.st.push (t := .mem R) (some g.val)).lift (Thin.atop (.mem R :: ps) Γ)
      (some g.val, TEnv.wk g.ext _ (TEnv.append ps a σ.env))) _).map _ = _
    rw [Stmt.trunSt, Stmt.trun_block_wk]
    unfold TRun.callFrom Prog.trun
    dsimp only
    cases Prog.trunR body (g.st.push (t := .mem R) (some g.val)) with
    | error => rfl
    | ok o =>
      exact congrArg Except.ok (by
        simp only [Out.drop, Out.lift, TState.lift, TState.drop, TState.thin, TState.withEnv,
          CallRet.leaveT]
        erw [TEnv.thin_keep_put_atop]
        rfl)

/-! ## `functionCallArgCapture` -/

/-- A call's body run from the caller with a captured value on top: what it
leaves the caller, the capture popped (`F`), is what it leaves without it. -/
theorem TRun.callFrom_capture {Γ' Γ'' ps rs Γf : Ctx} {t : LTy} (ret : CallRet Γ rs Γ')
    (ret' : CallRet (t :: Γ) rs Γ'') (hb : Ext (rs ++ ps) Γf) (B : TStep C (rs ++ ps) Γf)
    (σ : TState C Γ) (w : t.TDenote C σ.H) (o₁ : Out C σ.H (rs ++ ps))
    (F : TState C Γ'' → TState C Γ')
    (hF : ∀ (τ : TState C Γf) (e : σ.H <+: τ.H) (x : TEnv C τ.H rs),
      F (τ.withEnv (ret'.leaveT (TEnv.wk e (t :: Γ) (σ.push w).env) x)) =
        τ.withEnv (ret.leaveT (TEnv.wk e Γ σ.env) x)) :
    ((TRun.callFrom ret' hb B (σ.push w) o₁).map (·.st)).map F =
      (TRun.callFrom ret hb B σ o₁).map (·.st) := by
  unfold TRun.callFrom
  cases B o₁.st with
  | error => rfl
  | ok o => exact congrArg Except.ok (hF _ _ _)

/-- `functionCallArgCapture` (none return). -/
theorem Premise.sound_callCaptureNone {ps Γf : Ctx} (k : Nat) (f : Name) (args : Args C Γ ps)
    (body : Prog C ([] ++ ps) Γf) {p : PrimTy} {v : Val C Γ p}
    {as' : Args C (.val p :: Γ) ps} (hc : args.capture = some ⟨p, v, as'⟩) (σ : TState C Γ) :
    Premise.Runs m (.call f args .none body)
      (.capture p (fse k) v (.call f as' .none body)) σ := by
  refine Premise.sound_unfold σ ?_
  rw [Prog.trunSt_cons, Stmt.trunSt_declLocal]
  show _ = (TRun.call args .none body.ext body.trunR σ).map (·.st)
  rw [TRun.call_eq, Args.evalT_capture σ args hc, bind_assoc]
  cases v.evalT σ with
  | error => rfl
  | ok w =>
    rw [TRes.ok_bind']
    show (Prog.trunSt (σ.push (t := .val p) w) _).map _ = _
    rw [Prog.trunSt_single]
    show ((TRun.call as' .none body.ext body.trunR (σ.push (t := .val p) w)).map _).map _ = _
    rw [TRun.call_eq]
    cases as'.evalT (σ.push (t := .val p) w) with
    | error => rfl
    | ok a =>
      exact TRun.callFrom_capture (t := .val p) .none .none body.ext body.trunR σ w _
        (TState.drop (.push .refl))
        (fun _ _ _ => rfl)

/-- `functionCallArgCapture` (val return). -/
theorem Premise.sound_callCaptureVal {ps Γf : Ctx} (k : Nat) (f : Name) (args : Args C Γ ps)
    (q : PrimTy) (r : Var) (res : Option (Idx Γ (.val q)))
    (body : Prog C ([.val q] ++ ps) Γf) {p : PrimTy} {v : Val C Γ p}
    {as' : Args C (.val p :: Γ) ps} (hc : args.capture = some ⟨p, v, as'⟩) (σ : TState C Γ) :
    Premise.Runs m (.call f args (.val q r res) body)
      (.capture p (fse k) v (.call f as' (.val q r (res.map .there)) body)) σ := by
  refine Premise.sound_unfold σ ?_
  rw [Prog.trunSt_cons, Stmt.trunSt_declLocal]
  show _ = (TRun.call args (.val q r res) body.ext body.trunR σ).map (·.st)
  rw [TRun.call_eq, Args.evalT_capture σ args hc, bind_assoc]
  cases v.evalT σ with
  | error => rfl
  | ok w =>
    rw [TRes.ok_bind']
    show (Prog.trunSt (σ.push (t := .val p) w) _).map _ = _
    rw [Prog.trunSt_single]
    show ((TRun.call as' (.val q r (res.map .there)) body.ext body.trunR
      (σ.push (t := .val p) w)).map _).map _ = _
    rw [TRun.call_eq]
    cases as'.evalT (σ.push (t := .val p) w) with
    | error => rfl
    | ok a =>
      exact TRun.callFrom_capture (t := .val p) (.val q r res) (.val q r (res.map .there))
        body.ext body.trunR σ w _
        (TState.drop (.push .refl))
        (fun _ _ _ => by cases res <;> rfl)

/-- `functionCallArgCapture` (rets return). -/
theorem Premise.sound_callCaptureRets {ps rs Γf : Ctx} (k : Nat) (f : Name) (args : Args C Γ ps)
    (bs : Binders rs) (body : Prog C (rs ++ ps) Γf) {p : PrimTy} {v : Val C Γ p}
    {as' : Args C (.val p :: Γ) ps} (hc : args.capture = some ⟨p, v, as'⟩) (σ : TState C Γ) :
    Premise.Runs m (.call f args (.rets bs) body)
      (.inline (.cons (.declLocal p (fse k) (some v)) (.cons (.call f as' (.rets bs) body) .nil))
        (Thin.keepAll rs (.drop .refl))) σ := by
  refine Premise.sound_inline σ ?_
  rw [Prog.trunSt_cons, Stmt.trunSt_declLocal]
  show _ = (TRun.call args (.rets bs) body.ext body.trunR σ).map (·.st)
  rw [TRun.call_eq, Args.evalT_capture σ args hc, bind_assoc]
  cases v.evalT σ with
  | error => rfl
  | ok w =>
    rw [TRes.ok_bind']
    show (Prog.trunSt (σ.push (t := .val p) w) _).map _ = _
    rw [Prog.trunSt_single]
    show ((TRun.call as' (.rets bs) body.ext body.trunR (σ.push (t := .val p) w)).map _).map _ = _
    rw [TRun.call_eq]
    cases as'.evalT (σ.push (t := .val p) w) with
    | error => rfl
    | ok a =>
      exact TRun.callFrom_capture (t := .val p) (.rets bs) (.rets bs) body.ext body.trunR σ w _
        (TState.thin (Thin.keepAll rs (.drop .refl)))
        (fun _ _ _ => by
          simp only [TState.thin, TState.withEnv, CallRet.leaveT]
          erw [TEnv.thin_keepAll]
          rfl)

/-- `functionCallArgCapture` (mem return). -/
theorem Premise.sound_callCaptureMem {ps Γf : Ctx} (k : Nat) (f : Name) (args : Args C Γ ps)
    (R : RefTy) (r : Var) (hd : (Ty.ref R).defaultOkS = true)
    (hm : (Ty.ref R).mapFree = true) (body : Prog C ([.mem R] ++ ps) Γf) {p : PrimTy}
    {v : Val C Γ p}
    {as' : Args C (.val p :: Γ) ps} (hc : args.capture = some ⟨p, v, as'⟩) (σ : TState C Γ) :
    Premise.Runs m (.call f args (.mem R r hd hm) body)
      (.inline (.cons (.declLocal p (fse k) (some v))
          (.cons (.call f as' (.mem R r hd hm) body) .nil))
        (.keep (.drop .refl))) σ := by
  refine Premise.sound_inline σ ?_
  rw [Prog.trunSt_cons, Stmt.trunSt_declLocal]
  show _ = (TRun.call args (.mem R r hd hm) body.ext body.trunR σ).map (·.st)
  rw [TRun.call_eq, Args.evalT_capture σ args hc, bind_assoc]
  cases v.evalT σ with
  | error => rfl
  | ok w =>
    rw [TRes.ok_bind']
    show (Prog.trunSt (σ.push (t := .val p) w) _).map _ = _
    rw [Prog.trunSt_single]
    show ((TRun.call as' (.mem R r hd hm) body.ext body.trunR
      (σ.push (t := .val p) w)).map _).map _ = _
    rw [TRun.call_eq]
    cases as'.evalT (σ.push (t := .val p) w) with
    | error => rfl
    | ok a =>
      exact TRun.callFrom_capture (t := .val p) (.mem R r hd hm) (.mem R r hd hm)
        body.ext body.trunR σ w _
        (TState.thin (.keep (.drop .refl)))
        (fun _ _ _ => rfl)

/-- **The rule of a call is sound** over the typed state: its leftmost
argument that is not simple captured, or its body inlined. -/
theorem Stmt.sound_call (k : Nat) (m : Modality) {Γ' ps rs Γf : Ctx} (f : Name)
    (args : Args C Γ ps) (ret : CallRet Γ rs Γ') (body : Prog C (rs ++ ps) Γf) (σ : TState C Γ)
    (pr : Premise C Γ Γ') (hp : Stmt.step k m (.call f args ret body) = some pr) :
    Premise.Runs m (.call f args ret body) pr σ := by
  change callStep k f args ret body = some pr at hp
  unfold callStep at hp
  cases ret with
  | none =>
    dsimp only at hp
    cases hc : args.capture with
    | some q =>
      obtain ⟨p, v, as'⟩ := q
      rw [hc] at hp; cases hp
      exact Premise.sound_callCaptureNone k f args body hc σ
    | none =>
      rw [hc] at hp; cases hp
      exact Premise.sound_callNone f args body σ
  | val q r res =>
    dsimp only at hp
    cases hc : args.capture with
    | some x =>
      obtain ⟨p, v, as'⟩ := x
      rw [hc] at hp; cases hp
      exact Premise.sound_callCaptureVal k f args q r res body hc σ
    | none =>
      rw [hc] at hp; cases hp
      cases res with
      | none => exact Premise.sound_callVal f args q r none body σ
      | some j => exact Premise.sound_callVal f args q r (some j) body σ
  | rets bs =>
    dsimp only at hp
    cases hc : args.capture with
    | some x =>
      obtain ⟨p, v, as'⟩ := x
      rw [hc] at hp; cases hp
      exact Premise.sound_callCaptureRets k f args bs body hc σ
    | none =>
      rw [hc] at hp; cases hp
      exact Premise.sound_callRets f args bs body σ
  | mem R r hd hm =>
    dsimp only at hp
    cases hc : args.capture with
    | some x =>
      obtain ⟨p, v, as'⟩ := x
      rw [hc] at hp; cases hp
      exact Premise.sound_callCaptureMem k f args R r hd hm body hc σ
    | none =>
      rw [hc] at hp; cases hp
      exact Premise.sound_callMem f args R r hd hm body σ

end Calls

/-! ## `try` -/

section Try

variable {Γ : Ctx}

/-- Decoding reverts, never panics. -/
theorem Binders.decodeT_ne_panic {H : HTy} {ρ : Ctx} (bs : Binders ρ) :
    ∀ (vs : List Semantics.Value), bs.decodeT (C := C) (H := H) vs ≠ .error .panic := by
  induction bs with
  | nil => intro _ h; cases h
  | snoc bs p x ih =>
    intro vs h
    have hb : Binders.decodeT (C := C) (H := H) (Binders.snoc bs p x) vs =
        (bs.decodeT (C := C) (H := H) vs >>= fun er => match er.2 with
          | v :: rest => match PrimTy.ofValue? p v with
            | some x => pure ((x, er.1), rest)
            | none => .error .revert
          | [] => .error .revert) := rfl
    rw [hb] at h
    cases hd : bs.decodeT (C := C) (H := H) vs with
    | error e => rw [hd] at h; cases h; exact ih vs hd
    | ok er =>
      rw [hd] at h
      obtain ⟨e, rest⟩ := er
      cases rest with
      | nil => cases h
      | cons v rest =>
        change (match PrimTy.ofValue? p v with
          | some x => pure ((x, e), rest)
          | none => Except.error THalt.revert : TRes _) = _ at h
        split at h <;> cases h

theorem CodeBinder.decodeT_ne_panic {H : HTy} {κ : Ctx} (code : CodeBinder κ)
    (c : Semantics.Value) : code.decodeT (C := C) (H := H) c ≠ .error .panic := by
  cases code with
  | none => intro h; cases h
  | some x =>
    intro h
    change (match PrimTy.ofValue? .uint c with
      | Option.some x => pure (x, ())
      | Option.none => Except.error THalt.revert : TRes _) = _ at h
    split at h <;> cases h

/-- `∀ xs. ψ` holds at every typed value of the binders. -/
theorem holds_binders_all {ρ : Ctx} (bs : Binders ρ) :
    ∀ (σ : TState C Γ) (ψ : Fml C (ρ ++ Γ)) (r : TEnv C σ.H ρ), holds σ (bs.all ψ) →
      holds (σ.withEnv (TEnv.append ρ r σ.env)) ψ := by
  induction bs with
  | nil => intro σ ψ _ h; exact h
  | snoc bs p x ih =>
    intro σ ψ r h
    exact ih σ (.all x p ψ) r.2 h r.1

/-- A block's goal under the box, its locals popped by `h`: the block's run,
then the rest. -/
theorem holds_modalK_pop {Γ₂ Γ₀ Δ Γ₁ : Ctx} (τ : TState C Δ) (P : Prog C Δ Γ₁) (h : Ext Γ Γ₁)
    (ω : Prog C Γ Γ₂) (κ : Frames C Γ₂ Γ₀) (φ : Fml C Γ₀)
    (hp : holds τ (Fml.modalK .box P (.pop .block h (.seq ω κ)) φ)) :
    Modality.afterRunTR .box (holds · φ)
      (((Prog.trunSt τ P).map (TState.drop h)).bind fun υ =>
        (Prog.trunSt υ ω).bind (Frames.trunSt · κ)) := by
  have h' := (holds_modal_iff τ P _ φ).1 (holds_modalK τ P _ φ hp)
  revert h'
  cases Prog.trunSt τ P with
  | error => exact id
  | ok υ =>
    intro h'
    change Modality.afterRunTR .box _ (Frames.trunSt υ (.pop .block h (.seq ω κ))) at h'
    rw [Frames.trunSt_pop, Frames.trunSt_seq] at h'
    exact h'

/-- An outcome's states, each mapped, read through the states. -/
theorem TRes.map_st {H : HTy} {Δ Γ' : Ctx} (X : TRes (Out C H Δ)) (f : Out C H Δ → Out C H Γ')
    (g : TState C Δ → TState C Γ') (hfg : ∀ o, (f o).st = g o.st) :
    (X.map f).map (·.st) = (X.map (·.st)).map g := by
  cases X with
  | error => rfl
  | ok o => exact congrArg Except.ok (hfg o)

/-- A halt that is no panic, under the box. -/
theorem afterRunTR_box_error {Γ₂ Γ₀ : Ctx} {ω : Prog C Γ Γ₂} {κ : Frames C Γ₂ Γ₀} {φ : Fml C Γ₀}
    {e : THalt} (he : e ≠ .panic) :
    Modality.afterRunTR .box (holds · φ)
      ((Except.error e : TRes (TState C Γ)).bind fun υ =>
        (Prog.trunSt υ ω).bind (Frames.trunSt · κ)) :=
  ⟨trivial, fun h => he (Except.error.inj h)⟩

/-- `tryCallNoCallbackBox`: under the box, a goal per clause, each for every
typed value its outcome binds. -/
theorem Premise.sound_tryCallBox {ρ κc Γ₁ Γe Γ₃ Γ₄ : Ctx} (call : ExtCall C Γ)
    (rets : Binders ρ) (ok : Prog C (ρ ++ Γ) Γ₁) (err : Prog C Γ Γe) (code : CodeBinder κc)
    (pnc : Prog C (κc ++ Γ) Γ₃) (other : Prog C Γ Γ₄) (σ : TState C Γ) :
    Premise.Runs .box (.tryCall call rets ok err code pnc other)
      (.branches [⟨rets, ok⟩, ⟨Binders.nil, err⟩, ⟨code.binders, pnc⟩, ⟨Binders.nil, other⟩])
      σ := by
  intro _ _ ω κ φ
  rintro ⟨h1, h2, h3, h4⟩
  rw [holds_modal_iff, trunSt_cons_frames]
  show Modality.afterRunTR .box _ (((TRun.tryCall call rets ok.ext ok.trunR err.ext err.trunR
    code pnc.ext pnc.trunR other.ext other.trunR σ).map (·.st)).bind _)
  unfold TRun.tryCall
  cases lookupBy (call.keyT σ) σ.tx.ext with
  | none => exact afterRunTR_box_error (by decide)
  | some res =>
    cases res with
    | ok vs =>
      dsimp only
      cases hd : rets.decodeT (C := C) (H := σ.H) vs with
      | error e => exact afterRunTR_box_error (fun he => rets.decodeT_ne_panic vs (he ▸ hd))
      | ok p =>
        obtain ⟨r, rest⟩ := p
        rw [TRes.ok_bind']
        dsimp only
        rw [TRes.map_st _ _ (TState.drop ((Ext.append Γ ρ).trans ok.ext)) fun _ => rfl]
        exact holds_modalK_pop _ ok _ ω κ φ (holds_binders_all rets σ _ r h1)
    | error =>
      dsimp only
      have h2' := holds_modalK_pop σ err ((Ext.append Γ []).trans err.ext) ω κ φ h2
      rw [show (Ext.append Γ []).trans err.ext = err.ext from Subsingleton.elim _ _] at h2'
      rw [TRes.map_st _ _ (TState.drop err.ext) fun _ => rfl]
      exact h2'
    | panic c =>
      dsimp only
      cases hd : code.decodeT (C := C) (H := σ.H) c with
      | error e => exact afterRunTR_box_error (fun he => code.decodeT_ne_panic c (he ▸ hd))
      | ok r =>
        rw [TRes.ok_bind', TRes.map_st _ _ (TState.drop ((Ext.append Γ κc).trans pnc.ext))
          fun _ => rfl]
        exact holds_modalK_pop _ pnc _ ω κ φ (holds_binders_all code.binders σ _ r h3)
    | other =>
      dsimp only
      have h4' := holds_modalK_pop σ other ((Ext.append Γ []).trans other.ext) ω κ φ h4
      rw [show (Ext.append Γ []).trans other.ext = other.ext from Subsingleton.elim _ _] at h4'
      rw [TRes.map_st _ _ (TState.drop other.ext) fun _ => rfl]
      exact h4'

/-- **The rule of a `try` is sound** over the typed state: a goal per clause
under the box, `false` under the diamond. -/
theorem Stmt.sound_tryCall (k : Nat) (m : Modality) {ρ κc Γ₁ Γe Γ₃ Γ₄ : Ctx}
    (call : ExtCall C Γ) (rets : Binders ρ) (ok : Prog C (ρ ++ Γ) Γ₁) (err : Prog C Γ Γe)
    (code : CodeBinder κc) (pnc : Prog C (κc ++ Γ) Γ₃) (other : Prog C Γ Γ₄) (σ : TState C Γ)
    (pr : Premise C Γ Γ) (hp : Stmt.step k m (.tryCall call rets ok err code pnc other) = some pr) :
    Premise.Runs m (.tryCall call rets ok err code pnc other) pr σ := by
  change tryStep m rets ok err code pnc other = some pr at hp
  cases m with
  | box => cases hp; exact Premise.sound_tryCallBox call rets ok err code pnc other σ
  | diamond => cases hp; exact Premise.sound_done σ false nofun

end Try

end Solidity.Core
