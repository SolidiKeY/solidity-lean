import Solidity.Calculus.Core.SoundBlocks
import Solidity.Calculus.Core.SoundArms
import Solidity.Calculus.Core.SoundCapture
import Solidity.Calculus.Core.RunWk

/-!
# The rule of a call is sound

`Calculus/Core/Blocks.lean`'s `callStep` against M3's interpreter
(`Core.Stmt.run`, `Run.call`), in the shape of `Calculus/Core/SoundKit.lean`.

* **`expand_function_body`.**  The parameters declared with the arguments
  (`Args.run_declsThen`: each read under the ones before reads as in the
  caller, `Val.eval_unders`), the return variables (`Binders.run_declsThen`,
  their defaults, as `CallRet.enter` enters them), the body weakened by
  `Thin.atop` run as the body in its own frame (`Prog.run_wk`; the frame's
  state lifted is the caller's with the frame pushed, `Env.put_atop`), the
  result assigned, and the frame popped (`Premise.unfold`) or dropped from
  under the returns (`Premise.inline`, `Env.thin_keepAll`).
* **`functionCallArgCapture`.**  The leftmost argument that is not simple is
  read first: the ones before it are simple, so read without effect, and the
  arguments with it captured read as before (`Args.eval_capture`).
-/

namespace Solidity.Core

open Semantics (Value Res Halt)
open Solidity (Modality)

variable {C : Contract}

/-! ## Environments of a frame -/

namespace Env

theorem put_nilTo : (Γ : Ctx) → (x : Env C []) → (d : Env C Γ) → Env.put (Thin.nilTo Γ) x d = d
  | [], _, _ => rfl
  | _ :: Γ, x, d => by
    show (d.1, Env.put (Thin.nilTo Γ) x d.2) = d
    rw [put_nilTo Γ x d.2]; rfl

/-- A frame's locals put over the caller's: the frame on top. -/
theorem put_atop {Γ : Ctx} : (ps : Ctx) → (x : Env C ps) → (d : Env C (ps ++ Γ)) →
    Env.put (Thin.atop ps Γ) x d = Env.append ps x (Env.drop (Ext.append Γ ps) d)
  | [], x, d => put_nilTo Γ x d
  | _ :: ps, x, d => by
    show (x.1, Env.put (Thin.atop ps Γ) x.2 d.2) =
      (x.1, Env.append ps x.2 (Env.drop (Ext.append Γ ps) d.2))
    rw [put_atop ps x.2 d.2]

theorem append_take_drop {Γ : Ctx} : (ρ : Ctx) → (e : Env C (ρ ++ Γ)) →
    Env.append ρ (Env.take ρ e) (Env.drop (Ext.append Γ ρ) e) = e
  | [], _ => rfl
  | _ :: ρ, e => by
    show (e.1, Env.append ρ (Env.take ρ e.2) (Env.drop (Ext.append Γ ρ) e.2)) = e
    rw [append_take_drop ρ e.2]; rfl

theorem drop_set_under {Γ : Ctx} {t : LTy} (j : Idx Γ t) (v : t.Denote C) :
    (ρ : Ctx) → (e : Env C (ρ ++ Γ)) →
      Env.drop (Ext.append Γ ρ) (Env.set (j.under ρ) v e) =
        Env.set j v (Env.drop (Ext.append Γ ρ) e)
  | [], _ => rfl
  | _ :: ρ, e => drop_set_under j v ρ e.2

theorem drop_push_append {Γ : Ctx} {t : LTy} (ps : Ctx) (x : Env C (t :: ps)) (e : Env C Γ) :
    Env.drop (Ext.append Γ ps).push (Env.append (t :: ps) x e) = e :=
  Env.drop_append ps x.2 e

theorem drop_push_set_under {Γ : Ctx} {t u : LTy} (j : Idx Γ t) (v : t.Denote C) (ps : Ctx)
    (y : Env C (u :: (ps ++ Γ))) :
    Env.drop (Ext.append Γ ps).push (Env.set (j.under ps).there v y) =
      Env.set j v (Env.drop (Ext.append Γ ps) y.2) :=
  drop_set_under j v ps y.2

theorem thin_ofExt {Γ : Ctx} : {Δ : Ctx} → (h : Ext Γ Δ) → (e : Env C Δ) →
    Env.thin (Thin.ofExt h) e = Env.drop h e
  | _, .refl, _ => rfl
  | _, .push h, e => thin_ofExt h e.2

theorem thin_keep_ofExt_append {Γ : Ctx} {t : LTy} (ps : Ctx) (x : Env C (t :: ps)) (e : Env C Γ) :
    Env.thin (Thin.keep (Thin.ofExt (Ext.append Γ ps))) (Env.append (t :: ps) x e) = (x.1, e) := by
  show (x.1, Env.thin (Thin.ofExt (Ext.append Γ ps)) (Env.append ps x.2 e)) = _
  rw [thin_ofExt, drop_append]

theorem thin_keepAll {Γ Δ : Ctx} (h : Thin Γ Δ) : (ρ : Ctx) → (r : Env C ρ) → (e : Env C Δ) →
    Env.thin (Thin.keepAll ρ h) (Env.append ρ r e) = Env.append ρ r (Env.thin h e)
  | [], _, _ => rfl
  | _ :: ρ, r, e => by
    show (r.1, Env.thin (Thin.keepAll ρ h) (Env.append ρ r.2 e)) = _
    rw [thin_keepAll h ρ r.2 e]; rfl

end Env

/-! ## The arguments -/

section Args

variable {Γ : Ctx}

theorem Args.eval_snoc_bind (σ : State C Γ) {ps : Ctx} (as : Args C Γ ps) (p : PrimTy) (x : Var)
    (e : Val C Γ p) :
    (Args.snoc as p x e).eval σ = as.eval σ >>= fun r => e.eval σ >>= fun v => pure (v, r) := rfl

theorem Args.eval_up {t : LTy} (σ : State C Γ) (w : t.Denote C) : {ps : Ctx} →
    (as : Args C Γ ps) → (as.up (t := t)).eval (σ.push w) = as.eval σ
  | _, .nil => rfl
  | _, .snoc as p x e => by
    show (Args.snoc (as.up (t := t)) p x e.up).eval (σ.push w) = _
    rw [Args.eval_snoc_bind, Args.eval_snoc_bind, Args.eval_up σ w as, Val.eval_up]

theorem Args.capture_snoc {ps : Ctx} (as : Args C Γ ps) (p : PrimTy) (x : Var) (e : Val C Γ p) :
    (Args.snoc as p x e).capture = match as.capture with
      | some ⟨p', v, as'⟩ => some ⟨p', v, .snoc as' p x e.up⟩
      | none => if e.isSimple then none else
          some ⟨p, e, .snoc as.up p x (.simple (.local .here))⟩ := rfl

/-- Arguments that are all simple read without halting. -/
theorem Args.eval_ok (σ : State C Γ) : {ps : Ctx} → (as : Args C Γ ps) → as.capture = none →
    ∃ a, as.eval σ = .ok a
  | _, .nil, _ => ⟨(), rfl⟩
  | _, .snoc as p x e, h => by
    rw [Args.capture_snoc] at h
    cases hc : as.capture with
    | some q => rw [hc] at h; cases h
    | none =>
      rw [hc] at h
      obtain ⟨a, ha⟩ := Args.eval_ok σ as hc
      cases e with
      | simple s =>
        obtain ⟨v, hv⟩ := Simple.eval_ok σ s
        refine ⟨(v, a), ?_⟩
        rw [Args.eval_snoc_bind, ha]
        exact (congrArg (· >>= fun v => (pure (v, a) : Res _)) hv : _)
      | _ => simp only [Val.isSimple, Bool.false_eq_true, if_false, reduceCtorEq] at h

/-- **The arguments with one captured** read as the captured value, then the
arguments over it. -/
theorem Args.eval_capture (σ : State C Γ) : {ps : Ctx} → (as : Args C Γ ps) →
    ∀ {p : PrimTy} {v : Val C Γ p} {as' : Args C (.val p :: Γ) ps},
      as.capture = some ⟨p, v, as'⟩ → as.eval σ = v.eval σ >>= fun w => as'.eval (σ.push w)
  | _, .nil, _, _, _, h => by cases h
  | _, .snoc as p' x e, p, v, as', h => by
    rw [Args.capture_snoc] at h
    cases hc : as.capture with
    | some q =>
      obtain ⟨p₀, v₀, as₀⟩ := q
      rw [hc] at h
      dsimp only at h
      cases h
      simp only [Args.eval_snoc_bind, Args.eval_capture σ as hc, bind_assoc, Val.eval_up]
    | none =>
      rw [hc] at h
      dsimp only at h
      split at h
      · cases h
      · cases h
        obtain ⟨a, ha⟩ := Args.eval_ok σ as hc
        show _ = e.eval σ >>= fun w =>
          (Args.snoc (as.up (t := .val p')) p' x (.simple (.local .here))).eval (σ.push (t := .val p') w)
        simp only [Args.eval_snoc_bind, Args.eval_up, ha]
        cases e.eval σ <;> rfl

theorem Val.eval_unders {p : PrimTy} (v : Val C Γ p) (σ : State C Γ) : (ρ : Ctx) → (r : Env C ρ) →
    (v.unders ρ).eval (σ.withEnv (Env.append ρ r σ.env)) = v.eval σ
  | [], _ => by
    show v.eval (σ.withEnv σ.env) = _
    rw [State.withEnv_self]
  | _ :: ρ, r => by
    show ((v.unders ρ).up).eval ((σ.withEnv (Env.append ρ r.2 σ.env)).push r.1) = _
    rw [Val.eval_up, Val.eval_unders v σ ρ r.2]

/-- **The parameters declared** with the arguments: the arguments read, then
the rest with them on top. -/
theorem Args.run_declsThen {Δ : Ctx} (σ : State C Γ) : {ps : Ctx} → (as : Args C Γ ps) →
    (rest : Prog C (ps ++ Γ) Δ) →
      Prog.run σ (as.declsThen rest) =
        as.eval σ >>= fun a => Prog.run (σ.withEnv (Env.append ps a σ.env)) rest
  | _, .nil, rest => by
    show Prog.run σ rest = Prog.run (σ.withEnv σ.env) rest
    rw [State.withEnv_self]
  | _, .snoc (ps := ps') as p x e, rest => by
    show Prog.run σ (as.declsThen (.cons (.declLocal p x (some (e.unders ps'))) rest)) = _
    rw [Args.run_declsThen σ as, Args.eval_snoc_bind, bind_assoc]
    refine congrArg (as.eval σ >>= ·) (funext fun a => ?_)
    rw [Prog.run_cons]
    show (Run.declLocal p (some (e.unders ps')) (σ.withEnv (Env.append ps' a σ.env))).bind _ = _
    simp only [Run.declLocal, Val.eval_unders, bind_assoc, pure_bind]
    cases e.eval σ <;> rfl

/-- **The return variables declared** at their defaults. -/
theorem Binders.run_declsThen {Δ : Ctx} (σ : State C Γ) : {ρ : Ctx} → (bs : Binders ρ) →
    (rest : Prog C (ρ ++ Γ) Δ) →
      Prog.run σ (bs.declsThen rest) =
        Prog.run (σ.withEnv (Env.append ρ (bs.defaults (C := C)) σ.env)) rest
  | _, .nil, rest => by
    show Prog.run σ rest = Prog.run (σ.withEnv σ.env) rest
    rw [State.withEnv_self]
  | _, .snoc (ρ := ρ') bs p x, rest => by
    show Prog.run σ (bs.declsThen (.cons (.declLocal p x none) rest)) = _
    rw [Binders.run_declsThen σ bs, Prog.run_cons]
    rfl

end Args

/-! ## A body run in its frame -/

theorem Res.ok_bind {α β : Type} (a : α) (f : α → Res β) : (Except.ok a : Res α) >>= f = f a := rfl

theorem Res.ok_bind' {α β : Type} (a : α) (f : α → Res β) :
    Except.bind (Except.ok a : Res α) f = f a := rfl

theorem Run.declMem_none {Γ : Ctx} (R : RefTy) (σ : State C Γ) :
    Run.declMem R none σ =
      (Semantics.allocDefault σ.glob R).map fun x =>
        (σ.withGlob x.1).push (t := .mem R) (some x.2) := by
  show (do
    let (τ, id) ← Semantics.allocDefault σ.glob R
    pure ((σ.withGlob τ).push (t := .mem R) (some id))) = _
  cases Semantics.allocDefault σ.glob R <;> rfl

theorem CallRet.enter_mem {Γ : Ctx} (R : RefTy) (r : Var) (hd : (Ty.ref R).defaultOkS = true)
    (hm : (Ty.ref R).mapFree = true) (g : Semantics.State) :
    CallRet.enter (C := C) g (CallRet.mem (Γ := Γ) R r hd hm) =
      (Semantics.allocDefault g R).map fun x => (x.1, (some x.2, ())) := by
  show (do let (τ', id) ← Semantics.allocDefault g R; pure (τ', (some id, ()))) = _
  cases Semantics.allocDefault g R <;> rfl

section Body

variable {Γ : Ctx}

/-- A body weakened under its caller's locals, run from the caller's state
with the frame pushed, as a block: the body's run in its frame, lifted. -/
theorem Prog.run_atop {ps Γf : Ctx} (body : Prog C ps Γf) (σ : State C Γ) (g : Semantics.State)
    (a : Env C ps) :
    (Prog.run ((σ.withGlob g).withEnv (Env.append ps a σ.env)) (body.wk (Thin.atop ps Γ)).2.2).map
        (State.drop (body.wk (Thin.atop ps Γ)).2.2.ext) =
      (Prog.run (State.ofGlob g a) body).map fun υ =>
        (υ.drop body.ext).withEnv (Env.append ps (υ.drop body.ext).env σ.env) := by
  have hs : (State.ofGlob g a).lift (Thin.atop ps Γ) (Env.append ps a σ.env) =
      (σ.withGlob g).withEnv (Env.append ps a σ.env) := by
    simp only [State.lift, Env.put_atop, Env.drop_append]; rfl
  have hw := WkRel.eq_lifted (WkRel.drop (Prog.wk_over body (Thin.atop ps Γ))
    (Prog.run_wk body (Thin.atop ps Γ) (Env.append ps a σ.env) (State.ofGlob g a)))
  rw [← hs, hw]
  cases Prog.run (State.ofGlob g a) body with
  | error => rfl
  | ok υ =>
    show Except.ok _ = Except.ok _
    simp only [State.lift, Env.put_atop, Env.drop_append]

/-- A body weakened under its caller's locals with its return variables kept
on top (`CallRet.rets`), run from the caller's state with the frame pushed. -/
theorem Prog.run_keepAllAtop {rs ps Γf : Ctx} (body : Prog C (rs ++ ps) Γf) (σ : State C Γ)
    (g : Semantics.State) (r : Env C rs) (a : Env C ps) :
    (Prog.run ((σ.withGlob g).withEnv (Env.append rs r (Env.append ps a σ.env)))
        (body.wk (Thin.keepAll rs (Thin.atop ps Γ))).2.2).map
        (State.drop (body.wk (Thin.keepAll rs (Thin.atop ps Γ))).2.2.ext) =
      (Prog.run (State.ofGlob g (Env.append rs r a)) body).map fun υ =>
        (υ.drop body.ext).withEnv (Env.put (Thin.keepAll rs (Thin.atop ps Γ)) (υ.drop body.ext).env
          (Env.append rs r (Env.append ps a σ.env))) := by
  have hs : (State.ofGlob g (Env.append rs r a)).lift (Thin.keepAll rs (Thin.atop ps Γ))
      (Env.append rs r (Env.append ps a σ.env)) =
      (σ.withGlob g).withEnv (Env.append rs r (Env.append ps a σ.env)) := by
    show (State.ofGlob g (Env.append rs r a)).withEnv (Env.put (Thin.keepAll rs (Thin.atop ps Γ))
      (Env.append rs r a) (Env.append rs r (Env.append ps a σ.env))) = _
    rw [Env.put_keepAll, Env.put_atop, Env.drop_append]; rfl
  have hw := WkRel.eq_lifted (WkRel.drop (Prog.wk_over body (Thin.keepAll rs (Thin.atop ps Γ)))
    (Prog.run_wk body (Thin.keepAll rs (Thin.atop ps Γ)) (Env.append rs r (Env.append ps a σ.env))
      (State.ofGlob g (Env.append rs r a))))
  rw [← hs, hw]
  cases Prog.run (State.ofGlob g (Env.append rs r a)) body <;> rfl

/-- The frame dropped from under the return variables it leaves. -/
theorem Env.thin_put_keepAllAtop {rs ps : Ctx} (x : Env C (rs ++ ps)) (r : Env C rs)
    (a : Env C ps) (e : Env C Γ) :
    Env.thin (Thin.keepAll rs (Thin.ofExt (Ext.append Γ ps)))
        (Env.put (Thin.keepAll rs (Thin.atop ps Γ)) x (Env.append rs r (Env.append ps a e))) =
      Env.append rs (Env.take rs x) e := by
  conv => lhs; rw [← Env.append_take_drop rs x]
  rw [Env.put_keepAll, Env.put_atop, Env.drop_append, Env.thin_keepAll, Env.thin_ofExt,
    Env.drop_append]

end Body

/-! ## `expand_function_body` -/

section Calls

variable {Γ : Ctx} {m : Modality}

/-- `internalCallExpand` of a call with no result. -/
theorem Premise.Sound.callNone {ps Γf : Ctx} (f : Name) (args : Args C Γ ps)
    (body : Prog C ([] ++ ps) Γf) (σ : State C Γ) :
    Premise.Sound m (.call f args .none body)
      (.unfold (args.declsThen (.cons (.block (body.wk (Thin.atop ps Γ)).2.2) .nil))
        (Ext.append Γ ps)) σ := by
  refine Premise.Sound.unfold ?_
  rw [Args.run_declsThen]
  show _ = Run.call args .none body.ext body.runR σ
  unfold Run.call
  cases args.eval σ with
  | error => rfl
  | ok a =>
    show (Prog.run ((σ.withGlob σ.glob).withEnv (Env.append ps a σ.env))
      (.cons (.block (body.wk (Thin.atop ps Γ)).2.2) .nil)).map _ = _
    rw [Prog.run_cons, Stmt.run_block, bind_run_nil, Prog.run_atop]
    show _ = (Prog.run (State.ofGlob σ.glob a) body).bind fun υ => pure (υ.withEnv σ.env)
    cases Prog.run (State.ofGlob σ.glob a) body with
    | error => rfl
    | ok υ => exact congrArg Except.ok (by simp only [State.drop, State.withEnv, Env.drop_append])


/-- `functionBodyExpand` of a call whose result lands in `res`. -/
theorem Premise.Sound.callVal {ps Γf : Ctx} (f : Name) (args : Args C Γ ps) (p : PrimTy) (r : Var)
    (res : Option (Idx Γ (.val p))) (body : Prog C ([.val p] ++ ps) Γf) (σ : State C Γ) :
    Premise.Sound m (.call f args (.val p r res) body)
      (.unfold (args.declsThen (.cons (.declLocal p r none)
        (.cons (.block (body.wk (Thin.atop (.val p :: ps) Γ)).2.2) (match res with
          | none => .nil
          | some j => .cons (.assignLocal (j.under ps).there (.simple (.local .here))) .nil))))
        (.push (Ext.append Γ ps))) σ := by
  refine Premise.Sound.unfold ?_
  rw [Args.run_declsThen]
  show _ = Run.call args (.val p r res) body.ext body.runR σ
  unfold Run.call
  cases args.eval σ with
  | error => rfl
  | ok a =>
    show (Prog.run ((σ.withGlob σ.glob).withEnv (Env.append (.val p :: ps) ((PrimTy.default p, a) : Env C (.val p :: ps)) σ.env))
      (.cons (.block (body.wk (Thin.atop (.val p :: ps) Γ)).2.2) _)).map _ = _
    rw [Prog.run_cons, Stmt.run_block, Prog.run_atop (ps := .val p :: ps)]
    show _ = (Prog.run (State.ofGlob (C := C) (Γ := .val p :: ps) σ.glob (PrimTy.default p, a)) body).bind fun υ =>
      pure (υ.withEnv (CallRet.leave σ.env (.val p r res) (Env.take [.val p] (Env.drop body.ext υ.env))))
    cases Prog.run (State.ofGlob (C := C) (Γ := .val p :: ps) σ.glob (PrimTy.default p, a)) body with
    | error => rfl
    | ok υ =>
      cases res with
      | none =>
        exact congrArg Except.ok (by simp only [State.drop, State.withEnv, Env.drop_push_append]; rfl)
      | some j =>
        exact congrArg Except.ok (by
          simp only [State.drop, State.setLocal, State.withEnv, Env.drop_push_set_under]
          rw [show (Env.append (.val p :: ps) (Env.drop body.ext υ.env) σ.env).2 =
            Env.append ps (Env.drop body.ext υ.env).2 σ.env from rfl, Env.drop_append]
          rfl)


/-- `internalCallExpand` of a call that leaves its return variables
(`CallRet.rets`): the frame dropped from under them. -/
theorem Premise.Sound.callRets {ps rs Γf : Ctx} (f : Name) (args : Args C Γ ps) (bs : Binders rs)
    (body : Prog C (rs ++ ps) Γf) (σ : State C Γ) :
    Premise.Sound m (.call f args (.rets bs) body)
      (.inline (args.declsThen (bs.declsThen
          (.cons (.block (body.wk (Thin.keepAll rs (Thin.atop ps Γ))).2.2) .nil)))
        (Thin.keepAll rs (Thin.ofExt (Ext.append Γ ps)))) σ := by
  refine Premise.Sound.inline ?_
  rw [Args.run_declsThen]
  show _ = Run.call args (.rets bs) body.ext body.runR σ
  unfold Run.call
  cases args.eval σ with
  | error => rfl
  | ok a =>
    show (Prog.run (σ.withEnv (Env.append ps a σ.env)) (bs.declsThen _)).map _ = _
    rw [Binders.run_declsThen]
    show (Prog.run ((σ.withGlob σ.glob).withEnv (Env.append rs bs.defaults (Env.append ps a σ.env)))
      (.cons (.block (body.wk (Thin.keepAll rs (Thin.atop ps Γ))).2.2) .nil)).map _ = _
    rw [Prog.run_cons, Stmt.run_block, bind_run_nil, Prog.run_keepAllAtop]
    show _ = (Prog.run (State.ofGlob σ.glob (Env.append rs bs.defaults a)) body).bind fun υ =>
      pure (υ.withEnv (Env.append rs (Env.take rs (Env.drop body.ext υ.env)) σ.env))
    cases Prog.run (State.ofGlob σ.glob (Env.append rs bs.defaults a)) body with
    | error => rfl
    | ok υ =>
      exact congrArg Except.ok (by
        simp only [State.thin, State.drop, State.withEnv, Env.thin_put_keepAllAtop])

/-- `internalCallExpand` of a call with a memory return: the frame dropped
from under the object. -/
theorem Premise.Sound.callMem {ps Γf : Ctx} (f : Name) (args : Args C Γ ps) (R : RefTy) (r : Var)
    (hd : (Ty.ref R).defaultOkS = true) (hm : (Ty.ref R).mapFree = true)
    (body : Prog C ([.mem R] ++ ps) Γf) (σ : State C Γ) :
    Premise.Sound m (.call f args (.mem R r hd hm) body)
      (.inline (args.declsThen (.cons (.declMem R r none hd hm)
          (.cons (.block (body.wk (Thin.atop (.mem R :: ps) Γ)).2.2) .nil)))
        (.keep (Thin.ofExt (Ext.append Γ ps)))) σ := by
  refine Premise.Sound.inline ?_
  rw [Args.run_declsThen]
  show _ = Run.call args (.mem R r hd hm) body.ext body.runR σ
  unfold Run.call
  cases args.eval σ with
  | error => rfl
  | ok a =>
    rw [Res.ok_bind, Res.ok_bind, Prog.run_cons, CallRet.enter_mem, Stmt.run_declMem, Run.declMem_none]
    show (Except.bind ((Semantics.allocDefault σ.glob R).map _) _).map _ =
      Except.bind ((Semantics.allocDefault σ.glob R).map _) _
    cases Semantics.allocDefault σ.glob R with
    | error => rfl
    | ok x =>
      obtain ⟨g, id⟩ := x
      show (Prog.run ((σ.withGlob g).withEnv (Env.append (.mem R :: ps) (some id, a) σ.env))
          (.cons (.block (body.wk (Thin.atop (.mem R :: ps) Γ)).2.2) .nil)).map _ =
        (Prog.run (State.ofGlob (C := C) (Γ := .mem R :: ps) g (some id, a)) body).bind fun υ =>
          pure (υ.withEnv (CallRet.leave σ.env (.mem R r hd hm)
            (Env.take [.mem R] (Env.drop body.ext υ.env))))
      rw [Prog.run_cons, Stmt.run_block, bind_run_nil, Prog.run_atop (ps := .mem R :: ps)]
      cases Prog.run (State.ofGlob (C := C) (Γ := .mem R :: ps) g (some id, a)) body with
      | error => rfl
      | ok υ =>
        exact congrArg Except.ok (by
          simp only [State.thin, State.drop, State.withEnv, Env.thin_keep_ofExt_append]; rfl)

/-- `functionCallArgCapture` of a call with no result. -/
theorem Premise.Sound.callCaptureNone {ps Γf : Ctx} (k : Nat) (f : Name) (args : Args C Γ ps)
    (body : Prog C ([] ++ ps) Γf) {p : PrimTy} {v : Val C Γ p} {as' : Args C (.val p :: Γ) ps}
    (hc : args.capture = some ⟨p, v, as'⟩) (σ : State C Γ) :
    Premise.Sound m (.call f args .none body) (.capture p (fse k) v (.call f as' .none body)) σ := by
  refine Premise.Sound.capture (fun w hw => ?_) (fun e he => ?_)
  · show (Run.call as' .none body.ext body.runR (σ.push (t := .val p) w)).map (State.drop (.push .refl)) =
      Run.call args .none body.ext body.runR σ
    unfold Run.call
    rw [Args.eval_capture σ args hc, hw]
    show _ = Except.bind (as'.eval (σ.push (t := .val p) w)) _
    cases as'.eval (σ.push (t := .val p) w) with
    | error => rfl
    | ok a =>
      show (Except.bind (Prog.run (State.ofGlob σ.glob a) body) fun υ =>
          pure (υ.withEnv (σ.push (t := .val p) w).env)).map _ =
        Except.bind (Prog.run (State.ofGlob σ.glob a) body) fun υ => pure (υ.withEnv σ.env)
      cases Prog.run (State.ofGlob σ.glob a) body <;> rfl
  · show Run.call args .none body.ext body.runR σ = _
    unfold Run.call
    rw [Args.eval_capture σ args hc, he]; rfl

/-- `functionCallArgCapture` of a call whose result lands in `res`. -/
theorem Premise.Sound.callCaptureVal {ps Γf : Ctx} (k : Nat) (f : Name) (args : Args C Γ ps)
    (q : PrimTy) (r : Var) (res : Option (Idx Γ (.val q))) (body : Prog C ([.val q] ++ ps) Γf)
    {p : PrimTy} {v : Val C Γ p} {as' : Args C (.val p :: Γ) ps}
    (hc : args.capture = some ⟨p, v, as'⟩) (σ : State C Γ) :
    Premise.Sound m (.call f args (.val q r res) body)
      (.capture p (fse k) v (.call f as' (.val q r (res.map .there)) body)) σ := by
  refine Premise.Sound.capture (fun w hw => ?_) (fun e he => ?_)
  · show (Run.call as' (.val q r (res.map .there)) body.ext body.runR (σ.push (t := .val p) w)).map
        (State.drop (.push .refl)) = Run.call args (.val q r res) body.ext body.runR σ
    unfold Run.call
    rw [Args.eval_capture σ args hc, hw]
    show _ = Except.bind (as'.eval (σ.push (t := .val p) w)) _
    cases as'.eval (σ.push (t := .val p) w) with
    | error => rfl
    | ok a =>
      show (Except.bind (Prog.run (State.ofGlob (C := C) (Γ := .val q :: ps) σ.glob
            (PrimTy.default q, a)) body) fun υ =>
          pure (υ.withEnv (CallRet.leave (σ.push (t := .val p) w).env (.val q r (res.map .there))
            (Env.take [.val q] (Env.drop body.ext υ.env))))).map _ =
        Except.bind (Prog.run (State.ofGlob (C := C) (Γ := .val q :: ps) σ.glob
            (PrimTy.default q, a)) body) fun υ =>
          pure (υ.withEnv (CallRet.leave σ.env (.val q r res)
            (Env.take [.val q] (Env.drop body.ext υ.env))))
      cases Prog.run (State.ofGlob (C := C) (Γ := .val q :: ps) σ.glob (PrimTy.default q, a)) body with
      | error => rfl
      | ok υ => cases res <;> rfl
  · show Run.call args (.val q r res) body.ext body.runR σ = _
    unfold Run.call
    rw [Args.eval_capture σ args hc, he]; rfl

/-- `functionCallArgCapture` of a call that leaves its return variables. -/
theorem Premise.Sound.callCaptureRets {ps rs Γf : Ctx} (k : Nat) (f : Name) (args : Args C Γ ps)
    (bs : Binders rs) (body : Prog C (rs ++ ps) Γf) {p : PrimTy} {v : Val C Γ p}
    {as' : Args C (.val p :: Γ) ps} (hc : args.capture = some ⟨p, v, as'⟩) (σ : State C Γ) :
    Premise.Sound m (.call f args (.rets bs) body)
      (.inline (.cons (.declLocal p (fse k) (some v)) (.cons (.call f as' (.rets bs) body) .nil))
        (Thin.keepAll rs (.drop .refl))) σ := by
  refine Premise.Sound.inline ?_
  rw [Prog.run_cons]
  show (Except.bind (Run.declLocal p (some v) σ) _).map _ =
    Run.call args (.rets bs) body.ext body.runR σ
  unfold Run.call
  rw [Args.eval_capture σ args hc]
  simp only [Run.declLocal]
  cases v.eval σ with
  | error => rfl
  | ok w =>
    show (Prog.run (σ.push (t := .val p) w) (.cons (.call f as' (.rets bs) body) .nil)).map _ =
      Except.bind (as'.eval (σ.push (t := .val p) w)) _
    rw [Prog.run_cons, bind_run_nil]
    show (Run.call as' (.rets bs) body.ext body.runR (σ.push (t := .val p) w)).map _ = _
    unfold Run.call
    cases as'.eval (σ.push (t := .val p) w) with
    | error => rfl
    | ok a =>
      show (Except.bind (Prog.run (State.ofGlob σ.glob (Env.append rs bs.defaults a)) body) fun υ =>
          pure (υ.withEnv (Env.append rs (Env.take rs (Env.drop body.ext υ.env))
            (σ.push (t := .val p) w).env))).map _ =
        Except.bind (Prog.run (State.ofGlob σ.glob (Env.append rs bs.defaults a)) body) fun υ =>
          pure (υ.withEnv (Env.append rs (Env.take rs (Env.drop body.ext υ.env)) σ.env))
      cases Prog.run (State.ofGlob σ.glob (Env.append rs bs.defaults a)) body with
      | error => rfl
      | ok υ =>
        exact congrArg Except.ok (by simp only [State.thin, State.withEnv, Env.thin_keepAll]; rfl)

/-- `functionCallArgCapture` of a call with a memory return. -/
theorem Premise.Sound.callCaptureMem {ps Γf : Ctx} (k : Nat) (f : Name) (args : Args C Γ ps)
    (R : RefTy) (r : Var) (hd : (Ty.ref R).defaultOkS = true) (hm : (Ty.ref R).mapFree = true)
    (body : Prog C ([.mem R] ++ ps) Γf) {p : PrimTy} {v : Val C Γ p}
    {as' : Args C (.val p :: Γ) ps} (hc : args.capture = some ⟨p, v, as'⟩) (σ : State C Γ) :
    Premise.Sound m (.call f args (.mem R r hd hm) body)
      (.inline (.cons (.declLocal p (fse k) (some v)) (.cons (.call f as' (.mem R r hd hm) body) .nil))
        (.keep (.drop .refl))) σ := by
  refine Premise.Sound.inline ?_
  rw [Prog.run_cons]
  show (Except.bind (Run.declLocal p (some v) σ) _).map _ =
    Run.call args (.mem R r hd hm) body.ext body.runR σ
  unfold Run.call
  rw [Args.eval_capture σ args hc]
  simp only [Run.declLocal]
  cases v.eval σ with
  | error => rfl
  | ok w =>
    show (Prog.run (σ.push (t := .val p) w) (.cons (.call f as' (.mem R r hd hm) body) .nil)).map _ =
      Except.bind (as'.eval (σ.push (t := .val p) w)) _
    rw [Prog.run_cons, bind_run_nil]
    show (Run.call as' (.mem R r hd hm) body.ext body.runR (σ.push (t := .val p) w)).map _ = _
    unfold Run.call
    cases as'.eval (σ.push (t := .val p) w) with
    | error => rfl
    | ok a =>
      simp only [Res.ok_bind, Res.ok_bind', State.glob_push, CallRet.enter_mem]
      cases Semantics.allocDefault σ.glob R with
      | error => rfl
      | ok x =>
        obtain ⟨g, id⟩ := x
        show (Except.bind (Prog.run (State.ofGlob (C := C) (Γ := [LTy.mem R] ++ ps) g (some id, a))
          body) _).map _ = Except.bind (Prog.run (State.ofGlob (C := C) (Γ := [LTy.mem R] ++ ps) g
            (some id, a)) body) _
        cases Prog.run (State.ofGlob (C := C) (Γ := [LTy.mem R] ++ ps) g (some id, a)) body <;> rfl

/-- **The rule of a call is sound**: its leftmost argument that is not simple
captured, or its body inlined. -/
theorem Stmt.stepSound_call (k : Nat) (m : Modality) {Γ' ps rs Γf : Ctx} (f : Name)
    (args : Args C Γ ps) (ret : CallRet Γ rs Γ') (body : Prog C (rs ++ ps) Γf) :
    Stmt.StepSound k m (.call f args ret body) := by
  intro σ pr hp
  change callStep k f args ret body = some pr at hp
  unfold callStep at hp
  cases ret with
  | none =>
    dsimp only at hp
    cases hc : args.capture with
    | some q =>
      obtain ⟨p, v, as'⟩ := q
      rw [hc] at hp; cases hp
      exact Premise.Sound.callCaptureNone (m := m) k f args body hc σ
    | none =>
      rw [hc] at hp; cases hp
      exact Premise.Sound.callNone (m := m) f args body σ
  | val q r res =>
    dsimp only at hp
    cases hc : args.capture with
    | some x =>
      obtain ⟨p, v, as'⟩ := x
      rw [hc] at hp; cases hp
      exact Premise.Sound.callCaptureVal (m := m) k f args q r res body hc σ
    | none =>
      rw [hc] at hp; cases hp
      cases res with
      | none => dsimp only; exact Premise.Sound.callVal (m := m) f args q r none body σ
      | some j => dsimp only; exact Premise.Sound.callVal (m := m) f args q r (some j) body σ
  | rets bs =>
    dsimp only at hp
    cases hc : args.capture with
    | some x =>
      obtain ⟨p, v, as'⟩ := x
      rw [hc] at hp; cases hp
      exact Premise.Sound.callCaptureRets (m := m) k f args bs body hc σ
    | none =>
      rw [hc] at hp; cases hp
      exact Premise.Sound.callRets (m := m) f args bs body σ
  | mem R r hd hm =>
    dsimp only at hp
    cases hc : args.capture with
    | some x =>
      obtain ⟨p, v, as'⟩ := x
      rw [hc] at hp; cases hp
      exact Premise.Sound.callCaptureMem (m := m) k f args R r hd hm body hc σ
    | none =>
      rw [hc] at hp; cases hp
      exact Premise.Sound.callMem (m := m) f args R r hd hm body σ

end Calls

end Solidity.Core
