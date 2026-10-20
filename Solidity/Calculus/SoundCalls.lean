import Solidity.Calculus.SoundArms
import Solidity.Calculus.SoundCapture
import Solidity.Calculus.SoundStore
import Solidity.Calculus.SoundKit
import Solidity.Semantics.NativeDeferred
import Solidity.Semantics.RevertOnly

/-!
# The rules of calls and `try` are sound

`Calculus/Blocks.lean`'s `callStep` and `tryStep` against the typed run
(`Stmt.run`, `TRun.call`, `TRun.tryCall`), in the shape of
`Calculus/SoundKit.lean` (`Premise.Sound`).

* **`expand_function_body`.**  The parameters declared with the arguments
  (`Args.runSt_declsThen`), the return variables at their defaults
  (`Binders.runSt_declsThen`), the body weakened by `Thin.atop` run as the
  body in its own frame (`Stmt.run_block_wk`, from `Prog.run_wk`): the
  frame's state lifted is the caller's with the frame pushed
  (`TEnv.put_atop`), and the caller's locals come out weakened along the
  heap the body grew, as `TRun.call` gives them back.
* **`functionCallArgCapture`.**  The arguments with one captured read as
  before (`Args.evalT_capture`).
* **`try`** under the box: each clause's goal, for every typed value its
  outcome binds (`holds_binders_all`), is the run of that clause.
-/

namespace Solidity
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

theorem Args.capture_snocStorage {ps : Ctx} (as : Args C Γ ps) (R : RefTy) (x : Var)
    (e : SPath C Γ (.ref R)) :
    (Args.snocStorage as R x e).capture = match as.capture with
      | some ⟨p, v, as'⟩ => some ⟨p, v, .snocStorage as' R x e.up⟩
      | none => none := rfl

theorem Args.capture_snocMemory {ps : Ctx} (as : Args C Γ ps) (R : RefTy) (x : Var)
    (e : MPath C Γ (.ref R)) :
    (Args.snocMemory as R x e).capture = match as.capture with
      | some ⟨p, v, as'⟩ => some ⟨p, v, .snocMemory as' R x e.up⟩
      | none => none := rfl

end Args

/-! ## A body run in its frame -/

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

theorem Val.evalT_unders {p : PrimTy} (v : Val C Γ p) (σ : State C Γ) :
    (ρ : Ctx) → (r : TEnv C σ.H ρ) →
      (v.unders ρ).evalT (σ.withEnv (TEnv.append ρ r σ.env)) = v.evalT σ
  | [], _ => rfl
  | _ :: ρ, r => by
    show ((v.unders ρ).up).evalT ((σ.withEnv (TEnv.append ρ r.2 σ.env)).push r.1) = _
    rw [Val.evalT_up, Val.evalT_unders v σ ρ r.2]

theorem SPath.resolveT_unders {a : Ty} (v : SPath C Γ a) (σ : State C Γ) :
    (ρ : Ctx) → (r : TEnv C σ.H ρ) →
      (v.unders ρ).resolveT (σ.withEnv (TEnv.append ρ r σ.env)) = v.resolveT σ
  | [], _ => rfl
  | _ :: ρ, r => by
    show ((v.unders ρ).up).resolveT
      ((σ.withEnv (TEnv.append ρ r.2 σ.env)).push r.1) = _
    rw [SPath.resolveT_up, SPath.resolveT_unders v σ ρ r.2]

theorem MPath.mvalT_unders {a : Ty} (v : MPath C Γ a) (σ : State C Γ) :
    (ρ : Ctx) → (r : TEnv C σ.H ρ) →
      (v.unders ρ).mvalT (σ.withEnv (TEnv.append ρ r σ.env)) = v.mvalT σ
  | [], _ => rfl
  | _ :: ρ, r => by
    show ((v.unders ρ).up).mvalT
      ((σ.withEnv (TEnv.append ρ r.2 σ.env)).push r.1) = _
    rw [MPath.mvalT_up, MPath.mvalT_unders v σ ρ r.2]

theorem Stmt.runSt_declLocal_none (p : PrimTy) (x : Var) (σ : State C Γ) :
    Stmt.runSt σ (.declLocal p x none) = .ok (σ.push (t := .val p) (PrimTy.dflt p)) := rfl

theorem Args.evalT_snoc (σ : State C Γ) {ps : Ctx} (as : Args C Γ ps) (p : PrimTy) (x : Var)
    (e : Val C Γ p) :
    (Args.snoc as p x e).evalT σ = as.evalT σ >>= fun r => e.evalT σ >>= fun v => pure (v, r) :=
  rfl

theorem Args.evalT_snocStorage (σ : State C Γ) {ps : Ctx} (as : Args C Γ ps)
    (R : RefTy) (x : Var) (e : SPath C Γ (.ref R)) :
    (Args.snocStorage as R x e).evalT σ =
      as.evalT σ >>= fun r => e.resolveT σ >>= fun v => pure (some v, r) := rfl

theorem Args.evalT_snocMemory (σ : State C Γ) {ps : Ctx} (as : Args C Γ ps)
    (R : RefTy) (x : Var) (e : MPath C Γ (.ref R)) :
    (Args.snocMemory as R x e).evalT σ =
      as.evalT σ >>= fun r => e.mvalT σ >>= fun v => pure (some v, r) := rfl

theorem Args.evalT_up {t : LTy} (σ : State C Γ) (w : t.TDenote C σ.H) : {ps : Ctx} →
    (as : Args C Γ ps) → (as.up (t := t)).evalT (σ.push w) = as.evalT σ
  | _, .nil => rfl
  | _, .snoc as p x e => by
    show (Args.snoc (as.up (t := t)) p x e.up).evalT (σ.push w) = _
    rw [Args.evalT_snoc, Args.evalT_snoc, Args.evalT_up σ w as, Val.evalT_up]
    rfl
  | _, .snocStorage as R x e => by
    show (Args.snocStorage (as.up (t := t)) R x e.up).evalT (σ.push w) = _
    rw [Args.evalT_snocStorage, Args.evalT_snocStorage, Args.evalT_up σ w as,
      SPath.resolveT_up]
    rfl
  | _, .snocMemory as R x e => by
    show (Args.snocMemory (as.up (t := t)) R x e.up).evalT (σ.push w) = _
    rw [Args.evalT_snocMemory, Args.evalT_snocMemory, Args.evalT_up σ w as,
      MPath.mvalT_up]
    rfl

/-- **The arguments with one captured** read as the captured value, then the
arguments over it. -/
theorem Args.evalT_capture (σ : State C Γ) : {ps : Ctx} → (as : Args C Γ ps) →
    ∀ {p : PrimTy} {v : Val C Γ p} {as' : Args C (.val p :: Γ) ps},
      as.capture = some ⟨p, v, as'⟩ →
        as.evalT σ = v.evalT σ >>= fun w => as'.evalT (σ.push (t := .val p) w)
  | _, .nil, _, _, _, h => by cases h
  | _, .snoc (ps := ps) as p' x e, p, v, as', h => by
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
        rw [Args.evalT_snoc]
        show _ = (e.evalT σ >>= fun w =>
          (as.up (t := .val p')).evalT (σ.push (t := .val p') w) >>= fun a =>
            (pure (w, a) : TRes (TEnv C σ.H (.val p' :: ps))))
        simp only [Args.evalT_up]
        exact TRes.RevertOnly.bind_comm (as.evalT_revertOnly σ) (e.evalT_revertOnly σ)
          (fun a w => pure (w, a))
  | _, .snocStorage as R x e, p, v, as', h => by
    rw [Args.capture_snocStorage] at h
    cases hc : as.capture with
    | none => rw [hc] at h; cases h
    | some q =>
      obtain ⟨p₀, v₀, as₀⟩ := q
      rw [hc] at h
      dsimp only at h
      cases h
      rw [Args.evalT_snocStorage, Args.evalT_capture σ as hc]
      cases v.evalT σ with
      | error => rfl
      | ok w =>
        show _ = (Args.snocStorage as₀ R x e.up).evalT (σ.push (t := .val p) w)
        rw [Args.evalT_snocStorage, SPath.resolveT_up]
        rfl
  | _, .snocMemory as R x e, p, v, as', h => by
    rw [Args.capture_snocMemory] at h
    cases hc : as.capture with
    | none => rw [hc] at h; cases h
    | some q =>
      obtain ⟨p₀, v₀, as₀⟩ := q
      rw [hc] at h
      dsimp only at h
      cases h
      rw [Args.evalT_snocMemory, Args.evalT_capture σ as hc]
      cases v.evalT σ with
      | error => rfl
      | ok w =>
        show _ = (Args.snocMemory as₀ R x e.up).evalT (σ.push (t := .val p) w)
        rw [Args.evalT_snocMemory, MPath.mvalT_up]
        rfl

/-- **The parameters declared** with the arguments: the arguments read, then
the rest with them on top. -/
theorem Args.runSt_declsThen {Δ : Ctx} (σ : State C Γ) : {ps : Ctx} → (as : Args C Γ ps) →
    (rest : Prog C (ps ++ Γ) Δ) →
      Prog.runSt σ (as.declsThen rest) =
        (as.evalT σ).bind fun a => Prog.runSt (σ.withEnv (TEnv.append ps a σ.env)) rest
  | _, .nil, rest => rfl
  | _, .snoc (ps := ps') as p x e, rest => by
    show Prog.runSt σ (as.declsThen (.cons (.declLocal p x (some (e.unders ps'))) rest)) = _
    rw [Args.runSt_declsThen σ as]
    show _ = (Args.evalT σ as >>= fun r => e.evalT σ >>= fun v => pure (v, r)).bind _
    cases as.evalT σ with
    | error => rfl
    | ok a =>
      show Prog.runSt _ (.cons _ rest) = (e.evalT σ >>= fun v => pure (v, a)).bind _
      rw [Prog.runSt_cons, Stmt.runSt_declLocal, Val.evalT_unders]
      cases e.evalT σ <;> rfl
  | _, .snocStorage (ps := ps') as R x e, rest => by
    show Prog.runSt σ (as.declsThen
      (.cons (.declStorage R x (some (.path (e.unders ps')))) rest)) = _
    rw [Args.runSt_declsThen σ as]
    show _ = (Args.evalT σ as >>= fun r =>
      e.resolveT σ >>= fun v => pure (some v, r)).bind _
    cases as.evalT σ with
    | error => rfl
    | ok a =>
      show Prog.runSt _ (.cons _ rest) =
        (e.resolveT σ >>= fun v => pure (some v, a)).bind _
      rw [Prog.runSt_cons, Stmt.runSt_declStorage, SPath.resolveT_unders]
      cases e.resolveT σ <;> rfl
  | _, .snocMemory (ps := ps') as R x e, rest => by
    show Prog.runSt σ (as.declsThen
      (.cons (.declMem R x (some (.alias (e.unders ps'))) rfl e.mapFree) rest)) = _
    rw [Args.runSt_declsThen σ as]
    show _ = (Args.evalT σ as >>= fun r =>
      e.mvalT σ >>= fun v => pure (some v, r)).bind _
    cases as.evalT σ with
    | error => rfl
    | ok a =>
      show Prog.runSt _ (.cons _ rest) =
        (e.mvalT σ >>= fun v => pure (some v, a)).bind _
      rw [Prog.runSt_cons, Stmt.runSt_declMem, MPath.mvalT_unders]
      cases e.mvalT σ <;> rfl

/-- **The return variables declared** at their defaults. -/
theorem Binders.runSt_declsThen {Δ : Ctx} (σ : State C Γ) : {ρ : Ctx} → (bs : Binders ρ) →
    (rest : Prog C (ρ ++ Γ) Δ) →
      Prog.runSt σ (bs.declsThen rest) =
        Prog.runSt (σ.withEnv (TEnv.append ρ (bs.defaultsT (C := C)) σ.env)) rest
  | _, .nil, rest => rfl
  | _, .snoc (ρ := ρ') bs p x, rest => by
    show Prog.runSt σ (bs.declsThen (.cons (.declLocal p x none) rest)) = _
    rw [Binders.runSt_declsThen σ bs, Prog.runSt_cons]
    rfl

/-- **A weakened body run as a block** runs as the body, lifted, its locals
popped. -/
theorem Stmt.run_block_wk {ρ Δ Γf : Ctx} (body : Prog C ρ Γf) (h : Thin ρ Δ) (τ : State C ρ)
    (d : TEnv C τ.H Δ) :
    Stmt.run (τ.lift h d) (.block (body.wk h).2.2) =
      liftedT h d ((Prog.run τ body).map (Out.drop body.ext)) :=
  (TWkRel.drop (Prog.wk_over body h) (Prog.run_wk body h τ d)).eq_lifted

/-- The caller's state with a frame's locals pushed, read as the frame's state
lifted (`Thin.atop`). -/
theorem State.withEnv_append_lift {ps : Ctx} (σ : State C Γ) (a : TEnv C σ.H ps) :
    σ.withEnv (TEnv.append ps a σ.env) =
      (σ.withEnv a).lift (Thin.atop ps Γ) (TEnv.append ps a σ.env) := by
  simp only [State.lift, State.withEnv, TEnv.put_atop, TEnv.drop_append]

end Pieces

/-! ## `expand_function_body` -/

section Calls

variable {Γ : Ctx} {m : Modality}

/-- `internalCallExpand` of a call with no result. -/
theorem Stmt.runSt_callNone {ps Γf : Ctx} (f : Name) (args : Args C Γ ps)
    (body : Prog C ([] ++ ps) Γf) (σ : State C Γ) :
    (Prog.runSt σ (args.declsThen
      (.cons (.block (body.wk (Thin.atop ps Γ)).2.2) .nil))).map (State.drop (Ext.append Γ ps)) =
      Stmt.runSt σ (.call f args .none body) := by
  rw [Args.runSt_declsThen]
  show _ = (TRun.call args .none body.ext body.runR σ).map (·.st)
  rw [TRun.call_eq]
  cases args.evalT σ with
  | error => rfl
  | ok a =>
    show (Prog.runSt _ _).map _ =
      (TRun.callFrom .none body.ext body.runR σ ⟨σ.withEnv a, List.prefix_refl _⟩).map _
    rw [Prog.runSt_single, State.withEnv_append_lift, Stmt.runSt, Stmt.run_block_wk]
    unfold TRun.callFrom Prog.run
    dsimp only
    cases Prog.runR body (σ.withEnv a) with
    | error => rfl
    | ok o =>
      exact congrArg Except.ok (by
        simp only [Out.drop, Out.lift, State.lift, State.drop, State.withEnv, TEnv.put_atop,
          TEnv.drop_append, TEnv.drop_wk, CallRet.leaveT])

/-- Soundness reuses the exact inlined call run. -/
theorem Premise.sound_callNone {ps Γf : Ctx} (f : Name) (args : Args C Γ ps)
    (body : Prog C ([] ++ ps) Γf) (σ : State C Γ) :
    Premise.Runs m (.call f args .none body)
      (.unfold (args.declsThen (.cons (.block (body.wk (Thin.atop ps Γ)).2.2) .nil))
        (Ext.append Γ ps)) σ :=
  Premise.sound_unfold σ (Stmt.runSt_callNone f args body σ)

theorem TRes.ok_bind {α β : Type} (a : α) (f : α → TRes β) : (Except.ok a : TRes α).bind f = f a :=
  rfl

/-- `functionBodyExpand` of a call whose result lands in `res`. -/
theorem Stmt.runSt_callVal {ps Γf : Ctx} (f : Name) (args : Args C Γ ps) (p : PrimTy)
    (r : Var) (res : Option (Idx Γ (.val p))) (body : Prog C ([.val p] ++ ps) Γf)
    (σ : State C Γ) :
    (Prog.runSt σ (args.declsThen (.cons (.declLocal p r none)
      (.cons (.block (body.wk (Thin.atop (.val p :: ps) Γ)).2.2) (match res with
        | none => .nil
        | some j => .cons (.assignLocal (j.under ps).there (.simple (.local .here))) .nil))))).map
      (State.drop (.push (Ext.append Γ ps))) = Stmt.runSt σ (.call f args (.val p r res) body) := by
  rw [Args.runSt_declsThen]
  show _ = (TRun.call args (.val p r res) body.ext body.runR σ).map (·.st)
  rw [TRun.call_eq]
  cases args.evalT σ with
  | error => rfl
  | ok a =>
    show (Prog.runSt _ _).map _ = (TRun.callFrom (.val p r res) body.ext body.runR σ
      ⟨σ.withEnv ((PrimTy.dflt p, a) : TEnv C σ.H (.val p :: ps)), List.prefix_refl _⟩).map _
    rw [Prog.runSt_cons, Stmt.runSt_declLocal_none, TRes.ok_bind, Prog.runSt_cons,
      show (σ.withEnv (TEnv.append ps a σ.env)).push (t := .val p) (PrimTy.dflt p) =
        σ.withEnv (TEnv.append (.val p :: ps) (PrimTy.dflt p, a) σ.env) from rfl,
      State.withEnv_append_lift (ps := .val p :: ps) σ (PrimTy.dflt p, a), Stmt.runSt,
      Stmt.run_block_wk]
    unfold TRun.callFrom Prog.run
    dsimp only
    cases Prog.runR body (σ.withEnv ((PrimTy.dflt p, a) : TEnv C σ.H (.val p :: ps))) with
    | error => rfl
    | ok o =>
      rw [show (Ext.append Γ ps).push = Ext.append Γ (LTy.val p :: ps) from rfl]
      cases res with
      | none =>
        exact congrArg Except.ok (by
          simp only [Out.drop, Out.lift, State.lift, State.drop, State.withEnv, CallRet.leaveT]
          erw [TEnv.drop_put_atop_wk (Γ := Γ) _ (LTy.val p :: ps)])
      | some j =>
        exact congrArg Except.ok (by
          simp only [Out.drop, Out.lift, State.lift, State.drop, State.withEnv, State.setLocal,
            show (j.under ps).there = j.under (LTy.val p :: ps) from rfl, TEnv.drop_set_under,
            CallRet.leaveT]
          erw [TEnv.drop_put_atop_wk (Γ := Γ) _ (LTy.val p :: ps)]
          rfl)

/-- Soundness reuses the exact inlined call run. -/
theorem Premise.sound_callVal {ps Γf : Ctx} (f : Name) (args : Args C Γ ps) (p : PrimTy)
    (r : Var) (res : Option (Idx Γ (.val p))) (body : Prog C ([.val p] ++ ps) Γf)
    (σ : State C Γ) :
    Premise.Runs m (.call f args (.val p r res) body)
      (.unfold (args.declsThen (.cons (.declLocal p r none)
        (.cons (.block (body.wk (Thin.atop (.val p :: ps) Γ)).2.2) (match res with
          | none => .nil
          | some j => .cons (.assignLocal (j.under ps).there (.simple (.local .here))) .nil))))
        (.push (Ext.append Γ ps))) σ := by
  cases res with
  | none => exact Premise.sound_unfold σ (Stmt.runSt_callVal f args p r none body σ)
  | some j => exact Premise.sound_unfold σ (Stmt.runSt_callVal f args p r (some j) body σ)

/-- `internalCallExpand` of a call that leaves its return variables
(`CallRet.rets`): the frame dropped from under them. -/
theorem Stmt.runSt_callRets {ps rs Γf : Ctx} (f : Name) (args : Args C Γ ps)
    (bs : Binders rs) (body : Prog C (rs ++ ps) Γf) (σ : State C Γ) :
    (Prog.runSt σ (args.declsThen (bs.declsThen
      (.cons (.block (body.wk (Thin.keepAll rs (Thin.atop ps Γ))).2.2) .nil)))).map
      (State.thin (Thin.keepAll rs (Thin.ofExt (Ext.append Γ ps)))) =
        Stmt.runSt σ (.call f args (.rets bs) body) := by
  rw [Args.runSt_declsThen]
  show _ = (TRun.call args (.rets bs) body.ext body.runR σ).map (·.st)
  rw [TRun.call_eq]
  cases args.evalT σ with
  | error => rfl
  | ok a =>
    show (Prog.runSt _ _).map _ = (TRun.callFrom (.rets bs) body.ext body.runR σ
      ⟨σ.withEnv (TEnv.append rs (bs.defaultsT (C := C)) a), List.prefix_refl _⟩).map _
    have hs : (σ.withEnv (TEnv.append ps a σ.env)).withEnv
        (TEnv.append rs (bs.defaultsT (C := C)) (σ.withEnv (TEnv.append ps a σ.env)).env) =
        (σ.withEnv (TEnv.append rs (bs.defaultsT (C := C)) a)).lift
          (Thin.keepAll rs (Thin.atop ps Γ))
          (TEnv.append rs (bs.defaultsT (C := C)) (TEnv.append ps a σ.env)) := by
      simp only [State.lift, State.withEnv, TEnv.put_keepAll, TEnv.put_atop, TEnv.drop_append]
    rw [Binders.runSt_declsThen, hs, Prog.runSt_single, Stmt.runSt, Stmt.run_block_wk]
    unfold TRun.callFrom Prog.run
    dsimp only
    cases Prog.runR body (σ.withEnv (TEnv.append rs (bs.defaultsT (C := C)) a)) with
    | error => rfl
    | ok o =>
      exact congrArg Except.ok (by
        simp only [Out.drop, Out.lift, State.lift, State.drop, State.thin, State.withEnv,
          CallRet.leaveT]
        erw [TEnv.thin_put_keepAllAtop])

/-- Soundness reuses the exact inlined call run. -/
theorem Premise.sound_callRets {ps rs Γf : Ctx} (f : Name) (args : Args C Γ ps)
    (bs : Binders rs) (body : Prog C (rs ++ ps) Γf) (σ : State C Γ) :
    Premise.Runs m (.call f args (.rets bs) body)
      (.inline (args.declsThen (bs.declsThen
          (.cons (.block (body.wk (Thin.keepAll rs (Thin.atop ps Γ))).2.2) .nil)))
        (Thin.keepAll rs (Thin.ofExt (Ext.append Γ ps)))) σ :=
  Premise.sound_inline σ (Stmt.runSt_callRets f args bs body σ)

theorem Stmt.runSt_declMem_none {Γ : Ctx} (R : RefTy) (x : Var) (hd : (Ty.ref R).defaultOkS = true)
    (hm : (Ty.ref R).mapFree = true) (σ : State C Γ) :
    Stmt.runSt σ (.declMem R x none hd hm) =
      .ok ((σ.allocDefaultG R hm).st.push (t := .mem R) (some (σ.allocDefaultG R hm).val)) := rfl

/-- `internalCallExpand` of a call with a memory return: the frame dropped
from under the object. -/
theorem Premise.sound_callMem {ps Γf : Ctx} (f : Name) (args : Args C Γ ps) (R : RefTy)
    (r : Var) (hd : (Ty.ref R).defaultOkS = true) (hm : (Ty.ref R).mapFree = true)
    (body : Prog C ([.mem R] ++ ps) Γf) (σ : State C Γ) :
    Premise.Runs m (.call f args (.mem R r hd hm) body)
      (.inline (args.declsThen (.cons (.declMem R r none hd hm)
          (.cons (.block (body.wk (Thin.atop (.mem R :: ps) Γ)).2.2) .nil)))
        (.keep (Thin.ofExt (Ext.append Γ ps)))) σ := by
  refine Premise.sound_inline σ ?_
  rw [Args.runSt_declsThen]
  show _ = (TRun.call args (.mem R r hd hm) body.ext body.runR σ).map (·.st)
  rw [TRun.call_eq]
  cases args.evalT σ with
  | error => rfl
  | ok a =>
    let g := (σ.withEnv a).allocDefaultG R hm
    show (Prog.runSt _ _).map _ = (TRun.callFrom (.mem R r hd hm) body.ext body.runR σ
      ⟨g.st.push (t := .mem R) (some g.val), g.ext⟩).map _
    rw [Prog.runSt_cons, Stmt.runSt_declMem_none, TRes.ok_bind, State.withEnv_append_lift,
      State.allocDefaultG_lift, Prog.runSt_single]
    show (Stmt.runSt ((g.st.push (t := .mem R) (some g.val)).lift (Thin.atop (.mem R :: ps) Γ)
      (some g.val, TEnv.wk g.ext _ (TEnv.append ps a σ.env))) _).map _ = _
    rw [Stmt.runSt, Stmt.run_block_wk]
    unfold TRun.callFrom Prog.run
    dsimp only
    cases Prog.runR body (g.st.push (t := .mem R) (some g.val)) with
    | error => rfl
    | ok o =>
      exact congrArg Except.ok (by
        simp only [Out.drop, Out.lift, State.lift, State.drop, State.thin, State.withEnv,
          CallRet.leaveT]
        erw [TEnv.thin_keep_put_atop]
        rfl)

/-! ## `functionCallArgCapture` -/

/-- `uint[] storage r;` starts an unset return alias without allocation. -/
theorem Stmt.runSt_declStorage_none {Γ : Ctx} (R : RefTy) (r : Var) (σ : State C Γ) :
    Stmt.runSt σ (.declStorage R r none) = .ok (σ.push (t := .alias R) none) := rfl

/-- `internalCallExpand` of `uint[] storage r = f();` keeps the returned
pointer while dropping the call's parameters and local frame. -/
theorem Premise.sound_callStorage {ps Γf : Ctx} (f : Name) (args : Args C Γ ps)
    (R : RefTy) (r : Var) (body : Prog C ([.alias R] ++ ps) Γf) (σ : State C Γ) :
    Premise.Runs m (.call f args (.storage R r) body)
      (.inline (args.declsThen (.cons (.declStorage R r none)
        (.cons (.block (body.wk (Thin.atop (.alias R :: ps) Γ)).2.2) .nil)))
        (.keep (Thin.ofExt (Ext.append Γ ps)))) σ := by
  refine Premise.sound_inline σ ?_
  rw [Args.runSt_declsThen]
  change _ = (TRun.call args (.storage R r) body.ext body.runR σ).map (·.st)
  rw [TRun.call_eq]
  cases args.evalT σ with
  | error => rfl
  | ok a =>
    simp only [TRes.ok_bind, ok_bind, Prog.runSt_cons, Stmt.runSt_declStorage_none]
    rw [show (σ.withEnv (TEnv.append ps a σ.env)).push (t := .alias R) none =
      σ.withEnv (TEnv.append (.alias R :: ps) (none, a) σ.env) from rfl,
      State.withEnv_append_lift, Stmt.runSt, Stmt.run_block_wk]
    unfold TRun.callFrom Prog.run CallRet.enterT
    dsimp only
    change _ = Except.map (fun o : Out C σ.H (.alias R :: Γ) => o.st)
      ((body.runR (σ.withEnv (Δ := .alias R :: ps) (none, a))).bind fun o =>
        .ok ⟨o.st.withEnv (Δ := .alias R :: Γ)
          ((TEnv.drop body.ext o.st.env).1, TEnv.wk o.ext Γ σ.env), o.ext⟩)
    cases body.runR (σ.withEnv (Δ := .alias R :: ps) (none, a)) with
    | error => rfl
    | ok o =>
      apply congrArg Except.ok
      simp only [Out.drop, Out.lift, State.lift, State.drop, State.thin, State.withEnv]
      erw [TEnv.thin_put_keepAllAtop (rs := [.alias R]) (r := (none, ()))]
      rfl

/-- A call's body run from the caller with a captured value on top: what it
leaves the caller, the capture popped (`F`), is what it leaves without it. -/
theorem TRun.callFrom_capture {Γ' Γ'' ps rs Γf : Ctx} {t : LTy} (ret : CallRet Γ rs Γ')
    (ret' : CallRet (t :: Γ) rs Γ'') (hb : Ext (rs ++ ps) Γf) (B : TStep C (rs ++ ps) Γf)
    (σ : State C Γ) (w : t.TDenote C σ.H) (o₁ : Out C σ.H (rs ++ ps))
    (F : State C Γ'' → State C Γ')
    (hF : ∀ (τ : State C Γf) (e : σ.H <+: τ.H) (x : TEnv C τ.H rs),
      F (τ.withEnv (ret'.leaveT (TEnv.wk e (t :: Γ) (σ.push w).env) x)) =
        τ.withEnv (ret.leaveT (TEnv.wk e Γ σ.env) x)) :
    ((TRun.callFrom ret' hb B (σ.push w) o₁).map (·.st)).map F =
      (TRun.callFrom ret hb B σ o₁).map (·.st) := by
  unfold TRun.callFrom
  cases B o₁.st with
  | error => rfl
  | ok o => exact congrArg Except.ok (hF _ _ _)

/-- **A call with an argument captured** (`functionCallArgCapture`): the
argument declared, then the call over it, what it leaves the caller with the
capture popped (`F`), runs as the call. -/
theorem TRun.call_capture_runSt {Γ' Γ'' ps rs Γf : Ctx} {f : Name} {x : Var} {p : PrimTy}
    (ret : CallRet Γ rs Γ') (ret' : CallRet (.val p :: Γ) rs Γ'') {args : Args C Γ ps}
    {v : Val C Γ p} {as' : Args C (.val p :: Γ) ps} (hc : args.capture = some ⟨p, v, as'⟩)
    (body : Prog C (rs ++ ps) Γf) (σ : State C Γ) (F : State C Γ'' → State C Γ')
    (hF : ∀ (w : p.Denote) (τ : State C Γf) (e : σ.H <+: τ.H) (y : TEnv C τ.H rs),
      F (τ.withEnv (ret'.leaveT (TEnv.wk e (.val p :: Γ) (σ.push (t := .val p) w).env) y)) =
        τ.withEnv (ret.leaveT (TEnv.wk e Γ σ.env) y))
    (hE : ∀ (w : p.Denote) (a : TEnv C σ.H ps),
      ret'.enterT ((σ.push (t := .val p) w).withEnv a) = ret.enterT (σ.withEnv a)) :
    (Prog.runSt σ (.cons (.declLocal p x (some v)) (.cons (.call f as' ret' body) .nil))).map F =
      Stmt.runSt σ (.call f args ret body) := by
  rw [Prog.runSt_cons, Stmt.runSt_declLocal]
  show _ = (TRun.call args ret body.ext body.runR σ).map (·.st)
  rw [TRun.call_eq, Args.evalT_capture σ args hc, bind_assoc]
  cases v.evalT σ with
  | error => rfl
  | ok w =>
    rw [ok_bind]
    show (Prog.runSt (σ.push (t := .val p) w) _).map _ = _
    rw [Prog.runSt_single]
    show ((TRun.call as' ret' body.ext body.runR (σ.push (t := .val p) w)).map _).map _ = _
    rw [TRun.call_eq]
    cases as'.evalT (σ.push (t := .val p) w) with
    | error => rfl
    | ok a =>
      rw [ok_bind, ok_bind, hE w a]
      exact TRun.callFrom_capture (t := .val p) ret ret' body.ext body.runR σ w _ F (hF w)

/-- `functionCallArgCapture` (none return). -/
theorem Premise.sound_callCaptureNone {ps Γf : Ctx} (k : Nat) (f : Name) (args : Args C Γ ps)
    (body : Prog C ([] ++ ps) Γf) {p : PrimTy} {v : Val C Γ p}
    {as' : Args C (.val p :: Γ) ps} (hc : args.capture = some ⟨p, v, as'⟩) (σ : State C Γ) :
    Premise.Runs m (.call f args .none body)
      (.capture p (fse k) v (.call f as' .none body)) σ :=
  Premise.sound_unfold σ
    (TRun.call_capture_runSt .none .none hc body σ _ (fun _ _ _ _ => rfl) fun _ _ => rfl)

/-- `functionCallArgCapture` (val return). -/
theorem Premise.sound_callCaptureVal {ps Γf : Ctx} (k : Nat) (f : Name) (args : Args C Γ ps)
    (q : PrimTy) (r : Var) (res : Option (Idx Γ (.val q)))
    (body : Prog C ([.val q] ++ ps) Γf) {p : PrimTy} {v : Val C Γ p}
    {as' : Args C (.val p :: Γ) ps} (hc : args.capture = some ⟨p, v, as'⟩) (σ : State C Γ) :
    Premise.Runs m (.call f args (.val q r res) body)
      (.capture p (fse k) v (.call f as' (.val q r (res.map .there)) body)) σ :=
  Premise.sound_unfold σ (TRun.call_capture_runSt (.val q r res) (.val q r (res.map .there)) hc
    body σ _ (fun _ _ _ _ => by cases res <;> rfl) fun _ _ => rfl)

/-- `functionCallArgCapture` (rets return). -/
theorem Premise.sound_callCaptureRets {ps rs Γf : Ctx} (k : Nat) (f : Name) (args : Args C Γ ps)
    (bs : Binders rs) (body : Prog C (rs ++ ps) Γf) {p : PrimTy} {v : Val C Γ p}
    {as' : Args C (.val p :: Γ) ps} (hc : args.capture = some ⟨p, v, as'⟩) (σ : State C Γ) :
    Premise.Runs m (.call f args (.rets bs) body)
      (.inline (.cons (.declLocal p (fse k) (some v)) (.cons (.call f as' (.rets bs) body) .nil))
        (Thin.keepAll rs (.drop .refl))) σ :=
  Premise.sound_inline σ (TRun.call_capture_runSt (.rets bs) (.rets bs) hc body σ _
    (fun _ _ _ _ => by
      simp only [State.thin, State.withEnv, CallRet.leaveT]
      erw [TEnv.thin_keepAll]
      rfl) fun _ _ => rfl)

/-- `functionCallArgCapture` (mem return). -/
theorem Premise.sound_callCaptureMem {ps Γf : Ctx} (k : Nat) (f : Name) (args : Args C Γ ps)
    (R : RefTy) (r : Var) (hd : (Ty.ref R).defaultOkS = true)
    (hm : (Ty.ref R).mapFree = true) (body : Prog C ([.mem R] ++ ps) Γf) {p : PrimTy}
    {v : Val C Γ p}
    {as' : Args C (.val p :: Γ) ps} (hc : args.capture = some ⟨p, v, as'⟩) (σ : State C Γ) :
    Premise.Runs m (.call f args (.mem R r hd hm) body)
      (.inline (.cons (.declLocal p (fse k) (some v))
          (.cons (.call f as' (.mem R r hd hm) body) .nil))
        (.keep (.drop .refl))) σ :=
  Premise.sound_inline σ (TRun.call_capture_runSt (.mem R r hd hm) (.mem R r hd hm) hc body σ _
    (fun _ _ _ _ => rfl) fun _ _ => rfl)

/-- `uint[] storage r = f(x + 1);`: capture the non-simple argument before
the storage-returning call and drop it from under the returned pointer. -/
theorem Premise.sound_callCaptureStorage {ps Γf : Ctx} (k : Nat) (f : Name)
    (args : Args C Γ ps) (R : RefTy) (r : Var) (body : Prog C ([.alias R] ++ ps) Γf)
    {p : PrimTy} {v : Val C Γ p} {as' : Args C (.val p :: Γ) ps}
    (hc : args.capture = some ⟨p, v, as'⟩) (σ : State C Γ) :
    Premise.Runs m (.call f args (.storage R r) body)
      (.inline (.cons (.declLocal p (fse k) (some v))
        (.cons (.call f as' (.storage R r) body) .nil)) (.keep (.drop .refl))) σ :=
  Premise.sound_inline σ (TRun.call_capture_runSt (.storage R r) (.storage R r) hc body σ _
    (fun _ _ _ _ => rfl) fun _ _ => rfl)

/-- **The rule of a call is sound** over the typed state: its leftmost
argument that is not simple captured, or its body inlined. -/
theorem Stmt.sound_call (k : Nat) (m : Modality) {Γ' ps rs Γf : Ctx} (f : Name)
    (args : Args C Γ ps) (ret : CallRet Γ rs Γ') (body : Prog C (rs ++ ps) Γf) (σ : State C Γ)
    (pr : Premise C Γ Γ') (hp : Stmt.step k m (.call f args ret body) = pr) :
    Premise.Runs m (.call f args ret body) pr σ := by
  change callStep k f args ret body = pr at hp
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
  | storage R r =>
    dsimp only at hp
    cases hc : args.capture with
    | some x =>
      obtain ⟨p, v, as'⟩ := x
      rw [hc] at hp; cases hp
      exact Premise.sound_callCaptureStorage k f args R r body hc σ
    | none =>
      rw [hc] at hp; cases hp
      exact Premise.sound_callStorage f args R r body σ

namespace CallReceiver

variable {E : Ty}

def shiftSource (v : Option (Src C Γ E)) :
    Option (Src C (.alias (.array E) :: Γ) E) :=
  v.map fun r => r.up

def pushAction (v : Option (Src C Γ E)) (hd : (v.isSome || E.defaultOkS) = true) :
    Stmt C (.alias (.array E) :: Γ) (.alias (.array E) :: Γ) :=
  .push (.alias .here) (shiftSource v) (by cases v <;> exact hd)

def pushCaptured (sp : Var) (v : Option (Src C Γ E))
    (hd : (v.isSome || E.defaultOkS) = true) :
    Prog C (.alias (.array E) :: Γ) (.alias (.array E) :: .alias (.array E) :: Γ) :=
  .cons (.declStorage (.array E) sp (some (.path (.alias .here))))
    (.cons (pushAction (shiftSource v) (by cases v <;> exact hd)) .nil)

/-- Duplicating the returned alias before push preserves the run, including
unset returns, argument failure, exhaustion and memory-copy sources. -/
theorem pushCaptureAgree (τ : State C (.alias (.array E) :: Γ)) (sp : Var)
    (v : Option (Src C Γ E)) (hd : (v.isSome || E.defaultOkS) = true) :
    (Prog.runSt τ (pushCaptured sp v hd)).map (State.drop (.push (.push .refl))) =
      (Stmt.runSt τ (pushAction v hd)).map (State.drop (.push .refl)) := by
  rw [pushCaptured, Prog.runSt_declStorage_cons, TRes.map_bind']
  cases hq : (SPath.alias (C := C) (Γ := .alias (.array E) :: Γ) (R := .array E) .here).resolveT τ with
  | ok q =>
    simp only [Except.bind, Prog.runSt_single]
    have hrun : (Stmt.runSt (τ.push (some q))
        (pushAction (shiftSource v) (by cases v <;> exact hd))).map (State.drop (.push .refl)) =
        Stmt.runSt τ (pushAction v hd) := by
      apply runSt_pushed τ (t := .alias (.array E)) (some q)
      cases v with
      | some src =>
        refine TRun.push_some_pushT τ (t := .alias (.array E)) (some q) _ _ _ _ ?_ ?_
        · exact hq.symm
        · exact Src.valueT_up τ (t := .alias (.array E)) (some q) src.up
      | none =>
        exact TRun.push_none_pushT τ (t := .alias (.array E)) (some q) _ _ hq.symm
    rw [← hrun]
    cases Stmt.runSt (τ.push (some q))
      (pushAction (shiftSource v) (by cases v <;> exact hd)) <;> rfl
  | error e =>
    simp only [bind, Except.bind, Except.map, pushAction, Stmt.runSt, Stmt.run, Stmt.runR,
      TRun.push, hq]

def popAction : Stmt C (.alias (.array E) :: Γ) (.alias (.array E) :: Γ) :=
  .pop (.alias .here)

def popCaptured (sp : Var) :
    Prog C (.alias (.array E) :: Γ) (.alias (.array E) :: .alias (.array E) :: Γ) :=
  .cons (.declStorage (.array E) sp (some (.path (.alias .here))))
    (.cons popAction .nil)

/-- A returned alias is captured once before pop, including an unset alias
or an empty array. -/
theorem popCaptureAgree (τ : State C (.alias (.array E) :: Γ)) (sp : Var) :
    (Prog.runSt τ (popCaptured sp)).map (State.drop (.push (.push .refl))) =
      (Stmt.runSt τ popAction).map (State.drop (.push .refl)) := by
  rw [popCaptured, Prog.runSt_declStorage_cons, TRes.map_bind']
  cases hq : (SPath.alias (C := C) (Γ := .alias (.array E) :: Γ) (R := .array E) .here).resolveT τ with
  | ok q =>
    simp only [Except.bind, Prog.runSt_single]
    have hrun : (Stmt.runSt (τ.push (some q)) popAction).map (State.drop (.push .refl)) =
        Stmt.runSt τ popAction :=
      runSt_pushed τ (t := .alias (.array E)) (some q)
        (TRun.pop_pushT τ (t := .alias (.array E)) (some q) _ _ hq.symm)
    rw [← hrun]
    cases Stmt.runSt (τ.push (some q)) (popAction (E := E)) <;> rfl
  | error e =>
    simp only [bind, Except.bind, Except.map, popAction, Stmt.runSt, Stmt.run, Stmt.runR,
      TRun.pop, hq]

def directPush {ps Γf : Ctx} (f : Name) (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf) (v : Option (Src C Γ E))
    (hd : (v.isSome || E.defaultOkS) = true) (σ : State C Γ) : TRes (State C Γ) :=
  (Stmt.runSt σ (.call f args (.storage (.array E) r) body)).bind fun τ =>
    (Stmt.runSt τ (pushAction v hd)).map (State.drop (.push .refl))

/-- The native push capture agrees for every callee, including failures,
heap growth and caller locals: the same getter is evaluated once on both sides. -/
theorem callPushCaptureAgree {ps Γf : Ctx} (f : Name) (args : Args C Γ ps) (r sp : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf) (v : Option (Src C Γ E))
    (hd : (v.isSome || E.defaultOkS) = true) (σ : State C Γ) :
    (Prog.runSt σ (.cons (.call f args (.storage (.array E) r) body)
      (pushCaptured sp v hd))).map (State.drop (.push (.push .refl))) =
        directPush f args r body v hd σ := by
  simp only [directPush, Prog.runSt_cons, TRes.map_bind', pushCaptureAgree]

def directPop {ps Γf : Ctx} (f : Name) (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf) (σ : State C Γ) : TRes (State C Γ) :=
  (Stmt.runSt σ (.call f args (.storage (.array E) r) body)).bind fun τ =>
    (Stmt.runSt τ popAction).map (State.drop (.push .refl))

/-- The native pop capture agrees for every callee, including failed and
unset storage returns. -/
theorem callPopCaptureAgree {ps Γf : Ctx} (f : Name) (args : Args C Γ ps) (r sp : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf) (σ : State C Γ) :
    (Prog.runSt σ (.cons (.call f args (.storage (.array E) r) body)
      (popCaptured sp))).map (State.drop (.push (.push .refl))) =
        directPop f args r body σ := by
  simp only [directPop, Prog.runSt_cons, TRes.map_bind', popCaptureAgree]

/-- Bridge the prototype's ordered push to the integrated typed statement. -/
theorem callReceiver_push_run {ps Γf : Ctx} (f : Name) (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf) (v : Option (Src C Γ E))
    (hd : (v.isSome || E.defaultOkS) = true) (σ : State C Γ) :
    Stmt.runSt σ (.callReceiver f args r body (.push v hd)) =
      directPush f args r body v hd σ := by
  change (TRun.callReceiver args r body.ext body.runR (.push v hd) σ).map (·.st) =
    ((TRun.call args (.storage (.array E) r) body.ext body.runR σ).map (·.st)).bind fun τ =>
      ((TRun.push (.alias .here) (shiftSource v) τ).map (·.st)).map (State.drop (.push .refl))
  simp only [TRun.callReceiver, TRun.receiverOp, ReceiverOp.wk, shiftSource, Src.up_eq]
  cases TRun.call args (.storage (.array E) r) body.ext body.runR σ with
  | error => rfl
  | ok o =>
    dsimp only [bind, Except.bind, Except.map]
    cases TRun.push (.alias .here) (v.map (·.wk (.drop .refl))) o.st <;> rfl

/-- Bridge the prototype's ordered pop to the integrated typed statement. -/
theorem callReceiver_pop_run {ps Γf : Ctx} (f : Name) (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf) (σ : State C Γ) :
    Stmt.runSt σ (.callReceiver f args r body (.pop (E := E))) =
      directPop f args r body σ := by
  change (TRun.callReceiver args r body.ext body.runR .pop σ).map (·.st) =
    ((TRun.call args (.storage (.array E) r) body.ext body.runR σ).map (·.st)).bind fun τ =>
      ((TRun.pop (.alias .here) τ).map (·.st)).map (State.drop (.push .refl))
  simp only [TRun.callReceiver, TRun.receiverOp, ReceiverOp.wk]
  cases TRun.call args (.storage (.array E) r) body.ext body.runR σ with
  | error => rfl
  | ok o =>
    dsimp only [bind, Except.bind, Except.map]
    cases TRun.pop (.alias .here) o.st <;> rfl

/-- The integrated strategy capture agrees with its native statement for every getter. -/
theorem callReceiver_capture_run {ps Γf : Ctx} (k : Nat) (f : Name) (args : Args C Γ ps)
    (r : Var) (body : Prog C ([.alias (.array E)] ++ ps) Γf) (op : ReceiverOp C Γ E)
    (σ : State C Γ) :
    (Prog.runSt σ (callReceiverCapture k f args r body op)).map
        (State.drop (.push (.push .refl))) =
      Stmt.runSt σ (.callReceiver f args r body op) := by
  cases op with
  | push v hd =>
    rw [callReceiver_push_run]
    simpa only [callReceiverCapture, ReceiverOp.wk, ReceiverOp.toStmt,
      pushCaptured, pushAction, shiftSource, Src.up_eq] using
      callPushCaptureAgree f args r (fsp k) body v hd σ
  | pop =>
    rw [callReceiver_pop_run]
    exact callPopCaptureAgree f args r (fsp k) body σ

end CallReceiver

/-- Capturing `f()` in `sp` before `sp.push(e)` or `sp.pop()` preserves its run. -/
theorem Stmt.sound_callReceiver (k : Nat) (m : Modality) {ps Γf : Ctx} {E : Ty}
    (f : Name) (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf) (op : ReceiverOp C Γ E)
    (σ : State C Γ) (pr : Premise C Γ Γ)
    (hp : Stmt.step k m (.callReceiver f args r body op) = pr) :
    Premise.Runs m (.callReceiver f args r body op) pr σ := by
  cases hp
  exact Premise.sound_unfold σ (CallReceiver.callReceiver_capture_run k f args r body op σ)

/-- The capture taclet for `f().push(i++)` preserves the native statement's run. -/
theorem Stmt.sound_callReceiverPush (k : Nat) (m : Modality) {ps Γf Γv : Ctx} {E : Ty}
    (f : Name) (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf)
    (code : Prog C Γ Γv) (value : Src C Γv E)
    (σ : State C Γ) (pr : Premise C Γ Γ)
    (hp : Stmt.step k m (.callReceiverPush f args r body code value) = pr) :
    Premise.Runs m (.callReceiverPush f args r body code value) pr σ := by
  cases hp
  apply Premise.sound_unfold σ
  have h := congrArg (fun x => x.map (·.st))
    (NativeDeferred.capture_run k f args r body code value σ)
  cases hr : (callReceiverPushCapture k f args r body code value).run σ <;>
    simpa only [Prog.runSt, Stmt.runSt, hr, Except.map, Out.drop] using h

end Calls

/-! ## `try` -/

section Try

variable {Γ : Ctx}

/-- Decoding reverts, never panics. -/
theorem Binders.decodeT_ne_panic {H : HTy} {ρ : Ctx} (bs : Binders ρ) :
    ∀ (vs : List Semantics.Word), bs.decodeT (C := C) (H := H) vs ≠ .error .panic := by
  induction bs with
  | nil => intro _ h; cases h
  | snoc bs p x ih =>
    intro vs h
    have hb : Binders.decodeT (C := C) (H := H) (Binders.snoc bs p x) vs =
        (bs.decodeT (C := C) (H := H) vs >>= fun er => match er.2 with
          | v :: rest => match PrimTy.ofWord? p v with
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
        change (match PrimTy.ofWord? p v with
          | some x => pure ((x, e), rest)
          | none => Except.error THalt.revert : TRes _) = _ at h
        split at h <;> cases h

/-- `∀ xs. ψ` holds at every typed value of the binders. -/
theorem holds_binders_all {ρ : Ctx} (bs : Binders ρ) :
    ∀ (σ : State C Γ) (ψ : Fml C (ρ ++ Γ)) (r : TEnv C σ.H ρ), holds σ (bs.all ψ) →
      holds (σ.withEnv (TEnv.append ρ r σ.env)) ψ := by
  induction bs with
  | nil => intro σ ψ _ h; exact h
  | snoc bs p x ih =>
    intro σ ψ r h
    exact ih σ (.all x p ψ) r.2 h r.1

/-- A block's goal under the box, its locals popped by `h`: the block's run,
then the rest. -/
theorem holds_modalK_pop {Γ₂ Γ₀ Δ Γ₁ : Ctx} (τ : State C Δ) (P : Prog C Δ Γ₁) (h : Ext Γ Γ₁)
    (ω : Prog C Γ Γ₂) (κ : Frames C Γ₂ Γ₀) (φ : Fml C Γ₀)
    (hp : holds τ (Fml.modalK .box P (.pop .block h (.seq ω κ)) φ)) :
    Modality.afterRunTR .box (holds · φ)
      (((Prog.runSt τ P).map (State.drop h)).bind fun υ =>
        (Prog.runSt υ ω).bind (Frames.runSt · κ)) := by
  have h' := (holds_modal_iff τ P _ φ).1 (holds_modalK τ P _ φ hp)
  revert h'
  cases Prog.runSt τ P with
  | error => exact id
  | ok υ =>
    intro h'
    change Modality.afterRunTR .box _ (Frames.runSt υ (.pop .block h (.seq ω κ))) at h'
    rw [Frames.runSt_pop, Frames.runSt_seq] at h'
    exact h'

/-- A halt that is no panic, under the box. -/
theorem afterRunTR_box_error {Γ₂ Γ₀ : Ctx} {ω : Prog C Γ Γ₂} {κ : Frames C Γ₂ Γ₀} {φ : Fml C Γ₀}
    {e : THalt} (he : e ≠ .panic) :
    Modality.afterRunTR .box (holds · φ)
      ((Except.error e : TRes (State C Γ)).bind fun υ =>
        (Prog.runSt υ ω).bind (Frames.runSt · κ)) :=
  ⟨trivial, fun h => he (Except.error.inj h)⟩

/-! ### Self-calls (`tryCallSelfBox`, Lean) -/

theorem ExtCall.hasCode_evalT (c : ExtCall C Γ) (σ : State C Γ) :
    c.hasCode.evalT σ = .ok (!decide ((c.addr.evalT σ).1 = 0) : Bool) := rfl

theorem ExtCall.isSelf_evalT (c : ExtCall C Γ) (σ : State C Γ) :
    c.isSelf.evalT σ = .ok (decide ((c.addr.evalT σ).1 = σ.tx.selfAddress.1) : Bool) := rfl

theorem ExtCall.notSelf_evalT (c : ExtCall C Γ) (σ : State C Γ) :
    c.notSelf.evalT σ = .ok (!decide ((c.addr.evalT σ).1 = σ.tx.selfAddress.1) : Bool) := rfl

theorem TEnv.put_ofExt_append {H : HTy} : (ρ : Ctx) → (r : TEnv C H ρ) → (x : TEnv C H Γ) →
    TEnv.put (Thin.ofExt (Ext.append Γ ρ)) x (TEnv.append ρ r x) = TEnv.append ρ r x
  | [], _, _ => rfl
  | _ :: ρ, r, x => by
    show (r.1, TEnv.put (Thin.ofExt (Ext.append Γ ρ)) x (TEnv.append ρ r.2 x)) =
      (r.1, TEnv.append ρ r.2 x)
    rw [TEnv.put_ofExt_append ρ r.2 x]

/-- A receiver read past the locals a clause binds. -/
theorem ExtCall.addr_wk_append {ρ : Ctx} (c : ExtCall C Γ) (σ : State C Γ)
    (r : TEnv C σ.H ρ) :
    (c.wk (Thin.ofExt (Ext.append Γ ρ))).addr.evalT (σ.withEnv (TEnv.append ρ r σ.env)) =
      c.addr.evalT σ := by
  have hl : σ.withEnv (TEnv.append ρ r σ.env) =
      σ.lift (Thin.ofExt (Ext.append Γ ρ)) (TEnv.append ρ r σ.env) := by
    show _ = σ.withEnv (TEnv.put _ σ.env _)
    rw [TEnv.put_ofExt_append]
  rw [hl]
  exact Simple.evalT_wk _ σ _ _

theorem Prog.runSt_require_true {Γ₁ : Ctx} {c : Val C Γ .bool} {σ : State C Γ}
    (h : c.evalT σ = .ok true) (P : Prog C Γ Γ₁) :
    Prog.runSt σ (.cons (.require c) P) = Prog.runSt σ P := by
  rw [Prog.runSt_cons]
  show ((TRun.require c σ).map (·.st)).bind _ = _
  simp only [TRun.require, h]
  rfl

theorem Prog.runSt_require_false {Γ₁ : Ctx} {c : Val C Γ .bool} {σ : State C Γ}
    (h : c.evalT σ = .ok false) (P : Prog C Γ Γ₁) :
    Prog.runSt σ (.cons (.require c) P) = .error .revert := by
  rw [Prog.runSt_cons]
  show ((TRun.require c σ).map (·.st)).bind _ = _
  simp only [TRun.require, h]
  rfl

/-- A `catch` clause of no binders run from the caller's state, under the
box, from its goal. -/
theorem holds_tryClause {Γ₁ Γ₂ Γ₀ : Ctx} (P : Prog C Γ Γ₁) (σ : State C Γ)
    (ω : Prog C Γ Γ₂) (κ : Frames C Γ₂ Γ₀) (φ : Fml C Γ₀)
    (h : holds σ (Binders.nil.all (Fml.modalK .box P
      (.pop .block ((Ext.append Γ []).trans P.ext) (.seq ω κ)) φ))) :
    Modality.afterRunTR .box (holds · φ)
      ((((P.runR σ).map fun o => (⟨o.st.drop P.ext, o.ext⟩ : Out C σ.H Γ)).map (·.st)).bind
        fun υ => (Prog.runSt υ ω).bind (Frames.runSt · κ)) := by
  have h' := holds_modalK_pop σ P ((Ext.append Γ []).trans P.ext) ω κ φ h
  rw [show (Ext.append Γ []).trans P.ext = P.ext from Subsingleton.elim _ _] at h'
  rw [TRes.map_st _ _ (State.drop P.ext) fun _ => rfl]
  exact h'

/-- The `Panic` clause run with the code `c` bound, under the box. -/
theorem holds_tryPanic {κc Γ₃ Γ₂ Γ₀ : Ctx} (code : CodeBinder κc) (pnc : Prog C (κc ++ Γ) Γ₃)
    (σ : State C Γ) (c : Semantics.Word) (ω : Prog C Γ Γ₂) (κ : Frames C Γ₂ Γ₀) (φ : Fml C Γ₀)
    (h : holds σ (code.binders.all (Fml.modalK .box pnc
      (.pop .block ((Ext.append Γ κc).trans pnc.ext) (.seq ω κ)) φ))) :
    Modality.afterRunTR .box (holds · φ)
      ((((pnc.runR (σ.withEnv (TEnv.append κc (code.decodeT (H := σ.H) c) σ.env))).map
          fun o => (⟨o.st.drop ((Ext.append Γ κc).trans pnc.ext), o.ext⟩ : Out C σ.H Γ)).map
            (·.st)).bind fun υ => (Prog.runSt υ ω).bind (Frames.runSt · κ)) := by
  rw [TRes.map_st _ _ (State.drop ((Ext.append Γ κc).trans pnc.ext)) fun _ => rfl]
  exact holds_modalK_pop _ pnc _ ω κ φ
    (holds_binders_all code.binders σ _ (code.decodeT (H := σ.H) c) h)

/-- The oracle's reading of a `try` (`TRun.tryCall` past the self-call):
under the box, a goal per clause, each for every typed value its outcome
binds; `h1` the success clause's goal at the values bound. -/
theorem Premise.sound_tryOracle {ρ κc Γ₁ Γe Γ₃ Γ₄ Γ₂ Γ₀ : Ctx} (call : ExtCall C Γ)
    (rets : Binders ρ) (ok : Prog C (ρ ++ Γ) Γ₁) (err : Prog C Γ Γe) (code : CodeBinder κc)
    (pnc : Prog C (κc ++ Γ) Γ₃) (other : Prog C Γ Γ₄) (σ : State C Γ)
    (ω : Prog C Γ Γ₂) (κ : Frames C Γ₂ Γ₀) (φ : Fml C Γ₀)
    (h1 : ∀ r : TEnv C σ.H ρ, Modality.afterRunTR .box (holds · φ)
      (((Prog.runSt (σ.withEnv (TEnv.append ρ r σ.env)) ok).map
        (State.drop ((Ext.append Γ ρ).trans ok.ext))).bind fun υ =>
          (Prog.runSt υ ω).bind (Frames.runSt · κ)))
    (h2 : holds σ (Binders.nil.all (Fml.modalK .box err
      (.pop .block ((Ext.append Γ []).trans err.ext) (.seq ω κ)) φ)))
    (h3 : holds σ (code.binders.all (Fml.modalK .box pnc
      (.pop .block ((Ext.append Γ κc).trans pnc.ext) (.seq ω κ)) φ)))
    (h4 : holds σ (Binders.nil.all (Fml.modalK .box other
      (.pop .block ((Ext.append Γ []).trans other.ext) (.seq ω κ)) φ))) :
    Modality.afterRunTR .box (holds · φ)
      (((match lookupBy (call.keyT σ) σ.tx.ext with
        | none => .error .revert
        | some (.ok vs) => do
          let (r, _) ← rets.decodeT (H := σ.H) vs
          (ok.runR (σ.withEnv (TEnv.append ρ r σ.env))).map fun o =>
            ⟨o.st.drop ((Ext.append Γ ρ).trans ok.ext), o.ext⟩
        | some .error => (err.runR σ).map fun o => ⟨o.st.drop err.ext, o.ext⟩
        | some (.panic c) =>
          (pnc.runR (σ.withEnv (TEnv.append κc (code.decodeT (H := σ.H) c) σ.env))).map
            fun o => ⟨o.st.drop ((Ext.append Γ κc).trans pnc.ext), o.ext⟩
        | some .other => (other.runR σ).map fun o => ⟨o.st.drop other.ext, o.ext⟩ :
          TRes (Out C σ.H Γ)).map (·.st)).bind fun υ =>
            (Prog.runSt υ ω).bind (Frames.runSt · κ)) := by
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
        rw [ok_bind]
        dsimp only
        rw [TRes.map_st _ _ (State.drop ((Ext.append Γ ρ).trans ok.ext)) fun _ => rfl]
        exact h1 r
    | error => exact holds_tryClause err σ ω κ φ h2
    | panic c => exact holds_tryPanic code pnc σ c ω κ φ h3
    | other => exact holds_tryClause other σ ω κ φ h4

/-- `tryCallNoCallbackBox`: under the box, a goal per clause, each for every
typed value its outcome binds (another contract's callee; at address `0`
the caller reverts, which the box accepts). -/
theorem Premise.sound_tryCallBox {ρ κc Γ₁ Γe Γ₃ Γ₄ ps Γf : Ctx} (call : ExtCall C Γ)
    (rets : Binders ρ) (ok : Prog C (ρ ++ Γ) Γ₁) (err : Prog C Γ Γe) (code : CodeBinder κc)
    (pnc : Prog C (κc ++ Γ) Γ₃) (other : Prog C Γ Γ₄) (sargs : Args C Γ ps)
    (sbody : Prog C (ρ ++ ps) Γf) (σ : State C Γ) :
    Premise.Runs .box (.tryCall call rets ok err code pnc other sargs sbody false)
      (.branches [⟨rets, ok⟩, ⟨Binders.nil, err⟩, ⟨code.binders, pnc⟩, ⟨Binders.nil, other⟩])
      σ := by
  intro _ _ ω κ φ
  rintro ⟨h1, h2, h3, h4⟩
  rw [holds_modal_iff, runSt_cons_frames]
  show Modality.afterRunTR .box _ (((TRun.tryCall call rets ok.ext ok.runR err.ext err.runR
    code pnc.ext pnc.runR other.ext other.runR sargs sbody.ext sbody.runR false σ).map
      (·.st)).bind _)
  unfold TRun.tryCall
  split
  · exact afterRunTR_box_error (by decide)
  rw [if_neg (by simp only [Bool.false_and, Bool.false_eq_true, not_false_eq_true])]
  exact Premise.sound_tryOracle call rets ok err code pnc other σ ω κ φ
    (fun r => holds_modalK_pop _ ok _ ω κ φ (holds_binders_all rets σ _ r h1)) h2 h3 h4

/-- **`tryCallSelfBox`** (Lean): the receiver the contract, the inlined
callee and then the success block; another, the oracle's success block,
both behind `require`s that are the run's case split; each `catch` block
from the caller's state, which a failed self-call goes to as the oracle's
does. -/
theorem Premise.sound_trySelfBox {ρ κc Γ₁ Γe Γ₃ Γ₄ ps Γf : Ctx} (call : ExtCall C Γ)
    (rets : Binders ρ) (ok : Prog C (ρ ++ Γ) Γ₁) (err : Prog C Γ Γe) (code : CodeBinder κc)
    (pnc : Prog C (κc ++ Γ) Γ₃) (other : Prog C Γ Γ₄) (sargs : Args C Γ ps)
    (sbody : Prog C (ρ ++ ps) Γf) (σ : State C Γ) :
    Premise.Runs .box (.tryCall call rets ok err code pnc other sargs sbody true)
      (trySelfStep call rets ok err code pnc other sargs sbody) σ := by
  intro _ _ ω κ φ
  rintro ⟨h0, h1, h2, h3, h4⟩
  rw [holds_modal_iff, runSt_cons_frames]
  show Modality.afterRunTR .box _ (((TRun.tryCall call rets ok.ext ok.runR err.ext err.runR
    code pnc.ext pnc.runR other.ext other.runR sargs sbody.ext sbody.runR true σ).map
      (·.st)).bind _)
  unfold TRun.tryCall
  split
  · exact afterRunTR_box_error (by decide)
  rename_i hz
  have hc : call.hasCode.evalT σ = .ok true := by
    rw [ExtCall.hasCode_evalT]; simp only [hz, decide_false, Bool.not_false]
  split
  · rename_i hs
    simp only [Bool.true_and, decide_eq_true_eq] at hs
    have hi : call.isSelf.evalT σ = .ok true := by
      rw [ExtCall.isSelf_evalT]; simp only [hs, decide_true]
    let P0 : Prog C Γ Γ₁ := .cons (.require call.hasCode) (.cons (.require call.isSelf)
      (.cons (.call call.fn sargs (.rets rets) sbody) ok))
    have h0' := holds_modalK_pop σ P0 ((Ext.append Γ ρ).trans ok.ext) ω κ φ (by
      rw [show (Ext.append Γ ρ).trans ok.ext = (Ext.append Γ []).trans P0.ext from
        Subsingleton.elim _ _]
      exact h0)
    rw [Prog.runSt_require_true hc, Prog.runSt_require_true hi, Prog.runSt_cons] at h0'
    change Modality.afterRunTR .box _ (((((TRun.call sargs (.rets rets) sbody.ext sbody.runR
      σ).map (·.st)).bind fun τ => Prog.runSt τ ok).map _).bind _) at h0'
    revert h0'
    cases TRun.call sargs (.rets rets) sbody.ext sbody.runR σ with
    | ok o =>
      intro h0'
      dsimp only
      rw [show ((Except.ok o : TRes (Out C σ.H (ρ ++ Γ))).map (·.st)).bind
        (fun τ => Prog.runSt τ ok) = (ok.runR o.st).map (·.st) from rfl] at h0'
      revert h0'
      cases ok.runR o.st <;> exact id
    | error e =>
      intro _
      cases e with
      | revert =>
        dsimp only
        split
        · exact holds_tryClause err σ ω κ φ h2
        · exact holds_tryClause other σ ω κ φ h4
      | panic => exact holds_tryPanic code pnc σ _ ω κ φ h3
      | diverge => exact afterRunTR_box_error (by decide)
      | exhausted => exact afterRunTR_box_error (by decide)
  · rename_i hs
    simp only [Bool.true_and, decide_eq_true_eq] at hs
    refine Premise.sound_tryOracle call rets ok err code pnc other σ ω κ φ (fun r => ?_) h2 h3 h4
    have h1' := holds_modalK_pop _ _ _ ω κ φ (holds_binders_all rets σ _ r h1)
    have hc' : (call.wk (Thin.ofExt (Ext.append Γ ρ))).hasCode.evalT
        (σ.withEnv (TEnv.append ρ r σ.env)) = .ok true := by
      rw [ExtCall.hasCode_evalT, ExtCall.addr_wk_append]; simp only [hz, decide_false, Bool.not_false]
    have hn : (call.wk (Thin.ofExt (Ext.append Γ ρ))).notSelf.evalT
        (σ.withEnv (TEnv.append ρ r σ.env)) = .ok true := by
      rw [ExtCall.notSelf_evalT, ExtCall.addr_wk_append]
      show Except.ok (!decide ((call.addr.evalT σ).1 = σ.tx.selfAddress.1)) = _
      simp only [hs, decide_false, Bool.not_false]
    dsimp only at h1'
    rw [Prog.runSt_require_true hc', Prog.runSt_require_true hn] at h1'
    rwa [show (Ext.append Γ ρ).trans (Prog.cons (.require _) (.cons (.require _) ok)).ext =
      (Ext.append Γ ρ).trans ok.ext from Subsingleton.elim _ _] at h1'

/-- **The rule of a `try` is sound** over the typed state: a goal per clause
under the box, `false` under the diamond. -/
theorem Stmt.sound_tryCall (k : Nat) (m : Modality) {ρ κc Γ₁ Γe Γ₃ Γ₄ ps Γf : Ctx}
    (call : ExtCall C Γ) (rets : Binders ρ) (ok : Prog C (ρ ++ Γ) Γ₁) (err : Prog C Γ Γe)
    (code : CodeBinder κc) (pnc : Prog C (κc ++ Γ) Γ₃) (other : Prog C Γ Γ₄)
    (sargs : Args C Γ ps) (sbody : Prog C (ρ ++ ps) Γf) (self : Bool) (σ : State C Γ)
    (pr : Premise C Γ Γ)
    (hp : Stmt.step k m (.tryCall call rets ok err code pnc other sargs sbody self) = pr) :
    Premise.Runs m (.tryCall call rets ok err code pnc other sargs sbody self) pr σ := by
  change tryStepS m call rets ok err code pnc other sargs sbody self = pr at hp
  cases self with
  | false =>
    cases m with
    | box => cases hp; exact Premise.sound_tryCallBox call rets ok err code pnc other sargs sbody σ
    | diamond => cases hp; exact Premise.sound_done σ false nofun
  | true =>
    cases m with
    | box => cases hp; exact Premise.sound_trySelfBox call rets ok err code pnc other sargs sbody σ
    | diamond => cases hp; exact Premise.sound_done σ false nofun

end Try

end Solidity
