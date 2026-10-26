import Solidity.Calculus.CallbackSound.Rules

/-!
# Callback soundness: calls, loops, the theorem

A call and a loop by its invariant with callbacks, soundness, and the
invariant assumed.

A piece of `Calculus/CallbackSound.lean`, whose docstring describes the whole.
-/

namespace Solidity

open Solidity (Modality RuleSet)

variable {C : Contract} {pay : Bool}

/-! ## A call, with callbacks

`Stmt.step`'s premise for a call inlines its body (`callStep`): the
parameters declared with the arguments (`Args.declsThen`), the body weakened
under the caller's locals (`Thin.atop`) as a block.  With callbacks the call
runs its body in its own frame (`ExecS.callBody`); the inlined block runs the
weakened body, which has the same runs, lifted (`Prog.exec_wk`). -/

section Calls

open DeferredSource.Callback (map_cat_refl singleton_iff block_of_execP)

variable {I : Fml C []} {J : StateInv C}

/-- A callback run from a state equal to another, the outcome at a heap
both have: from the other.  At states whose heaps reduce to the same one
(`hX hY := rfl`), the casts are the identity. -/
theorem ExecS.transport {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} {H : HTy} {X Y : State C Γ}
    (hX : X.H = H) (hY : Y.H = H) (e : X = Y) {u : COut C H Γ'} (h : ExecS J X s (hX ▸ u)) :
    ExecS J Y s (hY ▸ u) := by
  subst e; subst hX; exact h

/-- A statement that hands control to nobody and ends in `τ` has that
callback run. -/
theorem ExecS.det_ok {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} {σ : State C Γ} {τ : State C Γ'}
    (hs : s.forksIn J.pay = false) (h : Stmt.runSt σ s = .ok τ) :
    ∃ e : σ.H <+: τ.H, ExecS J σ s (.ok ⟨τ, e⟩) := by
  have hd := ExecS.det (J := J) (σ := σ) hs
  cases hr : s.run σ with
  | error e => simp only [Stmt.runSt, hr, Except.map, reduceCtorEq] at h
  | ok o =>
    rw [hr] at hd
    simp only [Stmt.runSt, hr, Except.map, Except.ok.injEq] at h
    subst h
    exact ⟨o.ext, hd⟩

/-- **The parameters declared, with callbacks**: they hand control to nobody,
so the rest runs from the arguments pushed. -/
theorem Args.execP_declsThen {Γ Δ : Ctx} : {ps : Ctx} → (as : Args C Γ ps) →
    (rest : Prog C (ps ++ Γ) Δ) → (σ : State C Γ) → (a : TEnv C σ.H ps) → as.evalT σ = .ok a →
    ∀ {u : COut C σ.H Δ}, ExecP J (σ.withEnv (TEnv.append ps a σ.env)) rest u →
      ExecP J σ (as.declsThen rest) u
  | _, .nil, _, _, _, _, _, h => h
  | _, .snoc (ps := ps') as p x e, rest, σ, a, ha, u, h => by
    obtain ⟨v, a'⟩ := a
    rw [Args.evalT_snoc] at ha
    cases ha' : as.evalT σ with
    | error => rw [ha'] at ha; cases ha
    | ok a'' =>
      rw [ha'] at ha
      cases hv : e.evalT σ with
      | error => simp only [hv, bind, Except.bind] at ha; cases ha
      | ok v' =>
        simp only [hv, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ha
        obtain ⟨rfl, rfl⟩ := ha
        refine Args.execP_declsThen as _ σ a'' ha' ?_
        obtain ⟨_, hd⟩ := ExecS.det_ok (J := J) (σ := σ.withEnv (TEnv.append ps' a'' σ.env))
          (s := .declLocal p x (some (e.unders ps'))) rfl
          (by rw [Stmt.runSt_declLocal, Val.evalT_unders, hv]; rfl)
        simpa only [map_cat_refl] using ExecP.cons hd h
  | _, .snocStorage (ps := ps') as R x e, rest, σ, a, ha, u, h => by
    obtain ⟨v, a'⟩ := a
    rw [Args.evalT_snocStorage] at ha
    cases ha' : as.evalT σ with
    | error => rw [ha'] at ha; cases ha
    | ok a'' =>
      rw [ha'] at ha
      cases hv : e.resolveT σ with
      | error => simp only [hv, bind, Except.bind] at ha; cases ha
      | ok q =>
        simp only [hv, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ha
        obtain ⟨rfl, rfl⟩ := ha
        refine Args.execP_declsThen as _ σ a'' ha' ?_
        obtain ⟨_, hd⟩ := ExecS.det_ok (J := J) (σ := σ.withEnv (TEnv.append ps' a'' σ.env))
          (s := .declStorage R x (some (.path (e.unders ps')))) rfl
          (by rw [Stmt.runSt_declStorage, SPath.resolveT_unders, hv]; rfl)
        simpa only [map_cat_refl] using ExecP.cons hd h
  | _, .snocMemory (ps := ps') as R x e, rest, σ, a, ha, u, h => by
    obtain ⟨v, a'⟩ := a
    rw [Args.evalT_snocMemory] at ha
    cases ha' : as.evalT σ with
    | error => rw [ha'] at ha; cases ha
    | ok a'' =>
      rw [ha'] at ha
      cases hv : e.mvalT σ with
      | error => simp only [hv, bind, Except.bind] at ha; cases ha
      | ok q =>
        simp only [hv, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ha
        obtain ⟨rfl, rfl⟩ := ha
        refine Args.execP_declsThen as _ σ a'' ha' ?_
        obtain ⟨_, hd⟩ := ExecS.det_ok (J := J) (σ := σ.withEnv (TEnv.append ps' a'' σ.env))
          (s := .declMem R x (some (.alias (e.unders ps'))) rfl e.mapFree) rfl
          (by rw [Stmt.runSt_declMem, MPath.mvalT_unders, hv]; rfl)
        simpa only [map_cat_refl] using ExecP.cons hd h

/-- A statement that hands control to nobody and halts has that callback run. -/
theorem ExecS.det_err {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} {σ : State C Γ} {e : THalt}
    (hs : s.forksIn J.pay = false) (h : Stmt.runSt σ s = .error e) :
    ExecS J σ s (.halt e) := by
  have hd := ExecS.det (J := J) (σ := σ) hs
  cases hr : s.run σ with
  | ok o => simp only [Stmt.runSt, hr, Except.map, reduceCtorEq] at h
  | error e' =>
    rw [hr] at hd
    simp only [Stmt.runSt, hr, Except.map, Except.error.injEq] at h
    subst h
    exact hd

/-- The parameters declared, an argument halting: the declarations halt. -/
theorem Args.execP_declsThen_halt {Γ Δ : Ctx} : {ps : Ctx} → (as : Args C Γ ps) →
    (rest : Prog C (ps ++ Γ) Δ) → (σ : State C Γ) → {e : THalt} → as.evalT σ = .error e →
      ExecP J σ (as.declsThen rest) (.halt e)
  | _, .nil, _, _, _, h => nomatch h
  | _, .snoc (ps := ps') as p x v, rest, σ, e, ha => by
    rw [Args.evalT_snoc] at ha
    cases ha' : as.evalT σ with
    | error e' =>
      rw [ha'] at ha; cases ha
      exact Args.execP_declsThen_halt as _ σ ha'
    | ok a'' =>
      rw [ha'] at ha
      cases hv : v.evalT σ with
      | ok => simp only [hv, bind, Except.bind, pure, Except.pure, reduceCtorEq] at ha
      | error e' =>
        simp only [hv, bind, Except.bind, Except.error.injEq] at ha
        subst ha
        refine Args.execP_declsThen as _ σ a'' ha' (.halt (ExecS.det_err rfl ?_))
        rw [Stmt.runSt_declLocal, Val.evalT_unders, hv]; rfl
  | _, .snocStorage (ps := ps') as R x v, rest, σ, e, ha => by
    rw [Args.evalT_snocStorage] at ha
    cases ha' : as.evalT σ with
    | error e' =>
      rw [ha'] at ha; cases ha
      exact Args.execP_declsThen_halt as _ σ ha'
    | ok a'' =>
      rw [ha'] at ha
      cases hv : v.resolveT σ with
      | ok => simp only [hv, bind, Except.bind, pure, Except.pure, reduceCtorEq] at ha
      | error e' =>
        simp only [hv, bind, Except.bind, Except.error.injEq] at ha
        subst ha
        refine Args.execP_declsThen as _ σ a'' ha' (.halt (ExecS.det_err rfl ?_))
        rw [Stmt.runSt_declStorage, SPath.resolveT_unders, hv]; rfl
  | _, .snocMemory (ps := ps') as R x v, rest, σ, e, ha => by
    rw [Args.evalT_snocMemory] at ha
    cases ha' : as.evalT σ with
    | error e' =>
      rw [ha'] at ha; cases ha
      exact Args.execP_declsThen_halt as _ σ ha'
    | ok a'' =>
      rw [ha'] at ha
      cases hv : v.mvalT σ with
      | ok => simp only [hv, bind, Except.bind, pure, Except.pure, reduceCtorEq] at ha
      | error e' =>
        simp only [hv, bind, Except.bind, Except.error.injEq] at ha
        subst ha
        refine Args.execP_declsThen as _ σ a'' ha' (.halt (ExecS.det_err rfl ?_))
        rw [Stmt.runSt_declMem, MPath.mvalT_unders, hv]; rfl

/-- Two outcomes over a heap end alike when their states do. -/
theorem Out.eq_of_st {H : HTy} {Γ : Ctx} {a b : Out C H Γ} (h : a.st = b.st) : a = b := by
  cases a; cases b; cases h; rfl

/-- `TEnv.put_atop` at a frame read as `[] ++ ps`, a call's with no return
variable. -/
theorem TEnv.put_atop_nil {H : HTy} {Γ : Ctx} (ps : Ctx) (x : TEnv C H ([] ++ ps))
    (d : TEnv C H (ps ++ Γ)) :
    TEnv.put (Thin.atop ps Γ) x d = TEnv.append ps x (TEnv.drop (Ext.append Γ ps) d) :=
  TEnv.put_atop ps x d

/-- **A call with no result, with callbacks, is its inlined body**
(`Premise.sound_callNone`'s program): the parameters declared, the body
lifted under the caller's locals as a block, the parameters popped. -/
theorem ExecS.callNone_inline {Γ ps Γf : Ctx} {σ : State C Γ} {f : Name} {args : Args C Γ ps}
    {body : Prog C ([] ++ ps) Γf} {o : COut C σ.H Γ}
    (he : ExecS J σ (.call f args .none body) o) :
    ∃ u, ExecP J σ (args.declsThen (.cons (.block (body.wk (Thin.atop ps Γ)).2.2) .nil)) u ∧
      o = u.map (Out.drop (Ext.append Γ ps)) := by
  rcases ExecS.call_cases he with ⟨e, ha, rfl⟩ | ⟨a, o', ha, hp, rfl⟩
  · exact ⟨.halt _, Args.execP_declsThen_halt args _ σ ha, rfl⟩
  · obtain ⟨o'', hw, hr⟩ := Prog.exec_wk J body (Thin.atop ps Γ) (σ.withEnv a)
      (TEnv.append ps a σ.env) hp
    have hb := ExecS.transport (H := σ.H)
      (X := (σ.withEnv a).lift (Thin.atop ps Γ) (TEnv.append ps a σ.env))
      (Y := σ.withEnv (TEnv.append ps a σ.env)) rfl rfl (State.withEnv_append_lift σ a).symm
      (block_of_execP hw)
    refine ⟨_, Args.execP_declsThen args _ σ a ha (singleton_iff.mpr hb), ?_⟩
    have hl := (CallbackWk.CWkRel.drop (Prog.wk_over body (Thin.atop ps Γ)) hr).eq_lifted
    rw [hl]
    cases o' with
    | ok x =>
      refine congrArg COut.ok (Out.eq_of_st ?_)
      simp only [Out.drop, Out.lift, TRun.callLeave, State.lift, State.drop, State.withEnv,
        CallRet.leaveT]
      exact congrArg (fun E => (State.mk x.st.storage x.st.H x.st.heap E x.st.net
        x.st.selfBalance x.st.tx : State C Γ)) (TEnv.drop_put_atop_wk (Γ := Γ) _ ps _ a σ.env).symm
    | halt => rfl
    | violated => rfl

/-- **The return variables declared, with callbacks**, at their defaults. -/
theorem Binders.execP_declsThen {Γ Δ : Ctx} : {ρ : Ctx} → (bs : Binders ρ) →
    (rest : Prog C (ρ ++ Γ) Δ) → (σ : State C Γ) → ∀ {u : COut C σ.H Δ},
      ExecP J (σ.withEnv (TEnv.append ρ (bs.defaultsT (C := C)) σ.env)) rest u →
        ExecP J σ (bs.declsThen rest) u
  | _, .nil, _, _, _, h => h
  | _, .snoc (ρ := ρ') bs p x, rest, σ, u, h => by
    refine Binders.execP_declsThen bs _ σ ?_
    obtain ⟨_, hd⟩ := ExecS.det_ok (J := J)
      (σ := σ.withEnv (TEnv.append ρ' (bs.defaultsT (C := C)) σ.env))
      (s := .declLocal p x none) rfl (Stmt.runSt_declLocal_none p x _)
    simpa only [map_cat_refl] using ExecP.cons hd h

/-- A call's callback runs: its arguments halt, or its body runs in its frame
(`ExecS.callArgs`, `ExecS.callBody`). -/
theorem ExecS.call_inv {Γ Γ' ps rs Γf : Ctx} {σ : State C Γ} {f : Name} {args : Args C Γ ps}
    {ret : CallRet Γ rs Γ'} {body : Prog C (rs ++ ps) Γf} {o : COut C σ.H Γ'}
    (he : ExecS J σ (.call f args ret body) o) :
    (∃ e, args.evalT σ = .error e ∧ o = .halt e) ∨
    ∃ (a : TEnv C σ.H ps) (o' : COut C (ret.enterT (σ.withEnv a)).st.H Γf),
      args.evalT σ = .ok a ∧ ExecP J (ret.enterT (σ.withEnv a)).st body o' ∧
      o = o'.map (TRun.callLeave ret body.ext σ (ret.enterT (σ.withEnv a))) :=
  ExecS.call_cases he

/-- **A call of several results, with callbacks, is its inlined body**
(`Premise.sound_callRets`' program): the parameters declared, the return
variables at their defaults, the body lifted under the caller's locals as a
block, the parameters thinned out from under the return variables. -/
theorem ExecS.callRets_inline {Γ ps rs Γf : Ctx} {σ : State C Γ} {f : Name}
    {args : Args C Γ ps} {bs : Binders rs} {body : Prog C (rs ++ ps) Γf} {o : COut C σ.H (rs ++ Γ)}
    (he : ExecS J σ (.call f args (.rets bs) body) o) :
    ∃ u, ExecP J σ (args.declsThen (bs.declsThen
        (.cons (.block (body.wk (Thin.keepAll rs (Thin.atop ps Γ))).2.2) .nil))) u ∧
      o = u.map fun x => ⟨x.st.thin (Thin.keepAll rs (Thin.ofExt (Ext.append Γ ps))), x.ext⟩ := by
  rcases ExecS.call_inv he with ⟨e, ha, rfl⟩ | ⟨a, o', ha, hp, rfl⟩
  · exact ⟨.halt _, Args.execP_declsThen_halt args _ σ ha, rfl⟩
  · obtain ⟨o'', hw, hr⟩ := Prog.exec_wk J body (Thin.keepAll rs (Thin.atop ps Γ))
      (σ.withEnv (TEnv.append rs (bs.defaultsT (C := C)) a))
      (TEnv.append rs (bs.defaultsT (C := C)) (TEnv.append ps a σ.env)) hp
    have hs : (σ.withEnv (TEnv.append rs (bs.defaultsT (C := C)) a)).lift
          (Thin.keepAll rs (Thin.atop ps Γ))
          (TEnv.append rs (bs.defaultsT (C := C)) (TEnv.append ps a σ.env)) =
        (σ.withEnv (TEnv.append ps a σ.env)).withEnv
          (TEnv.append rs (bs.defaultsT (C := C)) (σ.withEnv (TEnv.append ps a σ.env)).env) := by
      simp only [State.lift, State.withEnv, TEnv.put_keepAll, TEnv.put_atop, TEnv.drop_append]
    have hb := ExecS.transport (H := σ.H)
      (X := (σ.withEnv (TEnv.append rs (bs.defaultsT (C := C)) a)).lift
          (Thin.keepAll rs (Thin.atop ps Γ))
          (TEnv.append rs (bs.defaultsT (C := C)) (TEnv.append ps a σ.env)))
      (Y := (σ.withEnv (TEnv.append ps a σ.env)).withEnv
          (TEnv.append rs (bs.defaultsT (C := C)) (σ.withEnv (TEnv.append ps a σ.env)).env))
      rfl rfl hs (block_of_execP hw)
    refine ⟨_, Args.execP_declsThen args _ σ a ha
      (Binders.execP_declsThen bs _ _ (singleton_iff.mpr hb)), ?_⟩
    have hl := (CallbackWk.CWkRel.drop (Prog.wk_over body (Thin.keepAll rs (Thin.atop ps Γ)))
      hr).eq_lifted
    rw [hl]
    cases o' with
    | ok x =>
      refine congrArg COut.ok (Out.eq_of_st ?_)
      simp only [Out.drop, Out.lift, TRun.callLeave, State.lift, State.drop, State.thin,
        State.withEnv, CallRet.leaveT]
      exact congrArg (fun E => (State.mk x.st.storage x.st.H x.st.heap E x.st.net
        x.st.selfBalance x.st.tx : State C (rs ++ Γ)))
        (TEnv.thin_put_keepAllAtop _ _ _ a σ.env).symm
    | halt => rfl
    | violated => rfl

/-- An outcome's state thinned, read through the frames that thin it. -/
theorem COut.thenF_thin {H : HTy} {Γ Γ' Γ₀ : Ctx} {e : Thin Γ Γ'} {κ : Frames C Γ Γ₀}
    {m : Modality} {p : State C Γ₀ → Prop} (o : COut C H Γ')
    (h : o.thenF J (.drop e κ) m p) :
    (o.map fun x => ⟨x.st.thin e, x.ext⟩).thenF J κ m p := by
  cases o with
  | ok o => exact fun o' he => h o' (.drop he)
  | halt _ => exact h
  | violated => exact h

/-- **A call of several results, with callbacks**: its inlined body, the
parameters thinned out. -/
theorem holdsC_callRets {Γ ps rs Γf Γ₁ Γ₀ : Ctx} {m : Modality} {σ : State C Γ} {f : Name}
    {args : Args C Γ ps} {bs : Binders rs} {body : Prog C (rs ++ ps) Γf}
    {ω : Prog C (rs ++ Γ) Γ₁} {κ : Frames C Γ₁ Γ₀} {φ : Fml C Γ₀}
    (h : holdsC I pay σ (.modal m (args.declsThen (bs.declsThen
        (.cons (.block (body.wk (Thin.keepAll rs (Thin.atop ps Γ))).2.2) .nil)))
      (.drop (Thin.keepAll rs (Thin.ofExt (Ext.append Γ ps))) (.seq ω κ)) φ)) :
    holdsC I pay σ (.modal m (.cons (.call f args (.rets bs) body) ω) κ φ) := by
  refine holdsC_cons fun o₁ he => ?_
  obtain ⟨u, hu, rfl⟩ := ExecS.callRets_inline he
  exact COut.thenF_thin _ (h _ hu)

/-- **A call with no result, with callbacks**: its inlined body, the
parameters popped. -/
theorem holdsC_callNone {Γ ps Γf Γ₁ Γ₀ : Ctx} {m : Modality} {σ : State C Γ} {f : Name}
    {args : Args C Γ ps} {body : Prog C ([] ++ ps) Γf} {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀}
    {φ : Fml C Γ₀}
    (h : holdsC I pay σ (.modal m
      (args.declsThen (.cons (.block (body.wk (Thin.atop ps Γ)).2.2) .nil))
      (.pop .capture (Ext.append Γ ps) (.seq ω κ)) φ)) :
    holdsC I pay σ (.modal m (.cons (.call f args .none body) ω) κ φ) := by
  refine holdsC_cons fun o₁ he => ?_
  obtain ⟨u, hu, rfl⟩ := ExecS.callNone_inline he
  exact COut.thenF_drop _ (h _ hu)

/-- **A call of one value, with callbacks, is its inlined body**
(`Premise.sound_callVal`'s program): the parameters declared, the return
variable at its default, the body lifted under them as a block, the result
assigned to its target, the frame popped. -/
theorem ExecS.callVal_inline {Γ ps Γf : Ctx} {σ : State C Γ} {f : Name} {args : Args C Γ ps}
    {p : PrimTy} {r : Var} {res : Option (Idx Γ (.val p))} {body : Prog C ([.val p] ++ ps) Γf}
    {o : COut C σ.H Γ} (he : ExecS J σ (.call f args (.val p r res) body) o) :
    ∃ u, ExecP J σ (args.declsThen (.cons (.declLocal p r none)
        (.cons (.block (body.wk (Thin.atop (.val p :: ps) Γ)).2.2) (Prog.callResult res)))) u ∧
      o = u.map (Out.drop (.push (Ext.append Γ ps))) := by
  rcases ExecS.call_cases he with ⟨e, ha, rfl⟩ | ⟨a, o', ha, hp, rfl⟩
  · exact ⟨.halt _, Args.execP_declsThen_halt args _ σ ha, rfl⟩
  · have hp' : ExecP J (σ.withEnv (Δ := .val p :: ps) (PrimTy.dflt p, a)) body o' := hp
    obtain ⟨o'', hw, hr⟩ := Prog.exec_wk J body (Thin.atop (.val p :: ps) Γ)
      (σ.withEnv (Δ := .val p :: ps) (PrimTy.dflt p, a))
      (TEnv.append (.val p :: ps) (PrimTy.dflt p, a) σ.env) hp'
    have hb := ExecS.transport (H := σ.H)
      (X := (σ.withEnv (Δ := .val p :: ps) (PrimTy.dflt p, a)).lift
        (Thin.atop (.val p :: ps) Γ)
        (TEnv.append (.val p :: ps) (PrimTy.dflt p, a) σ.env))
      (Y := σ.withEnv (TEnv.append (.val p :: ps) (PrimTy.dflt p, a)
        σ.env)) rfl rfl
      (State.withEnv_append_lift (ps := .val p :: ps) σ (PrimTy.dflt p, a)).symm
      (block_of_execP hw)
    obtain ⟨_, hd⟩ := ExecS.det_ok (J := J) (σ := σ.withEnv (TEnv.append ps a σ.env))
      (s := .declLocal p r none) rfl (Stmt.runSt_declLocal_none p r _)
    have hl := (CallbackWk.CWkRel.drop (Prog.wk_over body (Thin.atop (.val p :: ps) Γ)) hr).eq_lifted
    rw [hl] at hb
    cases o' with
    | halt e =>
      exact ⟨.halt e, Args.execP_declsThen args _ σ a ha
        (by simpa only [map_cat_refl] using ExecP.cons hd (ExecP.halt hb)), rfl⟩
    | violated =>
      exact ⟨.violated, Args.execP_declsThen args _ σ a ha
        (by simpa only [map_cat_refl] using ExecP.cons hd (ExecP.violated hb)), rfl⟩
    | ok x =>
      let y := (Out.drop body.ext x).lift (Thin.atop (.val p :: ps) Γ)
        (TEnv.append (.val p :: ps) (PrimTy.dflt p, a) σ.env)
      have hb' : ExecS J (σ.withEnv (TEnv.append (.val p :: ps) (PrimTy.dflt p, a) σ.env))
          (.block (body.wk (Thin.atop (.val p :: ps) Γ)).2.2) (.ok y) := hb
      have ht := ExecP.of_run (J := J) (τ := y.st)
        (P := (Prog.callResult res : Prog C (.val p :: (ps ++ Γ)) _)) (by cases res <;> rfl)
      refine ⟨_, Args.execP_declsThen args _ σ a ha
        (by simpa only [map_cat_refl] using ExecP.cons hd (ExecP.cons hb' ht)), ?_⟩
      cases res with
      | none =>
        refine congrArg COut.ok (Out.eq_of_st ?_)
        simp only [Out.drop, Out.lift, Out.cat, TRun.callLeave, State.lift, State.drop,
          State.withEnv, CallRet.leaveT, y]
        erw [TEnv.drop_put_atop_wk (Γ := Γ) _ (LTy.val p :: ps)]
      | some j =>
        refine congrArg COut.ok (Out.eq_of_st ?_)
        rw [show (Ext.append Γ ps).push = Ext.append Γ (LTy.val p :: ps) from rfl]
        simp only [Out.drop, Out.lift, Out.cat, TRun.callLeave, State.lift, State.drop,
          State.withEnv, State.setLocal, show (j.under ps).there = j.under (LTy.val p :: ps) from rfl,
          TEnv.drop_set_under, CallRet.leaveT, y]
        erw [TEnv.drop_put_atop_wk (Γ := Γ) _ (LTy.val p :: ps)]
        rfl

/-- **A call of a storage reference, with callbacks, is its inlined body**
(`Premise.sound_callStorage`'s program): the parameters declared, the
return alias unset, the body lifted under them as a block, the parameters
thinned out from under the alias. -/
theorem ExecS.callStorage_inline {Γ ps Γf : Ctx} {σ : State C Γ} {f : Name}
    {args : Args C Γ ps} {R : RefTy} {r : Var} {body : Prog C ([.alias R] ++ ps) Γf}
    {o : COut C σ.H (.alias R :: Γ)} (he : ExecS J σ (.call f args (.storage R r) body) o) :
    ∃ u, ExecP J σ (args.declsThen (.cons (.declStorage R r none)
        (.cons (.block (body.wk (Thin.atop (.alias R :: ps) Γ)).2.2) .nil))) u ∧
      o = u.map fun x => ⟨x.st.thin (.keep (Thin.ofExt (Ext.append Γ ps))), x.ext⟩ := by
  rcases ExecS.call_cases he with ⟨e, ha, rfl⟩ | ⟨a, o', ha, hp, rfl⟩
  · exact ⟨.halt _, Args.execP_declsThen_halt args _ σ ha, rfl⟩
  · have hp' : ExecP J (σ.withEnv (Δ := .alias R :: ps) (none, a)) body o' := hp
    obtain ⟨o'', hw, hr⟩ := Prog.exec_wk J body (Thin.atop (.alias R :: ps) Γ)
      (σ.withEnv (Δ := .alias R :: ps) (none, a))
      (TEnv.append (.alias R :: ps) (none, a) σ.env) hp'
    have hb := ExecS.transport (H := σ.H)
      (X := (σ.withEnv (Δ := .alias R :: ps) (none, a)).lift
        (Thin.atop (.alias R :: ps) Γ) (TEnv.append (.alias R :: ps) (none, a) σ.env))
      (Y := σ.withEnv (TEnv.append (.alias R :: ps) (none, a) σ.env)) rfl rfl
      (State.withEnv_append_lift (ps := .alias R :: ps) σ (none, a)).symm
      (block_of_execP hw)
    obtain ⟨_, hd⟩ := ExecS.det_ok (J := J) (σ := σ.withEnv (TEnv.append ps a σ.env))
      (s := .declStorage R r none) rfl (Stmt.runSt_declStorage_none R r _)
    have hl := (CallbackWk.CWkRel.drop (Prog.wk_over body (Thin.atop (.alias R :: ps) Γ)) hr).eq_lifted
    rw [hl] at hb
    refine ⟨_, Args.execP_declsThen args _ σ a ha
      (by simpa only [map_cat_refl] using ExecP.cons hd (singleton_iff.mpr hb)), ?_⟩
    cases o' with
    | ok x =>
      refine congrArg COut.ok (Out.eq_of_st ?_)
      simp only [Out.drop, Out.lift, TRun.callLeave, State.lift, State.drop, State.thin,
        State.withEnv, CallRet.leaveT]
      erw [TEnv.thin_put_keepAllAtop (rs := [.alias R]) (r := (none, ()))]
      rfl
    | halt => rfl
    | violated => rfl

/-- **A call of a memory reference, with callbacks, is its inlined body**
(`Premise.sound_callMem`'s program): the parameters declared, the return
object allocated at its default, the body lifted under them as a block,
the parameters thinned out from under the object. -/
theorem ExecS.callMem_inline {Γ ps Γf : Ctx} {σ : State C Γ} {f : Name}
    {args : Args C Γ ps} {R : RefTy} {r : Var} {hd : (Ty.ref R).defaultOkS = true}
    {hm : (Ty.ref R).mapFree = true} {body : Prog C ([.mem R] ++ ps) Γf}
    {o : COut C σ.H (.mem R :: Γ)} (he : ExecS J σ (.call f args (.mem R r hd hm) body) o) :
    ∃ u, ExecP J σ (args.declsThen (.cons (.declMem R r none hd hm)
        (.cons (.block (body.wk (Thin.atop (.mem R :: ps) Γ)).2.2) .nil))) u ∧
      o = u.map fun x => ⟨x.st.thin (.keep (Thin.ofExt (Ext.append Γ ps))), x.ext⟩ := by
  rcases ExecS.call_cases he with ⟨e, ha, rfl⟩ | ⟨a, o', ha, hp, rfl⟩
  · exact ⟨.halt _, Args.execP_declsThen_halt args _ σ ha, rfl⟩
  · let g := (σ.withEnv a).allocDefaultG R hm
    let τ := σ.withEnv (TEnv.append ps a σ.env)
    have hp' : ExecP J (g.st.push (t := .mem R) (some g.val)) body o' := hp
    obtain ⟨o'', hw, hr⟩ := Prog.exec_wk J body (Thin.atop (.mem R :: ps) Γ)
      (g.st.push (t := .mem R) (some g.val))
      (some g.val, TEnv.wk g.ext _ (TEnv.append ps a σ.env)) hp'
    have hY : (g.st.push (t := .mem R) (some g.val)).lift (Thin.atop (.mem R :: ps) Γ)
          (some g.val, TEnv.wk g.ext _ (TEnv.append ps a σ.env)) =
        (τ.allocDefaultG R hm).st.push (t := .mem R) (some (τ.allocDefaultG R hm).val) := by
      show _ = ((σ.withEnv (TEnv.append ps a σ.env)).allocDefaultG R hm).st.push (t := .mem R)
        (some ((σ.withEnv (TEnv.append ps a σ.env)).allocDefaultG R hm).val)
      rw [State.withEnv_append_lift σ a, State.allocDefaultG_lift]
      simp only [g, Grew.lift, State.lift, State.push, Thin.atop, State.withEnv, TEnv.put]
      rfl
    have hb := ExecS.transport (H := g.st.H)
      (X := (g.st.push (t := .mem R) (some g.val)).lift (Thin.atop (.mem R :: ps) Γ)
          (some g.val, TEnv.wk g.ext _ (TEnv.append ps a σ.env)))
      (Y := (τ.allocDefaultG R hm).st.push (t := .mem R) (some (τ.allocDefaultG R hm).val))
      rfl rfl hY (block_of_execP hw)
    obtain ⟨_, hd'⟩ := ExecS.det_ok (J := J) (σ := τ)
      (s := .declMem R r none hd hm) rfl (Stmt.runSt_declMem_none R r hd hm _)
    have hl := (CallbackWk.CWkRel.drop (Prog.wk_over body (Thin.atop (.mem R :: ps) Γ)) hr).eq_lifted
    rw [hl] at hb
    refine ⟨_, Args.execP_declsThen args _ σ a ha (ExecP.cons hd' (singleton_iff.mpr hb)), ?_⟩
    cases o' with
    | ok x =>
      refine congrArg COut.ok (Out.eq_of_st ?_)
      simp only [Out.drop, Out.lift, Out.cat, TRun.callLeave, State.lift, State.drop, State.thin,
        State.withEnv, CallRet.leaveT]
      erw [TEnv.thin_keep_put_atop]
      rfl
    | halt => rfl
    | violated => rfl

/-- **A call of one value, with callbacks**: its inlined body, the result
assigned, the frame popped. -/
theorem holdsC_callVal {Γ ps Γf Γ₁ Γ₀ : Ctx} {m : Modality} {σ : State C Γ} {f : Name}
    {args : Args C Γ ps} {p : PrimTy} {r : Var} {res : Option (Idx Γ (.val p))}
    {body : Prog C ([.val p] ++ ps) Γf} {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀} {φ : Fml C Γ₀}
    (h : holdsC I pay σ (.modal m (args.declsThen (.cons (.declLocal p r none)
        (.cons (.block (body.wk (Thin.atop (.val p :: ps) Γ)).2.2) (Prog.callResult res))))
      (.pop .capture (.push (Ext.append Γ ps)) (.seq ω κ)) φ)) :
    holdsC I pay σ (.modal m (.cons (.call f args (.val p r res) body) ω) κ φ) := by
  refine holdsC_cons fun o₁ he => ?_
  obtain ⟨u, hu, rfl⟩ := ExecS.callVal_inline he
  exact COut.thenF_drop _ (h _ hu)

/-- **A call of a storage reference, with callbacks**: its inlined body, the
parameters thinned out from under the alias. -/
theorem holdsC_callStorage {Γ ps Γf Γ₁ Γ₀ : Ctx} {m : Modality} {σ : State C Γ} {f : Name}
    {args : Args C Γ ps} {R : RefTy} {r : Var} {body : Prog C ([.alias R] ++ ps) Γf}
    {ω : Prog C (.alias R :: Γ) Γ₁} {κ : Frames C Γ₁ Γ₀} {φ : Fml C Γ₀}
    (h : holdsC I pay σ (.modal m (args.declsThen (.cons (.declStorage R r none)
        (.cons (.block (body.wk (Thin.atop (.alias R :: ps) Γ)).2.2) .nil)))
      (.drop (.keep (Thin.ofExt (Ext.append Γ ps))) (.seq ω κ)) φ)) :
    holdsC I pay σ (.modal m (.cons (.call f args (.storage R r) body) ω) κ φ) := by
  refine holdsC_cons fun o₁ he => ?_
  obtain ⟨u, hu, rfl⟩ := ExecS.callStorage_inline he
  exact COut.thenF_thin _ (h _ hu)

/-- **A call of a memory reference, with callbacks**: its inlined body, the
parameters thinned out from under the object. -/
theorem holdsC_callMem {Γ ps Γf Γ₁ Γ₀ : Ctx} {m : Modality} {σ : State C Γ} {f : Name}
    {args : Args C Γ ps} {R : RefTy} {r : Var} {hd : (Ty.ref R).defaultOkS = true}
    {hm : (Ty.ref R).mapFree = true} {body : Prog C ([.mem R] ++ ps) Γf}
    {ω : Prog C (.mem R :: Γ) Γ₁} {κ : Frames C Γ₁ Γ₀} {φ : Fml C Γ₀}
    (h : holdsC I pay σ (.modal m (args.declsThen (.cons (.declMem R r none hd hm)
        (.cons (.block (body.wk (Thin.atop (.mem R :: ps) Γ)).2.2) .nil)))
      (.drop (.keep (Thin.ofExt (Ext.append Γ ps))) (.seq ω κ)) φ)) :
    holdsC I pay σ (.modal m (.cons (.call f args (.mem R r hd hm) body) ω) κ φ) := by
  refine holdsC_cons fun o₁ he => ?_
  obtain ⟨u, hu, rfl⟩ := ExecS.callMem_inline he
  exact COut.thenF_thin _ (h _ hu)

end Calls

/-! ## A loop by its invariant, with callbacks

`whileInvariantBox` read over the callback runs (`ProvesC.invBox`): every
loop head is a state the body's frame allows from the first
(`ExecP.frame`: a callback replaces only the storage and the ledger, which a
body that calls back may write, `Prog.frame`'s `hv`), so the premise read
under `{anon(xs)}` (`{havoc}`) holds there (`holdsC_anonHavoc`); the
invariant holds at every head by induction over the iterations
(`ExecS.loop_box`: the typed run's where the body calls nobody back,
`CallbackUnwk.LoopExec`'s otherwise).  Under the box only: a loop whose body
calls back may diverge (`ExecS.loopDiverge`), which no diamond accepts
(`holdsC_diamond_loop`). -/

section Inv

variable {I : Fml C []} {J : StateInv C}

/-- **A state in a loop body's frame is one its anonymised premise covers**,
with callbacks (`holds_anonHavoc`). -/
theorem holdsC_anonHavoc {Γ : Ctx} {σ τ : State C Γ} {xs : List ((t : LTy) × Idx Γ t)}
    {hv : Option (List Name)} {μ : Mutability} {W : List (LTy × Nat)}
    (hxs : ∀ t (i : Idx Γ t), (t, i.toNat) ∈ W → (⟨t, i⟩ : (t : LTy) × Idx Γ t) ∈ xs)
    (hg : TGFrame μ σ τ) (ha : TLocAgree 0 W σ.env τ.env) (hk : FrameKeeps hv σ τ)
    {ψ : Fml C Γ} (h : holdsC I pay σ (Fml.anonHavoc xs hv ψ)) : holdsC I pay τ ψ := by
  obtain ⟨b, hb⟩ := State.eq_anonHavoc hxs hg ha
  match hv, hk, h with
  | none, _, h =>
    rw [hb]
    exact h b τ.storage τ.net τ.selfBalance
  | some [], hk, h =>
    have hst : τ.storage = σ.storage := hk.1.symm
    have hτ : τ = σ.anon xs b := by rw [hb, hst, hk.2.1, hk.2.2]; rfl
    rw [hτ]
    exact h b
  | some (r :: L), hk, h =>
    have h₁ := Modality.forallB_all (h b) τ.storage
    have hτ : τ = (σ.anon xs b).withStorage (Storage.anon (r :: L) (σ.anon xs b).storage τ.storage) := by
      have hs : Storage.anon (r :: L) (σ.anon xs b).storage τ.storage = τ.storage := hk.1
      rw [hs, hb, hk.2.1, hk.2.2]
      rfl
    rw [hτ]
    exact Upd.afterT.of_lands h₁ (Upd.lands_anonSt (r :: L) (σ.anon xs b) τ.storage)

mutual

/-- **A statement with a modifies set calls nobody back**: a payment, a
`try` and a call out have none (`Stmt.storeAt`). -/
theorem Stmt.callsBack_of_storeAt (pay : Bool) : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') →
    {L : List Name} → s.storeAt = some L → Stmt.callsBack pay s = false
  | _, _, .ite _ thn els, _, h => by
    have h' : Locs.union (Prog.storeAt thn) (Prog.storeAt els) = some _ := h
    show (Prog.callsBack pay thn || Prog.callsBack pay els) = false
    cases h₁ : Prog.storeAt thn with
    | none => rw [h₁] at h'; cases h'
    | some L₁ =>
      cases h₂ : Prog.storeAt els with
      | none => rw [h₁, h₂] at h'; cases h'
      | some L₂ =>
        rw [Prog.callsBack_of_storeAt pay thn h₁, Prog.callsBack_of_storeAt pay els h₂]
        rfl
  | _, _, .call _ _ ret body, _, h => by
    have h' : (if ret.noMem then Prog.storeAt body else none) = some _ := h
    show Prog.callsBack pay body = false
    split at h'
    · exact Prog.callsBack_of_storeAt pay body h'
    · cases h'
  | _, _, .callRec _ _ _ ret body, _, h => by
    have h' : (if ret.noMem then Prog.storeAt (body ()) else none) = some _ := h
    show Prog.callsBack pay (body ()) = false
    split at h'
    · exact Prog.callsBack_of_storeAt pay (body ()) h'
    · cases h'
  | _, _, .loop _ _ body, _, h => Prog.callsBack_of_storeAt pay body h
  | _, _, .block body, _, h => Prog.callsBack_of_storeAt pay body h
  | _, _, .transfer .., _, h | _, _, .send .., _, h | _, _, .tryCall .., _, h
  | _, _, .callReceiver .., _, h | _, _, .callReceiverPush .., _, h
  | _, _, .catchData .., _, h => by cases h
  | _, _, .assign .., _, _ | _, _, .rebind .., _, _ | _, _, .assignLocal .., _, _
  | _, _, .declLocal .., _, _ | _, _, .declStorage .., _, _ | _, _, .opAssign .., _, _
  | _, _, .incDec .., _, _ | _, _, .assignIncDec .., _, _ | _, _, .assignLocalPush .., _, _
  | _, _, .pushOpAssign .., _, _ | _, _, .pushIncDec .., _, _ | _, _, .push .., _, _
  | _, _, .pop .., _, _ | _, _, .declMem .., _, _ | _, _, .rebindMem .., _, _
  | _, _, .assignFromMem .., _, _ | _, _, .assignMem .., _, _ | _, _, .delete .., _, _
  | _, _, .deleteMem .., _, _ | _, _, .assignNew .., _, _ | _, _, .require .., _, _
  | _, _, .assert .., _, _ | _, _, .revert, _, _ | _, _, .assumeFalse, _, _
  | _, _, .revertData .., _, _ => rfl

theorem Prog.callsBack_of_storeAt (pay : Bool) : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') →
    {L : List Name} → Prog.storeAt P = some L → Prog.callsBack pay P = false
  | _, _, .nil, _, _ => rfl
  | _, _, .cons s P, _, h => by
    have h' : Locs.union (Stmt.storeAt s) (Prog.storeAt P) = some _ := h
    rw [Prog.callsBack_cons]
    cases h₁ : Stmt.storeAt s with
    | none => rw [h₁] at h'; cases h'
    | some L₁ =>
      cases h₂ : Prog.storeAt P with
      | none => rw [h₁, h₂] at h'; cases h'
      | some L₂ =>
        rw [Stmt.callsBack_of_storeAt pay s h₁, Prog.callsBack_of_storeAt pay P h₂]
        rfl

end

/-- **What a loop body with a frame leaves of the global part, with
callbacks** (`Prog.frame_keeps`): a body within no mutability calls nobody
back and keeps the storage (`ExecP.frame`); one with a modifies set calls
nobody back either (`Prog.callsBack_of_storeAt`), so its callback run is
its run (`ExecP.eq_run`). -/
theorem ExecP.frame_keeps {Γ Γb : Ctx} {body : Prog C Γ Γb} {xs : List ((t : LTy) × Idx Γ t)}
    {hv : Option (List Name)} (hf : body.frame = some (xs, hv)) {τ : State C Γ}
    {υ : Out C τ.H Γb} (hp : ExecP J τ body (.ok υ)) : FrameKeeps hv τ (υ.st.drop body.ext) := by
  rcases (Prog.frame_some hf).1 with ⟨hw, -⟩ | ⟨-, rfl⟩
  · exact FrameKeeps.ofView ((ExecP.frame hp hw 0 υ rfl).1.withEnv _)
  · cases hs : Prog.storeAt body with
    | none => trivial
    | some L =>
      have hr := ExecP.eq_run hp (Prog.callsBack_of_storeAt J.pay body hs)
      have hr' : Prog.run τ body = .ok υ := by
        revert hr
        cases Prog.run τ body with
        | error _ => exact fun h => nomatch h
        | ok _ => intro h; cases h; rfl
      have := (Prog.run_keeps body hr').withEnv (TEnv.drop body.ext υ.st.env)
      rw [hs] at this
      exact this

/-- **Induction over a loop's callback runs**, under the box: `P` holds at
the first head and at every head an iteration from a head in `P` goes on
in, where the condition is `true`; where it is `false`, `Q` holds. -/
theorem ExecS.loop_box {Γ Γb : Ctx} {a : LoopAnn C Γ} {c : Val C Γ .bool} {body : Prog C Γ Γb}
    {σ : State C Γ} (P Q : State C Γ → Prop) (h0 : P σ)
    (hexit : ∀ τ, P τ → c.evalT τ = .ok false → Q τ)
    (hstep : ∀ τ, P τ → c.evalT τ = .ok true → ∀ o, ExecP J τ body o →
      (o.map (Out.drop body.ext)).after .box P) :
    ∀ o, ExecS J σ (.loop a c body) o → o.after .box Q := by
  intro o he
  cases hb : body.callsBack J.pay with
  | false =>
    rw [ExecS.eq_run_of_forksIn he hb]
    show (COut.ofRes (TLoop.run (fun o : Out C σ.H Γ => (Prog.run o.st body).map
      fun o' => ⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩)
      (fun o => c.evalT o.st) ⟨σ, List.prefix_refl _⟩)).after .box Q
    refine TLoop.run_induct (P := fun x : Out C σ.H Γ => P x.st)
      (Q := fun r => (COut.ofRes r).after .box Q) h0 (fun x hx => ?_) ⟨trivial, nofun⟩
    unfold TLoop.step
    dsimp only
    cases hc : c.evalT x.st with
    | error e =>
      refine ⟨trivial, fun h => ?_⟩
      cases h
      exact Val.evalT_noPanic x.st c hc
    | ok v =>
      cases v with
      | false => exact hexit _ hx hc
      | true =>
        have hs := hstep _ hx hc _ (ExecP.of_run (J := J) (τ := x.st) (P := body) hb)
        dsimp only
        cases hr : Prog.run x.st body with
        | error e => rw [hr] at hs; exact hs
        | ok y => rw [hr] at hs; exact hs
  | true =>
    have hl : CallbackUnwk.LoopExec J a c body σ o := CallbackUnwk.asLoop he
    clear he
    induction hl with
    | det hf => exact absurd (hb.symm.trans hf) (by decide)
    | halt _ hc =>
      refine ⟨trivial, fun h => ?_⟩
      cases h
      exact Val.evalT_noPanic _ c hc
    | exit _ hc => exact hexit _ h0 hc
    | @iter τ υ o' _ hc hp _ ih =>
      have h1 : P (υ.st.drop body.ext) := hstep _ h0 hc _ hp
      exact (COut.after_map_cat _ _ Q).2 (ih h1)
    | @stop τ o' _ hc hp hn =>
      have h1 := hstep _ h0 hc _ hp
      cases o' with
      | ok => cases hn
      | halt e => exact h1
      | violated => exact h1.elim
    | diverge _ => exact ⟨trivial, nofun⟩

/-- A run through no frame: its outcome read after it. -/
theorem COut.thenF_nil {H : HTy} {Γ : Ctx} {m : Modality} {p : State C Γ → Prop}
    (o : COut C H Γ) (h : o.thenF J .nil m p) : o.after m p := by
  cases o with
  | ok o => exact h _ .nil
  | halt _ => exact h
  | violated => exact h

/-- **`whileInvariantBox` with callbacks**: the invariant now ("invariant
initially valid"); from every state the body's frame allows where it holds,
the body to the invariant where the condition holds ("body preserves
invariant"), the rest where it does not ("use case"); with a break test, a
body that broke goes on to the rest. -/
theorem holdsC_invBox {Γ Γb Γ₁ Γ₀ : Ctx} {Iv : Val C Γ .bool} {dec : Option (Val C Γ .uint)}
    {brk : Bool} {qs : List (LoopQ C Γ)} {c : Val C Γ .bool} {body : Prog C Γ Γb}
    {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀} {φ : Fml C Γ₀} {xs : List ((t : LTy) × Idx Γ t)}
    {hv : Option (List Name)} {k : Nat} (hf : body.frame = some (xs, hv)) {σ : State C Γ}
    (hI : holdsC I pay σ ((invFml Iv qs).invHyp (loopBreak brk c)))
    (hX : holdsC I pay σ (Fml.anonHavoc xs hv (.imp ((invFml Iv qs).invHyp (loopBreak brk c))
      (.upd .box (Upd.nil.decl (fse k) (.val (p := .bool) c.lower))
        (.and (.imp (.isBool (.pvV (p := .bool) .here) true)
          (.upd .box (Upd.nil.pop (.push .refl)) (Fml.modalK .box body (.pop .block body.ext .nil)
            (Fml.invPost .box .refl ω κ φ (invFml Iv qs) (loopBreak brk c)))))
          (.imp (.isBool (.pvV (p := .bool) .here) false)
            (.upd .box (Upd.nil.pop (.push .refl)) (Fml.modalK .box ω κ φ)))))))) :
    holdsC I pay σ (.modal .box (.cons (.loop (.inv Iv dec brk qs) c body) ω) κ φ) := by
  obtain ⟨μ, hwμ⟩ := Prog.frame_within hf
  have hxs := (Prog.frame_some hf).2
  have hB := breakTest_loopBreak brk c
  -- the premise at a head the frame allows, the condition read
  have hY : ∀ τ : State C Γ, TGFrame μ σ τ → FrameKeeps hv σ τ →
      TLocAgree 0 (Prog.writesAt 0 body) σ.env τ.env →
      holdsC I pay τ ((invFml Iv qs).invHyp (loopBreak brk c)) → ∀ v : Bool, c.evalT τ = .ok v →
      (v = true → holdsC I pay τ (Fml.modalK .box body (.pop .block body.ext .nil)
          (Fml.invPost .box .refl ω κ φ (invFml Iv qs) (loopBreak brk c)))) ∧
      (v = false → holdsC I pay τ (Fml.modalK .box ω κ φ)) := by
    intro τ hg hk hag hIτ v hc
    have hcl : (Rhs.val (p := .bool) c.lower).eval τ =
        some (LTy.VDen.ofT (H := τ.H) (.val .bool) v) := by
      show c.lower.eval τ = _
      exact Val.lower_eval_ok c τ hc
    obtain ⟨hT, hF⟩ := (holdsC_anonHavoc hxs hg hag hk hX hIτ).of_lands
      (Upd.lands_decl (Upd.lands_nil τ) (fse k) hcl)
    refine ⟨fun hv => ?_, fun hv => ?_⟩
    · subst hv
      exact Upd.afterT.of_lands (hT ((holds_isBool_pvV _ _ _).2 rfl)) (Upd.lands_pop_nil _ _)
    · subst hv
      exact Upd.afterT.of_lands (hF ((holds_isBool_pvV _ _ _).2 rfl)) (Upd.lands_pop_nil _ _)
  refine holdsC_cons fun o₁ he => ?_
  have hL := ExecS.loop_box (J := I.stateInv pay)
    (P := fun τ => (TGFrame μ σ τ ∧ FrameKeeps hv σ τ ∧ TLocAgree 0 (Prog.writesAt 0 body) σ.env τ.env ∧
        holdsC I pay τ ((invFml Iv qs).invHyp (loopBreak brk c))) ∨
      (c.evalT τ = .ok false ∧ holdsC I pay τ (Fml.modalK .box ω κ φ)))
    (Q := fun τ => holdsC I pay τ (Fml.modalK .box ω κ φ)) (.inl ⟨TGFrame.refl σ, FrameKeeps.refl _ σ, TLocAgree.refl _, hI⟩)
    (fun τ hτ hc => by
      rcases hτ with ⟨hg, hk, hag, hIτ⟩ | ⟨_, hR⟩
      · exact (hY τ hg hk hag hIτ false hc).2 rfl
      · exact hR)
    (fun τ hτ hc o hp => by
      rcases hτ with ⟨hg, hk, hag, hIτ⟩ | ⟨hc', _⟩
      · have hA := holdsC_modalK τ body _ _ ((hY τ hg hk hag hIτ true hc).1 rfl) o hp
        have hA' := COut.thenF_nil _ (COut.thenF_drop _ hA)
        cases o with
        | halt e => exact hA'
        | violated => exact hA'.elim
        | ok υ =>
          have hpost : holdsC I pay (υ.st.drop body.ext)
              (Fml.invPost .box .refl ω κ φ (invFml Iv qs) (loopBreak brk c)) := hA'
          obtain ⟨hg', ha'⟩ := ExecP.frame hp hwμ 0 υ rfl
          have hfr : TGFrame μ σ (υ.st.drop body.ext) := hg.trans (hg'.withEnv _)
          have hkr : FrameKeeps hv σ (υ.st.drop body.ext) := hk.trans (ExecP.frame_keeps hf hp)
          have hag' : TLocAgree 0 (Prog.writesAt 0 body) σ.env (υ.st.drop body.ext).env :=
            hag.trans ha'
          show _ ∨ _
          cases hBr : loopBreak brk c with
          | none =>
            rw [hBr] at hpost
            exact .inl ⟨hfr, hkr, hag', hpost⟩
          | some Bf =>
            rw [hBr] at hpost
            obtain ⟨x, rfl, hx⟩ := hB _ hBr
            by_cases hbk : holdsC I pay (υ.st.drop body.ext)
                (Fml.isBool (Tm.pvV (p := .bool) x) true)
            · refine .inr ⟨hx _ (by rw [← (holds_isBool_pvV x _ true).1 hbk]; rfl), ?_⟩
              exact Upd.afterT.of_lands
                (hpost.2 (Upd.afterT_intro (fun he => by
                    have hl := (Upd.lands_pop_nil (C := C) Ext.refl (υ.st.drop body.ext)).1
                    rw [he] at hl; cases hl)
                  fun _ σ' hL => (Upd.Lands.eq (Upd.lands_pop_nil _ _) hL) ▸ hbk))
                (Upd.lands_pop_nil _ _)
            · refine .inl ⟨hfr, hkr, hag', ?_⟩
              exact ⟨hpost.1 (fun hb' => hbk (Upd.afterT.of_lands hb' (Upd.lands_pop_nil _ _))),
                hbk⟩
      · rw [hc'] at hc; cases hc)
    o₁ he
  cases o₁ with
  | ok τ => exact COut.after_seq (holdsC_modalK τ.st ω κ φ hL)
  | halt e => exact hL
  | violated => exact hL.elim

/-- **A diamond over a loop whose body calls back never holds**: the loop
may diverge (`ExecS.loopDiverge`, the over-approximation a box accepts),
whatever its invariant or variant, so no diamond rule over it is sound
(`docs/options.md`, O3). -/
theorem holdsC_diamond_loop {Γ Γb Γ₁ Γ₀ : Ctx} {a : LoopAnn C Γ} {c : Val C Γ .bool}
    {body : Prog C Γ Γb} {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀} {φ : Fml C Γ₀} {σ : State C Γ}
    (hb : body.callsBack pay = true) :
    ¬ holdsC I pay σ (.modal .diamond (.cons (.loop a c body) ω) κ φ) := fun h =>
  nomatch (h _ (.halt (.loopDiverge hb))).1

end Inv

/-! ## Soundness -/

theorem holdsC_and_intro {I : Fml C []} {Γ : Ctx} {τ : State C Γ} {φ ψ : Fml C Γ}
    (a : holdsC I pay τ φ) (b : holdsC I pay τ ψ) : holdsC I pay τ (.and φ ψ) := ⟨a, b⟩

theorem holdsC_and_left {I : Fml C []} {Γ : Ctx} {τ : State C Γ} {φ ψ : Fml C Γ}
    (h : holdsC I pay τ (.and φ ψ)) : holdsC I pay τ φ := h.1

theorem holdsC_and_right {I : Fml C []} {Γ : Ctx} {τ : State C Γ} {φ ψ : Fml C Γ}
    (h : holdsC I pay τ (.and φ ψ)) : holdsC I pay τ ψ := h.2

/-- **Soundness of the calculus with callbacks**, for a first-order invariant
with no payment in it: what `ProvesC I pay H φ` proves holds, its context in
front, when the callees `pay` says may call back. -/
theorem ProvesC.sound_of {I : Fml C []} (hI : I.FO = true) (hT : I.hasTransfer = false)
    {Γ₀ Γ : Ctx} {H : Hyps C Γ₀ Γ} {φ : Fml C Γ} (d : ProvesC I pay Γ₀ H φ) :
    ∀ σ, holdsC I pay σ (H.wrap φ) := by
  induction d with
  | plain h hφ => exact fun σ => (holdsC_iff_holds _ hφ σ).2 (Proves.sound h σ)
  | @closeFalse Γ H φ h hH =>
    exact fun σ => H.wrapC_mono (φ := .ff) (ψ := φ)
      (fun _ hf => (hf trivial).elim) σ
      ((holdsC_iff_holds _ hH σ).2 (Proves.sound h σ))
  | intro _ ih => exact ih
  | @notLeft Γ H X φ _ ih =>
    exact fun σ => Hyps.wrapC_mono (ψ := .imp (.not X) φ) _ (fun _ hX hn => (hn hX).elim) σ (ih σ)
  | @hideLeft Γ H a φ _ ih =>
    exact fun σ => Hyps.wrapC_mono (ψ := .imp a φ) _ (fun _ h _ => h) σ (ih σ)
  | allIntro _ ih => exact ih
  | updIntro _ ih => exact ih
  | havocIntro _ ih => exact ih
  | growIntro _ ih => exact ih
  | bindIntro _ ih => exact ih
  | update d hs _ ih =>
    exact fun σ => Hyps.wrapC_mono _ (fun τ h => holdsC_update hs
      (Stmt.runs _ _ _ _ d.toStep τ) h) σ (ih σ)
  | updates d hs _ ih =>
    exact fun σ => Hyps.wrapC_mono _ (fun τ h => holdsC_updates hs
      (Stmt.runs _ _ _ _ d.toStep τ) h) σ (ih σ)
  | guardedUpdates d hs _ _ ihT ihE =>
    refine fun σ => Hyps.wrapC_and _ ?_ σ (ihT σ) (ihE σ)
    exact fun τ a b => holdsC_guardedUpdates hs (Stmt.runs _ _ _ _ d.toStep τ)
      (holdsC_and_intro a b)
  | unfold d hs hP _ ih =>
    exact fun σ => Hyps.wrapC_mono _ (fun τ h => holdsC_unfold hs hP
      (Stmt.runs _ _ _ _ d.toStep τ) h) σ (ih σ)
  | loopExit _ _ ihT ihE =>
    refine fun σ => Hyps.wrapC_and _ ?_ σ (ihT σ) (ihE σ)
    exact fun τ a b => holdsC_loopExit
      (loopExit_cond _ ((holdsC_iff_holds _ rfl τ).1 b)) (a b)
  | @invBox Γ Γb Γ₁ Γ₂ H Iv dec brk qs c body ω κ φ xs hv hf _ _ _ ihI ihT ihE =>
    intro σ
    let A0 : Fml C Γ := (invFml Iv qs).invHyp (loopBreak brk c)
    let U : Upd C Γ (.val .bool :: Γ) := Upd.nil.decl
      (fse (H.freshC I (.modal .box (.cons (.loop (.inv Iv dec brk qs) c body) ω) κ φ)))
      (.val (p := .bool) c.lower)
    let cT : Fml C (.val .bool :: Γ) := .isBool (.pvV (p := .bool) .here) true
    let cF : Fml C (.val .bool :: Γ) := .isBool (.pvV (p := .bool) .here) false
    let A : Fml C (.val .bool :: Γ) := .upd .box (Upd.nil.pop (.push .refl))
      (.modalK .box body (.pop .block body.ext .nil)
        (Fml.invPost .box .refl ω κ φ (invFml Iv qs) (loopBreak brk c)))
    let B : Fml C (.val .bool :: Γ) := .upd .box (Upd.nil.pop (.push .refl)) (.modalK .box ω κ φ)
    have hX : holdsC I pay σ ((H.anonHavoc xs hv).wrap
        (.imp A0 (.upd .box U (.and (.imp cT A) (.imp cF B))))) :=
      (H.anonHavoc xs hv).wrapC_and (φ := .imp A0 (.upd .box U (.imp cT A)))
        (ψ := .imp A0 (.upd .box U (.imp cF B)))
        (χ := .imp A0 (.upd .box U (.and (.imp cT A) (.imp cF B))))
        (fun _ x y hI => Upd.afterT_and (x hI) (y hI) fun _ f g => ⟨f, g⟩) σ (ihT σ) (ihE σ)
    rw [Hyps.wrap_anonHavoc] at hX
    exact H.wrapC_and (fun _ a b => holdsC_invBox hf a b) σ (ihI σ) hX
  | capture _ hc _ ih =>
    exact fun σ => Hyps.wrapC_mono _ (fun _ h => holdsC_capture hc h) σ (ih σ)
  | unfoldReceiver _ _ ih =>
    exact fun σ => Hyps.wrapC_mono _ (fun _ h => holdsC_unfoldReceiver h) σ (ih σ)
  | bind d hs hP _ ih =>
    exact fun σ => Hyps.wrapC_mono _ (fun τ h => holdsC_bind hs hP
      (Stmt.runs _ _ _ _ d.toStep τ) h) σ (ih σ)
  | split d _ _ ihT ihE =>
    refine fun σ => Hyps.wrapC_and _ ?_ σ (ihT σ) (ihE σ)
    exact fun τ a b => holdsC_split (Stmt.runs _ _ _ _ d.toStep τ) (holdsC_and_intro a b)
  | @empty Γ Γ₂ H m κ φ _ ih =>
    exact fun σ => H.wrapC_mono (φ := κ.exit m φ) (ψ := .modal m .nil κ φ)
      (fun τ h o ho => by cases ho; exact holdsC_exit_after κ φ τ h) σ (ih σ)
  | done d hs _ ih =>
    exact fun σ => Hyps.wrapC_mono _ (fun τ h => holdsC_done hs
      (by exact Stmt.runs _ _ _ _ d.toStep τ) h) σ (ih σ)
  | assert _ _ ihT ihE =>
    refine fun σ => Hyps.wrapC_and _ ?_ σ (ihT σ) (ihE σ)
    exact fun τ a b => holdsC_assert (holdsC_and_intro a b)
  | sendDet hp _ _ iho ihf =>
    refine fun σ => Hyps.wrapC_and _ ?_ σ (iho σ) (ihf σ)
    exact fun τ a b => holdsC_sendDet hp _ _ _ a b
  | block _ ih => exact fun σ => Hyps.wrapC_mono _ (fun _ h => holdsC_block h) σ (ih σ)
  | callNone _ ih => exact fun σ => Hyps.wrapC_mono _ (fun _ h => holdsC_callNone h) σ (ih σ)
  | callRets _ ih => exact fun σ => Hyps.wrapC_mono _ (fun _ h => holdsC_callRets h) σ (ih σ)
  | callVal _ ih => exact fun σ => Hyps.wrapC_mono _ (fun _ h => holdsC_callVal h) σ (ih σ)
  | callStorage _ ih =>
    exact fun σ => Hyps.wrapC_mono _ (fun _ h => holdsC_callStorage h) σ (ih σ)
  | callMem _ ih => exact fun σ => Hyps.wrapC_mono _ (fun _ h => holdsC_callMem h) σ (ih σ)
  | callback d _ _ ihx ihr =>
    cases d
    exact fun σ => Hyps.wrapC_and _ (fun τ a b => holdsC_transferCb hI hT _ _ a b) σ
      (ihx σ) (ihr σ)
  | send d _ _ _ ihx iho ihf =>
    cases d
    intro σ
    refine Hyps.wrapC_and _ ?_ σ
      (Hyps.wrapC_and _ (fun _ a b => holdsC_and_intro a b) σ (ihx σ) (iho σ)) (ihf σ)
    exact fun τ ab c => holdsC_sendCb hI hT _ _ _ _ (holdsC_and_left ab) (holdsC_and_right ab) c
  | sendD d _ _ _ _ _ ihx iho ihf =>
    cases d
    intro σ
    refine Hyps.wrapC_and _ ?_ σ
      (Hyps.wrapC_and _ (fun _ a b => holdsC_and_intro a b) σ (ihx σ) (iho σ)) (ihf σ)
    exact fun τ ab c => holdsC_sendCb hI hT _ _ _ _ (holdsC_and_left ab) (holdsC_and_right ab) c
  | sendDetD hp _ _ _ _ iho ihf =>
    refine fun σ => Hyps.wrapC_and _ ?_ σ (iho σ) (ihf σ)
    exact fun τ a b => holdsC_sendDet hp _ _ _ a b
  | tryCall d _ _ _ ihx iho ihc =>
    cases d
    intro σ
    have h₁ := ihc _ List.mem_cons_self σ
    have h₂ := ihc _ (List.mem_cons_of_mem _ List.mem_cons_self) σ
    have h₃ := ihc _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) σ
    refine Hyps.wrapC_and _ ?_ σ
      (Hyps.wrapC_and _ (fun _ a b => holdsC_and_intro a b) σ (ihx σ) (iho σ))
      (Hyps.wrapC_and _ (fun _ a b => holdsC_and_intro a b) σ h₁
        (Hyps.wrapC_and _ (fun _ a b => holdsC_and_intro a b) σ h₂ h₃))
    exact fun τ ab cd => holdsC_tryCb hI hT _ _ _ _ _ _ _ _ _ (holdsC_and_left ab)
      (holdsC_and_right ab) (holdsC_and_left cd) (holdsC_and_left (holdsC_and_right cd))
      (holdsC_and_right (holdsC_and_right cd))
  | recCall _ hc _ ih => exact fun σ => hc σ fun ψ hψ => ih ψ hψ σ
  | trySelf d _ _ _ _ ihx ih0 iho ihc =>
    cases d
    intro σ
    have h₁ := ihc _ List.mem_cons_self σ
    have h₂ := ihc _ (List.mem_cons_of_mem _ List.mem_cons_self) σ
    have h₃ := ihc _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) σ
    refine Hyps.wrapC_and _ ?_ σ
      (Hyps.wrapC_and _ (fun _ a b => holdsC_and_intro a b) σ (ihx σ)
        (Hyps.wrapC_and _ (fun _ a b => holdsC_and_intro a b) σ (ih0 σ) (iho σ)))
      (Hyps.wrapC_and _ (fun _ a b => holdsC_and_intro a b) σ h₁
        (Hyps.wrapC_and _ (fun _ a b => holdsC_and_intro a b) σ h₂ h₃))
    exact fun τ ab cd => holdsC_trySelfCb hI hT _ _ _ _ _ _ _ _ _ (holdsC_and_left ab)
      (holdsC_and_left (holdsC_and_right ab)) (holdsC_and_right (holdsC_and_right ab))
      (holdsC_and_left cd) (holdsC_and_left (holdsC_and_right cd))
      (holdsC_and_right (holdsC_and_right cd))

/-- **A derivation from the empty context proves validity with callbacks**
(the invariant first-order, `Invariant.fo`). -/
theorem ProvesC.fmlValid {I : Invariant C} {φ : Fml C []}
    (d : ProvesC I.fml pay [] .nil φ) : ValidC I φ pay :=
  ProvesC.sound_of I.fo I.noTransfer d

/-- The same, for a transfer semantics (`ValidT`). -/
theorem ProvesC.validT {ts : TransferSem C} {φ : Fml C []}
    (d : ProvesC ts.inv.fml ts.pay [] .nil φ) : ValidT ts φ :=
  ProvesC.fmlValid d

/-! ## The invariant assumed, opened at its scope

Past a frame end that drops every local, the invariant assumed reads the
global part only; where it is a closed first-order formula it is that
formula read at the scope it is assumed in (`Fml.reclose?`), first-order,
which the closer reads (`Proves.openInv`, at a leaf). -/

/-- A closed term, read at another scope: at the empty scope
(`Tm.toNil?`), then at `Γ'` (`Tm.ofNil`). -/
def Tm.reclose? {Γ Γ' : Ctx} {s : Srt} (t : Tm C Γ s) : Option (Tm C Γ' s) :=
  t.toNil?.map Tm.ofNil

/-- A closed first-order formula, read at another scope. -/
def Fml.reclose? {Γ Γ' : Ctx} : Fml C Γ → Option (Fml C Γ')
  | .tt => some .tt
  | .eq a b => do pure (.eq (← a.reclose?) (← b.reclose?))
  | .wellFormed t => (t.reclose?).map .wellFormed
  | .not φ => (Fml.reclose? φ).map .not
  | .and φ ψ => do pure (.and (← Fml.reclose? φ) (← Fml.reclose? ψ))
  | .imp φ ψ => do pure (.imp (← Fml.reclose? φ) (← Fml.reclose? ψ))
  | _ => none

/-- An assumption opened: the invariant past a frame end that drops every
local, read at the scope. -/
def Fml.openInv {Γ : Ctx} : Fml C Γ → Fml C Γ
  | .upd .box (.drop .nil h) φ => match Fml.reclose? (Γ' := Γ) φ with
    | some φ' => φ'
    | none => .upd .box (.drop .nil h) φ
  | φ => φ

/-- The context with each assumed invariant opened. -/
def Hyps.openInv {Γ₀ : Ctx} : {Γ : Ctx} → Hyps C Γ₀ Γ → Hyps C Γ₀ Γ
  | _, .nil => .nil
  | _, .pre H a => .pre (Hyps.openInv H) a.openInv
  | _, .upd H m U => .upd (Hyps.openInv H) m U
  | _, .havoc H => .havoc (Hyps.openInv H)
  | _, .all H x p => .all (Hyps.openInv H) x p
  | _, .bind H m x t => .bind (Hyps.openInv H) m x t
  | _, .anon H xs => .anon (Hyps.openInv H) xs
  | _, .allocAll H x A => .allocAll (Hyps.openInv H) x A
  | _, .grow H => .grow (Hyps.openInv H)

theorem Tm.reclose_eval {Γ Γ' : Ctx} {s : Srt} {t : Tm C Γ s} {t' : Tm C Γ' s}
    (h : t.reclose? = some t') (σ : State C Γ) (τ : State C Γ') (hg : σ.glob = τ.glob) :
    Srt.SameO s (t'.eval τ) (t.eval σ) := by
  obtain ⟨t₀, ht₀, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [Tm.eval_ofNil τ, Tm.eval_toNilS σ t ht₀]
  have key : ∀ g g' : State C [], g = g' → Srt.SameO s (t₀.eval g') (t₀.eval g) := by
    intro g g' e; subst e; exact Srt.SameO.refl _ _
  exact key _ _ hg

theorem Tm.reclose_denote {Γ Γ' : Ctx} {s : Srt} {t : Tm C Γ s} {t' : Tm C Γ' s}
    (h : t.reclose? = some t') (σ : State C Γ) (τ : State C Γ') (hg : σ.glob = τ.glob) :
    t'.denote τ = t.denote σ := by
  obtain ⟨t₀, ht₀, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [Tm.denote_ofNil τ, Tm.denote_toNilS σ t ht₀]
  show t₀.denote τ.glob = t₀.denote σ.glob
  rw [hg]

/-- **A closed formula reads alike at another scope**, over the same global
part. -/
theorem holds_reclose {Γ Γ' : Ctx} : (φ : Fml C Γ) → {φ' : Fml C Γ'} → φ.reclose? = some φ' →
    (σ : State C Γ) → (τ : State C Γ') → σ.glob = τ.glob →
      (holds τ φ' ↔ holds σ φ)
  | .tt, _, h, _, _, _ => by cases h; exact Iff.rfl
  | .eq a b, _, h, σ, τ, hg => by
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨b', hb, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    rw [holds_eq, holds_eq, Tm.reclose_denote ha _ _ hg, Tm.reclose_denote hb _ _ hg]
  | .wellFormed t, _, h, σ, τ, hg => by
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [holds_wellFormed, holds_wellFormed, Srt.sameO_st.1 (Tm.reclose_eval ht _ _ hg)]
  | .not φ, _, h, σ, τ, hg => by
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact not_congr (holds_reclose φ hφ σ τ hg)
  | .and φ ψ, _, h, σ, τ, hg => by
    obtain ⟨φ', hφ, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨ψ', hψ, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact and_congr (holds_reclose φ hφ σ τ hg) (holds_reclose ψ hψ σ τ hg)
  | .imp φ ψ, _, h, σ, τ, hg => by
    obtain ⟨φ', hφ, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨ψ', hψ, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact imp_congr (holds_reclose φ hφ σ τ hg) (holds_reclose ψ hψ σ τ hg)
  | .upd .., _, h, _, _, _ | .modal .., _, h, _, _, _ | .havoc _, _, h, _, _, _
  | .all .., _, h, _, _, _ | .bind .., _, h, _, _, _ | .anon .., _, h, _, _, _ => nomatch h

/-! ### The invariant assumed, at the end of a resumed program

"Resume after callback" assumes the invariant past a frame end that drops
every local (`Fml.closedAt`), and a goal past a program that ends where
it is resumed is the postcondition past the frames' scope ends
(`Frames.exit`).  Where the goal is the invariant read at its scope (a
closed first-order formula, `Fml.reclose?`), the assumption is the goal:
`Proves.assumeInv`, KeY's `close` on `I ⟹ I`. -/

/-- Frames that only end scopes. -/
def Frames.popsOnly {Γ Γ₀ : Ctx} : Frames C Γ Γ₀ → Bool
  | .nil => true
  | .seq .nil κ => Frames.popsOnly κ
  | .seq (.cons ..) _ => false
  | .pop _ _ κ | .drop _ κ => Frames.popsOnly κ

/-- Past scope ends, a closed formula holds where the formula it reads as
at the empty scope holds, over the same global part. -/
theorem holds_exit_closed {Γ₀ : Ctx} {φ : Fml C Γ₀} {I : Fml C []} (hφ : φ.reclose? = some I)
    {τ₀ : State C []} (h : holds τ₀ I) :
    {Γ : Ctx} → (κ : Frames C Γ Γ₀) → κ.popsOnly = true → ∀ σ : State C Γ,
      σ.glob = τ₀.glob → holds σ (κ.exit .box φ)
  | _, .nil, _, σ, e => (holds_reclose φ hφ σ τ₀ e).1 h
  | _, .seq .nil κ, hκ, σ, e => holds_exit_closed hφ h κ hκ σ e
  | _, .pop _ _ κ, hκ, _, e =>
    Upd.afterT_intro (fun _ => trivial) fun _ σ' hL =>
      holds_exit_closed hφ h κ hκ σ'
        ((hL.2.1.trans (congrArg Subtype.val (Option.some.inj hL.1).symm)).trans e)
  | _, .drop _ κ, hκ, _, e =>
    Upd.afterT_intro (fun _ => trivial) fun _ σ' hL =>
      holds_exit_closed hφ h κ hκ σ'
        ((hL.2.1.trans (congrArg Subtype.val (Option.some.inj hL.1).symm)).trans e)

/-- **The invariant assumed is the goal**: `…, {havoc}, I ⟹ I`, the
assumption past a frame end that drops every local, the goal past the
program's scope ends, read as `I` at the empty scope. -/
theorem Proves.assumeInv {R : RuleSet} {Γ₀ Γ Δ : Ctx} {H : Hyps C Γ₀ Γ} {I : Fml C []}
    {κ : Frames C Γ Δ} {φ : Fml C Δ} (hκ : κ.popsOnly = true := by rfl)
    (he : φ.reclose? = some I := by rfl) (hb : H.boxOnly = true := by rfl)
    (hm : ((H.pre (Fml.closedAt I)).wrap (κ.exit .box φ)).modalFree = true := by
      first | rfl | decide) :
    Proves C R Γ₀ (H.pre (Fml.closedAt I)) (κ.exit .box φ) := by
  refine .closeHolds (fun σ => H.wrap_valid (φ := .imp (Fml.closedAt I) (κ.exit .box φ)) hb
    (fun τ hτ => ?_) σ) hm
  exact holds_exit_closed he
    (Upd.afterT.of_lands hτ (Upd.lands_drop_nil (Thin.nilTo Γ) τ)) κ hκ τ rfl

/-- An assumption gives it opened. -/
theorem holds_openInv {Γ : Ctx} (a : Fml C Γ) (τ : State C Γ) (h : holds τ a) :
    holds τ a.openInv := by
  unfold Fml.openInv
  split
  · rename_i Δ e φ
    split
    · rename_i φ' hφ
      exact (holds_reclose φ hφ (τ.thin e) τ rfl).2
        (Upd.afterT.of_lands h (Upd.lands_drop_nil e τ))
    · exact h
  · exact h

/-- The context with its assumed invariants opened gives the context. -/
theorem Hyps.wrap_openInv {Γ₀ Γ : Ctx} (H : Hyps C Γ₀ Γ) :
    ∀ {φ ψ : Fml C Γ}, (∀ τ, holds τ φ → holds τ ψ) →
      ∀ σ, holds σ (H.openInv.wrap φ) → holds σ (H.wrap ψ) := by
  induction H with
  | nil => intro φ ψ h σ; exact h σ
  | pre H a ih =>
    intro φ ψ h
    exact ih (φ := .imp a.openInv φ) (ψ := .imp a ψ) fun τ f ha => h τ (f (holds_openInv a τ ha))
  | upd H m U ih =>
    intro φ ψ h
    exact ih (φ := .upd m U φ) (ψ := .upd m U ψ) fun τ f =>
      Upd.afterT_imp f fun σ' x => h σ' x
  | havoc H ih =>
    intro φ ψ h
    exact ih (φ := .havoc φ) (ψ := .havoc ψ) fun τ f st nt sb => h _ (f st nt sb)
  | all H x p ih =>
    intro φ ψ h
    exact ih (φ := .all x p φ) (ψ := .all x p ψ) fun τ f v => h _ (f v)
  | bind H m x t ih =>
    intro φ ψ h
    exact ih (φ := .bind m x t φ) (ψ := .bind m x t ψ) fun τ f =>
      Modality.forallB_imp (fun _ a => h _ a) f
  | anon H xs ih =>
    intro φ ψ h
    exact ih (φ := .anon xs φ) (ψ := .anon xs ψ) fun τ f b => h _ (f b)
  | allocAll H x A ih =>
    intro φ ψ h
    exact ih (φ := .allocAll x A φ) (ψ := .allocAll x A ψ) fun τ f o => h _ (f o)
  | grow H ih =>
    intro φ ψ h
    exact ih (φ := .grow φ) (ψ := .grow ψ) fun τ f st nt => h _ (f st nt)

/-- **The invariant assumed, opened**: at a leaf, each assumed invariant read
at its scope, a closed first-order formula the closer reads. -/
theorem Proves.openInv {R : RuleSet} {Γ₀ Γ : Ctx} {H : Hyps C Γ₀ Γ} {φ : Fml C Γ}
    (h : Proves C R Γ₀ H.openInv φ)
    (hm : (H.wrap φ).modalFree = true := by first | rfl | decide) : Proves C R Γ₀ H φ :=
  .closeHolds (fun σ => H.wrap_openInv (fun _ h => h) σ (Proves.sound h σ)) hm

/-- A derivation of the translation proves the direct correctness statement
under the given callback invariant and transfer policy. -/
theorem ProvesC.valid {I : Invariant C} {φ : Spec C []} {pay : Bool}
    (d : ProvesC I.fml pay [] .nil φ.toFml) : Spec.ValidC I φ pay :=
  (Spec.validC_iff I φ pay).mpr (ProvesC.fmlValid d)

/-- info: 'Solidity.ProvesC.valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ProvesC.valid

/-- info: 'Solidity.ProvesC.fmlValid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ProvesC.fmlValid

end Solidity
