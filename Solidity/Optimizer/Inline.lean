import Solidity.Optimizer.StmtFold
import Solidity.Semantics.RunWk

/-!
# O03 inlining of internal function calls

`f(e₁, …, eₙ);` for an internal function with no return value (`CallRet.none`)
runs its body in a frame of its own: the arguments evaluated in order, the body
run over them, the caller's locals restored. Inlining writes it as a block of the
caller:

`{ T₁ x₁ = e₁; …; Tₙ xₙ = eₙ; body' }`

with a value parameter declared as a value local, a storage parameter as the
storage alias `R storage xᵢ = eᵢ;` (`declStorage … (some (.path eᵢ))`, the
identity the call shares) and a memory parameter as the memory alias
`R memory xᵢ = eᵢ;` (`declMem … (some (.alias eᵢ))`, the object by identity, no
copy, as the call binds it), where each `eᵢ` is read past the parameters declared before it
(`Val.wk (thinUnder _)`) and `body'` is the body weakened into the caller's
context (`Prog.wk (thinTop Γ ps)`), so it reads only its parameters. The
block runs as the call (`inlineBlock_runC`; `inlineCall_runC` dispatches):
the declarations evaluate the arguments in the call's order with the same
halts (`bindArgs_runC`), the weakened body runs as the body with the caller's
locals kept alongside (`Prog.run_wk`, `TWkRel.drop`), and the block's end pops the parameters and
the body's locals, which leaves the caller's locals exactly as the call
restores them (`drop_put_top`, `off_bot_inj`).

Covered: calls with `CallRet.none` or one value return (`CallRet.val`, assigned
to a caller local or discarded), with value, storage and memory parameters.
A value-returning call becomes `{ params; T r; { body' } x = r; }`
(`inlineBlockVal_runC`, through `frame_runC`). Calls with several returns,
memory or storage returns,
recursive calls (`callRec`), receiver calls and external calls are left as
written. The pass inlines every covered call, including calls inside `if`
branches, blocks and loop bodies, once (a body's own calls are not inlined),
and not inside `try`, receiver-call or non-inlined call bodies. Only
`Stmt.runC` is preserved: the call's name, and whatever printers or automation
read from it, are gone, and gas and code size are not modelled.
-/
namespace Solidity.Optimizer.ConstFold
open Solidity

variable {C : Contract}

/-! ## Thinnings into a frame -/

/-- No local kept: the whole of `Γ` dropped. -/
def thinBot : (Γ : Ctx) → Thin [] Γ
  | [] => .refl
  | _ :: Γ => .drop (thinBot Γ)

/-- The frame `ps` kept, the caller's `Γ` dropped below it. -/
def thinTop (Γ : Ctx) : (ps : Ctx) → Thin ps (ps ++ Γ)
  | [] => thinBot Γ
  | _ :: ps => .keep (thinTop Γ ps)

/-- The caller's `Γ` kept, the parameters `ps` dropped above it. -/
def thinUnder {Γ : Ctx} : (ps : Ctx) → Thin Γ (ps ++ Γ)
  | [] => .refl
  | _ :: ps => .drop (thinUnder ps)

section Env
variable {H : HTy}

theorem put_bot : (Γ : Ctx) → (d : TEnv C H Γ) → TEnv.put (thinBot Γ) () d = d
  | [], _ => rfl
  | _ :: Γ, d => congrArg (Prod.mk d.1) (put_bot Γ d.2)

theorem put_top (Γ : Ctx) : (ps : Ctx) → (a a' : TEnv C H ps) → (e : TEnv C H Γ) →
    TEnv.put (thinTop Γ ps) a (TEnv.append ps a' e) = TEnv.append ps a e
  | [], _, _, e => put_bot Γ e
  | _ :: ps, a, a', e => congrArg (Prod.mk a.1) (put_top Γ ps a.2 a'.2 e)

theorem put_under {Γ : Ctx} : (ps : Ctx) → (a : TEnv C H ps) → (e : TEnv C H Γ) →
    TEnv.put (thinUnder ps) e (TEnv.append ps a e) = TEnv.append ps a e
  | [], _, _ => rfl
  | _ :: ps, a, e => congrArg (Prod.mk a.1) (put_under ps a.2 e)

theorem drop_put_top (Γ : Ctx) : (ps : Ctx) → (x : TEnv C H ps) → (d : TEnv C H (ps ++ Γ)) →
    TEnv.drop (Ext.append Γ ps) (TEnv.put (thinTop Γ ps) x d) = TEnv.drop (Ext.append Γ ps) d
  | [], _, d => put_bot Γ d
  | _ :: ps, x, d => drop_put_top Γ ps x.2 d.2

theorem off_top (Γ : Ctx) : (ps : Ctx) → (d : TEnv C H (ps ++ Γ)) →
    TEnv.off (thinTop Γ ps) d = TEnv.off (thinBot Γ) (TEnv.drop (Ext.append Γ ps) d)
  | [], _ => rfl
  | _ :: ps, d => off_top Γ ps d.2

theorem drop_append_append {Γ : Ctx} : (ps : Ctx) → (a : TEnv C H ps) → (e : TEnv C H Γ) →
    TEnv.drop (Ext.append Γ ps) (TEnv.append ps a e) = e
  | [], _, _ => rfl
  | _ :: ps, a, e => drop_append_append ps a.2 e

/-- An environment is determined by the list of all its values. -/
theorem off_bot_inj : (Γ : Ctx) → (x y : TEnv C H Γ) →
    TEnv.off (thinBot Γ) x = TEnv.off (thinBot Γ) y → x = y
  | [], _, _, _ => rfl
  | _ :: Γ, x, y, h => by
    simp only [thinBot, TEnv.off, List.cons.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at h
    obtain ⟨h1, h2⟩ := h
    have := off_bot_inj Γ x.2 y.2 h2
    cases x
    cases y
    simp only at h1 this
    rw [h1, this]

end Env

/-! ## Binding the arguments -/

/-- The parameters declared in order, each argument read past the ones before. -/
def bindArgs {Γ Δ : Ctx} : {ps : Ctx} → (as : Args C Γ ps) → Prog C (ps ++ Γ) Δ → Prog C Γ Δ
  | _, .nil, k => k
  | _, .snoc (ps := ps) as p x e, k =>
    bindArgs as (.cons (.declLocal p x (some (e.wk (thinUnder ps)))) k)
  | _, .snocStorage (ps := ps) as R x e, k =>
    bindArgs as (.cons (.declStorage R x (some (.path (e.wk (thinUnder ps))))) k)
  | _, .snocMemory (ps := ps) as R x e, k =>
    bindArgs as (.cons (.declMem R x (some (.alias (e.wk (thinUnder ps)))) rfl
      (e.wk (thinUnder ps)).mapFree) k)

theorem bindArgs_runC {Γ Δ : Ctx} (σ : State C Γ) : {ps : Ctx} → (as : Args C Γ ps) →
    (k : Prog C (ps ++ Γ) Δ) →
    Prog.runC (bindArgs as k) σ =
      (as.evalT σ).bind fun a => (Prog.runC k (σ.withEnv (TEnv.append ps a σ.env))).map
        fun o => ⟨o.st, o.ext⟩
  | _, .nil, k => by
    change Prog.runC k σ = (Prog.runC k σ).map fun o => ⟨o.st, o.ext⟩
    cases Prog.runC k σ <;> rfl
  | _, .snoc (ps := ps) as p x e, k => by
    simp only [bindArgs]
    rw [bindArgs_runC σ as]
    cases ha : as.evalT σ with
    | error err =>
      show Except.error err = (Args.evalT σ (.snoc as p x e)).bind _
      simp only [Args.evalT, ha, bind, Except.bind]
    | ok a =>
      have hv : (e.wk (thinUnder ps)).evalT (σ.withEnv (TEnv.append ps a σ.env)) = e.evalT σ := by
        have := Val.evalT_wk (h := thinUnder ps) (τ := σ) (d := TEnv.append ps a σ.env) e
        rw [← this]
        show _ = Val.evalT (σ.withEnv (TEnv.put (thinUnder ps) σ.env (TEnv.append ps a σ.env))) _
        rw [put_under]
      show (Prog.runC (.cons (.declLocal p x (some (e.wk (thinUnder ps)))) k)
          (σ.withEnv (TEnv.append ps a σ.env))).map _ = (Args.evalT σ (.snoc as p x e)).bind _
      simp only [Args.evalT, ha, Prog.runC, TRun.seq, Stmt.runC, TRun.declLocal, hv, bind,
        Except.bind, pure, Except.pure]
      cases he : e.evalT σ with
      | error err => rfl
      | ok v =>
        show Except.map _ (Except.map (fun o' => (⟨o'.st, _⟩ : Out C σ.H Δ))
            (Prog.runC k (σ.withEnv (TEnv.append (.val p :: ps) (v, a) σ.env)))) =
          Except.map _ (Prog.runC k (σ.withEnv (TEnv.append (.val p :: ps) (v, a) σ.env)))
        cases Prog.runC k (σ.withEnv (TEnv.append (.val p :: ps) (v, a) σ.env)) <;> rfl
  | _, .snocStorage (ps := ps) as R x e, k => by
    simp only [bindArgs]
    rw [bindArgs_runC σ as]
    cases ha : as.evalT σ with
    | error err =>
      show Except.error err = (Args.evalT σ (.snocStorage as R x e)).bind _
      simp only [Args.evalT, ha, bind, Except.bind]
    | ok a =>
      have hv : (e.wk (thinUnder ps)).resolveT (σ.withEnv (TEnv.append ps a σ.env)) =
          e.resolveT σ := by
        have := SPath.resolveT_wk (h := thinUnder ps) (τ := σ) (d := TEnv.append ps a σ.env) e
        rw [← this]
        show _ = SPath.resolveT (σ.withEnv (TEnv.put (thinUnder ps) σ.env (TEnv.append ps a σ.env))) _
        rw [put_under]
      show (Prog.runC (.cons (.declStorage R x (some (.path (e.wk (thinUnder ps))))) k)
          (σ.withEnv (TEnv.append ps a σ.env))).map _ = (Args.evalT σ (.snocStorage as R x e)).bind _
      simp only [Args.evalT, ha, Prog.runC, TRun.seq, Stmt.runC, TRun.declStorage, ARhs.evalT, hv,
        bind, Except.bind, pure, Except.pure]
      cases he : e.resolveT σ with
      | error err => rfl
      | ok v =>
        show Except.map _ (Except.map (fun o' => (⟨o'.st, _⟩ : Out C σ.H Δ))
            (Prog.runC k (σ.withEnv (TEnv.append (.alias R :: ps) (some v, a) σ.env)))) =
          Except.map _ (Prog.runC k (σ.withEnv (TEnv.append (.alias R :: ps) (some v, a) σ.env)))
        cases Prog.runC k (σ.withEnv (TEnv.append (.alias R :: ps) (some v, a) σ.env)) <;> rfl
  | _, .snocMemory (ps := ps) as R x e, k => by
    simp only [bindArgs]
    rw [bindArgs_runC σ as]
    cases ha : as.evalT σ with
    | error err =>
      show Except.error err = (Args.evalT σ (.snocMemory as R x e)).bind _
      simp only [Args.evalT, ha, bind, Except.bind]
    | ok a =>
      have hv : (e.wk (thinUnder ps)).mvalT (σ.withEnv (TEnv.append ps a σ.env)) = e.mvalT σ := by
        have := MPath.mvalT_wk (h := thinUnder ps) (τ := σ) (d := TEnv.append ps a σ.env) e
        rw [← this]
        show _ = MPath.mvalT (σ.withEnv (TEnv.put (thinUnder ps) σ.env (TEnv.append ps a σ.env))) _
        rw [put_under]
      show (Prog.runC (.cons (.declMem R x (some (.alias (e.wk (thinUnder ps)))) rfl
          (e.wk (thinUnder ps)).mapFree) k) (σ.withEnv (TEnv.append ps a σ.env))).map _ =
        (Args.evalT σ (.snocMemory as R x e)).bind _
      simp only [Args.evalT, ha, Prog.runC, TRun.seq, Stmt.runC, TRun.declMem, MRhs.evalT, hv,
        bind, Except.bind, pure, Except.pure]
      cases he : e.mvalT σ with
      | error err => rfl
      | ok v =>
        show Except.map _ (Except.map (fun o' => (⟨o'.st, _⟩ : Out C σ.H Δ))
            (Prog.runC k (σ.withEnv (TEnv.append (.mem R :: ps) (some v, a) σ.env)))) =
          Except.map _ (Prog.runC k (σ.withEnv (TEnv.append (.mem R :: ps) (some v, a) σ.env)))
        cases Prog.runC k (σ.withEnv (TEnv.append (.mem R :: ps) (some v, a) σ.env)) <;> rfl

/-! ## The inlined call -/

private theorem drop_trans' {H : HTy} {Γ Δ : Ctx} (a : Ext Γ Δ) : {Ε : Ctx} → (b : Ext Δ Ε) →
    (e : TEnv C H Ε) → TEnv.drop (a.trans b) e = TEnv.drop a (TEnv.drop b e)
  | _, .refl, _ => rfl
  | _, .push b, e => drop_trans' a b e.2

/-- A void call with value arguments, as a block of the caller. -/
def inlineBlock {Γ ps Γf : Ctx} (args : Args C Γ ps) (body : Prog C ps Γf) : Stmt C Γ Γ :=
  .block (bindArgs args (body.wk (thinTop Γ ps)).2.2)

/-- **An inlined void call runs as the call.** -/
theorem inlineBlock_runC {Γ ps Γf : Ctx} (f : Name) (args : Args C Γ ps)
    (body : Prog C ([] ++ ps) Γf) :
    Stmt.runC (inlineBlock args body) = Stmt.runC (.call f args .none body) := by
  funext σ
  simp only [inlineBlock, Stmt.runC, TRun.block, TRun.call]
  rw [bindArgs_runC]
  cases ha : args.evalT σ with
  | error e => rfl
  | ok a =>
    have hd := TWkRel.drop (Prog.wk_over body (thinTop Γ ps))
      (Prog.run_wk body (thinTop Γ ps) (σ.withEnv a) (TEnv.append ps a σ.env))
    change TWkRel _ _ _ (((body.wk (thinTop Γ ps)).2.2.run
      (σ.withEnv (TEnv.put (thinTop Γ ps) a (TEnv.append ps a σ.env)))).map _) at hd
    rw [put_top] at hd
    simp only [Prog.run, Prog.runR_eq] at hd
    generalize (Prog.wk (thinTop Γ ps) body).snd.snd = Pw at hd ⊢
    rw [Subsingleton.elim (bindArgs args Pw).ext ((Ext.append Γ ps).trans Pw.ext)]
    simp only [Except.bind, bind, pure, Except.pure]
    simp only [CallRet.enterT, CallRet.leaveT]
    cases hb : body.runC (σ.withEnv a) with
    | error e =>
      rw [hb] at hd
      cases hw : Pw.runC (σ.withEnv (TEnv.append ps a σ.env)) with
      | error e' =>
        rw [hw] at hd
        have : e = e' := hd
        subst this
        rfl
      | ok b =>
        rw [hw] at hd
        exact False.elim hd
    | ok o =>
      rw [hb] at hd
      cases hw : Pw.runC (σ.withEnv (TEnv.append ps a σ.env)) with
      | error e' =>
        rw [hw] at hd
        exact False.elim hd
      | ok b =>
        rw [hw] at hd
        obtain ⟨d'', hoff, hbd⟩ := hd
        have hst : State.drop Pw.ext b.st =
            State.lift (thinTop Γ ps) (State.drop body.ext o.st) d'' := congrArg Out.st hbd
        have key : TEnv.drop (Ext.append Γ ps) d'' = TEnv.wk o.ext Γ σ.env := by
          apply off_bot_inj Γ
          rw [← off_top, hoff, off_top Γ ps (TEnv.append ps a σ.env), drop_append_append,
            TEnv.off_wk]
        have e1 : State.drop ((Ext.append Γ ps).trans Pw.ext) b.st =
            State.drop (Ext.append Γ ps) (State.drop Pw.ext b.st) := by
          simp only [State.drop, State.withEnv, drop_trans']
        show Except.ok (⟨State.drop ((Ext.append Γ ps).trans Pw.ext) b.st, _⟩ : Out C σ.H Γ) =
          Except.ok ⟨o.st.withEnv (TEnv.wk o.ext Γ σ.env), _⟩
        simp only [Except.ok.injEq, Out.mk.injEq]
        rw [e1, hst]
        simp only [State.drop, State.lift, State.withEnv, drop_put_top, key]

/-- `put_top` for any background: the frame on top of what `d` holds below it. -/
theorem put_top_gen (Γ : Ctx) : (ps : Ctx) → {H : HTy} → (x : TEnv C H ps) →
    (d : TEnv C H (ps ++ Γ)) →
    TEnv.put (thinTop Γ ps) x d = TEnv.append ps x (TEnv.drop (Ext.append Γ ps) d)
  | [], _, _, d => put_bot Γ d
  | _ :: ps, _, x, d => congrArg (Prod.mk x.1) (put_top_gen Γ ps x.2 d.2)

/-- **The weakened body, its scope ended, leaves its frame's final locals on top
of the caller's locals as the call restores them.** -/
theorem frame_runC {Γ qs Γf : Ctx} (σ : State C Γ) (body : Prog C qs Γf) (x : TEnv C σ.H qs) :
    ((body.wk (thinTop Γ qs)).2.2.runC (σ.withEnv (TEnv.append qs x σ.env))).map
        (Out.drop (body.wk (thinTop Γ qs)).2.2.ext) =
      (body.runC (σ.withEnv x)).map fun o =>
        (⟨(State.drop body.ext o.st).withEnv
          (TEnv.append qs (TEnv.drop body.ext o.st.env) (TEnv.wk o.ext Γ σ.env)), o.ext⟩ :
          Out C σ.H (qs ++ Γ)) := by
  have hd := TWkRel.drop (Prog.wk_over body (thinTop Γ qs))
    (Prog.run_wk body (thinTop Γ qs) (σ.withEnv x) (TEnv.append qs x σ.env))
  change TWkRel _ _ _ (((body.wk (thinTop Γ qs)).2.2.run
    (σ.withEnv (TEnv.put (thinTop Γ qs) x (TEnv.append qs x σ.env)))).map _) at hd
  rw [put_top] at hd
  simp only [Prog.run, Prog.runR_eq] at hd
  generalize (Prog.wk (thinTop Γ qs) body).snd.snd = Pw at hd ⊢
  cases hb : body.runC (σ.withEnv x) with
  | error e =>
    rw [hb] at hd
    cases hw : Pw.runC (σ.withEnv (TEnv.append qs x σ.env)) with
    | error e' =>
      rw [hw] at hd
      have : e = e' := hd
      subst this
      rfl
    | ok b =>
      rw [hw] at hd
      exact False.elim hd
  | ok o =>
    rw [hb] at hd
    cases hw : Pw.runC (σ.withEnv (TEnv.append qs x σ.env)) with
    | error e' =>
      rw [hw] at hd
      exact False.elim hd
    | ok b =>
      rw [hw] at hd
      obtain ⟨d'', hoff, hbd⟩ := hd
      have key : TEnv.drop (Ext.append Γ qs) d'' = TEnv.wk o.ext Γ σ.env := by
        apply off_bot_inj Γ
        rw [← off_top, hoff, off_top Γ qs (TEnv.append qs x σ.env), drop_append_append,
          TEnv.off_wk]
      show Except.ok (Out.drop Pw.ext b) = Except.ok _
      rw [hbd]
      simp only [Except.ok.injEq, Out.mk.injEq, State.lift, put_top_gen, key]
      rfl

theorem drop_append_set {H : HTy} {Γ : Ctx} {p : PrimTy} (i : Idx Γ (.val p)) (v : p.Denote) :
    (qs : Ctx) → (X : TEnv C H (qs ++ Γ)) →
      TEnv.drop (Ext.append Γ qs) (TEnv.set (i.wk (thinUnder qs)) v X) =
        TEnv.set i v (TEnv.drop (Ext.append Γ qs) X)
  | [], X => by simp only [thinUnder, Idx.wk_refl]; rfl
  | _ :: qs, X => drop_append_set i v qs X.2

/-- After the body: the return local, assigned to the caller's local when one
receives it. -/
def retTail {Γ qs : Ctx} {p : PrimTy} :
    Option (Idx Γ (.val p)) → Prog C (.val p :: qs ++ Γ) (.val p :: qs ++ Γ)
  | some i => .cons (.assignLocal (i.wk (thinUnder (.val p :: qs))) (.simple (.local .here))) .nil
  | none => .nil

/-- A call with one value return and value arguments, as a block of the caller:
`{ params; T r; { body' } (x = r;) }`. -/
def inlineBlockVal {Γ ps Γf : Ctx} (args : Args C Γ ps) (p : PrimTy)
    (r : Var) (res : Option (Idx Γ (.val p))) (body : Prog C ([.val p] ++ ps) Γf) :
    Stmt C Γ Γ :=
  .block (bindArgs args (.cons (.declLocal p r none)
    (.cons (.block (body.wk (thinTop Γ (.val p :: ps))).2.2) (retTail res))))

theorem inlineBlockVal_runC {Γ ps Γf : Ctx} (f : Name) (args : Args C Γ ps)
    (p : PrimTy) (r : Var) (res : Option (Idx Γ (.val p)))
    (body : Prog C ([.val p] ++ ps) Γf) :
    Stmt.runC (inlineBlockVal args p r res body) =
      Stmt.runC (.call f args (.val p r res) body) := by
  funext σ
  simp only [inlineBlockVal, Stmt.runC, TRun.block, TRun.call]
  rw [bindArgs_runC]
  cases ha : args.evalT σ with
  | error e => rfl
  | ok a =>
    have hf := frame_runC (qs := .val p :: ps) σ body
      ((PrimTy.dflt p, a) : TEnv C σ.H (.val p :: ps))
    generalize (Prog.wk (thinTop Γ (.val p :: ps)) body).snd.snd = Pw at hf ⊢
    rw [Subsingleton.elim (bindArgs args _).ext (Ext.append Γ (.val p :: ps))]
    simp only [Except.bind, bind, pure, Except.pure, CallRet.enterT, CallRet.leaveT, TEnv.take,
      Prog.runC, TRun.seq, Stmt.runC, TRun.declLocal, TRun.block]
    have hf' : Except.map (fun o => (⟨State.drop Pw.ext o.st, o.ext⟩ : Out C σ.H _))
        (Pw.runC ((σ.withEnv (TEnv.append ps a σ.env)).push (t := .val p) (PrimTy.dflt p))) =
      Except.map (fun o =>
        (⟨(State.drop body.ext o.st).withEnv (TEnv.append (.val p :: ps)
          (TEnv.drop body.ext o.st.env) (TEnv.wk o.ext Γ σ.env)), o.ext⟩ :
          Out C σ.H (.val p :: ps ++ Γ)))
        (body.runC (σ.withEnv ((PrimTy.dflt p, a) : TEnv C σ.H (.val p :: ps)))) := hf
    have hb' : body.runC ((σ.withEnv a).push (t := .val p) (PrimTy.dflt p)) =
      body.runC (σ.withEnv ((PrimTy.dflt p, a) : TEnv C σ.H (.val p :: ps))) := rfl
    rw [hf', hb']
    cases body.runC (σ.withEnv ((PrimTy.dflt p, a) : TEnv C σ.H (.val p :: ps))) with
    | error e => rfl
    | ok o =>
      cases res with
      | none =>
        show Except.ok _ = Except.ok _
        simp only [State.drop, State.withEnv, drop_append_append]
      | some i =>
        show Except.ok _ = Except.ok _
        simp only [Except.ok.injEq, Out.mk.injEq, State.drop, State.withEnv, State.setLocal]
        rw [drop_append_set, drop_append_append]
        rfl

/-- A call, inlined when it is void or returns one value. -/
def inlineCall {Γ Γ' ps rs Γf : Ctx} (f : Name) (args : Args C Γ ps) :
    (ret : CallRet Γ rs Γ') → (body : Prog C (rs ++ ps) Γf) → Stmt C Γ Γ'
  | .none, body => inlineBlock args body
  | .val p r res, body => inlineBlockVal args p r res body
  | ret@(.rets ..), body | ret@(.mem ..), body | ret@(.storage ..), body =>
    .call f args ret body

theorem inlineCall_runC {Γ Γ' ps rs Γf : Ctx} (f : Name) (args : Args C Γ ps) :
    (ret : CallRet Γ rs Γ') → (body : Prog C (rs ++ ps) Γf) →
      Stmt.runC (inlineCall f args ret body) = Stmt.runC (.call f args ret body)
  | .none, body => inlineBlock_runC f args body
  | .val p r res, body => inlineBlockVal_runC f args p r res body
  | .rets .., _ | .mem .., _ | .storage .., _ => rfl

mutual
/-- Inline every covered call of a statement (in branches, blocks and loop bodies). -/
def Stmt.inl : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Stmt C Γ Γ'
  | _, _, .ite c thn els => .ite c (Prog.inl thn) (Prog.inl els)
  | _, _, .block body => .block (Prog.inl body)
  | _, _, .loop a c body => .loop a c (Prog.inl body)
  | _, _, .call f args ret body => inlineCall f args ret body
  | _, _, s@(.assign ..) => s
  | _, _, s@(.rebind ..) => s
  | _, _, s@(.assignLocal ..) => s
  | _, _, s@(.declLocal ..) => s
  | _, _, s@(.declStorage ..) => s
  | _, _, s@(.opAssign ..) => s
  | _, _, s@(.incDec ..) => s
  | _, _, s@(.assignIncDec ..) => s
  | _, _, s@(.assignLocalPush ..) => s
  | _, _, s@(.push ..) => s
  | _, _, s@(.pop ..) => s
  | _, _, s@(.transfer ..) => s
  | _, _, s@(.send ..) => s
  | _, _, s@(.declMem ..) => s
  | _, _, s@(.rebindMem ..) => s
  | _, _, s@(.assignFromMem ..) => s
  | _, _, s@(.assignMem ..) => s
  | _, _, s@(.delete ..) => s
  | _, _, s@(.deleteMem ..) => s
  | _, _, s@(.assignNew ..) => s
  | _, _, s@(.require ..) => s
  | _, _, s@(.assert ..) => s
  | _, _, s@(.revert) => s
  | _, _, s@(.assumeFalse) => s
  | _, _, s@(.tryCall ..) => s
  | _, _, s@(.pushOpAssign ..) => s
  | _, _, s@(.pushIncDec ..) => s
  | _, _, s@(.callReceiver ..) => s
  | _, _, s@(.callReceiverPush ..) => s
  | _, _, s@(.callRec ..) => s
  | _, _, s@(.revertData ..) => s
  | _, _, s@(.catchData ..) => s

/-- Inline every covered call of a sequence. -/
def Prog.inl : {Γ Γ' : Ctx} → Prog C Γ Γ' → Prog C Γ Γ'
  | _, _, .nil => .nil
  | _, _, .cons s P => .cons (Stmt.inl s) (Prog.inl P)
end

mutual
theorem Stmt.inl_runC : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → Stmt.runC (Stmt.inl s) = Stmt.runC s
  | _, _, .ite c thn els => by
    simp only [Stmt.inl, Stmt.runC]
    rw [Prog.inl_runC thn, Prog.inl_runC els]
    exact TRun.ite_congr (fun _ => rfl) _ _ _ _ _ _
  | _, _, .block body => by
    simp only [Stmt.inl, Stmt.runC]
    rw [Prog.inl_runC body]
    exact TRun.block_congr _ _ _
  | _, _, .loop a c body => by
    simp only [Stmt.inl, Stmt.runC]
    rw [Prog.inl_runC body]
    exact TRun.loop_congr (fun _ => rfl) _ _ _
  | _, _, .call f args ret body => by
    simp only [Stmt.inl]
    exact inlineCall_runC f args ret body
  | _, _, .assign ..
  | _, _, .rebind ..
  | _, _, .assignLocal ..
  | _, _, .declLocal ..
  | _, _, .declStorage ..
  | _, _, .opAssign ..
  | _, _, .incDec ..
  | _, _, .assignIncDec ..
  | _, _, .assignLocalPush ..
  | _, _, .push ..
  | _, _, .pop ..
  | _, _, .transfer ..
  | _, _, .send ..
  | _, _, .declMem ..
  | _, _, .rebindMem ..
  | _, _, .assignFromMem ..
  | _, _, .assignMem ..
  | _, _, .delete ..
  | _, _, .deleteMem ..
  | _, _, .assignNew ..
  | _, _, .require ..
  | _, _, .assert ..
  | _, _, .revert
  | _, _, .assumeFalse
  | _, _, .tryCall ..
  | _, _, .pushOpAssign ..
  | _, _, .pushIncDec ..
  | _, _, .callReceiver ..
  | _, _, .callReceiverPush ..
  | _, _, .callRec ..
  | _, _, .revertData ..
  | _, _, .catchData .. => rfl

theorem Prog.inl_runC : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → Prog.runC (Prog.inl P) = Prog.runC P
  | _, _, .nil => rfl
  | _, _, .cons s P => by
    simp only [Prog.inl, Prog.runC]
    rw [Stmt.inl_runC s, Prog.inl_runC P]
end

theorem inl_preserves (Γ Γ' : Ctx) :
    Preserves (SameRun (C := C) (Γ := Γ) (Γ' := Γ')) (Prog.inl : Lowering.Pass C Γ Γ') :=
  fun P => (Prog.inl_runC P).symm

end Solidity.Optimizer.ConstFold
