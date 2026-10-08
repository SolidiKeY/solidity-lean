import Solidity.Calculus.Core.Sound
import Solidity.Calculus.Core.Notation

/-!
# Function contracts over the typed call run

`Calculus/Contracts.lean`'s `useContract` (KeY's `useOperationContract` at
the box, with the goals `"pre"` and `"post"`) on the scoped calculus: a
call proved by its callee's contract instead of its inlined body.

```
  "pre":   Γ ⟹ [ params := args ] requires
  "post":  Γ ⟹ [ params := args ] {havoc} ∀ T r. (ensures → [ res = r; ..ω ] φ)
  ───────────────────────────────────────────────────────────────────────────
           Γ ⟹ [ f(args); ..ω ] φ
```

**A contract** (`FunContract`) is a fact about the typed call run: from any
typed state of the callee's frame (its parameters `ps`) where `requires`
holds, the body, entered as the call enters it (`CallRet.enterT`: its
return variables at their defaults), does not panic and, if it ends, ends
where `ensures` holds of its frame (return variables and parameters).  Its
obligation (`FunContract.obligation`) is a scoped formula of the frame,
`requires → [ T r; body ] ensures`, proved like any other
(`FunContract.ofValid`).  The return variables are values of their types by
the typed state, so no `typed(r)` is owed.

**The frame is the syntax's**: a callee's body is read in its own frame
(`Stmt.call`'s `Prog C (rs ++ ps) Γf`), so it cannot touch the caller's
locals; its mutability (`Prog.within`, `Calculus/Core/Blocks.lean`) bounds
what it does to the rest (`Prog.trun_frame`, `TGFrame`): a `pure` or
`view` callee keeps storage and ledger, a `nonpayable` one only the heap,
the funds and the transaction, hence `{havoc}` for it alone
(`Fml.anonC`).  "post" reads the parameters at the arguments' values, so
the body may write its return variables only (`writesRets`, by `rfl`).

**The goals are scoped formulas** at the caller's context: the parameters
declared with the arguments (`Args.declsThen`), `requires` read on them by
a frame that drops the caller's locals (`Frames.drop`, which prints as
nothing), and `ensures` weakened to the caller's context with the frame on
top (`Fml.wkD`, first-order formulas; any other is read as `true`, which
only weakens "post").  Supported calls: no result (`deposit(4);`) and one
result (`y = f(x);`, `f(x);` of a function that returns one); a call that
leaves several or a memory return has the goal `false`.
-/

namespace Solidity.Core

open Solidity (Modality Mutability Srt)

variable {C : Contract}

/-! ## First-order formulas, weakened -/

section Wk

/-- A term read with more locals around it (`Thin`). -/
def Tm.wk {Γ Δ : Ctx} (h : Thin Γ Δ) : {s : Srt} → Tm C Γ s → Tm C Δ s
  | _, .pvV i => .pvV (i.wk h)
  | _, .pvP i => .pvP (i.wk h)
  | _, .pvS i => .pvS (i.wk h)
  | _, .pvI i => .pvI (i.wk h)
  | _, .netOf i a => .netOf (i.wk h) (a.wk h)
  | _, .app0 o => .app0 o
  | _, .app1 o ho a => .app1 o ho (a.wk h)
  | _, .app2 o a b => .app2 o (a.wk h) (b.wk h)
  | _, .app3 o a b c => .app3 o (a.wk h) (b.wk h) (c.wk h)

theorem State.thin_glob {Γ Δ : Ctx} (h : Thin Γ Δ) (σ : State C Δ) : (σ.thin h).glob = σ.glob :=
  rfl

theorem Tm.eval_wk {Γ Δ : Ctx} (h : Thin Γ Δ) (σ : State C Δ) :
    {s : Srt} → (t : Tm C Γ s) → (t.wk h).eval σ = t.eval (σ.thin h)
  | _, .pvV i => by simp only [Tm.wk, Tm.eval, State.thin, State.withEnv, Env.get_thin]
  | _, .pvP i => by simp only [Tm.wk, Tm.eval, aliasPath, State.thin, State.withEnv, Env.get_thin]
  | _, .pvS i => by
    simp only [Tm.wk, Tm.eval, State.thin, State.withEnv, Env.get_thin]
    rfl
  | _, .pvI i => by simp only [Tm.wk, Tm.eval, memRef, State.thin, State.withEnv, Env.get_thin]
  | _, .netOf i a => by
    simp only [Tm.wk, Tm.eval, Tm.eval_wk h σ a]
    simp only [State.thin, State.withEnv, Env.get_thin]
  | _, .app0 o => rfl
  | _, .app1 o _ a => by simp only [Tm.wk, Tm.eval, Tm.eval_wk h σ a]; rfl
  | _, .app2 o a b => by simp only [Tm.wk, Tm.eval, Tm.eval_wk h σ a, Tm.eval_wk h σ b]; rfl
  | _, .app3 o a b c => by
    simp only [Tm.wk, Tm.eval, Tm.eval_wk h σ a, Tm.eval_wk h σ b, Tm.eval_wk h σ c]; rfl

theorem Tm.denote_wk {Γ Δ : Ctx} (h : Thin Γ Δ) (σ : State C Δ) :
    {s : Srt} → (t : Tm C Γ s) → (t.wk h).denote σ = t.denote (σ.thin h)
  | _, .pvV i => by simp only [Tm.wk, Tm.denote, State.thin, State.withEnv, Env.get_thin]
  | _, .pvP i => by
    simp only [Tm.wk, Tm.denote, aliasPath, State.thin, State.withEnv, Env.get_thin]
  | _, .pvS i => by simp only [Tm.wk, Tm.denote, State.thin, State.withEnv, Env.get_thin]
  | _, .pvI i => rfl
  | _, .netOf i a => by
    simp only [Tm.wk, Tm.denote, Tm.denote_wk h σ a]
    simp only [State.thin, State.withEnv, Env.get_thin]
  | _, .app0 o => rfl
  | _, .app1 o _ a => by simp only [Tm.wk, Tm.denote, Tm.denote_wk h σ a]; rfl
  | _, .app2 o a b => by
    simp only [Tm.wk, Tm.denote, Tm.denote_wk h σ a, Tm.denote_wk h σ b, Tm.eval_wk h σ a,
      Tm.eval_wk h σ b]
    rfl
  | _, .app3 o a b c => by
    simp only [Tm.wk, Tm.denote, Tm.denote_wk h σ a, Tm.denote_wk h σ b, Tm.denote_wk h σ c]

/-- A first-order formula read with more locals around it; `none` on an
update, a modality, a `havoc`, a hidden binder or an anonymising update. -/
def Fml.wkFO {Γ Δ : Ctx} (h : Thin Γ Δ) : Fml C Γ → Option (Fml C Δ)
  | .tt => some .tt
  | .eq a b => some (.eq (a.wk h) (b.wk h))
  | .defined t => some (.defined (t.wk h))
  | .not φ => (φ.wkFO h).map .not
  | .and φ ψ => do pure (.and (← φ.wkFO h) (← ψ.wkFO h))
  | .imp φ ψ => do pure (.imp (← φ.wkFO h) (← ψ.wkFO h))
  | .all x p φ => (φ.wkFO h.keep).map (.all x p)
  | _ => none

/-- `Fml.wkFO`, `true` where it is `none`. -/
def Fml.wkD {Γ Δ : Ctx} (h : Thin Γ Δ) (φ : Fml C Γ) : Fml C Δ := (φ.wkFO h).getD .tt

theorem TState.thin_push {Γ Δ : Ctx} (h : Thin Γ Δ) (σ : TState C Δ) {t : LTy}
    (v : t.TDenote C σ.H) : (σ.push v).thin h.keep = (σ.thin h).push v := rfl

/-- **A weakened first-order formula reads as the formula on the thinned
state.** -/
theorem holds_wkFO {Γ Δ : Ctx} (h : Thin Γ Δ) : (φ : Fml C Γ) → {φ' : Fml C Δ} →
    φ.wkFO h = some φ' → ∀ σ : TState C Δ, (holds σ φ' ↔ holds (σ.thin h) φ)
  | .tt, _, e, σ => by cases e; exact Iff.rfl
  | .eq a b, _, e, σ => by
    cases e
    show Theory.StValue.Equiv _ _ ↔ Theory.StValue.Equiv _ _
    rw [Tm.denote_wk, Tm.denote_wk, TState.thin_erase]
  | .defined t, _, e, σ => by
    cases e
    show (∃ x, _ = _) ↔ (∃ x, _ = _)
    rw [Tm.eval_wk, TState.thin_erase]
  | .not φ, _, e, σ => by
    cases hφ : φ.wkFO h with
    | none => simp only [Fml.wkFO, hφ, Option.map_none, reduceCtorEq] at e
    | some φ' =>
      simp only [Fml.wkFO, hφ, Option.map_some, Option.some.injEq] at e
      cases e
      exact not_congr (holds_wkFO h φ hφ σ)
  | .and φ ψ, _, e, σ => by
    cases hφ : φ.wkFO h with
    | none => simp only [Fml.wkFO, hφ, Option.bind_none, Option.bind_eq_bind, reduceCtorEq] at e
    | some φ' =>
      cases hψ : ψ.wkFO h with
      | none =>
        simp only [Fml.wkFO, hφ, hψ, Option.bind_some, Option.bind_none, Option.bind_eq_bind,
          reduceCtorEq] at e
      | some ψ' =>
        simp only [Fml.wkFO, hφ, hψ, Option.bind_some, Option.bind_eq_bind, Option.pure_def,
          Option.some.injEq] at e
        cases e
        exact and_congr (holds_wkFO h φ hφ σ) (holds_wkFO h ψ hψ σ)
  | .imp φ ψ, _, e, σ => by
    cases hφ : φ.wkFO h with
    | none => simp only [Fml.wkFO, hφ, Option.bind_none, Option.bind_eq_bind, reduceCtorEq] at e
    | some φ' =>
      cases hψ : ψ.wkFO h with
      | none =>
        simp only [Fml.wkFO, hφ, hψ, Option.bind_some, Option.bind_none, Option.bind_eq_bind,
          reduceCtorEq] at e
      | some ψ' =>
        simp only [Fml.wkFO, hφ, hψ, Option.bind_some, Option.bind_eq_bind, Option.pure_def,
          Option.some.injEq] at e
        cases e
        exact imp_congr (holds_wkFO h φ hφ σ) (holds_wkFO h ψ hψ σ)
  | .all x p φ, _, e, σ => by
    cases hφ : φ.wkFO h.keep with
    | none => simp only [Fml.wkFO, hφ, Option.map_none, reduceCtorEq] at e
    | some φ' =>
      simp only [Fml.wkFO, hφ, Option.map_some, Option.some.injEq] at e
      cases e
      exact forall_congr' fun v => holds_wkFO h.keep φ hφ (σ.push (t := .val p) v)
  | .upd .., _, e, _ | .modal .., _, e, _ | .havoc _, _, e, _ | .bind .., _, e, _
  | .anon .., _, e, _ => by simp only [Fml.wkFO, reduceCtorEq] at e

/-- What a formula says on the thinned state, its weakening says (`true`
where it does not weaken). -/
theorem holds_wkD {Γ Δ : Ctx} (h : Thin Γ Δ) (φ : Fml C Γ) (σ : TState C Δ)
    (hφ : holds (σ.thin h) φ) : holds σ (φ.wkD h) := by
  unfold Fml.wkD
  cases e : φ.wkFO h with
  | none => trivial
  | some φ' => exact (holds_wkFO h φ e σ).2 hφ

end Wk

/-! ## Contracts -/

section Contract

variable {Γ rs Γ' ps Γf : Ctx}

/-- The return variables declared, then `rest`: the frame a call enters
(`CallRet.enterT`), a memory return a fresh default object. -/
def CallRet.declsThen {Δ : Ctx} (ret : CallRet Γ rs Γ') (rest : Prog C (rs ++ ps) Δ) :
    Prog C ps Δ :=
  CallRet.casesOn (motive := fun rs _ _ => Prog C (rs ++ ps) Δ → Prog C ps Δ) ret
    (fun rest => rest) (fun p r _ rest => .cons (.declLocal p r Option.none) rest)
    (fun bs rest => bs.declsThen rest)
    (fun R r hd hm rest => .cons (.declMem R r Option.none hd hm) rest)
    rest

/-- **A function contract** over the typed call run: from a typed state of
the callee's frame where `req` holds, its body, entered as the call enters
it (its return variables at their defaults), does not panic and, if it
ends, ends where `ens` holds of its frame. -/
def FunContract (ret : CallRet Γ rs Γ') (body : Prog C (rs ++ ps) Γf) (req : Fml C ps)
    (ens : Fml C (rs ++ ps)) : Prop :=
  ∀ σ : TState C ps, holds σ req →
    Modality.box.afterRunTR (holds · ens)
      ((Prog.trun (ret.enterT σ).st body).map fun o => o.st.drop body.ext)

/-- **The obligation of a contract**, solkey's planned
`requires -> [g(args)@C] ensures` for the callee's frame:
`requires → [ T r; body ] ensures`, the body's own locals popped. -/
def FunContract.obligation (ret : CallRet Γ rs Γ') (body : Prog C (rs ++ ps) Γf) (req : Fml C ps)
    (ens : Fml C (rs ++ ps)) : Fml C ps :=
  .imp req (.modal .box (ret.declsThen body) (.pop .block body.ext .nil) ens)

theorem CallRet.trunSt_declsThen {Δ : Ctx} (ret : CallRet Γ rs Γ') (hr : ret.noMem = true)
    (rest : Prog C (rs ++ ps) Δ) (σ : TState C ps) :
    Prog.trunSt σ (ret.declsThen rest) = Prog.trunSt (ret.enterT σ).st rest := by
  cases ret with
  | none => rfl
  | val p r res =>
    show Prog.trunSt σ (.cons (.declLocal p r Option.none) rest) = _
    rw [Prog.trunSt_cons, Stmt.trunSt_declLocal_none]
    rfl
  | rets bs => exact Binders.trunSt_declsThen σ bs rest
  | mem => cases hr

/-- A contract from a proof of its obligation. -/
theorem FunContract.ofValid {ret : CallRet Γ rs Γ'} {body : Prog C (rs ++ ps) Γf} {req : Fml C ps}
    {ens : Fml C (rs ++ ps)} (hr : ret.noMem = true)
    (h : ∀ σ : TState C ps, holds σ (FunContract.obligation ret body req ens)) :
    FunContract ret body req ens := by
  intro σ hreq
  have h' := (holds_modal_iff σ _ _ ens).1 (h σ hreq)
  rw [CallRet.trunSt_declsThen ret hr] at h'
  have e : ((Prog.trunSt (ret.enterT σ).st body).bind fun τ =>
      Frames.trunSt τ (.pop .block body.ext .nil)) =
      (Prog.trun (ret.enterT σ).st body).map fun o => o.st.drop body.ext := by
    simp only [Prog.trunSt, Frames.trunSt_pop, Frames.trunSt_nil]
    cases Prog.trun (ret.enterT σ).st body <;> rfl
  rwa [e] at h'

end Contract

/-! ## The rule -/

section Rule

variable {Γ ps rs Γ' Γf Γ₂ Γ₀ : Ctx}

/-- What "post" forgets of the contract's state: storage and ledger, for a
`nonpayable` callee (`{havoc}`); nothing for a `pure` or `view` one. -/
def Fml.anonC (μ : Mutability) (φ : Fml C Γ) : Fml C Γ :=
  match μ with
  | .nonpayable => .havoc φ
  | .pure | .view => φ

/-- **"pre"**: `[ params := args ] requires`, the caller's locals dropped
under the parameters (`Frames.drop`). -/
def Fml.callPre (args : Args C Γ ps) (req : Fml C ps) : Fml C Γ :=
  .modal .box (args.declsThen .nil) (.drop (Thin.atop ps Γ) .nil) req

/-- `res = r;`, where the call's result lands, read under the frame. -/
def CallRet.resultC {p : PrimTy} (res : Option (Idx Γ (.val p))) :
    Prog C (.val p :: (ps ++ Γ)) (.val p :: (ps ++ Γ)) :=
  match res with
  | Option.none => .nil
  | some j => .cons (.assignLocal (j.under ps).there (.simple (.local .here))) .nil

/-- **"post"**: `[ params := args ] {havoc} ∀ T r. (ensures → [ res = r; ..ω ] φ)`,
`ensures` weakened to the caller's context (`Fml.wkD`), the frame popped
before the rest; `false` for a call that leaves several results or a
memory return. -/
def Fml.callPost (μ : Mutability) (args : Args C Γ ps) : {rs Γ' : Ctx} → CallRet Γ rs Γ' →
    Fml C (rs ++ ps) → Prog C Γ' Γ₂ → Frames C Γ₂ Γ₀ → Fml C Γ₀ → Fml C Γ
  | _, _, .none, ens, ω, κ, φ => .modal .box (args.declsThen .nil) .nil
    (Fml.anonC μ (.imp (ens.wkD (Thin.atop ps Γ))
      (.modal .box .nil (.pop .block (Ext.append Γ ps) (.seq ω κ)) φ)))
  | _, _, .val p r res, ens, ω, κ, φ => .modal .box (args.declsThen .nil) .nil
    (Fml.anonC μ (.all r p (.imp (ens.wkD (Thin.atop (.val p :: ps) Γ))
      (.modal .box (CallRet.resultC res) (.pop .block (Ext.append Γ (.val p :: ps)) (.seq ω κ))
        φ))))
  | _, _, .rets _, _, _, _, _ => .ff
  | _, _, .mem .., _, _, _, _ => .ff

/-- The body writes its return variables only, so "post" reads the
parameters at the arguments' values. -/
def writesRets (rs : Ctx) {Δ Δ' : Ctx} (body : Prog C Δ Δ') : Bool :=
  (Prog.writesAt 0 body).all fun w => decide (w.2 < rs.length)

end Rule

/-! ## Soundness -/

section Sound

variable {Γ ps rs Γ' Γf Γ₂ Γ₀ : Ctx}

theorem TEnv.thin_atop_append {H : HTy} : (ps : Ctx) → (a : TEnv C H ps) → (e : TEnv C H Γ) →
    TEnv.thin (Thin.atop ps Γ) (TEnv.append ps a e) = a
  | [], _, e => by
    induction Γ with
    | nil => rfl
    | cons t Γ ih => exact ih e.2
  | _ :: ps, a, e => congrArg (Prod.mk a.1) (TEnv.thin_atop_append ps a.2 e)

/-- A typed state is its parts, the heap and the locals up to the heap
typing. -/
theorem TState.ext' {Γ : Ctx} {σ τ : TState C Γ} (hst : σ.storage = τ.storage) (hH : σ.H = τ.H)
    (hheap : HEq σ.heap τ.heap) (henv : HEq σ.env τ.env) (hnet : σ.net = τ.net)
    (hsb : σ.selfBalance = τ.selfBalance) (htx : σ.tx = τ.tx) : σ = τ := by
  obtain ⟨st, H, heap, env, net, sb, tx⟩ := σ
  obtain ⟨st', H', heap', env', net', sb', tx'⟩ := τ
  dsimp only at hst hH hheap henv hnet hsb htx
  subst hst hH hnet hsb htx
  cases hheap
  cases henv
  rfl

/-- The arguments read, then `X` on the parameters declared. -/
theorem holds_declsThen {args : Args C Γ ps} {X : Fml C (ps ++ Γ)} {σ : TState C Γ}
    (h : holds σ (.modal .box (args.declsThen .nil) .nil X)) :
    (∀ e, args.evalT σ = .error e → e ≠ .panic) ∧
      ∀ a, args.evalT σ = .ok a → holds (σ.withEnv (TEnv.append ps a σ.env)) X := by
  rw [holds_modal_iff, Args.trunSt_declsThen] at h
  refine ⟨fun e he => ?_, fun a ha => ?_⟩
  · rw [he] at h
    exact fun hp => h.2 (by rw [hp]; rfl)
  · rw [ha] at h
    exact h.1

/-- "pre": the arguments read, `requires` of the parameters. -/
theorem holds_callPre {args : Args C Γ ps} {req : Fml C ps} {σ : TState C Γ}
    (h : holds σ (Fml.callPre args req)) :
    (∀ e, args.evalT σ = .error e → e ≠ .panic) ∧
      ∀ a, args.evalT σ = .ok a → holds (σ.withEnv a) req := by
  unfold Fml.callPre at h
  rw [holds_modal_iff, Args.trunSt_declsThen] at h
  refine ⟨fun e he => ?_, fun a ha => ?_⟩
  · rw [he] at h
    exact fun hp => h.2 (by rw [hp]; rfl)
  · rw [ha] at h
    have h1 := h.1
    simp only [Except.bind, Prog.trunSt_nil, Frames.trunSt_drop, Frames.trunSt_nil] at h1
    rwa [show (σ.withEnv (TEnv.append ps a σ.env)).thin (Thin.atop ps Γ) = σ.withEnv a by
      simp only [TState.thin, TState.withEnv, TEnv.thin_atop_append]] at h1

/-- A call by its contract, one result. -/
theorem holds_callVal {μ : Mutability} {f : Name} {args : Args C Γ ps} {p : PrimTy} {r : Var}
    {res : Option (Idx Γ (.val p))} {body : Prog C ([.val p] ++ ps) Γf} {ω : Prog C Γ Γ₂}
    {κ : Frames C Γ₂ Γ₀} {φ : Fml C Γ₀} {req : Fml C ps} {ens : Fml C ([.val p] ++ ps)}
    (hc : FunContract (.val p r res) body req ens) (hμ : Prog.within μ body = true)
    (hw : writesRets [.val p] body = true) {σ : TState C Γ}
    (hpre : holds σ (Fml.callPre args req))
    (hpost : holds σ (Fml.callPost μ args (.val p r res) ens ω κ φ)) :
    holds σ (.modal .box (.cons (.call f args (.val p r res) body) ω) κ φ) := by
  obtain ⟨hpe, hpa⟩ := holds_callPre hpre
  obtain ⟨-, hqa⟩ := holds_declsThen hpost
  rw [holds_modal_iff, Prog.trunSt_cons]
  show Modality.box.afterRunTR _ ((((TRun.call args (.val p r res) body.ext body.trunR σ).map
    (·.st)).bind _).bind _)
  rw [TRun.call_eq]
  cases hA : args.evalT σ with
  | error e => exact ⟨trivial, fun hp => hpe e hA (by cases hp; rfl)⟩
  | ok a =>
    have hct := hc _ (hpa a hA)
    have hX := hqa a hA
    show Modality.box.afterRunTR _ (((Except.map (·.st) (TRun.callFrom (.val p r res) body.ext
      body.trunR σ ((CallRet.val p r res).enterT (σ.withEnv a)))).bind _).bind _)
    unfold TRun.callFrom
    unfold FunContract at hc
    cases hB : body.trunR ((CallRet.val p r res).enterT (σ.withEnv a)).st with
    | error e =>
      rw [show Prog.trun _ body = body.trunR _ from rfl, hB] at hct
      exact ⟨trivial, fun hp => hct.2 (by cases hp; rfl)⟩
    | ok o =>
      rw [show Prog.trun _ body = body.trunR _ from rfl, hB] at hct
      have hens : holds (o.st.drop body.ext) ens := hct.1
      obtain ⟨hg, hag⟩ := Prog.trun_frame body hμ 0 hB
      obtain ⟨⟨st, H', heap, env, net, sb, tx⟩, ext⟩ := o
      obtain ⟨hH, hheap, hsb, htx, hkeep⟩ := hg
      dsimp only [CallRet.enterT, TState.push, TState.withEnv] at hH hheap hsb htx hkeep hag hens
      subst hH
      cases hheap
      -- the parameters keep the arguments' values
      have hps : (TEnv.drop body.ext env).2 = a := by
        apply TEnv.ext
        intro t i
        have hni : (t, (Idx.there (u := LTy.val p) i).toNat - 0) ∉ Prog.writesAt 0 body := by
          intro hm
          have := List.all_eq_true.1 hw _ hm
          simp only [decide_eq_true_eq, List.length_cons, List.length_nil, Nat.zero_add,
            Nat.sub_zero, Idx.toNat] at this
          omega
        exact eq_of_heq (hag t (.there i) (Nat.zero_le _) hni)
      -- "post", the callee's state and result read in
      have hX' : holds ((σ.withEnv (TEnv.append ps a σ.env)).havoc st net)
          (.all r p (.imp (ens.wkD (Thin.atop (.val p :: ps) Γ))
            (.modal .box (CallRet.resultC res) (.pop .block (Ext.append Γ (.val p :: ps))
              (.seq ω κ)) φ))) := by
        cases μ with
        | nonpayable => exact hX st net
        | pure =>
          obtain ⟨h1, h2⟩ := hkeep (by decide)
          subst h1 h2
          exact hX
        | view =>
          obtain ⟨h1, h2⟩ := hkeep (by decide)
          subst h1 h2
          exact hX
      have hens' : holds (((σ.withEnv (TEnv.append ps a σ.env)).havoc st net).push
          (t := .val p) (TEnv.drop body.ext env).1) (ens.wkD (Thin.atop (.val p :: ps) Γ)) := by
        apply holds_wkD
        have hst : TState.drop body.ext
            ⟨st, σ.H, σ.heap, env, net, sb, tx⟩ = TState.thin (Thin.atop (.val p :: ps) Γ)
              (((σ.withEnv (TEnv.append ps a σ.env)).havoc st net).push (t := .val p)
                (TEnv.drop body.ext env).1) := by
          refine TState.ext' rfl rfl HEq.rfl (heq_of_eq ?_) rfl hsb htx
          show _ = ((TEnv.drop body.ext env).1,
            TEnv.thin (Thin.atop ps Γ) (TEnv.append ps a σ.env))
          rw [TEnv.thin_atop_append, ← hps]
          rfl
        exact hst ▸ hens
      have hM := hX' (TEnv.drop body.ext env).1 hens'
      rw [holds_modal_iff] at hM
      dsimp only [bind, Except.bind, Except.map, pure, Except.pure]
      rw [TEnv.wk_self]
      cases res with
      | none =>
        have hT : TState.drop (Ext.append Γ (.val p :: ps))
            (((σ.withEnv (TEnv.append ps a σ.env)).havoc st net).push (t := .val p)
              (TEnv.drop body.ext env).1) =
            (⟨st, σ.H, σ.heap, env, net, sb, tx⟩ : TState C Γf).withEnv
              (CallRet.leaveT σ.env (CallRet.val p r Option.none)
                (TEnv.take [LTy.val p] (TEnv.drop body.ext env))) :=
          TState.ext' rfl rfl HEq.rfl (heq_of_eq (TEnv.drop_append ps a σ.env)) rfl hsb.symm
            htx.symm
        simp only [CallRet.resultC, Prog.trunSt_nil, Except.bind, Frames.trunSt_pop,
          Frames.trunSt_seq, hT] at hM
        exact hM
      | some j =>
        have hT : TState.drop (Ext.append Γ (.val p :: ps))
            ((((σ.withEnv (TEnv.append ps a σ.env)).havoc st net).push (t := .val p)
              (TEnv.drop body.ext env).1).setLocal (j.under ps).there
                (TEnv.drop body.ext env).1) =
            (⟨st, σ.H, σ.heap, env, net, sb, tx⟩ : TState C Γf).withEnv
              (CallRet.leaveT σ.env (CallRet.val p r (some j))
                (TEnv.take [LTy.val p] (TEnv.drop body.ext env))) := by
          refine TState.ext' rfl rfl HEq.rfl (heq_of_eq ?_) rfl hsb.symm htx.symm
          show TEnv.drop (Ext.append Γ (.val p :: ps)) (TEnv.set (j.under (.val p :: ps)) _ _) = _
          rw [TEnv.drop_set_under]
          show TEnv.set j _ (TEnv.drop (Ext.append Γ ps) (TEnv.append ps a σ.env)) = _
          rw [TEnv.drop_append]
          rfl
        have hs : Prog.trunSt (((σ.withEnv (TEnv.append ps a σ.env)).havoc st net).push
            (t := .val p) (TEnv.drop body.ext env).1) (CallRet.resultC (some j)) =
            .ok ((((σ.withEnv (TEnv.append ps a σ.env)).havoc st net).push (t := .val p)
              (TEnv.drop body.ext env).1).setLocal (j.under ps).there
                (TEnv.drop body.ext env).1) := rfl
        simp only [hs, Except.bind, Frames.trunSt_pop, Frames.trunSt_seq, hT] at hM
        exact hM

/-- A call by its contract, no result. -/
theorem holds_callNone {μ : Mutability} {f : Name} {args : Args C Γ ps}
    {body : Prog C ([] ++ ps) Γf} {ω : Prog C Γ Γ₂} {κ : Frames C Γ₂ Γ₀} {φ : Fml C Γ₀}
    {req : Fml C ps} {ens : Fml C ([] ++ ps)}
    (hc : FunContract (CallRet.none (Γ := Γ)) body req ens) (hμ : Prog.within μ body = true)
    (hw : writesRets [] body = true) {σ : TState C Γ}
    (hpre : holds σ (Fml.callPre args req))
    (hpost : holds σ (Fml.callPost μ args .none ens ω κ φ)) :
    holds σ (.modal .box (.cons (.call f args .none body) ω) κ φ) := by
  obtain ⟨hpe, hpa⟩ := holds_callPre hpre
  obtain ⟨-, hqa⟩ := holds_declsThen hpost
  rw [holds_modal_iff, Prog.trunSt_cons]
  show Modality.box.afterRunTR _ ((((TRun.call args .none body.ext body.trunR σ).map
    (·.st)).bind _).bind _)
  rw [TRun.call_eq]
  cases hA : args.evalT σ with
  | error e => exact ⟨trivial, fun hp => hpe e hA (by cases hp; rfl)⟩
  | ok a =>
    have hct := hc _ (hpa a hA)
    have hX := hqa a hA
    show Modality.box.afterRunTR _ (((Except.map (·.st) (TRun.callFrom .none body.ext
      body.trunR σ ((CallRet.none (Γ := Γ)).enterT (σ.withEnv a)))).bind _).bind _)
    unfold TRun.callFrom
    unfold FunContract at hc
    cases hB : body.trunR ((CallRet.none (Γ := Γ)).enterT (σ.withEnv a)).st with
    | error e =>
      rw [show Prog.trun _ body = body.trunR _ from rfl, hB] at hct
      exact ⟨trivial, fun hp => hct.2 (by cases hp; rfl)⟩
    | ok o =>
      rw [show Prog.trun _ body = body.trunR _ from rfl, hB] at hct
      have hens : holds (o.st.drop body.ext) ens := hct.1
      obtain ⟨hg, hag⟩ := Prog.trun_frame body hμ 0 hB
      obtain ⟨⟨st, H', heap, env, net, sb, tx⟩, ext⟩ := o
      obtain ⟨hH, hheap, hsb, htx, hkeep⟩ := hg
      dsimp only [CallRet.enterT, TState.withEnv] at hH hheap hsb htx hkeep hag hens
      subst hH
      cases hheap
      -- the parameters keep the arguments' values
      have hps : TEnv.drop body.ext env = a := by
        apply TEnv.ext
        intro t i
        have hni : (t, i.toNat - 0) ∉ Prog.writesAt 0 body := by
          intro hm
          have := List.all_eq_true.1 hw _ hm
          simp only [decide_eq_true_eq, List.length_nil, Nat.not_lt_zero] at this
        exact eq_of_heq (hag t i (Nat.zero_le _) hni)
      have hX' : holds ((σ.withEnv (TEnv.append ps a σ.env)).havoc st net)
          (.imp (ens.wkD (Thin.atop ps Γ))
            (.modal .box .nil (.pop .block (Ext.append Γ ps) (.seq ω κ)) φ)) := by
        cases μ with
        | nonpayable => exact hX st net
        | pure =>
          obtain ⟨h1, h2⟩ := hkeep (by decide)
          subst h1 h2
          exact hX
        | view =>
          obtain ⟨h1, h2⟩ := hkeep (by decide)
          subst h1 h2
          exact hX
      have hens' : holds ((σ.withEnv (TEnv.append ps a σ.env)).havoc st net)
          (ens.wkD (Thin.atop ps Γ)) := by
        apply holds_wkD
        have hst : TState.drop body.ext
            ⟨st, σ.H, σ.heap, env, net, sb, tx⟩ = TState.thin (Thin.atop ps Γ)
              ((σ.withEnv (TEnv.append ps a σ.env)).havoc st net) := by
          refine TState.ext' rfl rfl HEq.rfl (heq_of_eq ?_) rfl hsb htx
          show _ = TEnv.thin (Thin.atop ps Γ) (TEnv.append ps a σ.env)
          rw [TEnv.thin_atop_append, ← hps]
          rfl
        exact hst ▸ hens
      have hM := hX' hens'
      rw [holds_modal_iff] at hM
      dsimp only [bind, Except.bind, Except.map, pure, Except.pure]
      rw [TEnv.wk_self]
      have hT : TState.drop (Ext.append Γ ps)
          ((σ.withEnv (TEnv.append ps a σ.env)).havoc st net) =
          (⟨st, σ.H, σ.heap, env, net, sb, tx⟩ : TState C Γf).withEnv
            (CallRet.leaveT σ.env (CallRet.none (Γ := Γ))
              (TEnv.take [] (TEnv.drop body.ext env))) :=
        TState.ext' rfl rfl HEq.rfl (heq_of_eq (TEnv.drop_append ps a σ.env)) rfl hsb.symm
          htx.symm
      simp only [Prog.trunSt_nil, Except.bind, Frames.trunSt_pop, Frames.trunSt_seq, hT] at hM
      exact hM

/-- **A call by its callee's contract is sound** (`useContract`, at the
state): "pre" and "post" there give the call and the rest. -/
theorem holds_callContract {μ : Mutability} {f : Name} {args : Args C Γ ps}
    {ret : CallRet Γ rs Γ'} {body : Prog C (rs ++ ps) Γf} {ω : Prog C Γ' Γ₂}
    {κ : Frames C Γ₂ Γ₀} {φ : Fml C Γ₀} {req : Fml C ps} {ens : Fml C (rs ++ ps)}
    (hc : FunContract ret body req ens) (hμ : Prog.within μ body = true)
    (hw : writesRets rs body = true) {σ : TState C Γ}
    (hpre : holds σ (Fml.callPre args req))
    (hpost : holds σ (Fml.callPost μ args ret ens ω κ φ)) :
    holds σ (.modal .box (.cons (.call f args ret body) ω) κ φ) := by
  cases ret with
  | none => exact holds_callNone hc hμ hw hpre hpost
  | val p r res => exact holds_callVal hc hμ hw hpre hpost
  | rets => exact (hpost trivial).elim
  | mem => exact (hpost trivial).elim

end Sound

/-! ## The rule on sequents -/

section RuleSeq

variable {Γ ps rs Γ' Γf Γ₂ Γ₀ : Ctx}

/-- A formula of the parameters closed by `∀` over each, the first
parameter outermost, named as the call names them. -/
def Fml.allArgs : {ps : Ctx} → Args C Γ ps → Fml C ps → Fml C []
  | _, .nil, φ => φ
  | _, .snoc as p x _, φ => Fml.allArgs as (.all x p φ)

theorem holds_allArgs : {ps : Ctx} → (args : Args C Γ ps) → {φ : Fml C ps} →
    Valid (Fml.allArgs args φ) → ∀ σ : TState C ps, holds σ φ
  | _, .nil, _, h, σ => h σ
  | _, .snoc as p x _, φ, h, σ =>
    holds_allArgs as (φ := .all x p φ) h (σ.withEnv σ.env.2) σ.env.1

/-- A contract from a proof of its obligation, the parameters bound by `∀`
(`Fml.allArgs`), as `sol_symex; sol_close` prove it. -/
theorem FunContract.ofValid' {args : Args C Γ ps} {ret : CallRet Γ rs Γ'}
    {body : Prog C (rs ++ ps) Γf} {req : Fml C ps} {ens : Fml C (rs ++ ps)}
    (h : Valid (Fml.allArgs args (FunContract.obligation ret body req ens)))
    (hr : ret.noMem = true := by rfl) : FunContract ret body req ens :=
  FunContract.ofValid hr (holds_allArgs args h)

/-- **`useContract`** of a contract, its goals proved valid. -/
theorem useContractC_of_valid {H : Hyps C [] Γ} {μ : Mutability} {f : Name}
    {args : Args C Γ ps} {ret : CallRet Γ rs Γ'} {body : Prog C (rs ++ ps) Γf}
    {ω : Prog C Γ' Γ₂} {κ : Frames C Γ₂ Γ₀} {φ : Fml C Γ₀} {req : Fml C ps}
    {ens : Fml C (rs ++ ps)} (hc : FunContract ret body req ens)
    («pre» : Valid (H.wrap (Fml.callPre args req)))
    («post» : Valid (H.wrap (Fml.callPost μ args ret ens ω κ φ)))
    (hμ : Prog.within μ body = true := by rfl) (hw : writesRets rs body = true := by rfl) :
    Valid (H.wrap (.modal .box (.cons (.call f args ret body) ω) κ φ)) :=
  fun σ => H.wrap_and (fun _ h₁ h₂ => holds_callContract hc hμ hw h₁ h₂) σ («pre» σ) («post» σ)

/-- **`useContract`** with its goals proved valid, the contract by its
obligation (`FunContract.ofValid'`): what goals closed by
`sol_symex; sol_close` give. -/
theorem useContract_of_valid {H : Hyps C [] Γ} {μ : Mutability} {f : Name}
    {args : Args C Γ ps} {ret : CallRet Γ rs Γ'} {body : Prog C (rs ++ ps) Γf}
    {ω : Prog C Γ' Γ₂} {κ : Frames C Γ₂ Γ₀} {φ : Fml C Γ₀} {req : Fml C ps}
    {ens : Fml C (rs ++ ps)}
    (hc : Valid (Fml.allArgs args (FunContract.obligation ret body req ens)))
    («pre» : Valid (H.wrap (Fml.callPre args req)))
    («post» : Valid (H.wrap (Fml.callPost μ args ret ens ω κ φ)))
    (hμ : Prog.within μ body = true := by rfl) (hw : writesRets rs body = true := by rfl)
    (hr : ret.noMem = true := by rfl) :
    Valid (H.wrap (.modal .box (.cons (.call f args ret body) ω) κ φ)) :=
  useContractC_of_valid (FunContract.ofValid' hc hr) «pre» «post» hμ hw

/-- **`useContract`**: a call proved by its callee's contract, KeY's
`useOperationContract` at the box, with the goals `"pre"` and `"post"`
derived (`⊢`). -/
theorem useContract {R : RuleSet} {H : Hyps C [] Γ} {μ : Mutability} {f : Name}
    {args : Args C Γ ps} {ret : CallRet Γ rs Γ'} {body : Prog C (rs ++ ps) Γf}
    {ω : Prog C Γ' Γ₂} {κ : Frames C Γ₂ Γ₀} {φ : Fml C Γ₀} {req : Fml C ps}
    {ens : Fml C (rs ++ ps)}
    (hc : Valid (Fml.allArgs args (FunContract.obligation ret body req ens)))
    («pre» : Proves C R [] H (Fml.callPre args req))
    («post» : Proves C R [] H (Fml.callPost μ args ret ens ω κ φ))
    (hμ : Prog.within μ body = true := by rfl) (hw : writesRets rs body = true := by rfl)
    (hr : ret.noMem = true := by rfl) :
    Valid (H.wrap (.modal .box (.cons (.call f args ret body) ω) κ φ)) :=
  useContractC_of_valid (FunContract.ofValid' hc hr) «pre».sound «post».sound hμ hw

end RuleSeq

/-! ## Writing a contract: `cdlIn[C | uint x, uint r]{ φ }`

A contract's `requires` and `ensures` are formulas of the callee's frame,
not closed ones: `cdlIn[C | uint se1, uint se2]{ se2 == se1 + 1 }` reads `φ`
as `cdl[C]{ φ }` does, at the locals listed (outermost first: the
parameters in order, then the return variables), none of them bound by it. -/

section Notation

variable [FreshNames] (C : Contract)

/-- The named context of the locals `ns`, listed outermost first. -/
def ctxOfLocals (ns : List (String × PrimTy)) : NCtx :=
  ns.reverse.map fun (x, p) => (Var.ofName x, LTy.val p)

/-- A formula read at the locals `ns` (`cdlIn`). -/
def elabFmlAtC (ns : List (String × PrimTy)) (φ : RawFml) :
    Except String (Fml C (ctxOfLocals ns).ctx) :=
  let scope : ECtx := ns.reverse.map fun (x, p) => (x, LocalTy.val p)
  let taken := (ns.map fun (x, _) => (Var.ofName x).idx).filter (· > 0)
  ((elabFmlC C taken false φ (ctxOfLocals ns)).run { funs := C.funs }).run' (scope, 1)

end Notation

/-- A local of `cdlIn`: its type and name. -/
declare_syntax_cat cdl_local
syntax ident ident : cdl_local

/-- `cdlIn[C | uint x, uint r]{ φ }`: `φ` read at the locals listed,
outermost first. -/
syntax "cdlIn[" term " | " cdl_local,* "]{ " dl_fml " }" : term

/-- `cdlIn![uint x, uint r]{ φ }`: `cdlIn[C | …]{ φ }` for the file's
`InContract` contract. -/
syntax "cdlIn![" cdl_local,* "]{ " dl_fml " }" : term

open Lean Elab Term Meta in
elab_rules : term
  | `(cdlIn[ $c | $ls,* ]{ $φ:dl_fml }) => do
    let holes := fmlHoles φ
    unless holes.isEmpty do throwError "cdlIn: a Lean formula cannot stand in a contract's formula"
    let items ← ls.getElems.mapM fun l => match l with
      | `(cdl_local| $t:ident $x:ident) => do
        let p : Lean.Term ← match t.getId.toString with
          | "uint" | "address" => `(PrimTy.uint)
          | "int" => `(PrimTy.int)
          | "bool" => `(PrimTy.bool)
          | s => throwErrorAt t
            "cdlIn: a local of a contract is a uint, int, address or bool, not {s}"
        `(($(quote x.getId.toString), $p))
      | _ => throwUnsupportedSyntax
    let ns ← `([$items,*])
    let raw ← liftMacroM (expandFml { holes } φ)
    elabAgainstQ c fun q => `((elabFmlAtC $c $ns $raw).map (Core.Fml.quote $q))

macro_rules
  | `(cdlIn![ $ls,* ]{ $φ:dl_fml }) => `(cdlIn[InContract.contract | $ls,* ]{ $φ })

/-! ## The tactic -/

namespace Contract

open Lean Elab Tactic Meta

/-- The context `H` of a formula's head, up to its first modality: its
`∀`s, hidden binders, preconditions, updates and `havoc`s, outermost first;
the context it ends in and the rest. -/
partial def peel (C H Γ φ : Expr) : MetaM (Expr × Expr × Expr) := do
  let φ ← whnfR (← instantiateMVars φ)
  let nil := mkApp (mkConst ``List.nil [0]) (mkConst ``LTy)
  let a := φ.getAppArgs
  let cons (t Γ : Expr) := mkApp3 (mkConst ``List.cons [0]) (mkConst ``LTy) t Γ
  if φ.isAppOfArity ``Fml.all 5 then
    peel C (mkAppN (mkConst ``Hyps.all) #[C, nil, Γ, H, a[2]!, a[3]!])
      (cons (mkApp (mkConst ``LTy.val) a[3]!) Γ) a[4]!
  else if φ.isAppOfArity ``Fml.imp 4 then
    peel C (mkAppN (mkConst ``Hyps.pre) #[C, nil, Γ, H, a[2]!]) Γ a[3]!
  else if φ.isAppOfArity ``Fml.bind 6 then
    peel C (mkAppN (mkConst ``Hyps.bind) #[C, nil, Γ, H, a[2]!, a[3]!, a[4]!]) (cons a[4]! Γ) a[5]!
  else if φ.isAppOfArity ``Fml.upd 6 then
    peel C (mkAppN (mkConst ``Hyps.upd) #[C, nil, Γ, a[2]!, H, a[3]!, a[4]!]) a[2]! a[5]!
  else if φ.isAppOfArity ``Fml.havoc 3 then
    peel C (mkAppN (mkConst ``Hyps.havoc) #[C, nil, Γ, H]) Γ a[2]!
  else return (H, Γ, φ)

/-- `core_contract` on `⊨ φ`: the call at the head of `φ`'s first box,
behind its context, proved by `rule` (`useContract_of_valid`,
`useContract`), the goals `hc`, `pre` and `post` left. -/
def run (rule : Lean.Name) (μ req ens : Syntax) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← g.getType))
  let_expr Core.Valid C φ := ty | throwError "core_contract: expected a goal `⊨ φ`, scoped"
  let nil := mkApp (mkConst ``List.nil [0]) (mkConst ``LTy)
  let (H, _, χ) ← peel C (mkApp2 (mkConst ``Hyps.nil) C nil) nil φ
  unless χ.isAppOf ``Fml.modal do
    throwError "core_contract: no modality at the head of the formula{indentExpr χ}"
  let HS ← Term.exprToSyntax H
  let r := mkIdent rule
  let tac ← if rule == ``useContract then
      `(tactic| refine $r (R := RuleSet.all) (H := $HS) (μ := $(⟨μ⟩)) (req := $(⟨req⟩))
        (ens := $(⟨ens⟩)) ?hc ?pre ?post (by rfl) (by rfl) (by rfl))
    else
      `(tactic| refine $r (H := $HS) (μ := $(⟨μ⟩)) (req := $(⟨req⟩)) (ens := $(⟨ens⟩))
        ?hc ?pre ?post (by rfl) (by rfl) (by rfl))
  evalTactic tac

end Contract

/-- `core_contract μ req ens`: a call by its callee's contract
(`useContract_of_valid`), its goals `hc` (the contract's obligation,
`FunContract.ofValid'`), `pre` and `post` left as `⊨`. -/
syntax "core_contract " term:max ppSpace term:max ppSpace term:max : tactic

/-- `core_contract_walk μ req ens`: the same, its goals `pre` and `post`
left as sequents (`useContract`), for a walk. -/
syntax "core_contract_walk " term:max ppSpace term:max ppSpace term:max : tactic

elab_rules : tactic
  | `(tactic| core_contract $μ $req $ens) =>
    Contract.run ``useContract_of_valid μ req ens
  | `(tactic| core_contract_walk $μ $req $ens) =>
    Contract.run ``useContract μ req ens

end Solidity.Core
