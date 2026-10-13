import Solidity.Calculus.Sound
import Solidity.Calculus.Notation
import Solidity.Calculus.Close

/-!
# Function contracts over the typed call run

Today's `Calculus/Contracts` `useContract` (deleted at W4 `calc-del`) (KeY's `useOperationContract` at
the box, with the goals `"pre"` and `"post"`) on the scoped calculus: a
call proved by its callee's contract instead of its inlined body.

```
  "pre":   Γ ⟹ [ params := args ] requires
  "post":  Γ ⟹ [ params := args ] {old := storage ‖ oldNet := net} {havoc}
             ∀ T r. (ensures → [ res = r; ..ω ] φ)
  ───────────────────────────────────────────────────────────────────────────
           Γ ⟹ [ f(args); ..ω ] φ
```

**A contract** (`FunContract`) is a fact about the typed call run: from any
typed state of the callee's frame (its parameters `ps`) where `requires`
holds, the body, entered as the call enters it (`CallRet.enterT`: its
return variables at their defaults, a memory return a fresh default
object), does not panic and, if it ends, ends where `ensures` holds of its
frame: the return variables, the snapshots `old` and `oldNet` of the
storage and the ledger it was entered with (`\old`, `Olds`), and the
parameters.  Its obligation (`FunContract.obligation`) is a scoped formula
of the frame, `requires → {old := storage ‖ oldNet := net} [ T r; { body } ]
ensures`, the body read under the snapshots as a block (`thinOlds`), proved
like any other (`FunContract.ofValid`).  The return variables are values of
their types by the typed state, so no `typed(r)` is owed.

**The frame is the syntax's**: a callee's body is read in its own frame
(`Stmt.call`'s `Prog C (rs ++ ps) Γf`), so it cannot touch the caller's
locals; its mutability (`Prog.within`, `Calculus/Blocks.lean`) bounds
what it does to the rest (`Prog.run_frame`, `TGFrame`): a `pure` or
`view` callee keeps storage and ledger, a `nonpayable` one only the heap,
the funds and the transaction, hence `{havoc}` for it alone
(`Fml.anonC`).  "post" reads the parameters at the arguments' values, so
the body may write its value return variables only (`writesRets`,
`CallRet.nVals`, by `rfl`).

**The goals are scoped formulas** at the caller's context: the parameters
declared with the arguments (`Args.declsThen`), `requires` read on them by
a frame that drops the caller's locals (`Frames.drop`, which prints as
nothing), the snapshots declared by an update (`snapOld`), and `ensures`
weakened to the caller's context with the frame on top (`Fml.wkD`,
first-order formulas; any other is read as `true`, which only weakens
"post").  What "post" says past `{havoc}` is by what the call leaves
(`Fml.callResult`): no result (`deposit(4);`), one (`y = f(x);`), several,
left in the caller's context for the tuple's targets (`∀` over each, the
frame dropped from under them), or a memory return (`[ T memory r; ]`, the
fresh object the callee is entered with, which a callee within a
mutability leaves as it is).
-/

namespace Solidity

open Solidity (Modality Mutability Srt)

variable {C : Contract}

/-! ## First-order formulas, weakened -/

section Wk

/-- A term read with more locals around it (`Thin`). -/
def Tm.wk {Γ Δ : Ctx} (h : Thin Γ Δ) : {s : Srt} → Tm C Γ s → Tm C Δ s
  | _, t => Tm.casesOn (motive := fun s _ => Tm C Δ s) t
    (pvV := fun i => .pvV (i.wk h)) (pvP := fun i => .pvP (i.wk h))
    (pvS := fun i => .pvS (i.wk h)) (pvI := fun i => .pvI (i.wk h))
    (netOf := fun i a => .netOf (i.wk h) (Tm.wk h a)) (app0 := fun o => .app0 o)
    (app1 := fun o a => .app1 o (Tm.wk h a))
    (app2 := fun o a b => .app2 o (Tm.wk h a) (Tm.wk h b))
    (app3 := fun o a b c => .app3 o (Tm.wk h a) (Tm.wk h b) (Tm.wk h c))
    (pvZ := fun i => .pvZ (i.wk h))
  termination_by structural _ t => t

/-! `Tm.wk`'s equations, one a constructor: its own equation unfolds to
the `casesOn`, which `simp` would unfold again inside it. -/

section WkEqns

variable {Γ Δ : Ctx} (h : Thin Γ Δ)

theorem Tm.wk_pvV {p : PrimTy} (i : Idx Γ (.val p)) : (Tm.pvV (C := C) i).wk h = .pvV (i.wk h) :=
  rfl
theorem Tm.wk_pvP {R : RefTy} (i : Idx Γ (.alias R)) :
    (Tm.pvP (C := C) i).wk h = .pvP (i.wk h) := rfl
theorem Tm.wk_pvS (i : Idx Γ .old) : (Tm.pvS (C := C) i).wk h = .pvS (i.wk h) := rfl
theorem Tm.wk_pvI {R : RefTy} (i : Idx Γ (.mem R)) :
    (Tm.pvI (C := C) i).wk h = .pvI (i.wk h) := rfl
theorem Tm.wk_netOf (i : Idx Γ .oldNet) (a : Tm C Γ (.val .uint)) :
    (Tm.netOf i a).wk h = .netOf (i.wk h) (a.wk h) := rfl
theorem Tm.wk_app0 {s : Srt} (o : Op0 C s) : (Tm.app0 (C := C) (Γ := Γ) o).wk h = .app0 o := rfl
theorem Tm.wk_app1 {a s : Srt} (o : Op1 C a s) (x : Tm C Γ a) :
    (Tm.app1 o x).wk h = .app1 o (x.wk h) := rfl
theorem Tm.wk_app2 {a b s : Srt} (o : Op2 C a b s) (x : Tm C Γ a) (y : Tm C Γ b) :
    (Tm.app2 o x y).wk h = .app2 o (x.wk h) (y.wk h) := rfl
theorem Tm.wk_app3 {a b c s : Srt} (o : Op3 C a b c s) (x : Tm C Γ a) (y : Tm C Γ b)
    (z : Tm C Γ c) : (Tm.app3 o x y z).wk h = .app3 o (x.wk h) (y.wk h) (z.wk h) := rfl
theorem Tm.wk_pvZ (i : Idx Γ .kint) : (Tm.pvZ (C := C) i).wk h = .pvZ (i.wk h) := rfl

end WkEqns

theorem Tm.eval_wk {Γ Δ : Ctx} (h : Thin Γ Δ) (σ : State C Δ) :
    {s : Srt} → (t : Tm C Γ s) → (t.wk h).eval σ = t.eval (σ.thin h)
  | _, .pvV i => by
    show some (TEnv.get (i.wk h) σ.env) = some (TEnv.get i (TEnv.thin h σ.env))
    rw [TEnv.get_thin_wk]
  | _, .pvP i => by
    show TEnv.get (i.wk h) σ.env = TEnv.get i (TEnv.thin h σ.env)
    rw [TEnv.get_thin_wk]
  | _, .pvS i => by
    show some (TEnv.get (i.wk h) σ.env) = some (TEnv.get i (TEnv.thin h σ.env))
    rw [TEnv.get_thin_wk]
  | _, .pvI i => by
    show (TEnv.get (i.wk h) σ.env).map (·.id) = (TEnv.get i (TEnv.thin h σ.env)).map (·.id)
    rw [TEnv.get_thin_wk]
  | _, .netOf i a => by
    show ((a.wk h).eval σ).bind _ = (a.eval (σ.thin h)).bind (Tm.netOfT (TEnv.get i (TEnv.thin h σ.env)))
    rw [Tm.eval_wk h σ a, TEnv.get_thin_wk]
  | _, .app0 o => rfl
  | _, .app1 o a => by
    show o.eval σ.glob ((a.wk h).eval σ) = o.eval σ.glob (a.eval (σ.thin h))
    rw [Tm.eval_wk h σ a]
  | _, .app2 o a b => by
    show o.eval σ.glob ((a.wk h).eval σ) ((b.wk h).eval σ) =
      o.eval σ.glob (a.eval (σ.thin h)) (b.eval (σ.thin h))
    rw [Tm.eval_wk h σ a, Tm.eval_wk h σ b]
  | _, .app3 o a b c => by
    show o.eval σ.glob ((a.wk h).eval σ) ((b.wk h).eval σ) ((c.wk h).eval σ) =
      o.eval σ.glob (a.eval (σ.thin h)) (b.eval (σ.thin h)) (c.eval (σ.thin h))
    rw [Tm.eval_wk h σ a, Tm.eval_wk h σ b, Tm.eval_wk h σ c]
  | _, .pvZ i => by
    show some (TEnv.get (i.wk h) σ.env) = some (TEnv.get i (TEnv.thin h σ.env))
    rw [TEnv.get_thin_wk]

theorem Tm.denote_wk {Γ Δ : Ctx} (h : Thin Γ Δ) (σ : State C Δ) :
    {s : Srt} → (t : Tm C Γ s) → (t.wk h).denote σ = t.denote (σ.thin h)
  | _, .pvV i => by simp only [Tm.wk_pvV, Tm.denote, State.thin, State.withEnv, TEnv.get_thin_wk]
  | _, .pvP i => by simp only [Tm.wk_pvP, Tm.denote, State.thin, State.withEnv, TEnv.get_thin_wk]; split <;> rfl
  | _, .pvS i => by simp only [Tm.wk_pvS, Tm.denote, State.thin, State.withEnv, TEnv.get_thin_wk]
  | _, .pvI i => rfl
  | _, .netOf i a => by
    simp only [Tm.wk_netOf, Tm.denote, Tm.denote_wk h σ a, State.thin, State.withEnv,
      TEnv.get_thin_wk]
  | _, .app0 o => rfl
  | _, .app1 o a => by
    show o.denote σ.glob ((a.wk h).denote σ) = o.denote σ.glob (a.denote (σ.thin h))
    rw [Tm.denote_wk h σ a]
  | _, .app2 o a b => by
    show o.denote σ.glob ((a.wk h).eval σ) ((b.wk h).eval σ) ((a.wk h).denote σ) ((b.wk h).denote σ) =
      o.denote σ.glob (a.eval (σ.thin h)) (b.eval (σ.thin h)) (a.denote (σ.thin h))
        (b.denote (σ.thin h))
    rw [Tm.denote_wk h σ a, Tm.denote_wk h σ b, Tm.eval_wk h σ a, Tm.eval_wk h σ b]
  | _, .app3 o a b c => by
    show o.denote ((a.wk h).denote σ) ((b.wk h).denote σ) ((c.wk h).denote σ) =
      o.denote (a.denote (σ.thin h)) (b.denote (σ.thin h)) (c.denote (σ.thin h))
    rw [Tm.denote_wk h σ a, Tm.denote_wk h σ b, Tm.denote_wk h σ c]
  | _, .pvZ i => by simp only [Tm.wk_pvZ, Tm.denote, State.thin, State.withEnv, TEnv.get_thin_wk]

/-- A first-order formula read with more locals around it; `none` on an
update, a modality, a `havoc`, a hidden binder or an anonymising update. -/
def Fml.wkFO {Γ Δ : Ctx} (h : Thin Γ Δ) (φ : Fml C Γ) : Option (Fml C Δ) :=
  Fml.casesOn (motive := fun Γ _ => (Δ : Ctx) → Thin Γ Δ → Option (Fml C Δ)) φ
    (tt := fun _ _ => some .tt) (eq := fun a b _ h => some (.eq (a.wk h) (b.wk h)))
    (defined := fun t _ h => some (.defined (t.wk h)))
    (not := fun φ _ h => (Fml.wkFO h φ).map .not)
    (and := fun φ ψ _ h => do pure (.and (← Fml.wkFO h φ) (← Fml.wkFO h ψ)))
    (imp := fun φ ψ _ h => do pure (.imp (← Fml.wkFO h φ) (← Fml.wkFO h ψ)))
    (upd := fun _ _ _ _ _ => none) (modal := fun _ _ _ _ _ _ => none)
    (havoc := fun _ _ _ => none) (all := fun x p φ _ h => (Fml.wkFO h.keep φ).map (.all x p))
    (bind := fun _ _ _ _ _ _ => none) (anon := fun _ _ _ _ => none) Δ h
  termination_by structural φ

section WkFOEqns

variable {Γ Δ : Ctx} (h : Thin Γ Δ)

theorem Fml.wkFO_not (φ : Fml C Γ) : (Fml.not φ).wkFO h = (φ.wkFO h).map .not := rfl
theorem Fml.wkFO_and (φ ψ : Fml C Γ) :
    (Fml.and φ ψ).wkFO h = (do pure (.and (← φ.wkFO h) (← ψ.wkFO h))) := rfl
theorem Fml.wkFO_imp (φ ψ : Fml C Γ) :
    (Fml.imp φ ψ).wkFO h = (do pure (.imp (← φ.wkFO h) (← ψ.wkFO h))) := rfl
theorem Fml.wkFO_all (x : Var) (p : PrimTy) (φ : Fml C (.val p :: Γ)) :
    (Fml.all x p φ).wkFO h = (φ.wkFO h.keep).map (.all x p) := rfl

end WkFOEqns

/-- `Fml.wkFO`, `true` where it is `none`. -/
def Fml.wkD {Γ Δ : Ctx} (h : Thin Γ Δ) (φ : Fml C Γ) : Fml C Δ := (φ.wkFO h).getD .tt

/-- **A weakened first-order formula reads as the formula on the thinned
state.** -/
theorem holds_wkFO {Γ Δ : Ctx} (h : Thin Γ Δ) : (φ : Fml C Γ) → {φ' : Fml C Δ} →
    φ.wkFO h = some φ' → ∀ σ : State C Δ, (holds σ φ' ↔ holds (σ.thin h) φ)
  | .tt, _, e, σ => by cases e; exact Iff.rfl
  | .eq a b, _, e, σ => by
    cases e
    rw [holds_eq, holds_eq, Tm.denote_wk, Tm.denote_wk]
  | .defined t, _, e, σ => by
    cases e
    rw [holds_defined, holds_defined, Tm.eval_wk]
  | .not φ, _, e, σ => by
    cases hφ : φ.wkFO h with
    | none => simp only [Fml.wkFO_not, hφ, Option.map_none, reduceCtorEq] at e
    | some φ' =>
      simp only [Fml.wkFO_not, hφ, Option.map_some, Option.some.injEq] at e
      cases e
      exact not_congr (holds_wkFO h φ hφ σ)
  | .and φ ψ, _, e, σ => by
    cases hφ : φ.wkFO h with
    | none => simp only [Fml.wkFO_and, hφ, Option.bind_none, Option.bind_eq_bind, reduceCtorEq] at e
    | some φ' =>
      cases hψ : ψ.wkFO h with
      | none =>
        simp only [Fml.wkFO_and, hφ, hψ, Option.bind_some, Option.bind_none, Option.bind_eq_bind,
          reduceCtorEq] at e
      | some ψ' =>
        simp only [Fml.wkFO_and, hφ, hψ, Option.bind_some, Option.bind_eq_bind, Option.pure_def,
          Option.some.injEq] at e
        cases e
        exact and_congr (holds_wkFO h φ hφ σ) (holds_wkFO h ψ hψ σ)
  | .imp φ ψ, _, e, σ => by
    cases hφ : φ.wkFO h with
    | none => simp only [Fml.wkFO_imp, hφ, Option.bind_none, Option.bind_eq_bind, reduceCtorEq] at e
    | some φ' =>
      cases hψ : ψ.wkFO h with
      | none =>
        simp only [Fml.wkFO_imp, hφ, hψ, Option.bind_some, Option.bind_none, Option.bind_eq_bind,
          reduceCtorEq] at e
      | some ψ' =>
        simp only [Fml.wkFO_imp, hφ, hψ, Option.bind_some, Option.bind_eq_bind, Option.pure_def,
          Option.some.injEq] at e
        cases e
        exact imp_congr (holds_wkFO h φ hφ σ) (holds_wkFO h ψ hψ σ)
  | .all x p φ, _, e, σ => by
    cases hφ : φ.wkFO h.keep with
    | none => simp only [Fml.wkFO_all, hφ, Option.map_none, reduceCtorEq] at e
    | some φ' =>
      simp only [Fml.wkFO_all, hφ, Option.map_some, Option.some.injEq] at e
      cases e
      exact forall_congr' fun v => holds_wkFO h.keep φ hφ (σ.push (t := .val p) v)
  | .upd .., _, e, _ | .modal .., _, e, _ | .havoc _, _, e, _ | .bind .., _, e, _
  | .anon .., _, e, _ => nomatch e

/-- What a formula says on the thinned state, its weakening says (`true`
where it does not weaken). -/
theorem holds_wkD {Γ Δ : Ctx} (h : Thin Γ Δ) (φ : Fml C Γ) (σ : State C Δ)
    (hφ : holds (σ.thin h) φ) : holds σ (φ.wkD h) := by
  unfold Fml.wkD
  cases e : φ.wkFO h with
  | none => trivial
  | some φ' => exact (holds_wkFO h φ e σ).2 hφ

end Wk

/-! ## Contracts -/

section Contract

variable {Γ rs Γ' ps Γf : Ctx}

/-- The snapshots `\old` reads, as `{old := storage ‖ oldNet := net}`
declares them: `oldNet` on top, `old` under it. -/
abbrev Olds : Ctx := [.oldNet, .old]

/-- `{old := storage ‖ oldNet := net}`: the storage and the ledger where the
callee is entered, the snapshots `\old` reads (`find(old, total)`,
`net(oldNet, a)`), declared at their own types (`LTy.old`, `LTy.oldNet`). -/
def snapOld {Δ : Ctx} : Upd C Δ (Olds ++ Δ) :=
  (Upd.nil.decl (.user "old") (.store (.app0 .storage))).decl (.user "oldNet") .saveNet

/-- The snapshots `n` (the ledger) and `s` (the storage) on the locals `B`. -/
abbrev TEnv.olds {H : HTy} {Δ : Ctx} (n : Ledger) (s : Storage C) (B : TEnv C H Δ) :
    TEnv C H (Olds ++ Δ) :=
  (n, (s, B))

/-- The state `snapOld` leaves. -/
def State.snap {Δ : Ctx} (σ : State C Δ) : State C (Olds ++ Δ) :=
  σ.withEnv (TEnv.olds σ.net σ.storage σ.env)

/-- What a formula says past `snapOld`, it says of the snapshots. -/
theorem holds_snapOld {Δ : Ctx} {X : Fml C (Olds ++ Δ)} {σ : State C Δ}
    (h : holds σ (.upd .box snapOld X)) : holds σ.snap X := by
  refine Upd.afterT.of_lands (U := snapOld) h (g := σ.globG) ⟨rfl, rfl, fun i => ?_⟩
  cases i with
  | here => rfl
  | there i =>
    cases i with
    | here => rfl
    | there j => rfl

/-- The callee's frame `τ` with the snapshots `n` (the ledger) and `s` (the
storage) declared under its return variables. -/
def State.withOlds (rs : Ctx) {ps : Ctx} (n : Ledger) (s : Storage C)
    (τ : State C (rs ++ ps)) : State C (rs ++ (Olds ++ ps)) :=
  τ.withEnv (TEnv.append rs (TEnv.take rs τ.env)
    (TEnv.olds n s (TEnv.drop (Ext.append ps rs) τ.env)))

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
ends, ends where `ens` holds of its frame, `old` and `oldNet` the storage
and the ledger it was entered with. -/
def FunContract (ret : CallRet Γ rs Γ') (body : Prog C (rs ++ ps) Γf) (req : Fml C ps)
    (ens : Fml C (rs ++ (Olds ++ ps))) : Prop :=
  ∀ σ : State C ps, holds σ req →
    Modality.box.afterRunTR (fun τ => holds (τ.withOlds rs σ.net σ.storage) ens)
      ((Prog.run (ret.enterT σ).st body).map fun o => o.st.drop body.ext)

/-- The callee's frame read under the snapshots, between its return
variables and its parameters. -/
def thinOlds (rs ps : Ctx) : Thin (rs ++ ps) (rs ++ (Olds ++ ps)) :=
  Thin.keepAll rs (Thin.ofExt (Ext.append ps Olds))

/-- **The obligation of a contract**, solkey's planned
`requires -> [g(args)@C] ensures` for the callee's frame:
`requires → {old := storage ‖ oldNet := net} [ T r; { body } ] ensures`,
the body read under the snapshots (`thinOlds`), as a block. -/
def FunContract.obligation (ret : CallRet Γ rs Γ') (body : Prog C (rs ++ ps) Γf) (req : Fml C ps)
    (ens : Fml C (rs ++ (Olds ++ ps))) : Fml C ps :=
  .imp req (.upd .box snapOld (.modal .box
    (ret.declsThen (.cons (.block (body.wk (thinOlds rs ps)).2.2) .nil)) .nil ens))

theorem CallRet.runSt_declsThen {Δ : Ctx} (ret : CallRet Γ rs Γ')
    (rest : Prog C (rs ++ ps) Δ) (σ : State C ps) :
    Prog.runSt σ (ret.declsThen rest) = Prog.runSt (ret.enterT σ).st rest := by
  cases ret with
  | none => rfl
  | val p r res =>
    show Prog.runSt σ (.cons (.declLocal p r Option.none) rest) = _
    rw [Prog.runSt_cons, Stmt.runSt_declLocal_none]
    rfl
  | rets bs => exact Binders.runSt_declsThen σ bs rest
  | mem R r hd hm =>
    show Prog.runSt σ (.cons (.declMem R r Option.none hd hm) rest) = _
    rw [Prog.runSt_cons, Stmt.runSt_declMem_none]
    rfl

theorem TEnv.take_append {H : HTy} {Δ : Ctx} : (ρ : Ctx) → (r : TEnv C H ρ) → (e : TEnv C H Δ) →
    TEnv.take ρ (TEnv.append ρ r e) = r
  | [], _, _ => rfl
  | _ :: ρ, r, e => congrArg (Prod.mk r.1) (TEnv.take_append ρ r.2 e)

/-- A frame lifted under the snapshots is the frame with them declared. -/
theorem State.lift_thinOlds (τ : State C (rs ++ ps)) (A : TEnv C τ.H rs) (n : Ledger)
    (s : Storage C) (B : TEnv C τ.H ps) :
    τ.lift (thinOlds rs ps) (TEnv.append rs A (TEnv.olds n s B)) =
      τ.withOlds rs n s := by
  have e := TEnv.append_take_drop rs τ.env
  unfold State.lift State.withOlds thinOlds
  conv => lhs; rw [← e]
  rw [TEnv.put_keepAll]
  rfl

/-- The frame a call enters past the snapshots: the frame it enters, the
snapshots declared under its return variables. -/
theorem CallRet.enterT_snap (ret : CallRet Γ rs Γ') (σ : State C ps) :
    (ret.enterT σ.snap).st = (ret.enterT σ).st.withOlds rs σ.net σ.storage := by
  cases ret with
  | none => rfl
  | val => rfl
  | rets bs =>
    show σ.snap.withEnv (TEnv.append rs _ σ.snap.env) = State.withEnv _ (TEnv.append rs
      (TEnv.take rs (TEnv.append rs _ σ.env))
      (TEnv.olds σ.net σ.storage (TEnv.drop (Ext.append ps rs) (TEnv.append rs _ σ.env))))
    rw [TEnv.take_append, TEnv.drop_append]
    rfl
  | mem => rfl

/-- A contract from a proof of its obligation. -/
theorem FunContract.ofValid {ret : CallRet Γ rs Γ'} {body : Prog C (rs ++ ps) Γf} {req : Fml C ps}
    {ens : Fml C (rs ++ (Olds ++ ps))}
    (h : ∀ σ : State C ps, holds σ (FunContract.obligation ret body req ens)) :
    FunContract ret body req ens := by
  intro σ hreq
  have ho : holds σ req → holds σ (.upd .box snapOld _) := h σ
  have h' := (holds_modal_iff σ.snap _ _ ens).1 (holds_snapOld (ho hreq))
  rw [CallRet.runSt_declsThen ret, CallRet.enterT_snap, Prog.runSt_single,
    ← State.lift_thinOlds _ (TEnv.take rs (ret.enterT σ).st.env) σ.net σ.storage
      (TEnv.drop (Ext.append ps rs) (ret.enterT σ).st.env), Stmt.runSt, Stmt.run_block_wk] at h'
  revert h'
  cases Prog.run (ret.enterT σ).st body with
  | error e => exact fun h' => ⟨h'.1, fun hp => h'.2 (by cases hp; rfl)⟩
  | ok o =>
    intro h'
    refine ⟨?_, nofun⟩
    show holds ((o.st.drop body.ext).withOlds rs σ.net σ.storage) ens
    have e : (Out.lift (thinOlds rs ps) (TEnv.append rs (TEnv.take rs (ret.enterT σ).st.env)
        (TEnv.olds σ.net σ.storage (TEnv.drop (Ext.append ps rs) (ret.enterT σ).st.env)))
        (Out.drop body.ext o)).st =
        (o.st.drop body.ext).withOlds rs σ.net σ.storage := by
      simp only [Out.lift, Out.drop]
      rw [TEnv.append_wk]
      exact State.lift_thinOlds _ _ _ _ _
    rw [← e]
    exact h'.1

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

/-- `res = r;`, where the call's result lands, read under the frame `ρ`. -/
def CallRet.resultC {p : PrimTy} (ρ : Ctx) (res : Option (Idx Γ (.val p))) :
    Prog C (.val p :: (ρ ++ Γ)) (.val p :: (ρ ++ Γ)) :=
  match res with
  | Option.none => .nil
  | some j => .cons (.assignLocal (j.under ρ).there (.simple (.local .here))) .nil

/-- What "post" says past the snapshots and `{havoc}`, by what the call
leaves: `ensures → [ ..ω ] φ` for no result; `∀ T r. (ensures → [ res = r;
..ω ] φ)` for one; `∀ T r₁ … T rₙ. (ensures → [ ..ω ] φ)` for several, left
in the caller's context; `[ T memory r; ] (ensures → [ ..ω ] φ)` for a
memory return, the fresh object the callee is entered with.  `ensures` is
weakened to the caller's context (`Fml.wkD`), the frame popped (or dropped
from under the results) before the rest. -/
def Fml.callResult {rs Γ' : Ctx} (ret : CallRet Γ rs Γ') (ens : Fml C (rs ++ (Olds ++ ps)))
    (ω : Prog C Γ' Γ₂) (κ : Frames C Γ₂ Γ₀) (φ : Fml C Γ₀) : Fml C (Olds ++ (ps ++ Γ)) :=
  CallRet.casesOn (motive := fun rs Γ' _ =>
      Fml C (rs ++ (Olds ++ ps)) → Prog C Γ' Γ₂ → Fml C (Olds ++ (ps ++ Γ))) ret
    (fun ens ω => .imp (ens.wkD (Thin.atop (Olds ++ ps) Γ))
      (.modal .box .nil (.pop .block (Ext.append Γ (Olds ++ ps)) (.seq ω κ)) φ))
    (fun p r res ens ω => .all r p (.imp (ens.wkD (Thin.atop (.val p :: (Olds ++ ps)) Γ))
      (.modal .box (CallRet.resultC (Olds ++ ps) res)
        (.pop .block (Ext.append Γ (.val p :: (Olds ++ ps))) (.seq ω κ)) φ)))
    (fun {rs} bs ens ω => bs.all (.imp (ens.wkD (Thin.keepAll rs (Thin.atop (Olds ++ ps) Γ)))
      (.modal .box .nil (.drop (Thin.keepAll rs (Thin.ofExt (Ext.append Γ (Olds ++ ps))))
        (.seq ω κ)) φ)))
    (fun R r hd hm ens ω => .modal .box (.cons (.declMem R r Option.none hd hm) .nil) .nil
      (.imp (ens.wkD (Thin.atop (.mem R :: (Olds ++ ps)) Γ))
        (.modal .box .nil (.drop (.keep (Thin.ofExt (Ext.append Γ (Olds ++ ps)))) (.seq ω κ)) φ)))
    ens ω

/-- **"post"**: `[ params := args ] {old := storage ‖ oldNet := net} {havoc}
…`, the rest as `Fml.callResult` says by what the call leaves. -/
def Fml.callPost (μ : Mutability) (args : Args C Γ ps) {rs Γ' : Ctx} (ret : CallRet Γ rs Γ')
    (ens : Fml C (rs ++ (Olds ++ ps))) (ω : Prog C Γ' Γ₂) (κ : Frames C Γ₂ Γ₀) (φ : Fml C Γ₀) :
    Fml C Γ :=
  .modal .box (args.declsThen .nil) .nil
    (.upd .box snapOld (Fml.anonC μ (Fml.callResult ret ens ω κ φ)))

/-- The return variables "post" reads off the body's end: every value one,
none of a memory return (which stays the fresh object it was entered
with). -/
def CallRet.nVals {rs Γ' : Ctx} (r : CallRet Γ rs Γ') : Nat :=
  CallRet.casesOn (motive := fun _ _ _ => Nat) r 0 (fun _ _ _ => 1) (fun {rs} _ => rs.length)
    (fun _ _ _ _ => 0)

/-- The body writes only its first `n` locals, its value return variables,
so "post" reads the parameters at the arguments' values. -/
def writesRets (n : Nat) {Δ Δ' : Ctx} (body : Prog C Δ Δ') : Bool :=
  (Prog.writesAt 0 body).all fun w => decide (w.2 < n)

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

theorem Idx.toNat_ext_append {t : LTy} (i : Idx ps t) : (ρ : Ctx) →
    (i.ext (Ext.append ps ρ)).toNat = i.toNat + ρ.length
  | [] => rfl
  | _ :: ρ => by
    show (i.ext (Ext.append ps ρ)).toNat + 1 = _
    rw [Idx.toNat_ext_append i ρ, List.length_cons, Nat.add_assoc]

/-- The locals below the first `n` keep their values when the run writes
only the first `n`. -/
theorem TLocAgree.drop_eq {H : HTy} {W : List (LTy × Nat)} {ρ : Ctx} {e E : TEnv C H (ρ ++ ps)}
    (hag : TLocAgree 0 W e E) (hw : W.all (fun w => decide (w.2 < ρ.length)) = true) :
    TEnv.drop (Ext.append ps ρ) E = TEnv.drop (Ext.append ps ρ) e := by
  apply TEnv.ext
  intro t i
  have hni : (t, (i.ext (Ext.append ps ρ)).toNat - 0) ∉ W := by
    intro hm
    have h := List.all_eq_true.1 hw _ hm
    simp only [decide_eq_true_eq, Nat.sub_zero, Idx.toNat_ext_append] at h
    omega
  have h := eq_of_heq (hag t (i.ext (Ext.append ps ρ)) (Nat.zero_le _) hni)
  rwa [TEnv.get_ext_drop, TEnv.get_ext_drop] at h

/-- No local written, none changed. -/
theorem TLocAgree.eq_of_none {H : HTy} {W : List (LTy × Nat)} {e E : TEnv C H Γ}
    (hag : TLocAgree 0 W e E) (hw : W.all (fun w => decide (w.2 < 0)) = true) : E = e := by
  apply TEnv.ext
  intro t i
  have hni : (t, i.toNat - 0) ∉ W := by
    intro hm
    have h := List.all_eq_true.1 hw _ hm
    simp only [decide_eq_true_eq, Nat.not_lt_zero] at h
  exact eq_of_heq (hag t i (Nat.zero_le _) hni)

/-- A typed state is its parts, the heap and the locals up to the heap
typing. -/
theorem State.ext' {Γ : Ctx} {σ τ : State C Γ} (hst : σ.storage = τ.storage) (hH : σ.H = τ.H)
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
theorem holds_declsThen {args : Args C Γ ps} {X : Fml C (ps ++ Γ)} {σ : State C Γ}
    (h : holds σ (.modal .box (args.declsThen .nil) .nil X)) :
    (∀ e, args.evalT σ = .error e → e ≠ .panic) ∧
      ∀ a, args.evalT σ = .ok a → holds (σ.withEnv (TEnv.append ps a σ.env)) X := by
  rw [holds_modal_iff, Args.runSt_declsThen] at h
  refine ⟨fun e he => ?_, fun a ha => ?_⟩
  · rw [he] at h
    exact fun hp => h.2 (by rw [hp]; rfl)
  · rw [ha] at h
    exact h.1

/-- "pre": the arguments read, `requires` of the parameters. -/
theorem holds_callPre {args : Args C Γ ps} {req : Fml C ps} {σ : State C Γ}
    (h : holds σ (Fml.callPre args req)) :
    (∀ e, args.evalT σ = .error e → e ≠ .panic) ∧
      ∀ a, args.evalT σ = .ok a → holds (σ.withEnv a) req := by
  unfold Fml.callPre at h
  rw [holds_modal_iff, Args.runSt_declsThen] at h
  refine ⟨fun e he => ?_, fun a ha => ?_⟩
  · rw [he] at h
    exact fun hp => h.2 (by rw [hp]; rfl)
  · rw [ha] at h
    have h1 := h.1
    simp only [Except.bind, Prog.runSt_nil, Frames.runSt_drop, Frames.runSt_nil] at h1
    rwa [show (σ.withEnv (TEnv.append ps a σ.env)).thin (Thin.atop ps Γ) = σ.withEnv a by
      simp only [State.thin, State.withEnv, TEnv.thin_atop_append]] at h1

/-- "post", opened: the arguments read, the snapshots taken, the storage and
the ledger the callee leaves read in (for a `pure` or `view` callee, the
ones it was entered with). -/
theorem holds_callPost {μ : Mutability} {args : Args C Γ ps} {ret : CallRet Γ rs Γ'}
    {ens : Fml C (rs ++ (Olds ++ ps))} {ω : Prog C Γ' Γ₂} {κ : Frames C Γ₂ Γ₀} {φ : Fml C Γ₀}
    {σ : State C Γ} (h : holds σ (Fml.callPost μ args ret ens ω κ φ)) (a : TEnv C σ.H ps)
    (ha : args.evalT σ = .ok a) (st : Storage C) (nt : Ledger)
    (hk : μ ≠ .nonpayable → st = σ.storage ∧ nt = σ.net) :
    holds ((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st nt)
      (Fml.callResult ret ens ω κ φ) := by
  have hX := holds_snapOld ((holds_declsThen h).2 a ha)
  cases μ with
  | nonpayable => exact hX st nt
  | pure =>
    obtain ⟨rfl, rfl⟩ := hk (by decide)
    exact hX
  | view =>
    obtain ⟨rfl, rfl⟩ := hk (by decide)
    exact hX

/-- A call by its contract, no result. -/
theorem holds_callNone {μ : Mutability} {f : Name} {args : Args C Γ ps}
    {body : Prog C ([] ++ ps) Γf} {ω : Prog C Γ Γ₂} {κ : Frames C Γ₂ Γ₀} {φ : Fml C Γ₀}
    {req : Fml C ps} {ens : Fml C ([] ++ (Olds ++ ps))}
    (hc : FunContract (CallRet.none (Γ := Γ)) body req ens) (hμ : Prog.within μ body = true)
    (hw : writesRets 0 body = true) {σ : State C Γ}
    (hpre : holds σ (Fml.callPre args req))
    (hpost : holds σ (Fml.callPost μ args .none ens ω κ φ)) :
    holds σ (.modal .box (.cons (.call f args .none body) ω) κ φ) := by
  obtain ⟨hpe, hpa⟩ := holds_callPre hpre
  rw [holds_modal_iff, Prog.runSt_cons]
  show Modality.box.afterRunTR _ ((((TRun.call args .none body.ext body.runR σ).map
    (·.st)).bind _).bind _)
  rw [TRun.call_eq]
  cases hA : args.evalT σ with
  | error e => exact ⟨trivial, fun hp => hpe e hA (by cases hp; rfl)⟩
  | ok a =>
    have hct := hc _ (hpa a hA)
    show Modality.box.afterRunTR _ (((Except.map (·.st) (TRun.callFrom .none body.ext
      body.runR σ ((CallRet.none (Γ := Γ)).enterT (σ.withEnv a)))).bind _).bind _)
    unfold TRun.callFrom
    cases hB : body.runR ((CallRet.none (Γ := Γ)).enterT (σ.withEnv a)).st with
    | error e =>
      rw [show Prog.run _ body = body.runR _ from rfl, hB] at hct
      exact ⟨trivial, fun hp => hct.2 (by cases hp; rfl)⟩
    | ok o =>
      rw [show Prog.run _ body = body.runR _ from rfl, hB] at hct
      have hens := hct.1
      obtain ⟨hg, hag⟩ := Prog.run_frame body hμ 0 hB
      have hX := holds_callPost hpost a hA o.st.storage o.st.net hg.keeps
      obtain ⟨⟨st, H', heap, env, net, sb, tx⟩, ext⟩ := o
      obtain ⟨hH, hheap, hsb, htx, -⟩ := hg
      dsimp only [CallRet.enterT, State.withEnv] at hH hheap hsb htx hag hens
      dsimp only at hX
      subst hH
      cases hheap
      -- the parameters keep the arguments' values
      have hps : TEnv.drop body.ext env = a :=
        TLocAgree.drop_eq (ρ := []) hag hw
      have hens' : holds ((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net)
          (ens.wkD (Thin.atop (Olds ++ ps) Γ)) := by
        apply holds_wkD
        have hst : (State.drop body.ext ⟨st, σ.H, σ.heap, env, net, sb, tx⟩).withOlds []
            σ.net σ.storage = State.thin (Thin.atop (Olds ++ ps) Γ)
              ((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net) := by
          refine State.ext' rfl rfl HEq.rfl (heq_of_eq ?_) rfl hsb htx
          show TEnv.olds σ.net σ.storage (TEnv.drop body.ext env) =
            TEnv.olds σ.net σ.storage (TEnv.thin (Thin.atop ps Γ) (TEnv.append ps a σ.env))
          rw [TEnv.thin_atop_append, hps]
        exact hst ▸ hens
      have hM := hX hens'
      rw [holds_modal_iff] at hM
      dsimp only [bind, Except.bind, Except.map, pure, Except.pure]
      rw [TEnv.wk_self]
      have hT : State.drop (Ext.append Γ (Olds ++ ps))
          ((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net) =
          (⟨st, σ.H, σ.heap, env, net, sb, tx⟩ : State C Γf).withEnv
            (CallRet.leaveT σ.env (CallRet.none (Γ := Γ))
              (TEnv.take [] (TEnv.drop body.ext env))) :=
        State.ext' rfl rfl HEq.rfl (heq_of_eq (TEnv.drop_append ps a σ.env)) rfl hsb.symm
          htx.symm
      simp only [Prog.runSt_nil, Except.bind, Frames.runSt_pop, Frames.runSt_seq, hT] at hM
      exact hM

/-- A call by its contract, one result. -/
theorem holds_callVal {μ : Mutability} {f : Name} {args : Args C Γ ps} {p : PrimTy} {r : Var}
    {res : Option (Idx Γ (.val p))} {body : Prog C ([.val p] ++ ps) Γf} {ω : Prog C Γ Γ₂}
    {κ : Frames C Γ₂ Γ₀} {φ : Fml C Γ₀} {req : Fml C ps} {ens : Fml C ([.val p] ++ (Olds ++ ps))}
    (hc : FunContract (.val p r res) body req ens) (hμ : Prog.within μ body = true)
    (hw : writesRets 1 body = true) {σ : State C Γ}
    (hpre : holds σ (Fml.callPre args req))
    (hpost : holds σ (Fml.callPost μ args (.val p r res) ens ω κ φ)) :
    holds σ (.modal .box (.cons (.call f args (.val p r res) body) ω) κ φ) := by
  obtain ⟨hpe, hpa⟩ := holds_callPre hpre
  rw [holds_modal_iff, Prog.runSt_cons]
  show Modality.box.afterRunTR _ ((((TRun.call args (.val p r res) body.ext body.runR σ).map
    (·.st)).bind _).bind _)
  rw [TRun.call_eq]
  cases hA : args.evalT σ with
  | error e => exact ⟨trivial, fun hp => hpe e hA (by cases hp; rfl)⟩
  | ok a =>
    have hct := hc _ (hpa a hA)
    show Modality.box.afterRunTR _ (((Except.map (·.st) (TRun.callFrom (.val p r res) body.ext
      body.runR σ ((CallRet.val p r res).enterT (σ.withEnv a)))).bind _).bind _)
    unfold TRun.callFrom
    cases hB : body.runR ((CallRet.val p r res).enterT (σ.withEnv a)).st with
    | error e =>
      rw [show Prog.run _ body = body.runR _ from rfl, hB] at hct
      exact ⟨trivial, fun hp => hct.2 (by cases hp; rfl)⟩
    | ok o =>
      rw [show Prog.run _ body = body.runR _ from rfl, hB] at hct
      have hens := hct.1
      obtain ⟨hg, hag⟩ := Prog.run_frame body hμ 0 hB
      have hX := holds_callPost hpost a hA o.st.storage o.st.net hg.keeps
      obtain ⟨⟨st, H', heap, env, net, sb, tx⟩, ext⟩ := o
      obtain ⟨hH, hheap, hsb, htx, -⟩ := hg
      dsimp only [CallRet.enterT, State.push, State.withEnv] at hH hheap hsb htx hag hens
      dsimp only at hX
      subst hH
      cases hheap
      -- the parameters keep the arguments' values
      have hps : (TEnv.drop body.ext env).2 = a :=
        TLocAgree.drop_eq (ρ := [.val p]) (e := (PrimTy.dflt p, a)) hag hw
      have hens' : holds (((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net).push
          (t := .val p) (TEnv.drop body.ext env).1)
          (ens.wkD (Thin.atop (.val p :: (Olds ++ ps)) Γ)) := by
        apply holds_wkD
        have hst : (State.drop body.ext ⟨st, σ.H, σ.heap, env, net, sb, tx⟩).withOlds [.val p]
            σ.net σ.storage = State.thin (Thin.atop (.val p :: (Olds ++ ps)) Γ)
              (((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net).push (t := .val p)
                (TEnv.drop body.ext env).1) := by
          refine State.ext' rfl rfl HEq.rfl (heq_of_eq ?_) rfl hsb htx
          show ((TEnv.drop body.ext env).1, TEnv.olds σ.net σ.storage (TEnv.drop body.ext env).2) =
            ((TEnv.drop body.ext env).1, TEnv.olds σ.net σ.storage
              (TEnv.thin (Thin.atop ps Γ) (TEnv.append ps a σ.env)))
          rw [TEnv.thin_atop_append, hps]
        exact hst ▸ hens
      have hM := hX (TEnv.drop body.ext env).1 hens'
      rw [holds_modal_iff] at hM
      dsimp only [bind, Except.bind, Except.map, pure, Except.pure]
      rw [TEnv.wk_self]
      cases res with
      | none =>
        have hT : State.drop (Ext.append Γ (.val p :: (Olds ++ ps)))
            (((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net).push (t := .val p)
              (TEnv.drop body.ext env).1) =
            (⟨st, σ.H, σ.heap, env, net, sb, tx⟩ : State C Γf).withEnv
              (CallRet.leaveT σ.env (CallRet.val p r Option.none)
                (TEnv.take [LTy.val p] (TEnv.drop body.ext env))) :=
          State.ext' rfl rfl HEq.rfl (heq_of_eq (TEnv.drop_append ps a σ.env)) rfl hsb.symm
            htx.symm
        simp only [CallRet.resultC, Prog.runSt_nil, Except.bind, Frames.runSt_pop,
          Frames.runSt_seq, hT] at hM
        exact hM
      | some j =>
        have hT : State.drop (Ext.append Γ (.val p :: (Olds ++ ps)))
            ((((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net).push (t := .val p)
              (TEnv.drop body.ext env).1).setLocal (j.under (Olds ++ ps)).there
                (TEnv.drop body.ext env).1) =
            (⟨st, σ.H, σ.heap, env, net, sb, tx⟩ : State C Γf).withEnv
              (CallRet.leaveT σ.env (CallRet.val p r (some j))
                (TEnv.take [LTy.val p] (TEnv.drop body.ext env))) := by
          refine State.ext' rfl rfl HEq.rfl (heq_of_eq ?_) rfl hsb.symm htx.symm
          show TEnv.drop (Ext.append Γ (.val p :: (Olds ++ ps)))
            (TEnv.set (j.under (.val p :: (Olds ++ ps))) _ _) = _
          rw [TEnv.drop_set_under]
          show TEnv.set j _ (TEnv.drop (Ext.append Γ ps) (TEnv.append ps a σ.env)) = _
          rw [TEnv.drop_append]
          rfl
        have hs : Prog.runSt (((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net).push
            (t := .val p) (TEnv.drop body.ext env).1) (CallRet.resultC (Olds ++ ps) (some j)) =
            .ok ((((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net).push (t := .val p)
              (TEnv.drop body.ext env).1).setLocal (j.under (Olds ++ ps)).there
                (TEnv.drop body.ext env).1) := rfl
        simp only [hs, Except.bind, Frames.runSt_pop, Frames.runSt_seq, hT] at hM
        exact hM

/-- A call by its contract, several results left in the caller's context. -/
theorem holds_callRets {μ : Mutability} {f : Name} {args : Args C Γ ps} {bs : Binders rs}
    {body : Prog C (rs ++ ps) Γf} {ω : Prog C (rs ++ Γ) Γ₂} {κ : Frames C Γ₂ Γ₀} {φ : Fml C Γ₀}
    {req : Fml C ps} {ens : Fml C (rs ++ (Olds ++ ps))}
    (hc : FunContract (CallRet.rets (Γ := Γ) bs) body req ens) (hμ : Prog.within μ body = true)
    (hw : writesRets rs.length body = true) {σ : State C Γ}
    (hpre : holds σ (Fml.callPre args req))
    (hpost : holds σ (Fml.callPost μ args (.rets bs) ens ω κ φ)) :
    holds σ (.modal .box (.cons (.call f args (.rets bs) body) ω) κ φ) := by
  obtain ⟨hpe, hpa⟩ := holds_callPre hpre
  rw [holds_modal_iff, Prog.runSt_cons]
  show Modality.box.afterRunTR _ ((((TRun.call args (.rets bs) body.ext body.runR σ).map
    (·.st)).bind _).bind _)
  rw [TRun.call_eq]
  cases hA : args.evalT σ with
  | error e => exact ⟨trivial, fun hp => hpe e hA (by cases hp; rfl)⟩
  | ok a =>
    have hct := hc _ (hpa a hA)
    show Modality.box.afterRunTR _ (((Except.map (·.st) (TRun.callFrom (.rets bs) body.ext
      body.runR σ ((CallRet.rets (Γ := Γ) bs).enterT (σ.withEnv a)))).bind _).bind _)
    unfold TRun.callFrom
    cases hB : body.runR ((CallRet.rets (Γ := Γ) bs).enterT (σ.withEnv a)).st with
    | error e =>
      rw [show Prog.run _ body = body.runR _ from rfl, hB] at hct
      exact ⟨trivial, fun hp => hct.2 (by cases hp; rfl)⟩
    | ok o =>
      rw [show Prog.run _ body = body.runR _ from rfl, hB] at hct
      have hens := hct.1
      obtain ⟨hg, hag⟩ := Prog.run_frame body hμ 0 hB
      have hX := holds_callPost hpost a hA o.st.storage o.st.net hg.keeps
      obtain ⟨⟨st, H', heap, env, net, sb, tx⟩, ext⟩ := o
      obtain ⟨hH, hheap, hsb, htx, -⟩ := hg
      dsimp only [CallRet.enterT, State.withEnv] at hH hheap hsb htx hag hens
      dsimp only at hX
      subst hH
      cases hheap
      have hps : TEnv.drop (Ext.append ps rs) (TEnv.drop body.ext env) = a := by
        rw [TLocAgree.drop_eq hag hw, TEnv.drop_append]
      have hX' := holds_binders_all bs _ (.imp (ens.wkD (Thin.keepAll rs (Thin.atop (Olds ++ ps) Γ)))
        (.modal .box .nil (.drop (Thin.keepAll rs (Thin.ofExt (Ext.append Γ (Olds ++ ps))))
          (.seq ω κ)) φ)) (TEnv.take rs (TEnv.drop body.ext env)) hX
      have hens' : holds (((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net).withEnv
          (TEnv.append rs (TEnv.take rs (TEnv.drop body.ext env))
            ((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net).env))
          (ens.wkD (Thin.keepAll rs (Thin.atop (Olds ++ ps) Γ))) := by
        apply holds_wkD
        have hst : (State.drop body.ext ⟨st, σ.H, σ.heap, env, net, sb, tx⟩).withOlds rs
            σ.net σ.storage = State.thin (Thin.keepAll rs (Thin.atop (Olds ++ ps) Γ))
              (((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net).withEnv
                (TEnv.append rs (TEnv.take rs (TEnv.drop body.ext env))
                  ((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net).env)) := by
          refine State.ext' rfl rfl HEq.rfl (heq_of_eq ?_) rfl hsb htx
          show TEnv.append rs (TEnv.take rs (TEnv.drop body.ext env))
              (TEnv.olds σ.net σ.storage (TEnv.drop (Ext.append ps rs) (TEnv.drop body.ext env))) =
            TEnv.thin (Thin.keepAll rs (Thin.atop (Olds ++ ps) Γ))
              (TEnv.append rs (TEnv.take rs (TEnv.drop body.ext env))
                (TEnv.olds σ.net σ.storage (TEnv.append ps a σ.env)))
          rw [TEnv.thin_keepAll, hps]
          show _ = TEnv.append rs _ (TEnv.olds σ.net σ.storage (TEnv.thin (Thin.atop ps Γ)
            (TEnv.append ps a σ.env)))
          rw [TEnv.thin_atop_append]
        exact hst ▸ hens
      have hM := hX' hens'
      rw [holds_modal_iff] at hM
      dsimp only [bind, Except.bind, Except.map, pure, Except.pure]
      rw [TEnv.wk_self]
      have hT : State.thin (Thin.keepAll rs (Thin.ofExt (Ext.append Γ (Olds ++ ps))))
          (((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net).withEnv
            (TEnv.append rs (TEnv.take rs (TEnv.drop body.ext env))
              ((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net).env)) =
          (⟨st, σ.H, σ.heap, env, net, sb, tx⟩ : State C Γf).withEnv
            (CallRet.leaveT σ.env (CallRet.rets bs)
              (TEnv.take rs (TEnv.drop body.ext env))) := by
        refine State.ext' rfl rfl HEq.rfl (heq_of_eq ?_) rfl hsb.symm htx.symm
        show TEnv.thin (Thin.keepAll rs (Thin.ofExt (Ext.append Γ (Olds ++ ps))))
            (TEnv.append rs _ (TEnv.olds σ.net σ.storage (TEnv.append ps a σ.env))) =
              TEnv.append rs _ σ.env
        rw [TEnv.thin_keepAll, TEnv.thin_ofExt]
        show TEnv.append rs _ (TEnv.drop (Ext.append Γ ps) (TEnv.append ps a σ.env)) = _
        rw [TEnv.drop_append]
      simp only [Prog.runSt_nil, Except.bind, Frames.runSt_drop, Frames.runSt_seq, hT] at hM
      exact hM

/-- A call by its contract, a memory return: the fresh object it is entered
with, which the body leaves as it is. -/
theorem holds_callMem {μ : Mutability} {f : Name} {args : Args C Γ ps} {R : RefTy} {r : Var}
    {hd : (Ty.ref R).defaultOkS = true} {hm : (Ty.ref R).mapFree = true}
    {body : Prog C ([.mem R] ++ ps) Γf} {ω : Prog C (.mem R :: Γ) Γ₂} {κ : Frames C Γ₂ Γ₀}
    {φ : Fml C Γ₀} {req : Fml C ps} {ens : Fml C ([.mem R] ++ (Olds ++ ps))}
    (hc : FunContract (CallRet.mem (Γ := Γ) R r hd hm) body req ens)
    (hμ : Prog.within μ body = true) (hw : writesRets 0 body = true) {σ : State C Γ}
    (hpre : holds σ (Fml.callPre args req))
    (hpost : holds σ (Fml.callPost μ args (.mem R r hd hm) ens ω κ φ)) :
    holds σ (.modal .box (.cons (.call f args (.mem R r hd hm) body) ω) κ φ) := by
  obtain ⟨hpe, hpa⟩ := holds_callPre hpre
  rw [holds_modal_iff, Prog.runSt_cons]
  show Modality.box.afterRunTR _ ((((TRun.call args (.mem R r hd hm) body.ext body.runR σ).map
    (·.st)).bind _).bind _)
  rw [TRun.call_eq]
  cases hA : args.evalT σ with
  | error e => exact ⟨trivial, fun hp => hpe e hA (by cases hp; rfl)⟩
  | ok a =>
    have hct := hc _ (hpa a hA)
    show Modality.box.afterRunTR _ (((Except.map (·.st) (TRun.callFrom (.mem R r hd hm) body.ext
      body.runR σ ((CallRet.mem (Γ := Γ) R r hd hm).enterT (σ.withEnv a)))).bind _).bind _)
    unfold TRun.callFrom
    cases hB : body.runR ((CallRet.mem (Γ := Γ) R r hd hm).enterT (σ.withEnv a)).st with
    | error e =>
      rw [show Prog.run _ body = body.runR _ from rfl, hB] at hct
      exact ⟨trivial, fun hp => hct.2 (by cases hp; rfl)⟩
    | ok o =>
      rw [show Prog.run _ body = body.runR _ from rfl, hB] at hct
      have hens := hct.1
      obtain ⟨hg, hag⟩ := Prog.run_frame body hμ 0 hB
      have hX := holds_callPost hpost a hA o.st.storage o.st.net hg.keeps
      obtain ⟨⟨st, H', heap, env, net, sb, tx⟩, ext⟩ := o
      obtain ⟨hH, hheap, hsb, htx, -⟩ := hg
      dsimp only [CallRet.enterT, State.push, State.withEnv] at hH hheap hsb htx hag hens
      dsimp only at hX
      subst hH
      cases hheap
      -- the object and the parameters as the callee was entered with them
      have hE := TLocAgree.eq_of_none hag hw
      have hX1 := (holds_modal_iff _ _ _ _).1 hX
      rw [Prog.runSt_single, Stmt.runSt_declMem_none] at hX1
      replace hX1 := hX1.1
      have hst : State.withOlds [.mem R] σ.net σ.storage (State.drop body.ext
          (⟨st, _, ((σ.withEnv a).allocDefaultG R hm).st.heap, env, net, sb, tx⟩ : State C Γf)) =
          State.thin (Thin.atop (.mem R :: (Olds ++ ps)) Γ)
            ((((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net).allocDefaultG R hm).st.push
              (t := .mem R)
              (some (((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net).allocDefaultG R hm).val)) := by
        refine State.ext' rfl rfl HEq.rfl (heq_of_eq ?_) rfl hsb htx
        show TEnv.append [.mem R] (TEnv.take [.mem R] (TEnv.drop body.ext env))
          (TEnv.olds σ.net σ.storage (TEnv.drop (Ext.append ps [.mem R]) (TEnv.drop body.ext env))) = _
        rw [hE]
        show (some _, TEnv.olds σ.net σ.storage (TEnv.wk _ ps a)) =
          (some _, TEnv.olds σ.net σ.storage
            (TEnv.thin (Thin.atop ps Γ) (TEnv.wk _ (ps ++ Γ) (TEnv.append ps a σ.env))))
        rw [TEnv.append_wk, TEnv.thin_atop_append]
        rfl
      have hens' := holds_wkD (Thin.atop (.mem R :: (Olds ++ ps)) Γ) ens _ (by rw [← hst]; exact hens)
      have hM := hX1 hens'
      rw [holds_modal_iff] at hM
      dsimp only [bind, Except.bind, Except.map, pure, Except.pure]
      have hT : State.thin (.keep (Thin.ofExt (Ext.append Γ (Olds ++ ps))))
          ((((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net).allocDefaultG R hm).st.push
            (t := .mem R)
            (some (((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net).allocDefaultG R hm).val)) =
          (⟨st, _, ((σ.withEnv a).allocDefaultG R hm).st.heap, env, net, sb, tx⟩ : State C Γf).withEnv
            (CallRet.leaveT (TEnv.wk (((CallRet.mem (Γ := Γ) R r hd hm).enterT (σ.withEnv a)).ext.trans
              ext) Γ σ.env) (CallRet.mem R r hd hm)
              (TEnv.take [.mem R] (TEnv.drop body.ext env))) := by
        refine State.ext' rfl rfl HEq.rfl (heq_of_eq ?_) rfl hsb.symm htx.symm
        show _ = ((TEnv.drop body.ext env).1, _)
        rw [hE]
        show (some _, TEnv.thin (Thin.ofExt (Ext.append Γ (Olds ++ ps)))
          (TEnv.wk _ (Olds ++ (ps ++ Γ)) (TEnv.olds σ.net σ.storage (TEnv.append ps a σ.env)))) = _
        rw [TEnv.thin_ofExt]
        show (some _, TEnv.drop (Ext.append Γ ps) (TEnv.wk _ (ps ++ Γ) (TEnv.append ps a σ.env))) = _
        rw [TEnv.append_wk, TEnv.drop_append]
        rfl
      simp only [Prog.runSt_nil, Except.bind, Frames.runSt_drop, Frames.runSt_seq, hT] at hM
      exact hM

/-- **A call by its callee's contract is sound** (`useContract`, at the
state): "pre" and "post" there give the call and the rest. -/
theorem holds_callContract {μ : Mutability} {f : Name} {args : Args C Γ ps}
    {ret : CallRet Γ rs Γ'} {body : Prog C (rs ++ ps) Γf} {ω : Prog C Γ' Γ₂}
    {κ : Frames C Γ₂ Γ₀} {φ : Fml C Γ₀} {req : Fml C ps} {ens : Fml C (rs ++ (Olds ++ ps))}
    (hc : FunContract ret body req ens) (hμ : Prog.within μ body = true)
    (hw : writesRets ret.nVals body = true) {σ : State C Γ}
    (hpre : holds σ (Fml.callPre args req))
    (hpost : holds σ (Fml.callPost μ args ret ens ω κ φ)) :
    holds σ (.modal .box (.cons (.call f args ret body) ω) κ φ) := by
  cases ret with
  | none => exact holds_callNone hc hμ hw hpre hpost
  | val p r res => exact holds_callVal hc hμ hw hpre hpost
  | rets => exact holds_callRets hc hμ hw hpre hpost
  | mem => exact holds_callMem hc hμ hw hpre hpost

end Sound

/-! ## The rule on sequents -/

section RuleSeq

variable {Γ ps rs Γ' Γf Γ₂ Γ₀ : Ctx}

/-- A formula of the parameters closed by `∀` over each, the first
parameter outermost, named as the call names them. -/
def Fml.allArgs : {ps : Ctx} → Args C Γ ps → Fml C ps → Fml C []
  | _, args, φ => Args.casesOn (motive := fun ps _ => Fml C ps → Fml C []) args
    (fun φ => φ) (fun as p x _ φ => Fml.allArgs as (.all x p φ)) φ
  termination_by structural _ args => args

theorem holds_allArgs : {ps : Ctx} → (args : Args C Γ ps) → {φ : Fml C ps} →
    Valid (Fml.allArgs args φ) → ∀ σ : State C ps, holds σ φ
  | _, .nil, _, h, σ => h σ
  | _, .snoc as p x _, φ, h, σ =>
    holds_allArgs as (φ := .all x p φ) h (σ.withEnv σ.env.2) σ.env.1

/-- A contract from a proof of its obligation, the parameters bound by `∀`
(`Fml.allArgs`), as `sol_symex; sol_close` prove it. -/
theorem FunContract.ofValid' {args : Args C Γ ps} {ret : CallRet Γ rs Γ'}
    {body : Prog C (rs ++ ps) Γf} {req : Fml C ps} {ens : Fml C (rs ++ (Olds ++ ps))}
    (h : Valid (Fml.allArgs args (FunContract.obligation ret body req ens))) :
    FunContract ret body req ens :=
  FunContract.ofValid (holds_allArgs args h)

/-- **`useContract`** of a contract, its goals proved valid. -/
theorem useContractC_of_valid {H : Hyps C [] Γ} {μ : Mutability} {f : Name}
    {args : Args C Γ ps} {ret : CallRet Γ rs Γ'} {body : Prog C (rs ++ ps) Γf}
    {ω : Prog C Γ' Γ₂} {κ : Frames C Γ₂ Γ₀} {φ : Fml C Γ₀} {req : Fml C ps}
    {ens : Fml C (rs ++ (Olds ++ ps))} (hc : FunContract ret body req ens)
    («pre» : Valid (H.wrap (Fml.callPre args req)))
    («post» : Valid (H.wrap (Fml.callPost μ args ret ens ω κ φ)))
    (hμ : Prog.within μ body = true := by rfl) (hw : writesRets ret.nVals body = true := by rfl) :
    Valid (H.wrap (.modal .box (.cons (.call f args ret body) ω) κ φ)) :=
  fun σ => H.wrap_and (fun _ h₁ h₂ => holds_callContract hc hμ hw h₁ h₂) σ («pre» σ) («post» σ)

/-- **`useContract`** with its goals proved valid, the contract by its
obligation (`FunContract.ofValid'`): what goals closed by
`sol_symex; sol_close` give. -/
theorem useContract_of_valid {H : Hyps C [] Γ} {μ : Mutability} {f : Name}
    {args : Args C Γ ps} {ret : CallRet Γ rs Γ'} {body : Prog C (rs ++ ps) Γf}
    {ω : Prog C Γ' Γ₂} {κ : Frames C Γ₂ Γ₀} {φ : Fml C Γ₀} {req : Fml C ps}
    {ens : Fml C (rs ++ (Olds ++ ps))}
    (hc : Valid (Fml.allArgs args (FunContract.obligation ret body req ens)))
    («pre» : Valid (H.wrap (Fml.callPre args req)))
    («post» : Valid (H.wrap (Fml.callPost μ args ret ens ω κ φ)))
    (hμ : Prog.within μ body = true := by rfl) (hw : writesRets ret.nVals body = true := by rfl) :
    Valid (H.wrap (.modal .box (.cons (.call f args ret body) ω) κ φ)) :=
  useContractC_of_valid (FunContract.ofValid' hc) «pre» «post» hμ hw

/-- **`useContract`**: a call proved by its callee's contract, KeY's
`useOperationContract` at the box, with the goals `"pre"` and `"post"`
derived (`⊢`). -/
theorem useContract {R : RuleSet} {H : Hyps C [] Γ} {μ : Mutability} {f : Name}
    {args : Args C Γ ps} {ret : CallRet Γ rs Γ'} {body : Prog C (rs ++ ps) Γf}
    {ω : Prog C Γ' Γ₂} {κ : Frames C Γ₂ Γ₀} {φ : Fml C Γ₀} {req : Fml C ps}
    {ens : Fml C (rs ++ (Olds ++ ps))}
    (hc : Valid (Fml.allArgs args (FunContract.obligation ret body req ens)))
    («pre» : Proves C R [] H (Fml.callPre args req))
    («post» : Proves C R [] H (Fml.callPost μ args ret ens ω κ φ))
    (hμ : Prog.within μ body = true := by rfl) (hw : writesRets ret.nVals body = true := by rfl) :
    Valid (H.wrap (.modal .box (.cons (.call f args ret body) ω) κ φ)) :=
  useContractC_of_valid (FunContract.ofValid' hc) «pre».sound «post».sound hμ hw

end RuleSeq

/-! ## Writing a contract: `cdlIn[C | uint x, old, oldNet, uint r]{ φ }`

A contract's `requires` and `ensures` are formulas of the callee's frame,
not closed ones: `cdlIn[C | uint se1, old, oldNet, uint se2]{ se2 == se1 + 1 }`
reads `φ` as `cdl[C]{ φ }` does, at the locals listed (outermost first: the
parameters in order, then, for `ensures`, the snapshots `old` and `oldNet`
that `\old` reads, then the return variables), none of them bound by it. -/

section Notation

variable [FreshNames] (C : Contract)

/-- The named context of the locals `ns`, listed outermost first. -/
def ctxOfLocals (ns : List (String × LTy)) : NCtx :=
  ns.reverse.map fun (x, t) => (Var.ofName x, t)

/-- A formula read at the locals `ns` (`cdlIn`): a value or a memory local
by its type, `old` as the reader's storage variable, `oldNet` by its name
alone (`net(oldNet, a)` reads it). -/
def elabFmlAtC (ns : List (String × LTy)) (φ : RawFml) :
    Except String (Fml C (ctxOfLocals ns).ctx) :=
  let scope : ECtx := ns.reverse.filterMap fun (x, t) => match t with
    | .val p => some (x, LocalTy.val p)
    | .old => some (x, LocalTy.store)
    | .mem R => some (x, LocalTy.mem R)
    | _ => none
  let taken := (ns.map fun (x, _) => (Var.ofName x).idx).filter (· > 0)
  ((elabFmlC C taken false φ (ctxOfLocals ns)).run { funs := C.funs }).run' (scope, 1)

end Notation

/-- A local of `cdlIn`: its type and name (`uint x`, a struct's memory
return `Person memory p`), or a snapshot (`old`, `oldNet`). -/
declare_syntax_cat cdl_local
syntax ident ident : cdl_local
syntax ident " memory " ident : cdl_local
syntax ident : cdl_local

/-- `cdlIn[C | uint x, old, oldNet, uint r]{ φ }`: `φ` read at the locals
listed, outermost first. -/
syntax "cdlIn[" term " | " cdl_local,* "]{ " dl_fml " }" : term

/-- `cdlIn![uint x, old, oldNet, uint r]{ φ }`: `cdlIn[C | …]{ φ }` for the
file's `InContract` contract. -/
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
        `(($(quote x.getId.toString), LTy.val $p))
      | `(cdl_local| $t:ident memory $x:ident) =>
        `(($(quote x.getId.toString), LTy.mem (RefTy.struct $(quote t.getId.toString))))
      | `(cdl_local| $x:ident) => match x.getId.toString with
        | "old" => `(("old", LTy.old))
        | "oldNet" => `(("oldNet", LTy.oldNet))
        | s => throwErrorAt x "cdlIn: {s} has no type; the snapshots are `old` and `oldNet`"
      | _ => throwUnsupportedSyntax
    let ns ← `([$items,*])
    let raw ← liftMacroM (expandFml { holes } φ)
    elabAgainstQ c fun q => `((elabFmlAtC $c $ns $raw).map (Fml.quote $q))

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
  let_expr Valid C φ := ty | throwError "core_contract: expected a goal `⊨ φ`, scoped"
  let nil := mkApp (mkConst ``List.nil [0]) (mkConst ``LTy)
  let (H, _, χ) ← peel C (mkApp2 (mkConst ``Hyps.nil) C nil) nil φ
  unless χ.isAppOf ``Fml.modal do
    throwError "core_contract: no modality at the head of the formula{indentExpr χ}"
  let HS ← Term.exprToSyntax H
  let r := mkIdent rule
  -- `req` and `ens` are read once the call has fixed the frame they stand in
  let tac ← if rule == ``useContract then
      `(tactic| refine $r (R := RuleSet.all) (H := $HS) (μ := $(⟨μ⟩)) (req := ?req) (ens := ?ens)
        ?hc ?pre ?post (by rfl) (by rfl))
    else
      `(tactic| refine $r (H := $HS) (μ := $(⟨μ⟩)) (req := ?req) (ens := ?ens)
        ?hc ?pre ?post (by rfl) (by rfl))
  evalTactic tac
  evalTactic (← `(tactic| case req => exact $(⟨req⟩)))
  evalTactic (← `(tactic| case ens => exact $(⟨ens⟩)))

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

end Solidity
