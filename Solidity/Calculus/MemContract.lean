import Solidity.Calculus.Recursion
import Solidity.Calculus.RunFrameMem

/-!
# A memory return by contract

`useContract`'s "post" for a memory return (`Fml.callResult`'s `.mem`)
declares the fresh default object the callee is entered with: right for a
callee within a mutability, which allocates nothing and so returns that
object as it was.  A callee that allocates (`Stmt.withinM`,
`Calculus/RunFrameMem.lean`) returns any object of a heap it grew, and leaves
garbage beside it.  Its "post" reads the call where it ends
(`docs/kernel-port.md`, "Recursion", "What is left", steps 2 and 3):

```
  "post":  Γ ⟹ [ params := args ] {old := storage ‖ oldNet := net} {havoc}
             {grow} ∀ T memory r. (ensures → [ ..ω ] φ)
```

`{grow}` (`Fml.grow`) is every heap grown from the caller's that keeps each
of the caller's objects (`Heap.Keeps`): the heap the callee leaves is one
(`Prog.run_frameM`), so the caller's goal is read at the very state the call
ends in, and no lemma that it cannot see the garbage is needed.  The
returned reference ranges over the grown heap's references (a hidden binder,
`Fml.bind`), `ensures` constraining it; the objects the caller had are read
as they were.
-/

namespace Solidity

open Solidity (Modality Mutability)

variable {C : Contract}

section Rule

variable {Γ ps Γf Γ₂ Γ₀ : Ctx} {m : Modality}

/-- What "post" says of a memory return that allocates, past the snapshots
and `{havoc}`: `{grow} ∀ T memory r. (ensures → [ ..ω ] φ)`. -/
def Fml.callResultM (R : RefTy) (r : Var) (ens : Fml C ([.mem R] ++ (Olds ++ ps)))
    (ω : Prog C (.mem R :: Γ) Γ₂) (κ : Frames C Γ₂ Γ₀) (φ : Fml C Γ₀) (m : Modality := .box) :
    Fml C (Olds ++ (ps ++ Γ)) :=
  .grow (.bind .box r (.mem R) (.imp (ens.wkD (Thin.atop (.mem R :: (Olds ++ ps)) Γ))
    (.modal m .nil (.drop (.keep (Thin.ofExt (Ext.append Γ (Olds ++ ps)))) (.seq ω κ)) φ)))

/-- **"post" of a memory return that allocates**: `[ params := args ] {old
:= storage ‖ oldNet := net} {havoc} {grow} ∀ T memory r. (ensures → [ ..ω ]
φ)`. -/
def Fml.callPostM (μ : Mutability) (args : Args C Γ ps) (R : RefTy) (r : Var)
    (ens : Fml C ([.mem R] ++ (Olds ++ ps))) (ω : Prog C (.mem R :: Γ) Γ₂) (κ : Frames C Γ₂ Γ₀)
    (φ : Fml C Γ₀) (m : Modality := .box) : Fml C Γ :=
  .modal m (args.declsThen .nil) .nil
    (.upd .box snapOld (Fml.anonC μ (Fml.callResultM R r ens ω κ φ m)))

end Rule

section Sound

variable {Γ ps Γf Γ₂ Γ₀ : Ctx} {m : Modality}

/-- The parameters below the return variable keep their values, weakened
along the heap the body grew, when the body writes only its return
variable. -/
theorem TLocAgreeM.params_eq {R : RefTy} {H H' : HTy} {e₀ : H <+: H'} {W : List (LTy × Nat)}
    {e : TEnv C H (.mem R :: ps)} {E : TEnv C H' (.mem R :: ps)}
    (hag : TLocAgreeM e₀ 0 W e E) (hw : W.all (fun w => decide (w.2 < 1)) = true) :
    E.2 = TEnv.wk e₀ ps e.2 := by
  apply TEnv.ext
  intro t i
  have hni : (t, (Idx.there (u := .mem R) i).toNat - 0) ∉ W := by
    intro hm
    have h := List.all_eq_true.1 hw _ hm
    simp only [decide_eq_true_eq, Nat.sub_zero] at h
    exact absurd h (by show ¬ (i.toNat + 1 < 1); omega)
  rw [TEnv.get_wk]
  exact hag t (.there i) (Nat.zero_le _) hni

/-- **A call of a memory return that allocates, by its callee's contract**:
"pre" and "post" (`Fml.callPostM`) give the call and the rest. -/
theorem holds_callMemM {μ : Mutability} {f : Name} {args : Args C Γ ps} {R : RefTy} {r : Var}
    {hd : (Ty.ref R).defaultOkS = true} {hm : (Ty.ref R).mapFree = true}
    {body : Prog C ([.mem R] ++ ps) Γf} {ω : Prog C (.mem R :: Γ) Γ₂} {κ : Frames C Γ₂ Γ₀}
    {φ : Fml C Γ₀} {req : Fml C ps} {ens : Fml C ([.mem R] ++ (Olds ++ ps))}
    (hc : FunContract (CallRet.mem (Γ := Γ) R r hd hm) body req ens m)
    (hμ : Prog.withinM μ body = true) (hw : writesRets 1 body = true) {σ : State C Γ}
    (hpre : holds σ (Fml.callPre args req m))
    (hpost : holds σ (Fml.callPostM μ args R r ens ω κ φ m)) :
    holds σ (.modal m (.cons (.call f args (.mem R r hd hm) body) ω) κ φ) := by
  obtain ⟨hpe, hpa⟩ := holds_callPre hpre
  rw [holds_modal_iff, Prog.runSt_cons]
  show m.afterRunTR _ ((((TRun.call args (.mem R r hd hm) body.ext body.runR σ).map
    (·.st)).bind _).bind _)
  rw [TRun.call_eq]
  cases hA : args.evalT σ with
  | error e => exact ⟨(hpe e hA).1, fun hp => (hpe e hA).2 (by cases hp; rfl)⟩
  | ok a =>
    have hct := hc _ (hpa a hA)
    show m.afterRunTR _ (((Except.map (·.st) (TRun.callFrom (.mem R r hd hm) body.ext
      body.runR σ ((CallRet.mem (Γ := Γ) R r hd hm).enterT (σ.withEnv a)))).bind _).bind _)
    unfold TRun.callFrom
    cases hB : body.runR ((CallRet.mem (Γ := Γ) R r hd hm).enterT (σ.withEnv a)).st with
    | error e =>
      rw [show Prog.run _ body = body.runR _ from rfl, hB] at hct
      exact ⟨hct.1, fun hp => hct.2 (by cases hp; rfl)⟩
    | ok o =>
      rw [show Prog.run _ body = body.runR _ from rfl, hB] at hct
      obtain ⟨hg, hag⟩ := Prog.run_frameM body hμ 0 hB
      have e₀ : σ.H <+: o.st.H :=
        ((CallRet.mem (Γ := Γ) R r hd hm).enterT (σ.withEnv a)).ext.trans o.ext
      have hfr : TGFrameM μ σ o.st e₀ := ((TGFrameM.env σ a (List.prefix_refl _)).trans
        (CallRet.enterT_frameM (μ := μ) (CallRet.mem (Γ := Γ) R r hd hm) (σ.withEnv a))
        ((CallRet.mem (Γ := Γ) R r hd hm).enterT (σ.withEnv a)).ext).trans hg e₀
      have hX := holds_snapOld ((holds_declsThen hpost).2 a hA)
      have hX' : holds ((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc o.st.storage o.st.net)
          (Fml.callResultM R r ens ω κ φ m) := by
        cases μ with
        | nonpayable => exact hX o.st.storage o.st.net
        | pure =>
          obtain ⟨h1, h2⟩ := hfr.keepsSt (by decide)
          rw [h1, h2]; exact hX
        | view =>
          obtain ⟨h1, h2⟩ := hfr.keepsSt (by decide)
          rw [h1, h2]; exact hX
      have hY := hX' ⟨e₀, o.st.heap, ()⟩ hfr.keeps (TEnv.drop body.ext o.st.env).1
      -- the parameters as the callee was entered with them, weakened
      have hps : (TEnv.drop body.ext o.st.env : TEnv C o.st.H (.mem R :: ps)).2 =
          TEnv.wk e₀ ps a := by
        rw [TLocAgreeM.params_eq (e := ((CallRet.mem (Γ := Γ) R r hd hm).enterT
          (σ.withEnv a)).st.env) hag hw]
        exact TEnv.wk_trans _ _ ps a
      have hst : State.thin (Thin.atop (.mem R :: (Olds ++ ps)) Γ)
          ((((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc o.st.storage o.st.net).adopt
            (⟨e₀, o.st.heap, ()⟩ : Grown σ.H fun _ => Unit)).1.push (t := .mem R) (TEnv.drop body.ext o.st.env).1) =
          State.withOlds [.mem R] (σ.withEnv a).net (σ.withEnv a).storage
            (State.drop body.ext o.st) := by
        refine State.ext' rfl rfl HEq.rfl (heq_of_eq ?_) rfl hfr.selfBalance.symm hfr.tx.symm
        show ((TEnv.drop body.ext o.st.env).1, TEnv.thin (Thin.atop (Olds ++ ps) Γ)
          (TEnv.wk e₀ (Olds ++ (ps ++ Γ))
            (TEnv.olds σ.net σ.storage (TEnv.append ps a σ.env)))) =
          ((TEnv.drop body.ext o.st.env).1, TEnv.olds σ.net σ.storage
            (TEnv.drop body.ext o.st.env : TEnv C o.st.H (.mem R :: ps)).2)
        rw [hps]
        show (_, TEnv.olds σ.net σ.storage (TEnv.thin (Thin.atop ps Γ)
          (TEnv.wk e₀ (ps ++ Γ) (TEnv.append ps a σ.env)))) = _
        rw [TEnv.append_wk, TEnv.thin_atop_append]
      have hens' := holds_wkD (Thin.atop (.mem R :: (Olds ++ ps)) Γ) ens _ (by rw [hst]; exact hct.1)
      have hM := hY hens'
      rw [holds_modal_iff] at hM
      dsimp only [bind, Except.bind, Except.map, pure, Except.pure]
      have hT : State.thin (.keep (Thin.ofExt (Ext.append Γ (Olds ++ ps))))
          ((((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc o.st.storage o.st.net).adopt
            (⟨e₀, o.st.heap, ()⟩ : Grown σ.H fun _ => Unit)).1.push (t := .mem R) (TEnv.drop body.ext o.st.env).1) =
          o.st.withEnv (CallRet.leaveT (TEnv.wk e₀ Γ σ.env) (CallRet.mem R r hd hm)
            (TEnv.take [.mem R] (TEnv.drop body.ext o.st.env))) := by
        refine State.ext' rfl rfl HEq.rfl (heq_of_eq ?_) rfl hfr.selfBalance.symm hfr.tx.symm
        show ((TEnv.drop body.ext o.st.env).1, TEnv.thin (Thin.ofExt (Ext.append Γ (Olds ++ ps)))
          (TEnv.wk e₀ (Olds ++ (ps ++ Γ))
            (TEnv.olds σ.net σ.storage (TEnv.append ps a σ.env)))) =
          ((TEnv.drop body.ext o.st.env).1, TEnv.wk e₀ Γ σ.env)
        rw [TEnv.thin_ofExt]
        show (_, TEnv.drop (Ext.append Γ ps) (TEnv.wk e₀ (ps ++ Γ) (TEnv.append ps a σ.env))) = _
        rw [TEnv.append_wk, TEnv.drop_append]
      simp only [Prog.runSt_nil, Except.bind, Frames.runSt_drop, Frames.runSt_seq, hT] at hM
      exact hM

end Sound

end Solidity
