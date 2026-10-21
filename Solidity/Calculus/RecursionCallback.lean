import Solidity.Calculus.Recursion
import Solidity.Calculus.CallbackDerive

/-!
# Recursive calls under the callback reading

`docs/kernel-port.md`, "Recursion", row "Callbacks (O7)".  A recursive
call's body is its unrolling (`recUnroll`), so whether it calls back
(`Stmt.callsBack`, `Semantics/Callback.lean`) is read off its frames.  Every
frame is the same body with the recursive site a hole, so it is read off one
frame (`Prog.callsBack_recUnroll`), the frame below by hypothesis:
`sol_no_callback` proves `φ.callsBack pay = false` so, never forcing the
`recDepth` frames.  A recursion that does not call back is then read without
callbacks (`validT_noCallback_iff`), where `rec_auto` proves it.
-/

namespace Solidity

open Solidity (Modality Mutability)

variable {C : Contract}

/-! ## `callsBack` by constructor

The equations `sol_no_callback` rewrites with: one per constructor, so that
`simp` never unfolds a definition at a term that is not one (an invariant
`I.fml`, an unrolling). -/

section Eqns

variable {pay : Bool} {Γ Γ₀ : Ctx}

theorem Prog.callsBack_nil : Prog.callsBack pay (.nil : Prog C Γ Γ) = false := rfl

theorem Fml.callsBack_tt : (Fml.tt : Fml C Γ).callsBack pay = false := rfl
theorem Fml.callsBack_not (φ : Fml C Γ) : (Fml.not φ).callsBack pay = φ.callsBack pay := rfl
theorem Fml.callsBack_upd {Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ) :
    (Fml.upd m U φ).callsBack pay = φ.callsBack pay := rfl
theorem Fml.callsBack_havoc (φ : Fml C Γ) : (Fml.havoc φ).callsBack pay = φ.callsBack pay := rfl
theorem Fml.callsBack_all (x : Var) (p : PrimTy) (φ : Fml C (.val p :: Γ)) :
    (Fml.all x p φ).callsBack pay = φ.callsBack pay := rfl
theorem Fml.callsBack_bind (m : Modality) (x : Var) (t : LTy) (φ : Fml C (t :: Γ)) :
    (Fml.bind m x t φ).callsBack pay = φ.callsBack pay := rfl
theorem Fml.callsBack_anon (xs : List ((t : LTy) × Idx Γ t)) (φ : Fml C Γ) :
    (Fml.anon xs φ).callsBack pay = φ.callsBack pay := rfl
theorem Fml.callsBack_closedAt (I : Fml C []) :
    (Fml.closedAt I : Fml C Γ).callsBack pay = I.callsBack pay := rfl

theorem Frames.callsBack_nil : (Frames.nil : Frames C Γ Γ).callsBack pay = false := rfl
theorem Frames.callsBack_pop {Γ' : Ctx} (b : BlockKind) (h : Ext Γ Γ') (κ : Frames C Γ Γ₀) :
    (Frames.pop b h κ).callsBack pay = κ.callsBack pay := rfl
theorem Frames.callsBack_drop {Γ' : Ctx} (h : Thin Γ Γ') (κ : Frames C Γ Γ₀) :
    (Frames.drop h κ).callsBack pay = κ.callsBack pay := rfl

theorem Hyps.wrap_nil' (φ : Fml C Γ₀) : (Hyps.nil : Hyps C Γ₀ Γ₀).wrap φ = φ := rfl
theorem Hyps.wrap_pre' (H : Hyps C Γ₀ Γ) (a φ : Fml C Γ) : (H.pre a).wrap φ = H.wrap (.imp a φ) :=
  rfl
theorem Hyps.wrap_upd' {Δ : Ctx} (H : Hyps C Γ₀ Γ) (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ) :
    (H.upd m U).wrap φ = H.wrap (.upd m U φ) := rfl
theorem Hyps.wrap_havoc' (H : Hyps C Γ₀ Γ) (φ : Fml C Γ) : H.havoc.wrap φ = H.wrap (.havoc φ) :=
  rfl
theorem Hyps.wrap_all' (H : Hyps C Γ₀ Γ) (x : Var) (p : PrimTy) (φ : Fml C (.val p :: Γ)) :
    (H.all x p).wrap φ = H.wrap (.all x p φ) := rfl
theorem Hyps.wrap_bind' (H : Hyps C Γ₀ Γ) (m : Modality) (x : Var) (t : LTy) (φ : Fml C (t :: Γ)) :
    (H.bind m x t).wrap φ = H.wrap (.bind m x t φ) := rfl
theorem Hyps.wrap_anon' (H : Hyps C Γ₀ Γ) (xs : List ((t : LTy) × Idx Γ t)) (φ : Fml C Γ) :
    (H.anon xs).wrap φ = H.wrap (.anon xs φ) := rfl

end Eqns

/-- **A recursive call that does not call back**, read without callbacks
(`ProvesC.recCall`, no goal): where nothing in the sequent calls back, the
two readings agree (`holdsC_iff_holds`), and `rec_auto` proves it `Valid`. -/
theorem ProvesC.recValid {I : Fml C []} {pay : Bool} {Γ Γ' ps rs Γ₁ Γ₂ : Ctx} {H : Hyps C [] Γ}
    {m : Modality} {f : Name} {d : Nat} {args : Args C Γ ps} {ret : CallRet Γ rs Γ'}
    {body : Unit → Prog C (rs ++ ps) (rs ++ ps)} {ω : Prog C Γ' Γ₁} {κ : Frames C Γ₁ Γ₂}
    {φ : Fml C Γ₂}
    (h : Valid (H.wrap (.modal m (.cons (.callRec f d args ret body) ω) κ φ)))
    (hφ : (H.wrap (.modal m (.cons (.callRec f d args ret body) ω) κ φ)).callsBack pay = false) :
    ProvesC I pay [] H (.modal m (.cons (.callRec f d args ret body) ω) κ φ) :=
  .recCall [] (fun τ _ => (holdsC_iff_holds _ hφ τ).2 (h τ)) nofun

namespace RecursionCallback

open Lean Elab Tactic Meta

/-- Whether `e` mentions an unrolling (`recUnroll`). -/
def hasUnroll (e : Expr) : Bool := (e.find? (·.isConstOf ``recUnroll)).isSome

/-- `X.callsBack pay = false` (or `hasTransfer`): the formula's statements by
`simp`, a recursive call's body frame by frame (`Prog.callsBack_recUnroll`,
the frame below by the hypothesis `ih`), what is left by `rfl` where no
unrolling is left in it. -/
partial def proveNoCallback (g : MVarId) (fuel : Nat := 32) : TacticM Bool := g.withContext do
  if fuel == 0 then return false
  let simpT ← `(tactic| simp only [Hyps.wrap_nil', Hyps.wrap_pre', Hyps.wrap_upd',
      Hyps.wrap_havoc', Hyps.wrap_all', Hyps.wrap_bind', Hyps.wrap_anon', Fml.modalK_nil,
      Fml.modalK_cons, Frames.exit_nil, Frames.exit_seq, Frames.exit_pop, Fml.callsBack_tt,
      Fml.callsBack_not, Fml.callsBack_and,
      Fml.callsBack_imp, Fml.callsBack_upd, Fml.callsBack_modal, Fml.callsBack_havoc,
      Fml.callsBack_all, Fml.callsBack_bind, Fml.callsBack_anon, Fml.callsBack_closedAt,
      Invariant.noCallsBack, Frames.callsBack_nil, Frames.callsBack_seq, Frames.callsBack_pop,
      Frames.callsBack_drop, Prog.callsBack_cons, Prog.callsBack_nil, Stmt.callsBack,
      CallbackWk.callsBack_prog, Bool.or_false, Bool.false_or, Bool.or_self, *])
  let gs ← match ← Recursion.tryOn g (evalTactic simpT) with
    | some gs => pure gs
    | none => pure [g]
  for g' in gs do
    let ty ← instantiateMVars (← g'.getType)
    unless hasUnroll ty do
      if let some [] ← Recursion.tryOn g' (evalTactic (← `(tactic| rfl))) then continue
      return false
    -- an unrolling: no frame calls back where none of one frame does
    let some gs' ← Recursion.tryOn g' (evalTactic (← `(tactic| rw [Prog.callsBack_recUnroll])))
      | return false
    for g'' in gs' do
      let ty ← instantiateMVars (← g''.getType)
      let g'' ← if ty.isForall then do
          let some [g₃] ← Recursion.tryOn g'' (evalTactic (← `(tactic| intro n t ih)))
            | return false
          pure g₃
        else pure g''
      unless ← proveNoCallback g'' (fuel - 1) do return false
  return true

end RecursionCallback

open Lean Elab Tactic Meta in
/-- `sol_no_callback`: `φ.callsBack pay = false` (`Fml.callsBack`, through
the context `Hyps.wrap`), a recursive call's unrolling read off one frame
(`Prog.callsBack_recUnroll`). -/
elab "sol_no_callback" : tactic => do
  let g ← getMainGoal
  unless ← RecursionCallback.proveNoCallback g do
    throwError "sol_no_callback: a statement may call back{indentExpr (← g.getType)}"
  setGoals ((← getGoals).filter (· != g))

end Solidity
