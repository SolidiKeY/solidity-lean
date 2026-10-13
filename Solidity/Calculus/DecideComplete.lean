import Solidity.Calculus.DecideTyped
import Solidity.Calculus.MemRead
import Solidity.Calculus.Symex

/-!
# `sol_decide` on a scoped leaf

`sol_decide` proves `⊨ φ` for a leaf whose modalities are gone (after
`sol_symex`): the leaf reduced by position (`Fml.reduceS`,
`Calculus/DecideScoped.lean`), computed by compiled code and quoted back,
the kernel checking the equation (`Valid.of_reduceS`); then the reduction,
a typed first-order formula over the starting state (`LFml`,
`Calculus/DecideLang.lean`), closed.
-/

namespace Solidity

namespace Decide

open Lean Elab Tactic Meta

variable {C : Contract}

/-- **A leaf the closer closes is valid**: its reduction closed
(`LFml.close`, `Calculus/Closer.lean`), the kernel evaluating both. -/
theorem _root_.Solidity.Valid.of_close {φ : Fml C []}
    (h : (φ.toLS true SymS.init).map LFml.decideMem = some true) : Valid φ := by
  rw [Option.map_eq_some_iff] at h
  obtain ⟨ψ, hψ, hc⟩ := h
  exact Valid.of_toLS hψ (LFml.decideMem_valid hc)

/-- The reduction quoted at the contract `c`, and printed. -/
def LFml.quoteOpt (c : Expr) : Option (LFml C) → Option (Expr × String)
  | some ψ => some ((ψ.quote).run c, ψ.pp)
  | none => none

/-- The reduction of the closed leaf `φ` of the contract `C` (a constant),
computed by compiled code: quoted and printed, `none` outside the
fragment. -/
def reduceExpr (C φ : Expr) : MetaM (Option (Expr × String)) := do
  let some n := C.constName? | throwError "sol_decide: the contract is not a constant"
  let φ ← Symex.evaluable φ
  let e := mkApp3 (mkConst ``LFml.quoteOpt) C (quoteConstName n) (mkApp2 (mkConst ``Fml.reduceS) C φ)
  unsafe evalExpr (Option (Expr × String))
    (mkApp (mkConst ``Option [0]) (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Expr) (mkConst ``String))) e

/-- The leaf `Valid φ` as `LFml.Valid ψ`, `ψ` its reduction computed and
quoted: `Valid.of_reduceS (Eq.refl _)`, the kernel checking the
reduction. -/
def reduceScoped (g : MVarId) (C φ : Expr) : MetaM (MVarId × String) := do
  if φ.hasFVar || φ.hasMVar then throwError "sol_decide: the leaf has free variables"
  let some (ψ, s) ← reduceExpr C φ | throwError "sol_decide: the leaf is outside the fragment"
  let ψ := ShareCommon.shareCommon ψ
  let lty := mkApp (mkConst ``LFml) C
  let some_ψ := mkApp2 (mkConst ``Option.some [0]) lty ψ
  let h := mkApp2 (mkConst ``Eq.refl [1]) (mkApp (mkConst ``Option [0]) lty) some_ψ
  let g' ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``LFml.Valid) C ψ) (← g.getTag)
  g.assign (mkAppN (mkConst ``Valid.of_reduceS) #[C, φ, ψ, h, g'])
  return (g'.mvarId!, s)

/-- `b = true` for a closed `Bool` term `b`, checked by the kernel. -/
def trueLemma (b : Expr) : MetaM Expr := do
  Derive.kernelLemma (← mkEq b (mkConst ``Bool.true)) (← mkEqRefl (mkConst ``Bool.true))

/-- `sol_reduce`: the leaf `⊨ φ` as `LFml.Valid ψ`, its reduction. -/
elab "sol_reduce" : tactic => withMainContext do
  let g ← getMainGoal
  let some (C, φ) ← Symex.validGoal? g | throwError "sol_reduce: expected `⊨ φ`"
  let (g', _) ← reduceScoped g C φ
  replaceMainGoal [g']

/-- `sol_reduce?`: `sol_reduce`, the reduction printed. -/
elab "sol_reduce?" : tactic => withMainContext do
  let g ← getMainGoal
  let some (C, φ) ← Symex.validGoal? g | throwError "sol_reduce: expected `⊨ φ`"
  let (g', s) ← reduceScoped g C φ
  logInfo s
  replaceMainGoal [g']

/-- `φ.toLS true SymS.init`, as an expression. -/
def toLSInit (C φ : Expr) : Expr :=
  mkAppN (mkConst ``Fml.toLS) #[C, mkConst ``List.nil [0] |>.app (mkConst ``LTy), mkConst ``Bool.true,
    mkApp (mkConst ``SymS.init) C, φ]

/-- The closer on the leaf `φ` of the contract `C`, computed by compiled
code: `none` outside the fragment. -/
def closeExpr (C φ : Expr) : MetaM (Option Bool) := do
  let φ ← Symex.evaluable φ
  let e := mkApp4 (mkConst ``Option.map [0, 0]) (mkApp (mkConst ``LFml) C) (mkConst ``Bool)
    (mkApp (mkConst ``LFml.decideMem) C) (toLSInit C φ)
  unsafe evalExpr (Option Bool) (mkApp (mkConst ``Option [0]) (mkConst ``Bool)) e

/-- The leaf `Valid φ` closed by the closer (`Valid.of_close`), the kernel
evaluating the reduction and the closer once; `false` where the closer
does not close it. -/
def closeScoped (g : MVarId) (C φ : Expr) : MetaM Bool := do
  match ← closeExpr C φ with
  | none => throwError "sol_decide: the leaf is outside the fragment"
  | some false => return false
  | some true =>
    let ob := mkApp (mkConst ``Option [0]) (mkConst ``Bool)
    let lhs := mkApp4 (mkConst ``Option.map [0, 0]) (mkApp (mkConst ``LFml) C) (mkConst ``Bool)
      (mkApp (mkConst ``LFml.decideMem) C) (toLSInit C φ)
    let rhs := mkApp2 (mkConst ``Option.some [0]) (mkConst ``Bool) (mkConst ``Bool.true)
    let h ← Derive.kernelLemma (mkApp3 (mkConst ``Eq [1]) ob lhs rhs)
      (mkApp2 (mkConst ``Eq.refl [1]) ob rhs)
    g.assign (mkApp3 (mkConst ``Valid.of_close) C φ h)
    return true

/-- `sol_decide_finish`: the reduction's goal `LFml.Valid ψ` closed by
unfolding and arithmetic. -/
syntax (name := tacticSol_decide_finish) "sol_decide_finish" : tactic

macro_rules
  | `(tactic| sol_decide_finish) => `(tactic| fail "sol_decide: the closer does not close the leaf")

/-- **`sol_decide`**: a leaf `⊨ φ` with no modality left (after
`sol_symex`) reduced by position (`Fml.reduceS`) and closed by the closer
(`LFml.close`, `Calculus/Closer.lean`), the kernel evaluating both; where
the closer does not close it, the reduction quoted (`sol_reduce`) and
finished by `sol_decide_finish`. -/
syntax (name := tacticSol_decide) "sol_decide" : tactic

@[tactic tacticSol_decide]
def evalSolDecide : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let some (C, φ) ← Symex.validGoal? g | throwError "sol_decide: expected `⊨ φ`"
  Symex.reporting g do
    if ← closeScoped g C φ then
      replaceMainGoal []
    else
      let (g', _) ← reduceScoped g C φ
      replaceMainGoal [g']
      evalTactic (← `(tactic| sol_decide_finish))

/-- `sol_decide_close`: the leaf closed by the closer alone. -/
elab "sol_decide_close" : tactic => withMainContext do
  let g ← getMainGoal
  let some (C, φ) ← Symex.validGoal? g | throwError "sol_decide_close: expected `⊨ φ`"
  unless ← closeScoped g C φ do throwError "sol_decide_close: the closer does not close the leaf"
  replaceMainGoal []

end Decide

end Solidity
