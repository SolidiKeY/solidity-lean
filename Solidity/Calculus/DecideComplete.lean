import Solidity.Calculus.DecideCleanTail
import Solidity.Calculus.Symex

/-!
# `sol_decide` on a scoped leaf

`sol_decide` proves `⊨ φ` for a leaf whose modalities are gone (after
`sol_symex`): its updates pushed in by position (`Fml.toLS`,
`Calculus/DecideScoped.lean`), the reads of writes eliminated under the
premises (`LFml.elimF`), memory read and the result closed by the closer
(`LFml.decideMem`), within the closer's bounds (`Seq.checkCore`:
`Seq.closeSize`, `Seq.stackSize`, or `concreteSize` and `concreteDepth`
where every storage history is concrete, `LFml.boundsOk`), all of it
evaluated once by the kernel
(`Seq.checkCore_valid`).  Where the closer does not close it, or the leaf
is past the bounds, it fails; `sol_reduce?` shows the reduction
(`Fml.reduceS`, `Valid.of_reduceS`).
-/

namespace Solidity

namespace Seq

open Decide

variable {C : Contract}

/-- The most nodes the closer takes in a leaf's formula with its updates
pushed in, counted as a tree (`LFml.fits`).  A storage written from a read
of the one before it appears twice in the next, so this tree doubles with
each such write.  It is the cheap first test: computing the reduction of a
leaf far past it would itself be slow. -/
def closeSize : Nat := normalizationSize

/-- The most storage updates one term of a leaf stacks, with its updates
pushed in and before the elimination (`LFml.stDepth`): the elimination
reads each through the ones below it, so its size grows with each.  A
bound on the stack, not on the elimination's nodes: the kernel would
build the elimination twice to count it. -/
def stackSize : Nat := normalizationDepth

/-- **The scoped closer on a leaf `ψ` of no modality**: `none` where the
reduction does not read it; else whether it closes it: within `closeSize`
nodes and within `stackSize` storage updates on the same pushed-in leaf,
or `concreteSize` and `concreteDepth` where its histories are concrete
(`LFml.boundsOk`, tested before the elimination), and closed by
`LFml.decideMem`. -/
def checkCore (ψ : Fml C []) : Option Bool :=
  (ψ.toLS true SymS.init).map fun l =>
    l.boundsOk && bif ψ.assumesCT then l.decideMemCT else l.decideMem

/-- What `checkCore` closes is valid: `Valid.of_toLS` and
`LFml.decideMem_valid`; under the premise `cleanTail(storage) = true`,
`LFml.decideMemCT_holds` where the storage shows clean tails and
`Fml.assumesCT_holds` where it does not. -/
theorem checkCore_valid {ψ : Fml C []} (h : checkCore ψ = some true) : Valid ψ := by
  simp only [checkCore, Option.map_eq_some_iff, Bool.and_eq_true] at h
  obtain ⟨l, hl, -, hc⟩ := h
  cases hct : ψ.assumesCT
  · rw [hct, cond_false] at hc
    exact Valid.of_toLS hl (LFml.decideMem_valid hc)
  · rw [hct, cond_true] at hc
    intro τ
    by_cases hg : TSto.CleanTails τ.storage.obs
    · exact (Fml.toLS_sound ψ true hl τ AEnv.dflt (Agrees.init τ AEnv.dflt)
        SymS.Fresh.init).1 rfl (LFml.decideMemCT_holds hc τ AEnv.dflt hg)
    · exact Fml.assumesCT_holds ψ hct τ hg

/-- `checkCore`'s bounds alone (`LFml.boundsOk`): `none` where the
reduction does not read the leaf; else whether it is within `closeSize` and
`stackSize`, or the concrete tier. -/
def fitsCore (ψ : Fml C []) : Option Bool :=
  (ψ.toLS true SymS.init).map fun l => l.boundsOk

end Seq

namespace Decide

open Lean Elab Tactic Meta

variable {C : Contract}

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

/-- `f C φ : Option Bool` of the leaf `φ` of the contract `C`, computed by
compiled code. -/
def evalCore (f : Lean.Name) (C φ : Expr) : MetaM (Option Bool) := do
  let φ ← Symex.evaluable φ
  unsafe evalExpr (Option Bool) (mkApp (mkConst ``Option [0]) (mkConst ``Bool))
    (mkApp2 (mkConst f) C φ)

/-- The closer on the leaf `φ` of the contract `C` within its bounds
(`Seq.checkCore`), computed by compiled code: `none` outside the
fragment. -/
def closeExpr (C φ : Expr) : MetaM (Option Bool) := evalCore ``Seq.checkCore C φ

/-- The leaf `Valid φ` closed by the closer (`Seq.checkCore_valid`), the
kernel evaluating the reduction and the closer once; `false` where the
closer does not close it, an error past its bounds. -/
def closeScoped (g : MVarId) (C φ : Expr) : MetaM Bool := do
  match ← closeExpr C φ with
  | none => throwError "sol_decide: the leaf is outside the fragment"
  | some false =>
    if (← evalCore ``Seq.fitsCore C φ) == some false then
      throwError "sol_decide: the leaf is past the closer's bounds (`Seq.closeSize` nodes, \
        `Seq.stackSize` storage updates; `concreteSize`, `concreteDepth` for a concrete history)"
    return false
  | some true =>
    let ob := mkApp (mkConst ``Option [0]) (mkConst ``Bool)
    let lhs := mkApp2 (mkConst ``Seq.checkCore) C φ
    let rhs := mkApp2 (mkConst ``Option.some [0]) (mkConst ``Bool) (mkConst ``Bool.true)
    let h ← Derive.kernelLemma (mkApp3 (mkConst ``Eq [1]) ob lhs rhs)
      (mkApp2 (mkConst ``Eq.refl [1]) ob rhs)
    g.assign (mkApp3 (mkConst ``Seq.checkCore_valid) C φ h)
    return true

/-- **`sol_decide`**: a leaf `⊨ φ` with no modality left (after
`sol_symex`) reduced by position (`Fml.toLS`) and closed by the closer
(`LFml.decideMem`, `Calculus/Closer.lean`) within its bounds
(`Seq.checkCore`), the kernel evaluating both; it fails where the closer
does not close the leaf (`sol_reduce?` shows the reduction). -/
syntax (name := tacticSol_decide) "sol_decide" : tactic

@[tactic tacticSol_decide]
def evalSolDecide : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let some (C, φ) ← Symex.validGoal? g | throwError "sol_decide: expected `⊨ φ`"
  Symex.reporting g do
    unless ← closeScoped g C φ do throwError "sol_decide: the closer does not close the leaf"
    replaceMainGoal []

/-- `sol_decide_close`: the leaf closed by the closer alone. -/
elab "sol_decide_close" : tactic => withMainContext do
  let g ← getMainGoal
  let some (C, φ) ← Symex.validGoal? g | throwError "sol_decide_close: expected `⊨ φ`"
  unless ← closeScoped g C φ do throwError "sol_decide_close: the closer does not close the leaf"
  replaceMainGoal []

end Decide

end Solidity
