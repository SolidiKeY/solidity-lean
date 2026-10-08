import Solidity.Calculus.Core.Symex
import Solidity.Calculus.Core.Close

/-!
# The scoped strategy as one kernel evaluation: `sol_prove`

`Derive.lean`'s `sol_prove` on a goal `Core.Valid φ`: the scoped strategy
runs to its end (`Core.symex`), what it leaves is erased (`Fml.erase`) and
handed to today's closer (`Derive.proves`, `Calculus/Closer.lean`), the
erasure being enough where `Fml.posB` takes the leaf (`Valid.of_erase`).
The kernel checks it as one evaluation, `Derive.proves φ = true`
(`Valid.of_proves`): the strategy, the check and the closer, with no term
quoted back.

Where the closer leaves goals, `sol_prove` computes today's residue of the
erasure (`Derive.residue`) and leaves one goal per leaf, `leaf1`, `leaf2`,
… , each a sequent of today's calculus, closed by today's tactics
(`Valid.of_residue`).

There is no search, so `sol_prove` is its own replay; the fuel of the
strategy (`fuel`) and the closer's budget (`Derive.budget`) bound the
compiled run before the kernel sees it.
-/

namespace Solidity.Core

open Solidity (Modality)

variable {C : Contract}

namespace Derive

/-- The steps `sol_prove` gives the scoped strategy. -/
def fuel : Nat := 5000

/-- A leaf left by the strategy is closed: taken by `Fml.posB`, its erasure
proved by today's closer. -/
def closes (ψ : Fml C []) : Bool :=
  (ψ.posB []).isSome && Solidity.Derive.proves [] (ψ.erase [])

/-- **`sol_prove`'s check**: the strategy run to its end, and what it leaves
closed. -/
def proves (φ : Fml C []) : Bool := closes (symex fuel φ)

end Derive

/-- What `Derive.closes` accepts is valid. -/
theorem Valid.of_closes {ψ : Fml C []} (h : Derive.closes ψ = true) : Valid ψ := by
  simp only [Derive.closes, Bool.and_eq_true] at h
  exact Valid.of_erase h.1 (Solidity.Proves.valid (Solidity.Proves.of_proves h.2))

/-- **`sol_prove`'s proof when nothing is left.** -/
theorem Valid.of_proves (hS : Stmt.SoundNC C) {φ : Fml C []} (h : Derive.proves φ = true) :
    Valid φ :=
  symex_valid hS Derive.fuel (Valid.of_closes h)

/-- **`sol_prove`'s proof when leaves are left**: today's residue of the
erasure, each leaf proved. -/
theorem Valid.of_residue (hS : Stmt.SoundNC C) {φ : Fml C []}
    (hp : ((symex Derive.fuel φ).posB []).isSome = true)
    {ls : List (Solidity.Derive.Leaf C)} {b' : Nat}
    (h : Solidity.Derive.residue Solidity.Derive.budget Solidity.Derive.synClose
      Solidity.Derive.budget [] ((symex Derive.fuel φ).erase []) = some (ls, b'))
    (hl : ∀ l ∈ ls, Solidity.Proves .all l.1 l.2) : Valid φ :=
  symex_valid hS Derive.fuel
    (Valid.of_erase hp (Solidity.Proves.valid (Solidity.Proves.of_synResidue h hl)))

/-! ## The tactic -/

namespace Derive

open Lean Elab Tactic Meta

/-- The residue of the erasure of what the strategy leaves of `φ`, quoted
(`Derive.residueQuote`), when the leaf is taken by `Fml.posB`. -/
def residueQuoteC (c : Lean.Expr) (φ : Fml C []) :
    Option (List (Lean.Expr × Lean.Expr) × Nat) :=
  let ψ := symex fuel φ
  if (ψ.posB []).isSome then Solidity.Derive.residueQuote c [] (ψ.erase []) else none

/-- `sol_prove` on the scoped goal `g`, `Core.Valid φ`: the goals it leaves,
one per leaf of today's residue. -/
def prove (g : MVarId) (C φ : Expr) : MetaM (List MVarId) := do
  let some n := C.constName? | throwError "sol_prove: the contract is not a named constant"
  if φ.hasFVar || φ.hasMVar then
    throwError "sol_prove: the formula mentions a local hypothesis or a metavariable"
  let sound := mkApp (mkConst Symex.soundName) C
  let φe ← Symex.evaluable φ
  let bool := mkConst ``Bool
  -- the kernel first: compiling the check of a formula with no code of its
  -- own costs about as much as the kernel's evaluation
  let type := mkApp3 (mkConst ``Eq [1]) bool (mkApp2 (mkConst ``proves) C φ) (mkConst ``Bool.true)
  if let some h ← (some <$> Solidity.Derive.kernelLemma type
      (mkApp2 (mkConst ``Eq.refl [1]) bool (mkConst ``Bool.true))) <|> pure none then
    g.assign (mkApp4 (mkConst ``Valid.of_proves) C sound φ h)
    return []
  let resTy := mkApp (mkConst ``Option [0]) (mkApp2 (mkConst ``Prod [0, 0])
    (mkApp (mkConst ``List [0])
      (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Expr) (mkConst ``Expr)))
    (mkConst ``Nat))
  let some (leaves, left) ← unsafe evalExpr (Option (List (Expr × Expr) × Nat)) resTy
      (mkAppN (mkConst ``residueQuoteC) #[C, quoteConstName n, φe])
    | throwError "sol_prove: the strategy leaves a formula the erasure does not close \
        (`Fml.posB`), or today's closer takes more than {Solidity.Derive.budget} steps"
  let ψ := mkAppN (mkConst ``symex) #[C, mkApp (mkConst ``List.nil [0]) (mkConst ``LTy),
    mkConst ``fuel, φ]
  let hpTy := mkApp3 (mkConst ``Eq [1]) bool
    (mkApp2 (mkConst ``Option.isSome [0]) (mkApp (mkConst ``List [0]) (mkConst ``Var))
      (mkAppN (mkConst ``Fml.posB) #[C, mkApp (mkConst ``List.nil [0]) (mkConst ``LTy), ψ,
        mkApp (mkConst ``List.nil [0]) (mkConst ``Var)]))
    (mkConst ``Bool.true)
  let hp ← try Solidity.Derive.kernelLemma hpTy (mkApp2 (mkConst ``Eq.refl [1]) bool (mkConst ``Bool.true))
    catch e => throwError "sol_prove: the kernel rejects the check of the leaf:{indentD e.toMessageData}"
  let hyp := mkApp (mkConst ``Solidity.Hyp) C
  let leafTy := mkApp2 (mkConst ``Prod [0, 0]) (mkApp (mkConst ``List [0]) hyp)
    (mkApp (mkConst ``Solidity.Fml) C)
  let mkLeaf (Γ' φ' : Expr) : Expr :=
    mkAppN (mkConst ``Prod.mk [0, 0]) #[mkApp (mkConst ``List [0]) hyp,
      mkApp (mkConst ``Solidity.Fml) C, Γ', φ']
  let ls ← mkListLit leafTy (leaves.map fun (Γ', φ') => mkLeaf Γ' φ')
  let pairTy := mkApp2 (mkConst ``Prod [0, 0]) (mkApp (mkConst ``List [0]) leafTy) (mkConst ``Nat)
  let someLs := mkApp2 (mkConst ``Option.some [0]) pairTy
    (mkAppN (mkConst ``Prod.mk [0, 0]) #[mkApp (mkConst ``List [0]) leafTy, mkConst ``Nat, ls,
      mkRawNatLit left])
  let erased := mkAppN (mkConst ``Fml.erase) #[C, mkApp (mkConst ``List.nil [0]) (mkConst ``LTy),
    mkApp (mkConst ``List.nil [0]) (mkConst ``Var), ψ]
  let type := mkApp3 (mkConst ``Eq [1]) (mkApp (mkConst ``Option [0]) pairTy)
    (mkAppN (mkConst ``Solidity.Derive.residue) #[C, mkConst ``Solidity.Derive.budget,
      mkApp (mkConst ``Solidity.Derive.synClose) C, mkConst ``Solidity.Derive.budget,
      mkApp (mkConst ``List.nil [0]) hyp, erased]) someLs
  let rfl' := mkApp2 (mkConst ``Eq.refl [1]) (mkApp (mkConst ``Option [0]) pairTy) someLs
  let h ← try Solidity.Derive.kernelLemma type rfl'
    catch e => throwError "sol_prove: the kernel rejects the residue:{indentD e.toMessageData}"
  let mut goals : Array MVarId := #[]
  let mut proofs : Array Expr := #[]
  for (Γ', φ') in leaves, i in [1:leaves.length + 1] do
    let gi ← mkFreshExprSyntheticOpaqueMVar
      (mkAppN (mkConst ``Solidity.Proves) #[C, mkConst ``RuleSet.all, Γ', φ'])
      (Name.mkSimple s!"leaf{i}")
    goals := goals.push gi.mvarId!
    proofs := proofs.push gi
  let mut hl := mkApp (mkConst ``Solidity.Derive.leaves_nil) C
  let mut rest := mkApp (mkConst ``List.nil [0]) leafTy
  for (Γ', φ') in leaves.reverse, p in proofs.reverse do
    hl := mkAppN (mkConst ``Solidity.Derive.leaves_cons) #[C, Γ', φ', rest, p, hl]
    rest := mkAppN (mkConst ``List.cons [0]) #[leafTy, mkLeaf Γ' φ', rest]
  g.assign (mkAppN (mkConst ``Valid.of_residue) #[C, sound, φ, hp, ls, mkRawNatLit left, h, hl])
  return goals.toList

end Derive

open Lean Elab Tactic Meta in
/-- `sol_prove` on a scoped goal `Core.Valid φ`: the scoped strategy, its
leaves erased and closed by today's closer, as one kernel evaluation
(`Valid.of_proves`); one goal `leafᵢ` per leaf the closer leaves. -/
@[tactic Solidity.tacticSol_prove]
def evalSolProveCore : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let some (C, φ) ← Symex.validGoal? g | throwUnsupportedSyntax
  let rest := (← getUnsolvedGoals).erase g
  let leaves ← Derive.prove g C φ
  setGoals (leaves ++ rest)

end Solidity.Core
