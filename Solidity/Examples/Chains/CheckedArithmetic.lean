import Solidity.Calculus.Chains
import Solidity.Calculus.Close

/-!
# Checked arithmetic: the overflow that reverts

The calculus's worked example `uint8 x = 250; x += 10;`, for any modality up to
the revert, then one chain per modality, and the updates merged to the printed
last line.  Lean has no guarded rule: the elaborator reads `uint8 x` as a
`uint` and appends the range check as a trailing `require(x <= 255);` after
the write (`narrowPost`), so the printed `arithCheckedLocalCompoundAssign` is
`localOpAssign` followed by `requireSimple`'s two goals.

The printed `inTy(uint8, 260)` is `x <= 255` read after the two updates, held
in the capture `se1` that the `require` makes; a comparison is not a line of
`dl{ … }`, so those lines write the capture as a Lean term (`inTy8`, `capX`).
The printed `260` is `250 + 10` (`t260`); nothing folds it.  The expansion of
`inTy` and the closing of the two goals are not drawn.
-/

namespace Solidity.Examples.Chains.CheckedArithmetic

open Proves

local instance : InContract := ⟨StandardExample⟩

/-! ## Example: Overflow Reverts -/

section Lines
variable (m : Modality) (φ : Post StandardExample)

/-- `inTy(uint8, t)`, as the check's capture holds it: `t <= 255`. -/
abbrev inTy8 (t : Term StandardExample) : Term StandardExample :=
  .binop .le .uint t (.lit (.int 255))

/-- `{ se1 := inTy(uint8, x) }`: the check's condition captured. -/
abbrev capX : Upd StandardExample := [.val (.fresh "se" 1) (inTy8 (.pv (.user "x")))]

/-- `require(se1);`, the check on its capture. -/
abbrev requireSe1 : Stmt StandardExample := .require (.simple (.local (.fresh "se" 1)))

/-- `uint8 x = 250; x += 10;` under either modality, to the check: the
declaration an update, the compound assignment an update (the printed
`arithCheckedLocalCompoundAssign` without its guard), the check's condition
captured. -/
def overflowToCheck :
    dl![m]{ ⟨[ uint8 x = 250; x += 10; ]⟩ φ }
    ~*> dl![m]{ { x := 250 } { x := x + 10 } ‹.upd m capX (.modal m [requireSe1] φ)› } :=
  calc dl![m]{ ⟨[ uint8 x = 250; x += 10; ]⟩ φ }
    _ ~[localValueDeclInitDrop]~> dl![m]{ ⟨[ x = 250; x += 10; require(x <= 255); ]⟩ φ } := by
      sol_chain
    _ ~[localValueAssign]~> dl![m]{ { x := 250 } ⟨[ x += 10; require(x <= 255); ]⟩ φ } := by sol_chain
    _ ~[localOpAssign]~> dl![m]{ { x := 250 } { x := x + 10 } ⟨[ require(x <= 255); ]⟩ φ } := by
      sol_chain
    _ ~*> dl![m]{ { x := 250 } { x := x + 10 } ‹.upd m capX (.modal m [requireSe1] φ)› } := by
      sol_chain

/-- The printed trace under every modality, up to the revert: the check splits
(`requireSimple`), its cover `⟨[ revert(); ]⟩ false ∨ c ∨ c'` the same under
either modality, and the in-range goal runs to its end.  The out-of-range goal
is left at `⟨[ revert(); ]⟩ φ`, where the modalities part. -/
def overflowTrace :
    dl![m]{ ⟨[ uint8 x = 250; x += 10; ]⟩ φ }
    ~*> dl![m]{ { x := 250 } { x := x + 10 }
          ‹.upd m capX dl![m]{ (se1 ≐ true → φ) ∧ (se1 ≐ false → ⟨[ revert(); ]⟩ φ) ∧
            (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false) }› } :=
  calc dl![m]{ ⟨[ uint8 x = 250; x += 10; ]⟩ φ }
    _ ~*> _ := overflowToCheck m φ
    _ ~[requireSimple]~> dl![m]{ { x := 250 } { x := x + 10 }
          ‹.upd m capX dl![m]{ (se1 ≐ true → ⟨[ ]⟩ φ) ∧ (se1 ≐ false → ⟨[ revert(); ]⟩ φ) ∧
            (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false) }› } := by
      sol_chain
    _ ~[emptyModality]~> dl![m]{ { x := 250 } { x := x + 10 }
          ‹.upd m capX dl![m]{ (se1 ≐ true → φ) ∧ (se1 ≐ false → ⟨[ revert(); ]⟩ φ) ∧
            (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false) }› } := by
      sol_chain

/-- `[ uint8 x = 250; x += 10; ] φ`: the out-of-range goal is a revert, which
the box closes to `true`. -/
def overflowBoxChain :
    dl![.box]{ ⟨[ uint8 x = 250; x += 10; ]⟩ φ }
    ~*> dl![.box]{ { x := 250 } { x := x + 10 }
          ‹.upd .box capX dl![.box]{ (se1 ≐ true → φ) ∧ (se1 ≐ false → true) ∧
            ([ revert(); ] false ∨ se1 ≐ true ∨ se1 ≐ false) }› } :=
  calc dl![.box]{ ⟨[ uint8 x = 250; x += 10; ]⟩ φ }
    _ ~*> _ := overflowTrace .box φ
    _ ~[revertBox]~> dl![.box]{ { x := 250 } { x := x + 10 }
          ‹.upd .box capX dl![.box]{ (se1 ≐ true → φ) ∧ (se1 ≐ false → true) ∧
            ([ revert(); ] false ∨ se1 ≐ true ∨ se1 ≐ false) }› } := by
      sol_chain

/-- The diamond's revert goal is `false`: the check must pass. -/
def overflowDiamondChain :
    dl![.diamond]{ ⟨[ uint8 x = 250; x += 10; ]⟩ φ }
    ~*> dl![.diamond]{ { x := 250 } { x := x + 10 }
          ‹.upd .diamond capX dl![.diamond]{ (se1 ≐ true → φ) ∧ (se1 ≐ false → false) ∧
            (⟨ revert(); ⟩ false ∨ se1 ≐ true ∨ se1 ≐ false) }› } :=
  (overflowTrace .diamond φ).trans (by sol_chain)

/-- `250 + 10`, the printed `260`. -/
abbrev t260 : Term StandardExample := .binop .add .uint (.lit (.int 250)) (.lit (.int 10))

/-- The printed last line under the box, `inTy(uint8, 260) ⊢ {x := 260} φ ;
¬inTy(uint8, 260) ⊢ ⊤`: the updates merged (`sequentialToParallel`), the
overwritten `x := 250` dropped (`simplifyUpdate`). -/
theorem overflowLastLine :
    dl![.box]{ ⟨[ uint8 x = 250; x += 10; ]⟩ φ }
    ~~> .upd .box [.val (.user "x") t260, .val (.fresh "se" 1) (inTy8 t260)]
          dl![.box]{ (se1 ≐ true → φ) ∧ (se1 ≐ false → true) ∧
            ([ revert(); ] false ∨ se1 ≐ true ∨ se1 ≐ false) } :=
  calc dl![.box]{ ⟨[ uint8 x = 250; x += 10; ]⟩ φ }
    _ ~*> _ := overflowBoxChain φ
    _ ~[sequentialToParallel]~> _ := by sol_chain
    _ ~[simplifyUpdate]~> .upd .box [.val (.user "x") t260, .val (.fresh "se" 1) (inTy8 t260)]
          dl![.box]{ (se1 ≐ true → φ) ∧ (se1 ≐ false → true) ∧
            ([ revert(); ] false ∨ se1 ≐ true ∨ se1 ≐ false) } := by sol_chain

end Lines

end Solidity.Examples.Chains.CheckedArithmetic
