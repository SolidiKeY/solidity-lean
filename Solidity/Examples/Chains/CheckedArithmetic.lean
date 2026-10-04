import Solidity.Calculus.LastLine
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
in the capture `se1` that the `require` makes.  Past the program, the updates
merge, `add_literals` and `leq_literals` fold the two literal operations one
line at a time, `applyOnRigid` exposes the branches, and `concrete` selects the
revert.  The box and diamond then close separately, each checked by
`#last_line`.
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

/-- The modality-independent part of the trace: merge the updates, drop the
overwritten assignment, fold `250 + 10` and `260 <= 255`, push the exact
update through the split, and select its failing branch. -/
theorem overflowMerged :
    dl![m]{ ⟨[ uint8 x = 250; x += 10; ]⟩ φ }
    ~~> dl![m]{ { x := 260 ‖ se1 := false } ⟨[ revert(); ]⟩ φ } :=
  calc dl![m]{ ⟨[ uint8 x = 250; x += 10; ]⟩ φ }
    _ ~*> _ := overflowTrace m φ
    _ ~[sequentialToParallel]~> _ := by sol_chain
    _ ~[simplifyUpdate]~> dl![m]{ { x := 250 + 10 ‖ se1 := 250 + 10 <= 255 }
          ((se1 ≐ true → φ) ∧ (se1 ≐ false → ⟨[ revert(); ]⟩ φ) ∧
            (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) } := by
      sol_chain
    _ ~[add_literals]~> dl![m]{ { x := 260 ‖ se1 := 260 <= 255 }
          ((se1 ≐ true → φ) ∧ (se1 ≐ false → ⟨[ revert(); ]⟩ φ) ∧
            (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) } := by
      sol_chain
    _ ~[leq_literals]~> dl![m]{ { x := 260 ‖ se1 := false }
          ((se1 ≐ true → φ) ∧ (se1 ≐ false → ⟨[ revert(); ]⟩ φ) ∧
            (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) } := by
      sol_chain
    _ ~[applyOnRigid]~> _ := by sol_chain
    _ ~[concrete]~> dl![m]{ { x := 260 ‖ se1 := false } ⟨[ revert(); ]⟩ φ } := by
      sol_chain

/-- Under the box the failing branch closes to `true`; its now-unused update
then disappears. -/
theorem overflowBox :
    dl![.box]{ ⟨[ uint8 x = 250; x += 10; ]⟩ φ } ~~> dl!{ true } :=
  calc dl![.box]{ ⟨[ uint8 x = 250; x += 10; ]⟩ φ }
    _ ~~> _ := overflowMerged .box φ
    _ ~[revertBox]~> dl![.box]{ { x := 260 ‖ se1 := false } true } := by sol_chain
    _ ~[simplifyUpdate]~> dl!{ true } := by sol_chain

#last_line overflowBox

/-- Under the diamond the failing branch closes to `false`; its update then
disappears as well. -/
theorem overflowDiamond :
    dl!{ ⟨ uint8 x = 250; x += 10; ⟩ φ } ~~> dl!{ false } :=
  calc dl!{ ⟨ uint8 x = 250; x += 10; ⟩ φ }
    _ ~~> _ := overflowMerged .diamond φ
    _ ~[revertDiamond]~> dl!{ { x := 260 ‖ se1 := false } false } := by sol_chain
    _ ~[simplifyUpdate]~> dl!{ false } := by sol_chain

#last_line overflowDiamond

end Lines

end Solidity.Examples.Chains.CheckedArithmetic
