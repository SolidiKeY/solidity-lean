import Solidity.Calculus.Chains
import Solidity.Calculus.ChainRewrites
import Solidity.Calculus.LastLine
import Solidity.Calculus.Close

/-!
# Checked arithmetic: the overflow that reverts

The calculus's worked example `uint8 x = 250; x += 10;` as one chain term per modality, box and diamond,
each from the program to its last line (`.claude/rules/derivations.md`).  The program is the paper's and
already concrete, so the first line needs no starting update.

Lean has no guarded rule: the elaborator reads `uint8 x` as a `uint` and appends the range check as a
trailing `require(x <= 255);` after the write (`narrowPost`).  The paper's one `⇝` through the guarded
`arithCheckedLocalCompoundAssign` is therefore three links: `~[localOpAssign]~>`, one `~*>` for the check
(its condition captured in `se1`, the capture's declaration dropped, `requireSimple`'s split), and the
revert closed (`~[revertBox]~>` to `true`, `~[revertDiamond]~>` to `false`).  Up to the revert the lines
are the same under either modality (`Examples/ChainNotation.lean` states them over a modality variable);
that line is the paper's two goals.  The printed `inTy(uint8, 260)` is
`se1`, which holds `x <= 255` read after the two updates.

Past the program the stack merges, every binding kept (the overwritten `x := 250` too), `add_literals` and
`leq_literals` fold `250 + 10` and `260 <= 255`, `applyOnRigid` pushes the update into the branches, and
`concrete` closes them: the in-range branch by its false antecedent, the revert branch by the folded check.
-/

namespace Solidity.Examples.Chains.CheckedArithmetic

local instance : InContract := ⟨StandardExample⟩

/-! ## Example: Overflow Reverts -/

section
variable (φ : Post StandardExample)

namespace OverflowReverts

/-- `[ uint8 x = 250; x += 10; ] φ`: the check fails, its revert is `true` under the box, and so is the
whole formula, for every `φ` (`Panic(0x11)`: no run survives). -/
theorem box :
    dl!{ [ uint8 x = 250; x += 10; ] φ }
    ~*> dl!{ { x := 250 } [ x += 10; require(x <= 255); ] φ }
    ~[localOpAssign]~> dl!{ { x := 250 } { x := x + 10 } [ require(x <= 255); ] φ }
    ~*> dl![.box]{ { x := 250 } { x := x + 10 } { se1 := x <= 255 }
          ((se1 ≐ true → φ) ∧ (se1 ≐ false → [ revert(); ] φ) ∧ ([ revert(); ] false ∨ se1 ≐ true ∨ se1 ≐ false)) }
    ~[revertBox]~> dl![.box]{ { x := 250 } { x := x + 10 } { se1 := x <= 255 }
          ((se1 ≐ true → φ) ∧ (se1 ≐ false → true) ∧ ([ revert(); ] false ∨ se1 ≐ true ∨ se1 ≐ false)) }
    ~[sequentialToParallel]~> dl![.box]{ { x := 250 ‖ x := 250 + 10 ‖ se1 := 250 + 10 <= 255 }
          ((se1 ≐ true → φ) ∧ (se1 ≐ false → true) ∧ ([ revert(); ] false ∨ se1 ≐ true ∨ se1 ≐ false)) }
    ~[add_literals]~> dl![.box]{ { x := 250 ‖ x := 260 ‖ se1 := 260 <= 255 }
          ((se1 ≐ true → φ) ∧ (se1 ≐ false → true) ∧ ([ revert(); ] false ∨ se1 ≐ true ∨ se1 ≐ false)) }
    ~[leq_literals]~> dl![.box]{ { x := 250 ‖ x := 260 ‖ se1 := false }
          ((se1 ≐ true → φ) ∧ (se1 ≐ false → true) ∧ ([ revert(); ] false ∨ se1 ≐ true ∨ se1 ≐ false)) }
    ~[applyOnRigid]~> dl![.box]{ (false ≐ true → { x := 250 ‖ x := 260 ‖ se1 := false } φ) ∧
          (false ≐ false → true) ∧
          ({ x := 250 ‖ x := 260 ‖ se1 := false } [ revert(); ] false ∨ false ≐ true ∨ false ≐ false) }
    ~[concrete]~> dl!{ true } := by
  sol_chain
#last_line box

/-- `⟨ uint8 x = 250; x += 10; ⟩ φ`: the same trace, but the diamond's revert is `false`, and so is the
last line.  A chain proves its first line from its last (`Fml.Via.leads`), and from `false` that says
nothing: the formula is not proved, since the check must pass and it does not. -/
theorem diamond :
    dl!{ ⟨ uint8 x = 250; x += 10; ⟩ φ }
    ~*> dl!{ { x := 250 } ⟨ x += 10; require(x <= 255); ⟩ φ }
    ~[localOpAssign]~> dl!{ { x := 250 } { x := x + 10 } ⟨ require(x <= 255); ⟩ φ }
    ~*> dl!{ { x := 250 } { x := x + 10 } { se1 := x <= 255 }
          ((se1 ≐ true → φ) ∧ (se1 ≐ false → ⟨ revert(); ⟩ φ) ∧ (⟨ revert(); ⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) }
    ~[revertDiamond]~> dl!{ { x := 250 } { x := x + 10 } { se1 := x <= 255 }
          ((se1 ≐ true → φ) ∧ (se1 ≐ false → false) ∧ (⟨ revert(); ⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) }
    ~[sequentialToParallel]~> dl!{ { x := 250 ‖ x := 250 + 10 ‖ se1 := 250 + 10 <= 255 }
          ((se1 ≐ true → φ) ∧ (se1 ≐ false → false) ∧ (⟨ revert(); ⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) }
    ~[add_literals]~> dl!{ { x := 250 ‖ x := 260 ‖ se1 := 260 <= 255 }
          ((se1 ≐ true → φ) ∧ (se1 ≐ false → false) ∧ (⟨ revert(); ⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) }
    ~[leq_literals]~> dl!{ { x := 250 ‖ x := 260 ‖ se1 := false }
          ((se1 ≐ true → φ) ∧ (se1 ≐ false → false) ∧ (⟨ revert(); ⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) }
    ~[applyOnRigid]~> dl!{ (false ≐ true → { x := 250 ‖ x := 260 ‖ se1 := false } φ) ∧
          (false ≐ false → false) ∧
          ({ x := 250 ‖ x := 260 ‖ se1 := false } ⟨ revert(); ⟩ false ∨ false ≐ true ∨ false ≐ false) }
    ~[concrete]~> dl!{ false } := by
  sol_chain
#last_line diamond

end OverflowReverts

end

end Solidity.Examples.Chains.CheckedArithmetic
