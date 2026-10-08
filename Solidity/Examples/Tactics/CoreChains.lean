import Solidity.Calculus.Core.LastLine
import Solidity.FreshNames

/-!
# Chains on scoped formulas, pinned

`Calculus/Core/Chains.lean`'s chains over `cdl!{ … }`: a step, a named
step, several, and past the program a rewrite on the erasure; the strategy's
lines (`#derivation`), a whole chain written out (`#chain`, `#chain_rest`)
and the check that it ends at a last line (`#last_line`).
-/

namespace Solidity.Examples.CoreChains

open Solidity

local instance : InContract := ⟨StandardExample⟩

/-! ## A closed formula -/

/--
info:
  dl{ ⟨ alice.age = 3; ⟩ true }
  ~[storageFieldWriteSave]~>
  dl{ { storage := save(storage, alice.age, 3) } true }
-/
#guard_msgs in
#derivation cdl!{ ⟨ alice.age = 3; ⟩ true }

theorem age : cdl!{ ⟨ alice.age = 3; ⟩ true }
    ~> cdl!{ { storage := save(storage, alice.age, 3) } true } := by
  sol_chain

/-- A chain proves its first line from its last (`Fml.OneStep.valid`). -/
theorem ageBox : cdl!{ [ alice.age = 3; ] true }
    ~> cdl![.box]{ { storage := save(storage, alice.age, 3) } true } := by
  sol_chain

example : Core.Valid cdl!{ [ alice.age = 3; ] true } :=
  ageBox.valid fun _ => Core.holds_upd_intro fun _ => by unfold Modality.afterC; split <;> trivial

theorem balance : cdl!{ ⟨ alice.account.balance = 10; ⟩ true }
    ~[storageFieldWrite_unfold_leftFst]~>
      cdl!{ ⟨ uint se1 = 10; Account storage sp1 = alice.account; sp1.balance = se1; ⟩ true }
    ~*> _ := by
  sol_chain

/--
info: Solidity.Examples.CoreChains.balance :
  dl{ ⟨ alice.account.balance = 10; ⟩ true }
      ~[storageFieldWrite_unfold_leftFst]~>
        dl{ ⟨ uint se1 = 10; Account storage sp1 = alice.account; sp1.balance = se1; ⟩ true }
      ~*> dl{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) } true }
-/
#guard_msgs in
#check balance

/-! ## Over a modality and a postcondition -/

section
variable (m : Modality) (φ : Core.Post StandardExample [])

theorem bal : cdl![m]{ ⟨[ alice.account.balance = 10; ]⟩ φ }
    ~[storageFieldWrite_unfold_leftFst]~>
      cdl![m]{ ⟨[ uint se1 = 10; Account storage sp1 = alice.account; sp1.balance = se1; ]⟩ φ }
    ~*> cdl![m]{ { se1 := 10 } { sp1 := alice.account } ⟨[ sp1.balance = se1; ]⟩ φ } := by
  sol_chain

/-- Past the program, a rewrite on the erasure. -/
theorem balLast : cdl![m]{ ⟨[ alice.account.balance = 10; ]⟩ φ }
    ~*> cdl![m]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) } φ }
    ~[sequentialToParallel]~> cdl![m]{ { se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10) } φ } := by
  sol_chain

#last_line balLast

/-- Stops before the rewrite. -/
def balProgram : cdl![m]{ ⟨[ alice.account.balance = 10; ]⟩ φ }
    ~*> cdl![m]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) } φ } := by
  sol_chain

/--
error: #last_line: balProgram does not end at a last line:
  dl{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) } φ }
3 updates stand in front of
  ↑φ
(one parallel update does: `~[sequentialToParallel]~>`)
sequentialToParallel still applies (under either modality), and gives
  dl{ { se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10) } φ }
-/
#guard_msgs in
#last_line balProgram

/--
info: lines to append to the statement of balProgram:
    ~[sequentialToParallel]~> cdl![m]{ { se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10) } φ }
-/
#guard_msgs in
#chain_rest balProgram

/--
info: theorem chain :
    cdl![m]{ ⟨[ alice.account.balance = 10; ]⟩ φ }
    ~[storageFieldWrite_unfold_leftFst]~> cdl![m]{ ⟨[ uint se1 = 10; Account storage sp1 = alice.account; sp1.balance = se1; ]⟩ φ }
    ~*> cdl![m]{ { se1 := 10 } { sp1 := alice.account } ⟨[ sp1.balance = se1; ]⟩ φ }
    ~[storageFieldWriteSave]~> cdl![m]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) } φ }
    ~[sequentialToParallel]~> cdl![m]{ { se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10) } φ } := by
  sol_chain

fresh variables (a `FreshNames` table renames them):
  [("?", "se1"), ("?", "sp1")]
-/
#guard_msgs in
#chain cdl![m]{ ⟨[ alice.account.balance = 10; ]⟩ φ }

/-- What `#chain` wrote, pasted. -/
theorem balChain :
    cdl![m]{ ⟨[ alice.account.balance = 10; ]⟩ φ }
    ~[storageFieldWrite_unfold_leftFst]~> cdl![m]{ ⟨[ uint se1 = 10; Account storage sp1 = alice.account; sp1.balance = se1; ]⟩ φ }
    ~*> cdl![m]{ { se1 := 10 } { sp1 := alice.account } ⟨[ sp1.balance = se1; ]⟩ φ }
    ~[storageFieldWriteSave]~> cdl![m]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) } φ }
    ~[sequentialToParallel]~> cdl![m]{ { se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10) } φ } := by
  sol_chain

#last_line balChain

/-- A branch: `ifElseSplit` and both goals. -/
theorem branch : cdl![m]{ ⟨[ if (alice.age > 4) { total = 1; } else { total = 2; }; ]⟩ φ }
    ~*> cdl![m]{ { se2 := find(storage, alice.age) } ⟨[ se1 = se2 > 4; if (se1) {total = 1;} else {total = 2;}; ]⟩ φ }
    ~*> _ := by
  sol_chain

/--
info: theorem chain :
    cdl![m]{ ⟨[ if (alice.age > 4) {total = 1;} else {total = 2;}; ]⟩ φ }
    ~[ifElseUnfold]~> cdl![m]{ ⟨[ bool se1 = alice.age > 4; if (se1) {total = 1;} else {total = 2;}; ]⟩ φ }
    ~[localValueDeclInitDrop]~> cdl![m]{ ⟨[ se1 = alice.age > 4; if (se1) {total = 1;} else {total = 2;}; ]⟩ φ }
    ~[binopUnfoldLeft]~> cdl![m]{ ⟨[ uint se2 = alice.age; se1 = se2 > 4; if (se1) {total = 1;} else {total = 2;}; ]⟩ φ }
    ~*> cdl![m]{ { se2 := find(storage, alice.age) } ⟨[ se1 = se2 > 4; if (se1) {total = 1;} else {total = 2;}; ]⟩ φ }
    ~[binopAssignment]~> cdl![m]{ { se2 := find(storage, alice.age) } { se1 := se2 > 4 } ⟨[ if (se1) {total = 1;} else {total = 2;}; ]⟩ φ }
    ~[ifElseSplit]~> cdl![m]{
        { se2 := find(storage, alice.age) }
          { se1 := se2 > 4 } ((se1 ≐ true → ⟨[ total = 1; } ]⟩ φ) ∧ (se1 ≐ false → ⟨[ total = 2; } ]⟩ φ)) }
    ~[storageRootWriteStore]~> cdl![m]{
        { se2 := find(storage, alice.age) }
          { se1 := se2 > 4 }
            ((se1 ≐ true → { storage := save(storage, total, 1) } φ) ∧ (se1 ≐ false → ⟨[ total = 2; } ]⟩ φ)) }
    ~[storageRootWriteStore]~> cdl![m]{
        { se2 := find(storage, alice.age) }
          { se1 := se2 > 4 }
            ((se1 ≐ true → { storage := save(storage, total, 1) } φ) ∧
                (se1 ≐ false → { storage := save(storage, total, 2) } φ)) }
    ~[sequentialToParallel]~> cdl![m]{
        { se2 := find(storage, alice.age) ‖ se1 := find(storage, alice.age) > 4 }
          ((se1 ≐ true → { storage := save(storage, total, 1) } φ) ∧
              (se1 ≐ false → { storage := save(storage, total, 2) } φ)) } := by
  sol_chain

fresh variables (a `FreshNames` table renames them):
  [("?", "se1"), ("?", "se2")]
-/
#guard_msgs in
#chain cdl![m]{ ⟨[ if (alice.age > 4) {total = 1;} else {total = 2;}; ]⟩ φ }

/-- `#chain` on the branch, pasted: a goal's program runs into the `}` of
its branch. -/
theorem branchChain :
    cdl![m]{ ⟨[ if (alice.age > 4) {total = 1;} else {total = 2;}; ]⟩ φ }
    ~[ifElseUnfold]~> cdl![m]{ ⟨[ bool se1 = alice.age > 4; if (se1) {total = 1;} else {total = 2;}; ]⟩ φ }
    ~[localValueDeclInitDrop]~> cdl![m]{ ⟨[ se1 = alice.age > 4; if (se1) {total = 1;} else {total = 2;}; ]⟩ φ }
    ~[binopUnfoldLeft]~> cdl![m]{ ⟨[ uint se2 = alice.age; se1 = se2 > 4; if (se1) {total = 1;} else {total = 2;}; ]⟩ φ }
    ~*> cdl![m]{ { se2 := find(storage, alice.age) } ⟨[ se1 = se2 > 4; if (se1) {total = 1;} else {total = 2;}; ]⟩ φ }
    ~[binopAssignment]~> cdl![m]{ { se2 := find(storage, alice.age) } { se1 := se2 > 4 } ⟨[ if (se1) {total = 1;} else {total = 2;}; ]⟩ φ }
    ~[ifElseSplit]~> cdl![m]{
        { se2 := find(storage, alice.age) }
          { se1 := se2 > 4 } ((se1 ≐ true → ⟨[ total = 1; } ]⟩ φ) ∧ (se1 ≐ false → ⟨[ total = 2; } ]⟩ φ)) }
    ~[storageRootWriteStore]~> cdl![m]{
        { se2 := find(storage, alice.age) }
          { se1 := se2 > 4 }
            ((se1 ≐ true → { storage := save(storage, total, 1) } φ) ∧ (se1 ≐ false → ⟨[ total = 2; } ]⟩ φ)) }
    ~[storageRootWriteStore]~> cdl![m]{
        { se2 := find(storage, alice.age) }
          { se1 := se2 > 4 }
            ((se1 ≐ true → { storage := save(storage, total, 1) } φ) ∧
                (se1 ≐ false → { storage := save(storage, total, 2) } φ)) }
    ~[sequentialToParallel]~> cdl![m]{
        { se2 := find(storage, alice.age) ‖ se1 := find(storage, alice.age) > 4 }
          ((se1 ≐ true → { storage := save(storage, total, 1) } φ) ∧
              (se1 ≐ false → { storage := save(storage, total, 2) } φ)) } := by
  sol_chain


-- `revert();` reads the modality: the strategy stops there.
/--
info:
  dl{ ⟨[ if (alice.age > 4) {total = 1;} else {revert();}; ]⟩ φ }
  ~[ifElseUnfold]~>
  dl{ ⟨[ bool se1 = alice.age > 4; if (se1) {total = 1;} else {revert();}; ]⟩ φ }
  ~[localValueDeclInitDrop]~>
  dl{ ⟨[ se1 = alice.age > 4; if (se1) {total = 1;} else {revert();}; ]⟩ φ }
  ~[binopUnfoldLeft]~>
  dl{ ⟨[ uint se2 = alice.age; se1 = se2 > 4; if (se1) {total = 1;} else {revert();}; ]⟩ φ }
  ~[localValueDeclInitDrop]~>
  dl{ ⟨[ se2 = alice.age; se1 = se2 > 4; if (se1) {total = 1;} else {revert();}; ]⟩ φ }
  ~[storageFieldReadFind]~>
  dl{ { se2 := find(storage, alice.age) } ⟨[ se1 = se2 > 4; if (se1) {total = 1;} else {revert();}; ]⟩ φ }
  ~[binopAssignment]~>
  dl{ { se2 := find(storage, alice.age) } { se1 := se2 > 4 } ⟨[ if (se1) {total = 1;} else {revert();}; ]⟩ φ }
  ~[ifElseSplit]~>
  dl{
    { se2 := find(storage, alice.age) }
      { se1 := se2 > 4 } ((se1 ≐ true → ⟨[ total = 1; } ]⟩ φ) ∧ (se1 ≐ false → ⟨[ revert(); } ]⟩ φ)) }
  ~[storageRootWriteStore]~>
  dl{
    { se2 := find(storage, alice.age) }
      { se1 := se2 > 4 }
        ((se1 ≐ true → { storage := save(storage, total, 1) } φ) ∧ (se1 ≐ false → ⟨[ revert(); } ]⟩ φ)) }
  (the line after depends on the modality m, through a rule that reads it (`revertBox`, `revertDiamond`, a loop's invariant rule): go on after `cases m`)
-/
#guard_msgs in
#derivation cdl![m]{ ⟨[ if (alice.age > 4) { total = 1; } else { revert(); }; ]⟩ φ }

end

/-! ## A scoped line with a parameter

The rewrites past the program are searched on the erasure with its outer
`∀ uint ageVal;` dropped, the line `Fml.ViaE` checks (`Examples/Chains/Storage.lean`'s
`AgeWrite.chain`). -/

section
variable (m : Modality) (φ : Core.Post StandardExample [.val .uint])

/--
info: theorem chain :
    cdl![m]{ ∀ uint ageVal; { ageVal := 42 } ⟨[ alice.age = ageVal; ]⟩ φ }
    ~[storageFieldWriteSave]~> cdl![m]{ ∀ uint ageVal; { ageVal := 42 } { storage := save(storage, alice.age, ageVal) } φ }
    ~[sequentialToParallel]~> cdl![m]{ { ageVal := 42 ‖ storage := save(storage, alice.age, 42) } φ } := by
  sol_chain
-/
#guard_msgs in
#chain cdl![m]{ { ageVal := 42 } ⟨[ alice.age = ageVal; ]⟩ φ }

/-- What `#chain` wrote, pasted. -/
theorem ageWriteChain :
    cdl![m]{ ∀ uint ageVal; { ageVal := 42 } ⟨[ alice.age = ageVal; ]⟩ φ }
    ~[storageFieldWriteSave]~> cdl![m]{ ∀ uint ageVal; { ageVal := 42 } { storage := save(storage, alice.age, ageVal) } φ }
    ~[sequentialToParallel]~> cdl![m]{ { ageVal := 42 ‖ storage := save(storage, alice.age, 42) } φ } := by
  sol_chain

#last_line ageWriteChain

end

/-! ## Under the box -/

section
variable (φ : Core.Post StandardExample [])

/--
info: theorem chain :
    cdl!{ [ alice.age = 3; total = 1; ] φ }
    ~[storageFieldWriteSave]~> cdl!{ { storage := save(storage, alice.age, 3) } [ total = 1; ] φ }
    ~[storageRootWriteStore]~> cdl![.box]{ { storage := save(storage, alice.age, 3) } { storage := save(storage, total, 1) } φ }
    ~[sequentialToParallel]~> cdl![.box]{ { storage := save(save(storage, alice.age, 3), total, 1) } φ } := by
  sol_chain
-/
#guard_msgs in
#chain cdl![.box]{ ⟨[ alice.age = 3; total = 1; ]⟩ φ }

theorem ageTotal :
    cdl!{ [ alice.age = 3; total = 1; ] φ }
    ~[storageFieldWriteSave]~> cdl!{ { storage := save(storage, alice.age, 3) } [ total = 1; ] φ }
    ~[storageRootWriteStore]~> cdl![.box]{ { storage := save(storage, alice.age, 3) } { storage := save(storage, total, 1) } φ }
    ~[sequentialToParallel]~> cdl![.box]{ { storage := save(save(storage, alice.age, 3), total, 1) } φ } := by
  sol_chain

#last_line ageTotal

end

/-! ## Fresh names -/

section
variable (m : Modality) (φ : Core.Post StandardExample [])

def names : FreshTable := [("pv", "se1"), ("acc", "sp1")]
local instance : FreshNames := .ofTable names

theorem balNamed : cdl![m]{ ⟨[ alice.account.balance = 10; ]⟩ φ }
    ~[storageFieldWrite_unfold_leftFst]~>
      cdl![m]{ ⟨[ uint pv = 10; Account storage acc = alice.account; acc.balance = pv; ]⟩ φ }
    ~*> cdl![m]{ { pv := 10 } { acc := alice.account } ⟨[ acc.balance = pv; ]⟩ φ } := by
  sol_chain

end

end Solidity.Examples.CoreChains
