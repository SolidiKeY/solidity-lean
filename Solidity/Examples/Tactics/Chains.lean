import Solidity.Calculus.LastLine
import Solidity.Calculus.Surface
import Solidity.FreshNames

/-!
# Chains on scoped formulas, pinned

`Calculus/Chains.lean`'s chains over `cdl!{ … }`: a step, a named
step, several, and past the program a rewrite on the erasure; the strategy's
lines (`#derivation`), a whole chain written out (`#chain`, `#chain_rest`)
and the check that it ends at a last line (`#last_line`); last, the chains
the tactics write on `dl!{ … }` read scoped (`sol_chain?`, `#chain`,
`sol_rws?`).
-/

namespace Solidity.Examples.Tactics.Chains

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

example : Valid cdl!{ [ alice.age = 3; ] true } :=
  ageBox.valid fun _ => by
    show Modality.afterC _ _ _
    unfold Modality.afterC
    split <;> first | trivial | exact fun _ _ _ => trivial

theorem balance : cdl!{ ⟨ alice.account.balance = 10; ⟩ true }
    ~[storageFieldWrite_unfold_leftFst]~>
      cdl!{ ⟨ uint se1 = 10; Account storage sp1 = alice.account; sp1.balance = se1; ⟩ true }
    ~*> _ := by
  sol_chain

/--
info: Solidity.Examples.Tactics.Chains.balance :
  dl{ ⟨ alice.account.balance = 10; ⟩ true }
      ~[storageFieldWrite_unfold_leftFst]~>
        dl{ ⟨ uint se1 = 10; Account storage sp1 = alice.account; sp1.balance = se1; ⟩ true }
      ~*> dl{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) } true }
-/
#guard_msgs in
#check balance

/-! ## Over a modality and a postcondition -/

section
variable (m : Modality) (φ : Post StandardExample [])

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
variable (m : Modality) (φ : Post StandardExample [.val .uint])

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

/-- Through a loop, as `#chain` writes it: `whileUnwind` leaves the body as
a block inside the branch (`if (c) { {body} while … }`), which the line
reads flattened, at any depth (`Stmt.keyStr`). -/
theorem loopChain :
    cdl![m]{ ∀ uint i; ⟨[ i = 0;
      /// @custom:key unwind 1
      while (i < 1) { i++; }; ]⟩ φ }
    ~[localValueAssign]~> cdl![m]{ ∀ uint i; { i := 0 } ⟨[
      /// @custom:key unwind 1
      while (i < 1) {i++;}; ]⟩ φ }
    ~[whileUnwind]~> cdl![m]{ ∀ uint i; { i := 0 } ⟨[ if (i < 1) {i++;while (i < 1) {i++;};}; ]⟩ φ }
    ~[ifElseUnfold]~> cdl![m]{ ∀ uint i; { i := 0 } ⟨[ bool se1 = i < 1; if (se1) {i++;while (i < 1) {i++;};}; ]⟩ φ }
    ~[localValueDeclInitDrop]~> cdl![m]{ ∀ uint i; { i := 0 } ⟨[ se1 = i < 1; if (se1) {i++;while (i < 1) {i++;};}; ]⟩ φ }
    ~[binopAssignment]~> cdl![m]{ ∀ uint i; { i := 0 } { se1 := i < 1 } ⟨[ if (se1) {i++;while (i < 1) {i++;};}; ]⟩ φ }
    ~[ifElseSplit]~> cdl![m]{
        ∀ uint i; { i := 0 } { se1 := i < 1 } ((se1 ≐ true → ⟨[ i++; while (i < 1) {i++;}; } ]⟩ φ) ∧ (se1 ≐ false → φ)) }
    ~[blockEmpty]~> cdl![m]{
        ∀ uint i; { i := 0 } { se1 := i < 1 } ((se1 ≐ true → ⟨[ i++; while (i < 1) {i++;}; } ]⟩ φ) ∧ (se1 ≐ false → φ)) }
    ~[localIncrement]~> cdl![m]{
        ∀ uint i;
          { i := 0 } { se1 := i < 1 } ((se1 ≐ true → { i := i + 1 } ⟨[ while (i < 1) {i++;}; } ]⟩ φ) ∧ (se1 ≐ false → φ)) } := by
  sol_chain

end

/-! ## Under the box -/

section
variable (φ : Post StandardExample [])

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
variable (m : Modality) (φ : Post StandardExample [])

def names : FreshTable := [("pv", "se1"), ("acc", "sp1")]
local instance : FreshNames := .ofTable names

theorem balNamed : cdl![m]{ ⟨[ alice.account.balance = 10; ]⟩ φ }
    ~[storageFieldWrite_unfold_leftFst]~>
      cdl![m]{ ⟨[ uint pv = 10; Account storage acc = alice.account; acc.balance = pv; ]⟩ φ }
    ~*> cdl![m]{ { pv := 10 } { acc := alice.account } ⟨[ acc.balance = pv; ]⟩ φ } := by
  sol_chain

end

/-! ## Chains the tactics write

`sol_chain?`, `#chain` and `sol_rws?` on `dl!{ … }` read scoped (`open scoped
Solidity.Scoped`), their lines `cdl![m]{ … }`
(`Calculus/ChainGen.lean`). -/

section Surface
open scoped Scoped

/-! ## `sol_chain?`: the chain written out

`sol_chain?` on `φ ~~> ψ` writes the derivation out as one chain term,
every line and every rule (`Calculus/ChainGen.lean`): the parameters
bound by `∀` in each line, and no `emptyModality` after the last statement. -/

/--
info: Try this:
  exact Solidity.Fml.Via.leads (show cdl!{ ∀ uint x; ∀ uint v; [ alice.age = v; x = 1; ] find(storage, alice.age) = v }
        ~[storageFieldWriteSave]~> cdl!{ ∀ uint x; ∀ uint v; { storage := save(storage, alice.age, v) } [ x = 1; ] find(storage, alice.age) = v }
        ~[localValueAssign]~> cdl![.box]{ ∀ uint x; ∀ uint v; { storage := save(storage, alice.age, v) } { x := 1 } find(storage, alice.age) = v } by sol_chain)
-/
#guard_msgs in
example : dl!{ [ alice.age = v; x = 1; ] alice.age == v }
    ~~> dl![.box]{ { storage := save(storage, alice.age, v) } { x := 1 } alice.age == v } := by
  sol_chain?

section
variable (m : Modality)

/-! At a modality `m` and a postcondition `φ`, the chain is `by sol_chain`. -/
/--
info: Try this:
  exact Solidity.Fml.SoundRel.leads (show cdl![m]{ ∀ uint v; ⟨[ alice.age = v; ]⟩ φ }
        ~[storageFieldWriteSave]~> cdl![m]{ ∀ uint v; { storage := save(storage, alice.age, v) } φ } by sol_chain)
-/
#guard_msgs in
example (φ : Post StandardExample [.val .uint]) :
    dl![m]{ ⟨[ alice.age = v; ]⟩ φ } ~~> dl![m]{ { storage := save(storage, alice.age, v) } φ } := by
  sol_chain?

/-! While the program is open, `~~>` reaches a line up to three merges and
rewrites past one of the derivation (`openRwPath`, a bounded search);
`sol_chain?` writes them out as links, which a re-check does not search
for (`Examples/ChainRewritesOpen.lean`). -/
/--
info: Try this:
  exact Solidity.Fml.Via.leads (show cdl![m]{ { x := 250 } { x := x + 10 } ⟨[ revert(); ]⟩ φ }
        ~[sequentialToParallel]~> cdl![m]{ { x := 250 ‖ x := 250 + 10 } ⟨[ revert(); ]⟩ φ }
        ~[simplifyUpdate]~> cdl![m]{ { x := 250 + 10 } ⟨[ revert(); ]⟩ φ } by sol_chain)
-/
#guard_msgs in
example (φ : Post StandardExample [.val .uint]) :
    dl![m]{ { x := 250 } { x := x + 10 } ⟨[ revert(); ]⟩ φ }
    ~~> dl![m]{ { x := 250 + 10 } ⟨[ revert(); ]⟩ φ } := by
  sol_chain?

end

/-! ## `#chain`, `sol_rws`: past the program

`#chain φ` writes the whole chain from `φ`: the program's steps, then,
from the erasure of the line the program ends at, one rewrite a link until
the line is last, written as one chain term to paste
(`Calculus/ChainGen.lean`).
The strategy's steps are grouped as the worked examples print them
(`NFml.Chain.groupSteps`): a declaration with the binding or read it leaves
is one `~*>`; no `emptyModality` follows a rule that leaves no statement. -/

section
variable (m : Modality)

variable (φ : Post StandardExample [.val .uint, .val .uint]) in
/--
info: theorem chain :
    cdl![m]{ ∀ uint x; ∀ uint v; ⟨[ alice.age = v; x = 1; ]⟩ φ }
    ~[storageFieldWriteSave]~> cdl![m]{ ∀ uint x; ∀ uint v; { storage := save(storage, alice.age, v) } ⟨[ x = 1; ]⟩ φ }
    ~[localValueAssign]~> cdl![m]{ ∀ uint x; ∀ uint v; { storage := save(storage, alice.age, v) } { x := 1 } φ }
    ~[sequentialToParallel]~> cdl![m]{ { storage := save(storage, alice.age, v) ‖ x := 1 } φ } := by
  sol_chain
-/
#guard_msgs in
#chain dl![m]{ ⟨[ alice.age = v; x = 1; ]⟩ φ }

-- A concrete starting state in front of the program: the declaration and
-- its read are one `~*>`, and the read resolves to the literal.
variable (φ : Post StandardExample [.val .uint]) in
/--
info: theorem chain :
    cdl![m]{ { storage := save(storage, alice.age, 42) } ⟨[ uint x = alice.age; ]⟩ φ }
    ~*> cdl![m]{ { storage := save(storage, alice.age, 42) } { x := find(storage, alice.age) } φ }
    ~[sequentialToParallel]~> cdl![m]{ { storage := save(storage, alice.age, 42) ‖ x := find(save(storage, alice.age, 42), alice.age) } φ }
    ~[findOnSave]~> cdl![m]{ { storage := save(storage, alice.age, 42) ‖ x := 42 } φ } := by
  sol_chain
-/
#guard_msgs in
#chain dl![m]{ { storage := save(storage, alice.age, 42) } ⟨[ uint x = alice.age; ]⟩ φ }

/-- The program by the strategy, then the merge and the read of the fresh
`Person`: past the program the rewrites are named (`sol_rws`), the
derivation to the program's end found. -/
example (φ : Post StandardExample [.mem (.struct "Person"), .val .uint]) :
    dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
            ⟨[ v = carol.account.balance; ]⟩ φ }
    ~~> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) ‖
          mv1 := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖ v := 0 } φ } := by
  sol_rws [sequentialToParallel, readAddEqual]

variable (φ : Post StandardExample [.val .uint, .val .uint]) in
/--
info: Try this:
  sol_rws [sequentialToParallel]
-/
#guard_msgs in
example : dl![m]{ { storage := save(storage, alice.age, v) } { x := 1 } φ }
    ~~> dl![m]{ { storage := save(storage, alice.age, v) ‖ x := 1 } φ } := by
  sol_rws?

/-! `sol_chain?` on `~~>` at any length: one rewrite, one step, none. -/
variable (φ : Post StandardExample [.val .uint, .val .uint]) in
#guard_msgs (drop info) in
example : dl![m]{ { storage := save(storage, alice.age, v) } { x := 1 } φ }
    ~~> dl![m]{ { storage := save(storage, alice.age, v) ‖ x := 1 } φ } := by
  sol_chain?

variable (φ : Post StandardExample [.val .uint]) in
#guard_msgs (drop info) in
example : dl![m]{ { x := 1 } ⟨[ ]⟩ φ } ~~> dl![m]{ { x := 1 } φ } := by
  sol_chain?

variable (φ : Post StandardExample [.val .uint]) in
#guard_msgs (drop info) in
example : dl![m]{ { x := 1 } φ } ~~> dl![m]{ { x := 1 } φ } := by
  sol_chain?

end

end Surface

end Solidity.Examples.Tactics.Chains
