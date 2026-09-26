import Solidity.Calculus.Close

/-!
# Values: operators, comparisons, the conditional

The value operators of solkey's `taclets` suite (`keyext.solidity.examples`),
one theorem per `.key` test, stated in the calculus and proved by the
strategy: `sol_symex` runs the rules, `sol_close` the arithmetic.

Three rules do the work.  An operator over simple operands is an update,
`binopAssignment` (`{ v := se₁ ⊕ se₂ }`); a non-simple operand is captured
first (`binopUnfoldLeft`, `binopUnfoldRight`); a compound assignment on a
local is `localOpAssign`.  One constructor stands for the whole family: `⊕`
is its schema variable, and `KeyTaclets.lean` maps each instance back to the
taclet solkey writes per operator.

The terms of an update are *checked*: `a + b` is read by the interpreter's
own `applyBinOp` and `checkArith`, so it halts on overflow, a zero divisor or
a negative `uint`, exactly as the statement would (`Update.lean`).  A
halting update satisfies the box and falsifies the diamond; the old
`division_unfold_result` revert branch is that, with no rule of its own.

`&&` and `||` do not capture their right operand: it runs only when the left
does not decide (`logicalAndShortCircuitRhs`), which is what makes
`false && values[7] == 0` safe on an empty array.  The conditional is
lowered to the statement `if` (`ternaryToIf`), and so short-circuits too.
-/

namespace Solidity.Examples

open Proves

local instance : InContract := ⟨StandardExample⟩

/-! ## The taclets -/

/--
info: @Taclet.binopAssignment : ∀ {C : Contract} {k : Nat} {m : Modality} {v : Var} {p : PrimTy} {op : BinOp}
  {hop : op.accepts p = true} {x : PrimTy} {hq : op.ret p = x} {se₁ se₂ : Simple C p},
  dl{ ⟨[ v = se₁ ⊕ se₂; ]⟩ ⇝ { v := se₁ ⊕ se₂ } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Taclet.binopAssignment

/--
info: @Taclet.logicalAndShortCircuitRhs : ∀ {C : Contract} {k : Nat} {m : Modality} {v : Var} {se : Simple C PrimTy.bool}
  {nse : Val C PrimTy.bool}, dl{ ⟨[ v = se && nse; ]⟩ ⇝ ⟨[ if (se) {v = nse;v = v && true;} else {v = false;}; ]⟩ }
-/
#guard_msgs in #check @Taclet.logicalAndShortCircuitRhs

/-! ## Arithmetic -/

/-- `addition-simple.key`: `uint r = 1 + 2;` -/
theorem additionSimple : ⊨ dl!{ ⟨ uint r = 1 + 2; ⟩ r == 3 } := by sol_symex; sol_close

/-- `subtraction-simple.key`: `uint r = 7 - 2;` -/
theorem subtractionSimple : ⊨ dl!{ ⟨ uint r = 7 - 2; ⟩ r == 5 } := by sol_symex; sol_close

/-- `multiplication-simple.key`: `uint r = 3 * 4;` -/
theorem multiplicationSimple : ⊨ dl!{ ⟨ uint r = 3 * 4; ⟩ r == 12 } := by sol_symex; sol_close

/-- `division-simple.key`: `uint r = 8 / 2;` -/
theorem divisionSimple : ⊨ dl!{ ⟨ uint r = 8 / 2; ⟩ r == 4 } := by sol_symex; sol_close

/-- `modulo-simple.key`: `uint r = 7 % 3;` -/
theorem moduloSimple : ⊨ dl!{ ⟨ uint r = 7 % 3; ⟩ r == 1 } := by sol_symex; sol_close

/-- `uint x; x = 4; uint y = x + 1;` — a declaration without initialiser
binds the default (`valueDeclSkip`), then a plain assignment. -/
theorem declThenAssign : ⊨ dl!{ ⟨ uint x; x = 4; uint y = x + 1; ⟩ y == 5 } := by
  sol_symex
  sol_close

/-! ## A zero divisor, an overflow: the box holds, the diamond does not -/

/-- `uint r = 8 / 0;` reverts, so every box formula holds of it … -/
theorem divisionByZeroBox : ⊨ dl!{ [ uint r = 8 / 0; ] r == 0 } := by sol_symex; sol_close

/-- … and no diamond formula does. -/
example : ¬ (⊨ dl!{ ⟨ uint r = 8 / 0; ⟩ r == 0 }) := fun h => h Semantics.State.exampleStore

/-- `localDivAssign`'s zero-divisor branch: `x /= y` with `y == 0`. -/
theorem divAssignByZeroBox : ⊨ dl!{ [ uint x = 10; uint y = 0; x /= y; ] x == 0 } := by
  sol_symex
  sol_close

/-- The diamond twin fails: without it the box above would also pass if
`x /= 0` silently produced `0`. -/
example : ¬ (⊨ dl!{ ⟨ uint x = 10; uint y = 0; x /= y; ⟩ x == 0 }) :=
  fun h => h Semantics.State.exampleStore

/-- Checked arithmetic: `2²⁵⁶ - 1 + 1` overflows and reverts. -/
theorem overflowBox :
    ⊨ dl!{ [ uint x = 115792089237316195423570985008687907853269984665640564039457584007913129639935;
             uint r = x + 1; ] r == 0 } := by
  sol_symex
  sol_close

example : ¬ (⊨ dl!{ ⟨ uint x = 115792089237316195423570985008687907853269984665640564039457584007913129639935;
                      uint r = x + 1; ⟩ true }) :=
  fun h => h Semantics.State.exampleStore

/-- `0 - 1` is below the `uint` range: it reverts too. -/
example : ¬ (⊨ dl!{ ⟨ uint r = 0 - 1; ⟩ true }) := fun h => h Semantics.State.exampleStore

/-! ## Comparisons -/

/-- `less-than-simple.key`: `bool r = 3 < 5;` -/
theorem lessThanSimple : ⊨ dl!{ ⟨ bool r = 3 < 5; ⟩ r == true } := by sol_symex; sol_close

/-- `less-equal-simple.key`: `bool r = 5 <= 5;` -/
theorem lessEqualSimple : ⊨ dl!{ ⟨ bool r = 5 <= 5; ⟩ r == true } := by sol_symex; sol_close

/-- `greater-than-simple.key`: `bool r = 5 > 3;` -/
theorem greaterThanSimple : ⊨ dl!{ ⟨ bool r = 5 > 3; ⟩ r == true } := by sol_symex; sol_close

/-- `greater-equal-simple.key`: `bool r = 5 >= 6;` -/
theorem greaterEqualSimple : ⊨ dl!{ ⟨ bool r = 5 >= 6; ⟩ r == false } := by sol_symex; sol_close

/-- `not-equal-simple.key`: `bool r = 3 != 4;` -/
theorem notEqualSimple : ⊨ dl!{ ⟨ bool r = 3 != 4; ⟩ r == true } := by sol_symex; sol_close

/-! ## Short-circuit

The right operand is a read that would revert: `values` is empty in
`exampleStore`, and in any state the box would have to cover a revert. -/

/--
trace: ⊢ ⊨ dl{ { r := false } ⟨ if (false) {r = values[7] == 0;r = r && true;} else {r = false;}; ⟩ r = false }
-/
#guard_msgs in
/-- `bool r; r = false && (values[7] == 0);` never reads `values[7]`. -/
theorem andShortCircuit : ⊨ dl!{ ⟨ bool r; r = false && (values[7] == 0); ⟩ r == false } := by
  sol_step
  sol_step
  trace_state
  sol_symex
  sol_close

/-- The conditional's untaken branch is not evaluated either. -/
theorem ternaryShortCircuit : ⊨ dl!{ ⟨ uint r = false ? values[7] : 5; ⟩ r == 5 } := by
  sol_symex
  sol_close

/-! ## Compound assignment and `++` -/

/-- `localAddAssign`, `localSubAssign`: `x += 5; x -= 3;` -/
theorem compoundLocal : ⊨ dl!{ ⟨ uint x = 10; x += 5; x -= 3; ⟩ x == 12 } := by
  sol_symex
  sol_close

/-- `localPreincrement`, `localPostincrement`: `++x; x++;` -/
theorem incrementLocal : ⊨ dl!{ ⟨ uint x = 5; ++x; x++; ⟩ x == 7 } := by
  sol_symex
  sol_close

/-- `storage-root-postincrement.key`: `age = 10; age++;` on a state variable
(`storageRootIncrement`). -/
theorem storageRootPostincrement : ⊨ dl!{ [ age = 10; age++; uint r = age; ] r == 11 } := by
  sol_symex
  sol_close

/-- `compoundAssignValueRhsCapture`: a non-simple right-hand side is
captured first. -/
theorem compoundCapture : ⊨ dl!{ ⟨ uint x = 1; uint y = 3; x += y + 2; ⟩ x == 6 } := by
  sol_symex
  sol_close

/-! ## The conditional -/

/-- `ternaryCaptureCond`, `ternaryToIf`: `x = (y > 2) ? 10 : 20` with a
complex condition captured first. -/
theorem ternaryCapture : ⊨ dl!{ ⟨ uint y = 3; uint x = (y > 2) ? 10 : 20; ⟩ x == 10 } := by
  sol_symex
  sol_close

/-- `ternaryToIf` on a simple condition. -/
theorem ternarySimple : ⊨ dl!{ ⟨ bool f = false; uint x = f ? 10 : 20; ⟩ x == 20 } := by
  sol_symex
  sol_close

/-! ## Operands in storage

Under the box: `⊨` quantifies over every state, including those without
`alice`, where the write is stuck (`Close.lean`). -/

/-- `addition-storage-read.key`: `alice.age = 10; uint r = alice.age + 1;` -/
theorem additionStorageRead :
    ⊨ dl!{ [ alice.age = 10; uint r = alice.age + 1; ] r == 11 } := by
  sol_symex
  sol_close

/-- `subtraction-storage-read.key`: `alice.age = 10; uint r = alice.age - 3;` -/
theorem subtractionStorageRead :
    ⊨ dl!{ [ alice.age = 10; uint r = alice.age - 3; ] r == 7 } := by
  sol_symex
  sol_close

/-- `addition-storage-write.key`: `alice.age = x + y;` -/
theorem additionStorageWrite :
    ⊨ dl!{ [ uint x = 5; uint y = 7; alice.age = x + y; uint r = alice.age; ] r == 12 } := by
  sol_symex
  sol_close

/-- `addition-both-storage.key`: `alice.age + bob.age`. -/
theorem additionBothStorage :
    ⊨ dl!{ [ alice.age = 10; bob.age = 5; uint r = alice.age + bob.age; ] r == 15 } := by
  sol_symex
  sol_close

/-- `addAssignValueRhsCapture` with a storage operand: `x += bob.age + 2;` -/
theorem compoundCaptureStorage :
    ⊨ dl!{ [ uint x = 1; bob.age = 3; x += bob.age + 2; ] x == 6 } := by
  sol_symex
  sol_close

/-- `ternaryCaptureCond` on a storage read: `(bob.age > 2) ? 10 : 20`. -/
theorem ternaryCaptureStorage :
    ⊨ dl!{ [ bob.age = 3; uint x = (bob.age > 2) ? 10 : 20; ] x == 10 } := by
  sol_symex
  sol_close

/-- `ternaryToIfStorage`: a storage target, `age = flag ? 10 : 20;` -/
theorem ternaryToIfStorage :
    ⊨ dl!{ [ bool f = false; age = f ? 10 : 20; uint r = age; ] r == 20 } := by
  sol_symex
  sol_close

end Solidity.Examples
