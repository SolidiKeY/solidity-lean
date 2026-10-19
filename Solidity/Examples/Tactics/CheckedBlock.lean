import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Inspect

/-!
# `checked { … }`: an overflow fails the proof

KeY Java's `arithmeticSemanticsCheckingOF` (`docs/options.md`, O2).  Outside
the block a checked operation that leaves its range reverts, as solc's
`Panic(0x11)` does, and the box accepts a revert: `[ uint x = 0; x -= 1; ]
false` holds.  Inside it every statement is preceded by an `assert` of the
ranges it needs (`Prog.checkOF`, `Syntax/Checked.lean`), and a failing
`assert` is a panic, which no modality accepts: the same box is false, and a
proof of one says that no checked operation overflows.

* §1 — the underflow, outside and inside the block, and what the block writes;
* §2 — proofs inside the block: the guards owed and discharged;
* §3 — evaluation order: `&&`, `?:`, a loop's condition, a narrow type;
* §4 — `ignoringOverflow { … }` (`ignoringOF`, O5): an overflowing run
  assumed away, under either modality.
-/

namespace Solidity.Examples.Tactics.CheckedBlock

local instance : InContract := ⟨StandardExample⟩

open scoped Scoped

/-! ## 1 · The underflow -/

/-- Outside the block, `0 - 1` reverts, and the box holds of `false`. -/
theorem underflowBox : ⊨ dl!{ [ uint x = 0; x -= 1; ] false } := by
  sol_symex
  sol_close

/-- Inside it, the run fails the `assert` first: the box does not hold. -/
theorem underflowChecked : ¬ (⊨ dl!{ [ checked { uint x = 0; x -= 1; }; ] false }) :=
  fun h => Modality.afterRunTR_not_panic (h (State.init _)) (by decide +kernel)

/-! What the block writes: `1 <= x` before `x -= 1`. -/

/--
info: dl{ [ uint x = 0; assert(1 <= x); x -= 1; ] false } : Fml StandardExample []
-/
#guard_msgs in
#check (dl!{ [ checked { uint x = 0; x -= 1; }; ] false } : Fml StandardExample [])

/-! ## 2 · Proofs inside the block -/

/-- In range, the guard holds: `5 - 1`. -/
theorem inRange : ⊨ dl!{ [ uint x = 5; checked { x -= 1; }; ] x == 4 } := by
  sol_symex
  sol_close

/-- A bound on the inputs discharges the guard of `a + 1`. -/
theorem bounded : ⊨ dl!{ ∀ uint a; a <= 100 → [ uint y; checked { y = a + 1; }; ] y <= 101 } := by
  sol_symex
  sol_close

/-- Without one, `a + 1` may overflow: the box fails at `a = 2^256 - 1`. -/
theorem unbounded : ¬ (⊨ dl!{ ∀ uint a; [ checked { uint y = a + 1; }; ] true }) :=
  fun h => Modality.afterRunTR_not_panic (h (State.init _) ⟨((2 ^ 256 - 1 : Nat) : Int), by decide⟩)
    (by decide +kernel)

/-! ## 3 · Evaluation order -/

/-- `z > 0 && z - 1 >= 0`: `z - 1` is guarded only where it is evaluated. -/
theorem shortCircuit : ⊨ dl!{ [ uint z = 0; bool b; checked { b = z > 0 && z - 1 >= 0; }; ] b == false } := by
  sol_symex
  sol_close

/-! A loop's condition is guarded at its head and after every iteration. -/

/--
info: dl{
  [ uint i = 0; assert(i <= i +% 1); while (i + 1 < 4) {assert(i <= i +% 1);i += 1;assert(i <= i +% 1);}; ]
    true } : Fml StandardExample []
-/
#guard_msgs in
#check (dl!{ [ checked { uint i = 0; while (i + 1 < 4) { i += 1; } }; ] true } : Fml StandardExample [])

/-- A narrow type's check is an `assert` inside the block: `250 + 10` at
`uint8` fails it. -/
theorem narrow : ¬ (⊨ dl!{ [ checked { uint8 x = 250; x += 10; }; ] false }) :=
  fun h => Modality.afterRunTR_not_panic (h (State.init _)) (by decide +kernel)

/-! ## 4 · `ignoringOverflow { … }`: an overflow assumed away

KeY Java's `arithmeticSemanticsIgnoringOF` reads integers as mathematical
ones, which the typed state cannot hold (a `uint` local is 256 bits).  The
block reads it soundly instead: where an operation would leave its range the
run is assumed away (`assume(false);`, `LeanTaclet.assumeFalse`), and an
assumed-away run satisfies every formula.  The box is unchanged in effect
(it accepts the revert already); the diamond now claims termination only
for the runs that do not overflow. -/

/-! What the block writes: `if (1 <= x) {} else { assume(false); }` before
`x -= 1`. -/

/--
info: dl{ ⟨ uint x = 0; if (1 <= x) {} else {assume(false);}; x -= 1; ⟩ false } : Fml StandardExample []
-/
#guard_msgs in
#check (dl!{ ⟨ ignoringOverflow { uint x = 0; x -= 1; }; ⟩ false } : Fml StandardExample [])

/-- The underflow is assumed away: even `false` holds after it. -/
theorem underflowIgnored : ⊨ dl!{ ⟨ ignoringOverflow { uint x = 0; x -= 1; }; ⟩ false } := by
  sol_symex
  sol_close

/-- Termination with `y > a`, for every `a` but the one where `a + 1`
overflows. -/
theorem endsIgnoring : ⊨ dl!{ ∀ uint a; ⟨ uint y; ignoringOverflow { y = a + 1; }; ⟩ y > a } := by
  sol_symex
  sol_close

/-- Without the block it is false: at `a = 2^256 - 1` the run reverts. -/
theorem endsPlain : ¬ (⊨ dl!{ ∀ uint a; ⟨ uint y; y = a + 1; ⟩ y > a }) :=
  fun h => Modality.afterRunTR_diamond_fail (h (State.init _) ⟨((2 ^ 256 - 1 : Nat) : Int), by decide⟩)
    (by decide +kernel)

/-! The two blocks do not nest in each other. -/

/--
error: Solidity elaboration failed: `checked { … }` and `ignoringOverflow { … }` do not nest in each other
-/
#guard_msgs in
#check (dl!{ [ checked { ignoringOverflow { uint x = 1; }; }; ] true } : Fml StandardExample [])

end Solidity.Examples.Tactics.CheckedBlock
