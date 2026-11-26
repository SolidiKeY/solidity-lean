import Solidity.Backend.AbiWorld.PublicCompilerTotal

/-!
# Default locals need not have a word-sized intrinsic memory address

These controls use the existing compiler and intrinsic machine only. They
exclude a universal fixed layout mapping cell `b` to byte address `32*b`
with a word-sized end address. They do not select a replacement layout or
claim byte execution agreement, or construct a full `Compilation.Input`.
-/

namespace Solidity.Examples.Backend.BytesFullMachine.FixedLayout

open Evm
open Backend.AbiWorld.PublicCompilerTotal

/-- Solidity `uint x;` is in the existing accepted program domain. -/
theorem defaultLocal_accepted (C : Contract) (x : Var) :
    ProgOk (C := C) (Γ := []) [] (.cons (.declLocal .uint x none) .nil) :=
  .cons (.declNone .uint x) .nil

/-- Solidity `uint x;` at an empty context writes the actual intrinsic cell `b`. -/
theorem defaultLocal_code (C : Contract) (x : Var) (b : Nat) :
    compileStmt b (C := C) (Γ := []) (.declLocal .uint x none) =
      [.push w[0], .mstore b] := rfl

/-- Solidity `uint x;` resets cell `b`, preserving all other machine fields. -/
theorem defaultLocal_run (C : Contract) (x : Var) (b : Nat) (m : Machine) :
    run (compileStmt b (C := C) (Γ := []) (.declLocal .uint x none)) m =
      .ok { m with mem := upd m.mem b w[0] } 0 := rfl

/-- The fixed byte layout cannot fit the cell for `uint x;` at base `W`. -/
theorem wordBase_not_fixedLayout : ¬ (32 * W + 32 ≤ W) := by omega

/-- No universal fixed-layout bound follows from acceptance of `uint x;`. -/
theorem accepted_not_universal_fixedLayout (C : Contract) (x : Var) :
    ¬ (ProgOk (C := C) (Γ := []) [] (.cons (.declLocal .uint x none) .nil) →
      ∀ b : Nat, 32 * b + 32 ≤ W) := by
  intro h
  exact wordBase_not_fixedLayout (h (defaultLocal_accepted C x) W)

end Solidity.Examples.Backend.BytesFullMachine.FixedLayout
