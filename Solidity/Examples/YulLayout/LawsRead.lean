import Solidity.Yul.Layout.Laws.Read

/-! Check of `Yul/Layout/Laws/Read.lean`: `local_read` at a full-width scalar. -/
namespace Solidity.Examples.YulLayout.LawsRead

open Solidity.Goals
open Solidity.Yul.Layout

/-- A memory word read sees only the 32 bytes of its word. -/
example (P : Shrink.Params) (a : Nat) (m m' : Shrink.Phys)
    (same : ∀ x, a ≤ x → x < a + 32 → m.memory x = m'.memory x) :
    geometry.read P (.scalar 32) ⟨.memory, a, 0⟩ m =
      geometry.read P (.scalar 32) ⟨.memory, a, 0⟩ m' :=
  local_read P (.scalar 32) ⟨.memory, a, 0⟩ m m' fun c hc => by
    cases c with
    | slot r w b => exact hc.elim
    | mem x => exact congrArg UInt8.toNat (same x hc.1 hc.2)

end Solidity.Examples.YulLayout.LawsRead
