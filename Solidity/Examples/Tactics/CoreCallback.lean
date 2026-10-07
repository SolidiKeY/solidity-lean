import Solidity.Semantics.Core.Callback
import Solidity.Calculus.Core.Notation

/-!
# The callback reading on scoped formulas

`Semantics/Core/Callback.lean` used: an invariant is a closed scoped formula
(`Core.Fml C []`, no closedness proof), and a modal formula over a program
that pays, valid with callbacks, is valid without (`valid_of_validC`); with no
payment the two readings agree (`holdsC_iff_holds`).
-/

namespace Solidity.Examples.Tactics.CoreCallback

open Solidity

local instance : InContract := ⟨StandardExample⟩

/-- `total` is never below `alice.age`: a formula of the storage alone. -/
def inv : Core.Invariant StandardExample := ⟨cdl!{ alice.age <= total }⟩

/-- A precondition, then a program that pays: valid with callbacks, it is
valid without. -/
example (H : Core.ValidC inv cdl!{ alice.age == 0 → [ uint to = 9; to.transfer(2); ] true }) :
    Core.Valid cdl!{ alice.age == 0 → [ uint to = 9; to.transfer(2); ] true } := by
  intro σ
  exact Core.holds_of_holdsC_imp (H σ) rfl rfl rfl

/-- With no payment the two readings agree. -/
example (σ : Core.State StandardExample []) :
    Core.holdsC inv σ cdl!{ [ alice.age = 1; uint y = alice.age; ] y == 1 } ↔
      Core.holds σ cdl!{ [ alice.age = 1; uint y = alice.age; ] y == 1 } :=
  Core.holdsC_iff_holds _ rfl σ

end Solidity.Examples.Tactics.CoreCallback
