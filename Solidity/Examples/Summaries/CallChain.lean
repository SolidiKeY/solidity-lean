import Solidity.Examples.Summaries.Support

/-! CallChain: cached typed helper certificates and actual source-edit key controls. -/
namespace Solidity.Examples.Summaries.CallChain
open Solidity.Automation.Summary Solidity.Examples.Summaries.Support

def CallChain : Contract := contract!{
  function seed(uint x) pure returns (uint r) { r = x + 1; }
  function middle(uint x) pure returns (uint r) { r = seed(x); }
  function outer(uint x) pure returns (uint r) { r = middle(x); }
  function first(uint x) pure returns (uint r) { r = outer(x); }
  function twice(uint x) pure returns (uint r) { r = middle(middle(x)); }
  function version() pure returns (uint r) { r = 1; }
}
local instance : InContract := ⟨CallChain⟩
open scoped Solidity.Scoped

def calleeGoal : Fml CallChain [] := dl!{ a < 1000 → ⟨ uint y = seed(a); ⟩ y == a + 1 }

def spec (m : Modality) : Specification CallChain [.val .uint] [.val .uint] [.val .uint, .val .uint] :=
  { body := summary_body dl!{ [ y = seed(4); ] true }
    requires := cdlIn![uint x]{ x < 1000 }
    ensures := cdlIn![uint x, old, oldNet, uint r]{ r == x + 1 }
    modality := m, mutability := .pure }
/-- Solidity: `seed` is certified once for all caller frames, targets and modalities. -/
theorem certified (m : Modality) : (spec m).Certified := by
  apply certifyScalar _ ?_ rfl rfl
  cases m <;> (sol_prove; all_goals (sol_leaf; sol_close))

def keyFor (C : Contract) : Key := leafKey C "seed" "x<1000; r=x+1; pure; box and diamond"
def key : Key := keyFor CallChain
private def calleeEdit := editFunction CallChain "seed"
  (contract!{ function seed(uint x) pure returns (uint r) { r = x + 2; } })
private def checked : CheckedSummary key (∀ m, (spec m).Certified) := ⟨certified⟩
/-- Solidity: retrieve the stored `seed` certificate. -/
private theorem cached : ∀ m, (spec m).Certified := checked.fromCache
#guard checked.edits (keyFor (editUnrelated CallChain)) (keyFor calleeEdit)

/-- Solidity: the original `seed` result claim consumes the cached certificate. -/
theorem seedVerified : Fml.Valid calleeGoal := by
  unfold calleeGoal
  summary_calls 1 (spec .diamond) (cached .diamond)

/-- Solidity: `first` uses the helper certificate 1 time(s). -/
theorem firstVerified : ⊨ᶠ dl!{ [ uint y = first(2); ] y == 3 } := by
  summary_calls 1 (spec .box) (cached .box)

/-- Solidity: `middle` uses the helper certificate 1 time(s). -/
theorem middleVerified : ⊨ᶠ dl!{ [ uint y = middle(2); ] y == 3 } := by
  summary_calls 1 (spec .box) (cached .box)

/-- Solidity: `twice` uses the helper certificate 2 time(s). -/
theorem twiceVerified : ⊨ᶠ dl!{ [ uint y = twice(2); ] y == 4 } := by
  summary_calls 2 (spec .box) (cached .box)

end Solidity.Examples.Summaries.CallChain
