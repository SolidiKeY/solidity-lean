import Solidity.Examples.Summaries.Support

/-! Library: cached typed helper certificates and actual source-edit key controls. -/
namespace Solidity.Examples.Summaries.Library
open Solidity.Automation.Summary Solidity.Examples.Summaries.Support

def Library : Contract := contract!{
  function increment(uint x) pure returns (uint r) { r = x + 1; }
  function left(uint x) pure returns (uint r) { r = increment(increment(x)); }
  function right(uint x) pure returns (uint r) { r = increment(increment(x)); }
  function version() pure returns (uint r) { r = 1; }
}
local instance : InContract := ⟨Library⟩
open scoped Solidity.Scoped

def calleeGoal : Fml Library [] := dl!{ a < 1000 → ⟨ uint y = increment(a); ⟩ y == a + 1 }

def spec (m : Modality) : Specification Library [.val .uint] [.val .uint] [.val .uint, .val .uint] :=
  { body := summary_body dl!{ [ y = increment(4); ] true }
    requires := cdlIn![uint x]{ x < 1000 }
    ensures := cdlIn![uint x, old, oldNet, uint r]{ r == x + 1 }
    modality := m, mutability := .pure }
/-- Solidity: `increment` is certified once for all caller frames, targets and modalities. -/
theorem certified (m : Modality) : (spec m).Certified := by
  apply certifyScalar _ ?_ rfl rfl
  cases m <;> (sol_prove; all_goals (sol_leaf; sol_close))

def keyFor (C : Contract) : Key := leafKey C "increment" "x<1000; r=x+1; pure; box and diamond"
def key : Key := keyFor Library
private def calleeEdit := editFunction Library "increment"
  (contract!{ function increment(uint x) pure returns (uint r) { r = x + 2; } })
private def checked : CheckedSummary key (∀ m, (spec m).Certified) := ⟨certified⟩
/-- Solidity: retrieve the stored `increment` certificate. -/
private theorem cached : ∀ m, (spec m).Certified := checked.fromCache
#guard checked.edits (keyFor (editUnrelated Library)) (keyFor calleeEdit)

/-- Solidity: the original `increment` result claim consumes the cached certificate. -/
theorem incrementVerified : Fml.Valid calleeGoal := by
  unfold calleeGoal
  summary_calls 1 (spec .diamond) (cached .diamond)

/-- Solidity: `left` uses the helper certificate 2 time(s). -/
theorem leftVerified : ⊨ᶠ dl!{ [ uint y = left(4); ] y == 6 } := by
  summary_calls 2 (spec .box) (cached .box)

/-- Solidity: `right` uses the helper certificate 2 time(s). -/
theorem rightVerified : ⊨ᶠ dl!{ [ uint y = right(4); ] y == 6 } := by
  summary_calls 2 (spec .box) (cached .box)

end Solidity.Examples.Summaries.Library
