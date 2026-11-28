import Solidity.Examples.Summaries.Support

/-! Pricing: cached typed helper certificates and actual source-edit key controls. -/
namespace Solidity.Examples.Summaries.Pricing
open Solidity.Automation.Summary Solidity.Examples.Summaries.Support

def Pricing : Contract := contract!{
  function quote(uint units) pure returns (uint r) { r = units + 7; }
  function buy(uint units) pure returns (uint r) { r = quote(units); }
  function estimate(uint units) pure returns (uint r) { r = quote(units); }
  function version() pure returns (uint r) { r = 1; }
}
local instance : InContract := ⟨Pricing⟩
open scoped Solidity.Scoped

def calleeGoal : Fml Pricing [] := dl!{ a < 1000 → ⟨ uint y = quote(a); ⟩ y == a + 7 }

def spec (m : Modality) : Specification Pricing [.val .uint] [.val .uint] [.val .uint, .val .uint] :=
  { body := summary_body dl!{ [ y = quote(4); ] true }
    requires := cdlIn![uint x]{ x < 1000 }
    ensures := cdlIn![uint x, old, oldNet, uint r]{ r == x + 7 }
    modality := m, mutability := .pure }
/-- Solidity: `quote` is certified once for all caller frames, targets and modalities. -/
theorem certified (m : Modality) : (spec m).Certified := by
  apply certifyScalar _ ?_ rfl rfl
  cases m <;> (sol_prove; all_goals (sol_leaf; sol_close))

def keyFor (C : Contract) : Key := leafKey C "quote" "x<1000; r=x+7; pure; box and diamond"
def key : Key := keyFor Pricing
private def calleeEdit := editFunction Pricing "quote"
  (contract!{ function quote(uint units) pure returns (uint r) { r = units + 8; } })
private def checked : CheckedSummary key (∀ m, (spec m).Certified) := ⟨certified⟩
/-- Solidity: retrieve the stored `quote` certificate. -/
private theorem cached : ∀ m, (spec m).Certified := checked.fromCache
#guard checked.edits (keyFor (editUnrelated Pricing)) (keyFor calleeEdit)

/-- Solidity: the original `quote` result claim consumes the cached certificate. -/
theorem quoteVerified : Fml.Valid calleeGoal := by
  unfold calleeGoal
  summary_calls 1 (spec .diamond) (cached .diamond)

/-- Solidity: `buy` uses the helper certificate 1 time(s). -/
theorem buyVerified : ⊨ᶠ dl!{ [ uint y = buy(4); ] y == 11 } := by
  summary_calls 1 (spec .box) (cached .box)

/-- Solidity: `estimate` uses the helper certificate 1 time(s). -/
theorem estimateVerified : ⊨ᶠ dl!{ [ uint y = estimate(4); ] y == 11 } := by
  summary_calls 1 (spec .box) (cached .box)

end Solidity.Examples.Summaries.Pricing
