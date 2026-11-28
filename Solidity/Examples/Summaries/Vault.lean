import Solidity.Examples.Summaries.Support

/-! Vault: cached typed helper certificates and actual source-edit key controls. -/
namespace Solidity.Examples.Summaries.Vault
open Solidity.Automation.Summary Solidity.Examples.Summaries.Support

def Vault : Contract := contract!{
  function shares(uint assets) pure returns (uint r) { r = assets * 2; }
  function deposit(uint assets) pure returns (uint r) { r = shares(assets); }
  function preview(uint assets) pure returns (uint r) { r = shares(assets); }
  function version() pure returns (uint r) { r = 1; }
}
local instance : InContract := ⟨Vault⟩
open scoped Solidity.Scoped

def calleeGoal : Fml Vault [] := dl!{ a < 1000 → ⟨ uint y = shares(a); ⟩ y == a + a }

def spec (m : Modality) : Specification Vault [.val .uint] [.val .uint] [.val .uint, .val .uint] :=
  { body := summary_body dl!{ [ y = shares(4); ] true }
    requires := cdlIn![uint x]{ x < 1000 }
    ensures := cdlIn![uint x, old, oldNet, uint r]{ r == x + x }
    modality := m, mutability := .pure }
/-- Solidity: `shares` is certified once for all caller frames, targets and modalities. -/
theorem certified (m : Modality) : (spec m).Certified := by
  apply certifyScalar _ ?_ rfl rfl
  cases m <;> (sol_prove; all_goals (sol_leaf; sol_close))

def keyFor (C : Contract) : Key := leafKey C "shares" "x<1000; r=x+x; pure; box and diamond"
def key : Key := keyFor Vault
private def calleeEdit := editFunction Vault "shares"
  (contract!{ function shares(uint assets) pure returns (uint r) { r = assets * 3; } })
private def checked : CheckedSummary key (∀ m, (spec m).Certified) := ⟨certified⟩
/-- Solidity: retrieve the stored `shares` certificate. -/
private theorem cached : ∀ m, (spec m).Certified := checked.fromCache
#guard checked.edits (keyFor (editUnrelated Vault)) (keyFor calleeEdit)

/-- Solidity: the original `shares` result claim consumes the cached certificate. -/
theorem sharesVerified : Fml.Valid calleeGoal := by
  unfold calleeGoal
  summary_calls 1 (spec .diamond) (cached .diamond)

/-- Solidity: `deposit` uses the helper certificate 1 time(s). -/
theorem depositVerified : ⊨ᶠ dl!{ [ uint y = deposit(4); ] y == 8 } := by
  summary_calls 1 (spec .box) (cached .box)

/-- Solidity: `preview` uses the helper certificate 1 time(s). -/
theorem previewVerified : ⊨ᶠ dl!{ [ uint y = preview(4); ] y == 8 } := by
  summary_calls 1 (spec .box) (cached .box)

end Solidity.Examples.Summaries.Vault
