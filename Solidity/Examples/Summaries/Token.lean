import Solidity.Examples.Summaries.Support

/-! Token: cached typed helper certificates and actual source-edit key controls. -/
namespace Solidity.Examples.Summaries.Token
open Solidity.Automation.Summary Solidity.Examples.Summaries.Support

def Token : Contract := contract!{
  uint senderBalance;
  uint recipientBalance;
  uint allowance;
  function _transfer(uint amount) {
    senderBalance = senderBalance - amount;
    recipientBalance = recipientBalance + amount;
  }
  function transfer(uint amount) { _transfer(amount); }
  function transferFrom(uint amount) { allowance = allowance - amount; _transfer(amount); }
  function version() pure returns (uint r) { r = 1; }
}
local instance : InContract := ⟨Token⟩
open scoped Solidity.Scoped

def calleeGoal : Fml Token [] := dl!{
  senderBalance == 10 ∧ recipientBalance == 0 ∧ a <= 10 →
  ⟨ _transfer(a); ⟩ (senderBalance == 10 - a ∧ recipientBalance == a) }

def spec (m : Modality) : Specification Token [.val .uint] [] [.val .uint] :=
  { body := summary_body dl!{ [ _transfer(4); ] true }
    requires := cdlIn![uint x]{ senderBalance == 10 ∧ recipientBalance == 0 ∧ x <= 10 }
    ensures := cdlIn![uint x, old, oldNet]{ (senderBalance == 10 - x ∧ recipientBalance == x) ∧ find(storage, allowance) = find(old, allowance) }
    modality := m, mutability := .nonpayable }
/-- Solidity: the box obligation for `_transfer`, including allowance preservation. -/
private theorem obligationBox : Fml.Valid (closedObligation (spec .box) .none) := by
  sol_prove
  sol_leaf
  sol_close
/-- Solidity: the diamond obligation also proves `_transfer` returns. -/
private theorem obligationDiamond : Fml.Valid (closedObligation (spec .diamond) .none) := by
  sol_prove
  sol_leaf
  sol_close
/-- Solidity: `_transfer` is certified once, including the unchanged allowance frame. -/
theorem certified (m : Modality) : (spec m).Certified := by
  apply certifyVoid _ (.snoc .nil .uint (.user "x") (.simple (.lit 0 rfl))) ?_ rfl rfl
  cases m with
  | box => exact obligationBox
  | diamond => exact obligationDiamond

def keyFor (C : Contract) : Key := leafKey C "_transfer" "sender=10; recipient=0; x<=10; sender=10-x; recipient=x; allowance=old allowance; nonpayable; box and diamond"
def key : Key := keyFor Token
private def calleeEdit := editFunction Token "_transfer"
  (contract!{ function _transfer(uint amount) { senderBalance -= amount; recipientBalance += 1; } })
private def checked : CheckedSummary key (∀ m, (spec m).Certified) := ⟨certified⟩
/-- Solidity: retrieve the stored `_transfer` certificate. -/
private theorem cached : ∀ m, (spec m).Certified := checked.fromCache
#guard checked.edits (keyFor (editUnrelated Token)) (keyFor calleeEdit)

/-- Solidity: the original `_transfer` result claim consumes the cached certificate. -/
theorem _transferVerified : Fml.Valid calleeGoal := by
  unfold calleeGoal
  summary_calls 1 (spec .diamond) (cached .diamond)

/-- Solidity: `transfer` uses the helper certificate 1 time(s). -/
theorem transferVerified : ⊨ᶠ dl!{ senderBalance == 10 ∧ recipientBalance == 0 →
  [ transfer(4); ] (senderBalance == 6 ∧ recipientBalance == 4) } := by
  summary_calls 1 (spec .box) (cached .box)

/-- Solidity: `transferFrom` uses the helper certificate 1 time(s). -/
theorem transferFromVerified : ⊨ᶠ dl!{ senderBalance == 10 ∧ recipientBalance == 0 ∧ allowance == 10 →
  [ transferFrom(4); ] (senderBalance == 6 ∧ recipientBalance == 4 ∧ allowance == 6) } := by
  summary_calls 1 (spec .box) (cached .box)

end Solidity.Examples.Summaries.Token
