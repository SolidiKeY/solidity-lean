import Solidity.Calculus.Closers
import Solidity.Automation.SummaryCache

/-!
# Token transfer with a shared storage-writing helper

Storage writes are outside the symbolic-call rule; these calls expand. The verdict cache below
is a separate, explicitly encoded consumer: it does not claim that the current
front end extracts canonical keys or consumes `Specification.Certified`.
-/
namespace Solidity.Examples.Summaries.Token
open Solidity.Automation.Summary

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

/-- The helper transfers any amount at most ten from a ten-unit sender to an empty recipient. This is the callee verdict saved below. -/
def calleeGoal : Fml Token [] := dl!{
  senderBalance == 10 ∧ recipientBalance == 0 ∧ a <= 10 →
  ⟨ _transfer(a); ⟩ (senderBalance == 10 - a ∧ recipientBalance == a) }

/-- Solidity: `_transfer(a)` debits the sender and credits the recipient. -/
theorem _transferVerified : Fml.Valid calleeGoal := by
  unfold calleeGoal
  sol_prove
  sol_leaf
  sol_close

/-- Solidity: `transfer(4)` executes the common `_transfer` body (summary unsupported). -/
theorem transferVerified : ⊨ᶠ dl!{ senderBalance == 10 ∧ recipientBalance == 0 →
  [ transfer(4); ] (senderBalance == 6 ∧ recipientBalance == 4) } := by
  sol_prove

/-- Solidity: `transferFrom(4)` debits allowance and executes the common helper (summary unsupported). -/
theorem transferFromVerified : ⊨ᶠ dl!{ senderBalance == 10 ∧ recipientBalance == 0 ∧ allowance == 10 →
  [ transferFrom(4); ] (senderBalance == 6 ∧ recipientBalance == 4 ∧ allowance == 6) } := by
  sol_prove

/-- The helper has no calls; all other semantic metadata is retained in context.
`reprStr` is only a fixture encoding, not a canonical serialization theorem. -/
def keyFor (C : Contract) : Key :=
  ⟨reprStr (Semantics.lookupBy "_transfer" C.funs), "senderBalance=10,recipientBalance=0,a<=10 -> <_transfer(a)> senderBalance=10-a,recipientBalance=a",
    reprStr { C with funs := [] }, []⟩
def key : Key := keyFor Token

private def unrelatedEdit : Contract := { Token with
  funs := Token.funs.map (fun (n, f) => if n == "version" then
    (n, (contract!{ function version() pure returns (uint r) { r = 2; } }).funs.head!.2)
    else (n, f)) }
private def calleeEdit : Contract := { Token with
  funs := Token.funs.map (fun (n, f) => if n == "_transfer" then
    (n, (contract!{ function _transfer(uint amount) { senderBalance = senderBalance - amount; recipientBalance += 1; } }).funs.head!.2) else (n, f)) }

private def valid (k : Key) : Prop := k = key ∧ Fml.Valid calleeGoal
private def verdict : Verdict valid key := .proved ⟨rfl, _transferVerified⟩
private def saved : Cache valid := ({} : Cache valid).insert key verdict

/-- Reusing the saved helper verdict invokes no checker. -/
theorem cachedVerdictReused (verify : (k : Key) → Option (Verdict valid k)) :
    saved.check key verify = (some verdict, saved, false) :=
  Cache.check_hit _ _ _ _ (Cache.lookup_insert _ _ _)

-- Real source fixtures: change the unrelated declaration, then the helper body.
#guard keyFor unrelatedEdit == key
#guard (saved.lookup (keyFor unrelatedEdit)).isSome
#guard (saved.check (keyFor unrelatedEdit) (fun _ => none)).2.2 == false
#guard (saved.lookup (keyFor calleeEdit)).isNone
#guard (saved.check (keyFor calleeEdit) (fun _ => none)).2.2 == true

end Solidity.Examples.Summaries.Token
