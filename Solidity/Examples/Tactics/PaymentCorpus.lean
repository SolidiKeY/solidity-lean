import Solidity.Calculus.Close
import Solidity.Calculus.PaymentClose
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.CallbackSound
import Solidity.Calculus.CallbackDerive
import Solidity.Calculus.WalkSyntax

/-!
# The PiggyBank callback payout body

The body and invariant of `net/piggybank-breakPiggyBank-withcallback.key`.
This hand-written typed body is kernel evidence, separate from the corpus
adapter and compiler/EVM evidence. The original zero-msg.value entry booking
is included explicitly. No corpus verdict changes before this proof checks.
The unrelated helpers are omitted: `ValidC` assumes invariant-preserving
callback resumptions. This does not establish those helpers' invariants or
whole-contract reentrancy safety.
-/



namespace Solidity.Examples.Tactics.PaymentCorpus

/-- The original PiggyBank fields and payment-last `breakPiggyBank` body. -/
def PiggyBank : Contract := contract!{
  address owner; address paidBy; uint paidValue;
  uint state; uint timeOfFirstDeposit; uint balance; uint timeNow; bool sent;
  function breakPiggyBank() {
    address own = owner;
    require(msg.sender == own);
    uint st = state;
    require(st == 1);
    uint dl = timeOfFirstDeposit + 31536000;
    require(timeNow >= dl);
    uint b = balance;
    state = 2;
    owner.transfer(b);
  }
}

local instance : InContract := ⟨PiggyBank⟩
open scoped Scoped
open Semantics

/-- Original ledger invariant, with each equality written symmetrically. -/
def piggyInv : Invariant PiggyBank := ⟨dl!{
  (state != 2 → net(owner) = balance) && (state == 2 → net(owner) = 0) }, rfl⟩

/-- The exact original entry update preserves the facts needed by the body. -/
private def entryPre (m : Modality) : Fml PiggyBank [] := dl![m]{
  msg.value == 0 → owner != this →
  ((state != 2 → net(owner) = balance) && (state == 2 → net(owner) = 0)) →
  { net := store(net, at(msg.sender), net(msg.sender) + msg.value) ‖
    selfBalance := selfBalance + msg.value }
  (owner != this &&
    ((state != 2 → net(owner) = balance) && (state == 2 → net(owner) = 0))) }

/-- Zero-value entry booking preserves observations, including missing ledger slots. -/
theorem entry_preserves_pre (m : Modality) : Fml.Valid (entryPre m) := by
  cases m <;> (unfold entryPre; sol_close)

/- The exact original payment-last body, from arbitrary states satisfying its invariant. -/
sol_auto_theorem breakPiggyBank_body_callback :
    ValidC piggyInv dl!{ owner != this →
      ((state != 2 → net(owner) = balance) && (state == 2 → net(owner) = 0)) →
      [ breakPiggyBank(); ]
      ((state != 2 → net(owner) = balance) && (state == 2 → net(owner) = 0)) } := by
  sol_payment_close

/-- The exact payment-last body keeps the original invariant with callbacks;
refusal and failed guards retain their original box reading. -/
theorem breakPiggyBank_callback :
    ValidC piggyInv dl!{ msg.value == 0 → owner != this →
      ((state != 2 → net(owner) = balance) && (state == 2 → net(owner) = 0)) →
      { net := store(net, at(msg.sender), net(msg.sender) + msg.value) ‖
        selfBalance := selfBalance + msg.value }
      [ breakPiggyBank(); ]
      ((state != 2 → net(owner) = balance) && (state == 2 → net(owner) = 0)) } := by
  intro σ hz ho hi
  have entry : holdsC piggyInv.fml true σ (entryPre .box) :=
    (holdsC_iff_holds (I := piggyInv.fml) (pay := true) (entryPre .box) rfl σ).2
      (entry_preserves_pre .box σ)
  apply Upd.afterT_imp (m := .box) (p := fun τ => holdsC piggyInv.fml true τ dl!{
    owner != this &&
      ((state != 2 → net(owner) = balance) && (state == 2 → net(owner) = 0)) })
    (entry hz ho hi)
  intro τ hp
  exact breakPiggyBank_body_callback τ hp.1 hp.2

#print axioms entry_preserves_pre
#print axioms breakPiggyBank_body_callback
#print axioms breakPiggyBank_callback

end Solidity.Examples.Tactics.PaymentCorpus
