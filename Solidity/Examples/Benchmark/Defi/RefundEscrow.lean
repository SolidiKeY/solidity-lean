import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# DeFi: refundable crowdfunding escrow

Source: OpenZeppelin Contracts v4.9.6 `RefundEscrow.sol`:
<https://github.com/OpenZeppelin/openzeppelin-contracts/blob/v4.9.6/contracts/utils/escrow/RefundEscrow.sol>.
The inherited Escrow/ConditionalEscrow owner and withdrawal checks are inlined.
Events, view accessors and ownership transfer/renunciation are omitted. Numeric
states are Active=0, Refunding=1, Closed=2. Transfers stand for Address.sendValue;
this is the accounting/state-machine benchmark, not EVM callback equivalence.
The beneficiary is fixed at deployment, as in the source. Constructor address(0)
is written 0. A closed escrow releases its actual ETH balance, not a sum supplied
by the caller; a refund clears the recorded credit before the payment.
-/
namespace Solidity.Examples.Benchmark.Defi.RefundEscrow

def RefundEscrow : Contract := contract!{
  address owner;
  address beneficiary;
  uint state;
  mapping(address => uint) deposits;
  ensures owner == msg.sender && beneficiary == recipient && state == 0;
  constructor(address recipient) {
    require(recipient != 0);
    owner = msg.sender;
    beneficiary = recipient;
    state = 0;
  }
  ensures state == 0 && deposits[payee] == \old(deposits[payee]) + msg.value;
  function deposit(address payee) public payable {
    require(msg.sender == owner);
    require(state == 0);
    deposits[payee] += msg.value;
  }
  ensures state == 2;
  function close() public {
    require(msg.sender == owner);
    require(state == 0);
    state = 2;
  }
  ensures state == 1;
  function enableRefunds() public {
    require(msg.sender == owner);
    require(state == 0);
    state = 1;
  }
  ensures state == 2;
  ensures beneficiary != this -> address(this).balance == 0;
  function beneficiaryWithdraw() public {
    require(state == 2);
    beneficiary.transfer(address(this).balance);
  }
  ensures state == 1 && deposits[payee] == 0;
  ensures payee != this -> net(payee) == \old(net(payee)) - \old(deposits[payee]);
  ensures payee == this -> net(payee) == \old(net(payee));
  function withdraw(address payee) public {
    require(msg.sender == owner);
    require(state == 1);
    uint payment = deposits[payee];
    deposits[payee] = 0;
    payee.transfer(payment);
  }
}
local instance : InContract := ⟨RefundEscrow⟩
open scoped Scoped

/-- Deployment fixes the beneficiary and opens the escrow. -/
theorem constructor_spec : ⊢ spec!{ constructor } := by sol_prove
/-- Only active deposits credit a payee. -/
def deposit_obligation : Fml RefundEscrow [] := spec!{ deposit }
/- Unknown: after the payable snapshot and credit save, show state=Active and
credit=old credit+msg.value. Missing payable mapping/snapshot leaf closure. -/
/-- Closing is available only to the owner from Active. -/
theorem close_spec : ⊢ spec!{ close } := by sol_prove
/-- Enabling refunds is available only to the owner from Active. -/
theorem enableRefunds_spec : ⊢ spec!{ enableRefunds } := by sol_prove
/-- Beneficiary release requires Closed. -/
def beneficiaryWithdraw_obligation : Fml RefundEscrow [] := spec!{ beneficiaryWithdraw }
/- Unknown: after pay(beneficiary,selfBalance), the calculus leaf still asks
beneficiary!=this -> selfBalance=0. Missing rule: transfer balance update in the
calculus (operational State.pay does debit selfBalance). -/

/-- The state-machine part of beneficiary release is proved separately. -/
theorem beneficiaryWithdraw_state : ⊢ dl!{ [ beneficiaryWithdraw(); ] state == 2 } := by
  sol_prove
/-- Refunds require Refunding, and clear the credit before payment. -/
def withdraw_obligation : Fml RefundEscrow [] := spec!{ withdraw }
/- Unknown: after clearing credit and pay, show Refunding, zero credit and the
oldNet debit/self-payment identity. Missing mapping-frame/ledger closure. -/

end Solidity.Examples.Benchmark.Defi.RefundEscrow
