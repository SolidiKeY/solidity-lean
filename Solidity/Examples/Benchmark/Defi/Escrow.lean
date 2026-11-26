import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# DeFi: owner-controlled escrow

Source: OpenZeppelin Contracts v4.9.6, `utils/escrow/Escrow.sol` and
`access/Ownable.sol`:
<https://github.com/OpenZeppelin/openzeppelin-contracts/blob/v4.9.6/contracts/utils/escrow/Escrow.sol>.

The inherited owner check is inlined. Events and ownership transfer/renunciation
are omitted; this is the escrow with a fixed deploying owner. `Address.sendValue`
is represented by `transfer`, so payment uses this model's transfer semantics,
not a claim about arbitrary EVM recipient callbacks. The checks-effects-payment
order and per-payee accounting are retained. Clauses spell the `@custom:key`
NatSpec in the surface notation, as in `Benchmark/Counter`.

Verdicts: constructor and depositsOf proved; deposit and withdraw unknown.
The payment obligation includes self-payment: the net ledger is unchanged when
payee is this contract. Box obligations concern successful runs, not liveness.
-/
namespace Solidity.Examples.Benchmark.Defi.Escrow

def Escrow : Contract := contract!{
  address owner;
  mapping(address => uint) deposits;
  ensures owner == msg.sender;
  constructor() {
    owner = msg.sender;
  }
  ensures \result == deposits[payee];
  function depositsOf(address payee) public view returns (uint) {
    return deposits[payee];
  }
  ensures deposits[payee] == \old(deposits[payee]) + msg.value;
  ensures owner == \old(owner);
  function deposit(address payee) public payable {
    require(msg.sender == owner);
    deposits[payee] += msg.value;
  }
  ensures deposits[payee] == 0;
  ensures owner == \old(owner);
  ensures payee != this -> net(payee) == \old(net(payee)) - \old(deposits[payee]);
  ensures payee == this -> net(payee) == \old(net(payee));
  function withdraw(address payee) public {
    require(msg.sender == owner);
    uint payment = deposits[payee];
    deposits[payee] = 0;
    payee.transfer(payment);
  }
}

local instance : InContract := ⟨Escrow⟩
open scoped Scoped

/-- The deploying account owns the escrow. -/
theorem constructor_spec : ⊢ spec!{ constructor } := by sol_prove
/-- Reading a payee's credit returns that credit. -/
theorem depositsOf_spec : ⊢ spec!{ depositsOf } := by sol_prove
/-- Unknown: after the payable snapshot and `save(deposits[payee], old + value)`,
`sol_prove` leaves credit equality and the owner frame. The standard leaf closer
also fails; the missing closure is old-storage/mapping-update normalization. -/
def deposit_obligation : Fml Escrow [] := spec!{ deposit }
/-- Unknown: the leaf is after `save(deposits[payee], 0); pay(payee, payment)`.
It must show cleared credit, unchanged owner, and the oldNet debit (or self-payment
identity). Missing closure: combined mapping-frame and snapshot-ledger reasoning. -/
def withdraw_obligation : Fml Escrow [] := spec!{ withdraw }

end Solidity.Examples.Benchmark.Defi.Escrow
