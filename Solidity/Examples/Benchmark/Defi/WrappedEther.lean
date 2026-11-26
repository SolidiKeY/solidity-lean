import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Run

/-!
# DeFi: WETH deposit/withdraw accounting

Source: Solmate v6 `src/tokens/WETH.sol`:
<https://github.com/transmissions11/solmate/blob/v6/src/tokens/WETH.sol>.

This benchmark isolates deposit and withdraw from inherited ERC20 transfers.
The inherited `_mint` and `_burn` accounting is inlined; events and metadata
are omitted. The low-level ETH call is represented by `transfer`, retaining
burn-before-payment order. This is a model-level accounting benchmark, not an
EVM callback or gas-stipend equivalence claim. The source's checked supply
increment and balance decrement, and unchecked companion updates, are retained.
The receive entry point is omitted: it only delegates to deposit.

The natural specifications retain both supply and individual balances. A
successful wrap/unwrap must debit the same amount it credited. No assumption
about an initially empty mapping or global supply equality is implicit.
-/
namespace Solidity.Examples.Benchmark.Defi.WrappedEther

def WrappedEther : Contract := contract!{
  uint public totalSupply;
  mapping(address => uint) public balanceOf;
  ensures balanceOf[msg.sender] == \old(balanceOf[msg.sender]) + msg.value;
  ensures totalSupply == \old(totalSupply) + msg.value;
  function deposit() public payable {
    totalSupply += msg.value;
    unchecked { balanceOf[msg.sender] += msg.value; };
  }
  ensures balanceOf[msg.sender] == \old(balanceOf[msg.sender]) - amount;
  ensures totalSupply == \old(totalSupply) - amount;
  ensures msg.sender != this -> net(msg.sender) == \old(net(msg.sender)) - amount;
  ensures msg.sender == this -> net(msg.sender) == \old(net(msg.sender));
  function withdraw(uint amount) public {
    balanceOf[msg.sender] -= amount;
    unchecked { totalSupply -= amount; };
    msg.sender.transfer(amount);
  }
}

local instance : InContract := ⟨WrappedEther⟩
open scoped Scoped

/-- Wrap: mint exactly the attached value. -/
def deposit_obligation : Fml WrappedEther [] := spec!{ deposit }
/- Refuted by the concrete run below; sol_prove leaves: the payable snapshot, mapping save and wrapping addition
leave balance=old balance+value and supply=old supply+value. The source relies on
a global supply invariant absent from a mere typed-storage layout. -/
/-- Unwrap: burn and return exactly the requested value. -/
def withdraw_obligation : Fml WrappedEther [] := spec!{ withdraw }
/- Refuted by the concrete run below; sol_prove leaves: after checked balance debit, wrapping supply debit and
pay, show both old-storage equations and oldNet debit/self-payment. Closure needs
wrapping arithmetic bounds from a supply invariant as well as ledger snapshots. -/

/-- A typed but unreachable WETH store: zero supply, one account credited `b`. -/
private def inconsistentStore (b : Nat) : Storage WrappedEther :=
  .cons (.prim (uintOfNat 0))
    (.cons (.map (.cons (uintOfNat 1) (.prim (uintOfNat b)) .nil)
      (.prim (uintOfNat 0))) .nil)

/-- Refuted over arbitrary typed stores: wrapping a wei with balance=max and
supply=0 yields supply=1 and balance=0, not old balance+1. This is not a reachable
WETH exploit; the missing global invariant is precisely what rules it out. -/
example :
    ((Prog.run { State.ofStorage (inconsistentStore (2 ^ 256 - 1)) with
        tx := { msgSender := uintOfNat 1, msgValue := uintOfNat 1 } }
      (sol{ deposit(); uint b = balanceOf[msg.sender]; uint s = totalSupply; })).toOption.map
        fun o => (o.st.env.1.1, o.st.env.2.1.1)) = some (1, 0) := by
  decide +kernel

/-- Refuted over arbitrary typed stores: burning a wei with balance=1 and
supply=0 wraps supply to max, rather than old supply-1. The balance debit succeeds
and the payment is funded. No invariant premise is added to rescue the clause. -/
example :
    ((Prog.run { State.ofStorage (inconsistentStore 1) with
        selfBalance := uintOfNat 1,
        tx := { msgSender := uintOfNat 1, selfAddress := uintOfNat 2 } }
      (sol{ withdraw(1); uint s = totalSupply; })).toOption.map
        fun o => o.st.env.1.1) = some (2 ^ 256 - 1) := by
  decide +kernel

end Solidity.Examples.Benchmark.Defi.WrappedEther
