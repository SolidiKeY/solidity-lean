import Solidity.Calculus.Close

/-!
# Benchmark: `Coin`

Source: solkey's `keyext.solidity.examples/benchmark/Coin.sol`, itself from
<https://raw.githubusercontent.com/ethereum/solidity/v0.8.30/docs/introduction-to-smart-contracts.rst>.
Changes from the published text, as solkey's benchmark file makes them: the
event `Sent` and the custom error `InsufficientBalance` are dropped, and so
is the `emit`; `require(c, Err(..))` is `require(c)`.  Here besides: the
`public` getters are not declared (a state variable is read directly), and
the constructor's body `minter = msg.sender;` is stated as a statement of its
own (`ctor`), since a contract here has no constructor.

The `@custom:key` clauses become `dl{}` obligations over every state, one
per clause; `\old(e)` is a local declared before the call (`uint b =
balances[r];`), and `msg.sender` is the transaction's (`Simple.env`), the
same before and after.  `requires amount >= 0` holds of a `uint`.

Two clauses of `send` are not proved symbolically: `msg.sender != receiver
→ balances[msg.sender] == \old(…) - amount && balances[receiver] == \old(…)
+ amount`.  `send` reads `balances[msg.sender]` twice (in the `require` and
in the `-=`) before writing it, and `sol_close`'s `simp` does not terminate
on two reads of one key followed by a write there, with any key, a local
included.  They are shown instead as runs of the interpreter (`sendRun`).
-/

namespace Solidity.Examples.Benchmark.Coin

open Proves

def Coin : Contract := contract!{
  address minter;
  mapping(address => uint) balances;
  function mint(address receiver, uint amount) {
    require(msg.sender == minter);
    balances[receiver] += amount;
  }
  function send(address receiver, uint amount) {
    require(amount <= balances[msg.sender]);
    balances[msg.sender] -= amount;
    balances[receiver] += amount;
  }
}

local instance : InContract := ⟨Coin⟩

/-! ## The constructor -/

/-- `minter = msg.sender;` — the constructor's body. -/
theorem ctor : ⊨ dl!{ [ minter = msg.sender; ] minter == msg.sender } := by
  sol_symex
  sol_close

/-! ## `mint`

`ensures \old(minter) == msg.sender && minter == \old(minter)`: a call by
anyone but the minter reverts, so under the box the caller is the minter. -/

theorem mintMinter :
    ⊨ dl!{ [ uint m = minter; mint(r, a); ] m == msg.sender && minter == m } := by
  sol_symex
  sol_close

set_option maxHeartbeats 2000000 in
/-- `ensures balances[receiver] == \old(balances[receiver]) + amount`. -/
theorem mintReceiver :
    ⊨ dl!{ [ uint b = balances[r]; mint(r, a); uint c = balances[r]; ] c == b + a } := by
  sol_symex
  sol_close

set_option maxHeartbeats 2000000 in
/-- `ensures \forall address a; a != receiver -> balances[a] == \old(balances[a])`. -/
theorem mintOthers :
    ⊨ dl!{ k != r → [ uint b = balances[k]; mint(r, a); ] balances[k] == b } := by
  sol_symex
  sol_close

/-! ## `send` -/

set_option maxHeartbeats 2000000 in
/-- `ensures \old(balances[msg.sender]) >= amount`: a formula has no `>=`,
so the comparison is a `bool` local of the pre-state. -/
theorem sendCovered :
    ⊨ dl!{ [ bool ok = a <= balances[msg.sender]; send(r, a); ] ok == true } := by
  sol_symex
  sol_close

set_option maxHeartbeats 2000000 in
/-- `ensures msg.sender == receiver -> balances[msg.sender] == \old(balances[msg.sender])`. -/
theorem sendSelf :
    ⊨ dl!{ msg.sender == r → [ uint b = balances[msg.sender]; send(r, a); ]
      balances[msg.sender] == b } := by
  sol_symex
  sol_close

set_option maxHeartbeats 2000000 in
/-- `ensures \forall address a; a != msg.sender && a != receiver -> balances[a] == \old(balances[a])`. -/
theorem sendOthers :
    ⊨ dl!{ k != msg.sender && k != r → [ uint b = balances[k]; send(r, a); ] balances[k] == b } := by
  sol_symex
  sol_close

/-! ## Runs

`7` deploys and mints `10` to itself, then sends `4` to `9`: the debit and
the credit of `send` when the two differ, which the box above does not
close. -/

/-- A fresh `Coin`, called by `7`. -/
def store : Semantics.State :=
  { storage := [("minter", .int 0), ("balances", .map [] (.int 0))], tx := { msgSender := 7 } }

/-- `balances[a]` after `P` runs from `store`. -/
def balanceAfter (P : Prog Coin) (a : Int) : Semantics.Res Semantics.SVal := do
  (← Prog.run store P).findStorage "balances" [.at a]

/-- The sender is debited. -/
theorem sendRunSender :
    balanceAfter sol{ minter = msg.sender; mint(7, 10); send(9, 4); } 7 = .ok (.int 6) := rfl

/-- The receiver is credited. -/
theorem sendRunReceiver :
    balanceAfter sol{ minter = msg.sender; mint(7, 10); send(9, 4); } 9 = .ok (.int 4) := rfl

/-- Anyone but the minter: `mint` reverts. -/
theorem mintRunOther :
    Prog.run store (sol{ minter = 3; mint(7, 10); } : Prog Coin) = .error .revert := rfl

end Solidity.Examples.Benchmark.Coin
