import Solidity.Tools.Run
import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.Surface
import Solidity.Calculus.Deploy
import Solidity.Calculus.Closers
import Solidity.Tools.Inspect

/-!
# Benchmark: `Coin`

Source: solkey's `keyext.solidity.examples/benchmark/Coin.sol`, itself from
<https://raw.githubusercontent.com/ethereum/solidity/v0.8.30/docs/introduction-to-smart-contracts.rst>.
Changes from the published text, as solkey's benchmark file makes them: the
event `Sent` and the custom error `InsufficientBalance` are dropped, and so
is the `emit`; `require(c, Err(..))` is `require(c)`.  Here besides: the
`public` getters are not declared (a state variable is read directly).
The constructor is the contract's (`Contract.ctor`): `constructor();` runs it
(`ctor`), and a deployment runs it from the empty storage
(`Contract.deploy`, `deployMinter`; `Examples/Tactics/Constructors.lean`).

solkey's `@custom:key` clauses are written above the functions, as its
file has them.  `spec!{ mint }`, the obligation solkey synthesizes
(`Calculus/SurfaceSpec.lean`), is derived as `⊢`, its leaves closed by `sol_spec`'s
steps (`spec_mint`); `send`'s is not.  Before it, the clauses by hand, as `⊢ dl{}` obligations, one per
clause, each by `sol_prove` (`Calculus/ProvesDerive.lean`): the calculus's steps
and each leaf closed by the closer (`LFml.close`), in one kernel evaluation.
`\old(e)` is a local declared before the call (`uint b = balances[r];`), and
`msg.sender` is the transaction's (`Simple.env`), the same before and after.
`requires amount >= 0` holds of a `uint`.  The runs of the interpreter
(`sendRun`) show the same debit and credit on a deployed contract.
-/

namespace Solidity.Examples.Benchmark.Coin


/-- `Coin.sol`, as solkey's benchmark has it, with its clauses. -/
def Coin : Contract := contract!{
  address minter;
  mapping(address => uint) balances;
  constructor() {
    minter = msg.sender;
  }
  requires amount >= 0;
  ensures \old(minter) == msg.sender && minter == \old(minter);
  ensures balances[receiver] == \old(balances[receiver]) + amount;
  ensures \forall address a; a != receiver -> balances[a] == \old(balances[a]);
  function mint(address receiver, uint amount) {
    require(msg.sender == minter);
    balances[receiver] += amount;
  }
  requires amount >= 0;
  ensures \old(balances[msg.sender]) >= amount;
  ensures msg.sender != receiver -> balances[msg.sender] == \old(balances[msg.sender]) - amount && balances[receiver] == \old(balances[receiver]) + amount;
  ensures msg.sender == receiver -> balances[msg.sender] == \old(balances[msg.sender]);
  ensures \forall address a; a != msg.sender && a != receiver -> balances[a] == \old(balances[a]);
  function send(address receiver, uint amount) {
    require(amount <= balances[msg.sender]);
    balances[msg.sender] -= amount;
    balances[receiver] += amount;
  }
}

local instance : InContract := ⟨Coin⟩

open scoped Scoped

/-! ## The constructor -/

/-- `constructor()`: the caller is the minter, from any storage. -/
theorem ctor : ⊢ dl!{ [ constructor(); ] minter == msg.sender } := by
  sol_prove

/-- A deployment, from the empty storage: it returns, the deployer the
minter.  (That no one holds a coin, a read at a free key of the empty
storage, is outside `sol_close_mt`; `deployRun` shows it of one run.) -/
theorem deployMinter :
    ⊨ dl!{ { storage := mtSt ‖ net := store(mtSt, at(msg.sender), msg.value) ‖
        selfBalance := msg.value }
      ⟨ constructor(); ⟩ minter == msg.sender } := by
  sol_symex
  sol_close_mt

/-! ## `mint`

`ensures \old(minter) == msg.sender && minter == \old(minter)`: a call by
anyone but the minter reverts, so under the box the caller is the minter. -/

theorem mintMinter :
    ⊢ dl!{ [ uint m = minter; mint(r, a); ] m == msg.sender && minter == m } := by
  sol_prove

/-- `ensures balances[receiver] == \old(balances[receiver]) + amount`. -/
theorem mintReceiver :
    ⊢ dl!{ [ uint b = balances[r]; mint(r, a); uint c = balances[r]; ] c == b + a } := by
  sol_prove

/-- `ensures \forall address a; a != receiver -> balances[a] == \old(balances[a])`. -/
theorem mintOthers :
    ⊢ dl!{ k != r → [ uint b = balances[k]; mint(r, a); ] balances[k] == b } := by
  sol_prove

set_option maxHeartbeats 400000 in
/-- `mint(receiver, amount)`'s obligation: only the minter mints, the
receiver credited, every other balance kept.  Each leaf on its scoped form
(`sol_leaf`) by `sol_spec_close`.  Not by `sol_decide`: the frame clause
needs the layout premise instantiated at the quantified key. -/
theorem spec_mint : ⊢ spec!{ mint } := by
  sol_derive
  all_goals
    sol_leaf
    sol_spec_close

/-! ## `send` -/

/-- `ensures \old(balances[msg.sender]) >= amount`: a formula has no `>=`,
so the comparison is a `bool` local of the pre-state. -/
theorem sendCovered :
    ⊢ dl!{ [ bool ok = a <= balances[msg.sender]; send(r, a); ] ok == true } := by
  sol_prove

/-- `ensures msg.sender == receiver -> balances[msg.sender] == \old(balances[msg.sender])`. -/
theorem sendSelf :
    ⊢ dl!{ msg.sender == r → [ uint b = balances[msg.sender]; send(r, a); ]
      balances[msg.sender] == b } := by
  sol_prove

/-- `ensures msg.sender != receiver -> balances[msg.sender] ==
\old(balances[msg.sender]) - amount && …`. -/
theorem sendMovesSender :
    ⊢ dl!{ msg.sender != r → [ uint b = balances[msg.sender]; send(r, a); ]
      balances[msg.sender] == b - a } := by
  sol_prove

/-- `ensures msg.sender != receiver -> … && balances[receiver] ==
\old(balances[receiver]) + amount`. -/
theorem sendMovesReceiver :
    ⊢ dl!{ msg.sender != r → [ uint c = balances[r]; send(r, a); ]
      balances[r] == c + a } := by
  sol_prove

/-- `ensures \forall address a; a != msg.sender && a != receiver -> balances[a] == \old(balances[a])`. -/
theorem sendOthers :
    ⊢ dl!{ k != msg.sender && k != r → [ uint b = balances[k]; send(r, a); ] balances[k] == b } := by
  sol_prove

/-! ## Runs

`7` deploys and mints `10` to itself, then sends `4` to `9`: the debit and
the credit of `send` when the two differ (`sendMovesSender`,
`sendMovesReceiver`), on one state. -/

/-- `7`, deploying and calling. -/
def tx : TTx := { msgSender := ⟨7, rfl⟩ }

/-! Each block is elaborated scoped and deployed in the typed run
(`Contract.deployT`), by the kernel (`decide +kernel`). -/

def ctorCore := (sol{ constructor(); } : Prog Coin [] _)
def mintSendCore := (sol{ constructor(); mint(7, 10); send(9, 4); } : Prog Coin [] _)
def mintCore := (sol{ mint(7, 10); } : Prog Coin [] _)

/-- `balances[a]` after `P` deploys and runs, `7` calling: read typed (an
entry, else the mapping's default, `SVal.find`), since the erasure of a
typed storage does not reduce in the kernel. -/
def balanceAfter {Γ' : Ctx} (P : Prog Coin [] Γ') (a : Int) : Option Int :=
  (Contract.deployT Coin P tx).toOption.bind fun σ =>
    ((σ.storage.get (f := "balances") (T := .ref (.mapping (.prim .uint) (.prim .uint))) rfl).find
      (.key a .nil)).map fun v => v.view.1

/-- What a deployment by `7` stores: `minter` is `7`, `balances` has no
entry and `0` at every key. -/
private def deployedStorage : Storage Coin :=
  .cons (.prim ⟨7, rfl⟩) (.cons (.map .nil (.prim ⟨0, rfl⟩)) .nil)

/-- The deployer is the minter, and no one holds a coin. -/
theorem deployRun :
    (Contract.deployT Coin ctorCore tx).toOption.map (·.storage.beq deployedStorage) =
      some true := by
  decide +kernel

/-- The sender is debited. -/
theorem sendRunSender : balanceAfter mintSendCore 7 = some 6 := by decide +kernel

/-- The receiver is credited. -/
theorem sendRunReceiver : balanceAfter mintSendCore 9 = some 4 := by decide +kernel

/-- Anyone but the minter: deployed by `3`, a `mint` by `7` reverts. -/
theorem mintRunOther :
    (Contract.deployT Coin ctorCore { msgSender := ⟨3, rfl⟩ }).toOption.map
      (fun σ => (Prog.run { σ with tx := tx } mintCore).halt?) = some (some .revert) := by
  decide +kernel

end Solidity.Examples.Benchmark.Coin
