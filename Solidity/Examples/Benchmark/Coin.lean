import Solidity.Calculus.Derive
import Solidity.Calculus.Spec
import Solidity.Calculus.DecideComplete

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
(`Calculus/Spec.lean`), is derived as `⊢`, its leaves closed by `sol_spec`'s
steps (`spec_mint`); `send`'s is not.  Before it, the clauses by hand, as `⊢ dl{}` obligations, one per
clause, each by `sol_prove` (`Calculus/Derive.lean`): the calculus's steps
and each leaf closed by the closer (`LFml.close`), in one kernel evaluation.
`\old(e)` is a local declared before the call (`uint b = balances[r];`), and
`msg.sender` is the transaction's (`Simple.env`), the same before and after.
`requires amount >= 0` holds of a `uint`.  The runs of the interpreter
(`sendRun`) show the same debit and credit on a deployed contract.
-/

namespace Solidity.Examples.Benchmark.Coin

open Proves

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
receiver credited, every other balance kept.  Each leaf by `sol_spec`'s steps
with its reads done once, over the premises taken in (`sol_close_reads_all`),
without `sol_close_facts` and `sol_close_reads` on the goal before them: the
same proof in three quarters of the heartbeats.  Not by `sol_decide`: the
frame clause needs the layout premise instantiated at the quantified key. -/
theorem spec_mint : ⊢ spec!{ mint } := by
  sol_derive
  all_goals
    refine close ?_
    sol_symex
    sol_close_unwrap
    intro σ
    sol_close_eval
    intros
    sol_close_reads_all
    all_goals sol_spec_finish

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
def tx : Semantics.TxEnv := { msgSender := 7 }

/-- `balances[a]` after `P` deploys and runs, `7` calling. -/
def balanceAfter (P : Prog Coin) (a : Int) : Semantics.Res Semantics.SVal := do
  (← Coin.deploy P tx).findStorage "balances" [.at a]

/-- The deployer is the minter, and no one holds a coin. -/
theorem deployRun :
    (Coin.deploy sol{ constructor(); } tx).map (·.storage) =
      .ok [("minter", .prim (.int 7)), ("balances", .map [] (.int 0))] := by
  simp only [Contract.deploy, Contract.deployState, Contract.initStorage, Coin,
    List.map, Semantics.defaultForTy]
  rfl

/-- The sender is debited. -/
theorem sendRunSender :
    balanceAfter sol{ constructor(); mint(7, 10); send(9, 4); } 7 = .ok (.int 6) := by
  simp only [balanceAfter, Contract.deploy, Contract.deployState, Contract.initStorage, Coin,
    List.map, Semantics.defaultForTy]
  rfl

/-- The receiver is credited. -/
theorem sendRunReceiver :
    balanceAfter sol{ constructor(); mint(7, 10); send(9, 4); } 9 = .ok (.int 4) := by
  simp only [balanceAfter, Contract.deploy, Contract.deployState, Contract.initStorage, Coin,
    List.map, Semantics.defaultForTy]
  rfl

/-- Anyone but the minter: deployed by `3`, a `mint` by `7` reverts. -/
theorem mintRunOther :
    (do
      let σ ← Coin.deploy sol{ constructor(); } { msgSender := 3 }
      Prog.run { σ with tx := tx } (sol{ mint(7, 10); } : Prog Coin)) = .error .revert := by
  simp only [Contract.deploy, Contract.deployState, Contract.initStorage, Coin,
    List.map, Semantics.defaultForTy]
  rfl

end Solidity.Examples.Benchmark.Coin
