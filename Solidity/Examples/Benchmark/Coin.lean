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
`public` getters are not declared (a state variable is read directly), and
the constructor's body `minter = msg.sender;` is stated as a statement of its
own (`ctor`), since a contract here has no constructor.

solkey's `@custom:key` clauses are written above the functions, as its
file has them.  `spec!{ mint }`, the obligation solkey synthesizes
(`Calculus/Spec.lean`), is derived as `⊢`, its leaves closed by `sol_spec`'s
steps (`spec_mint`); `send`'s is not.  Before it, the clauses by hand, as `⊢ dl{}` obligations, one per
clause, each by `sol_prove` (`Calculus/Derive.lean`): the calculus's steps
and each leaf closed by its terms (`LFml.syn`), in one kernel evaluation.
`mintMinter` leaves one leaf `LFml.syn` does not close, closed after it by
`sol_decide`'s heuristic step (`sol_decide_heuristic`).
`\old(e)` is a local declared before the call (`uint b = balances[r];`), and
`msg.sender` is the transaction's (`Simple.env`), the same before and after.
`requires amount >= 0` holds of a `uint`.  The runs of the interpreter
(`sendRun`) show the same debit and credit on a concrete state.
-/

namespace Solidity.Examples.Benchmark.Coin

open Proves

/-- `Coin.sol`, as solkey's benchmark has it, with its clauses. -/
def Coin : Contract := contract!{
  address minter;
  mapping(address => uint) balances;
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

/-- `minter = msg.sender;` — the constructor's body. -/
theorem ctor : ⊢ dl!{ [ minter = msg.sender; ] minter == msg.sender } := by
  sol_prove

/-! ## `mint`

`ensures \old(minter) == msg.sender && minter == \old(minter)`: a call by
anyone but the minter reverts, so under the box the caller is the minter. -/

theorem mintMinter :
    ⊢ dl!{ [ uint m = minter; mint(r, a); ] m == msg.sender && minter == m } := by
  sol_prove
  refine close ?_
  sol_symex
  refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
  sol_reduce
  sol_decide_heuristic

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
