import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.SolSpec
import Solidity.Tools.Inspect

/-!
# Specifications: clauses as obligations

A contract here carries `@custom:key` clauses where the NatSpec lines stand
(`requires e;`, `ensures e;`, `assignable l;` above the function).
`spec!{f}` is the obligation solkey's `SolidityProblemSynthesizer` builds for
`f` (`Calculus/SurfaceSpec.lean`), and `sol_spec` proves it.

solkey's benchmark contracts carry their clauses in their own files, with
their `spec!{f}` theorems: `Examples/Benchmark/Counter.lean` (with `dec`'s
obligation pinned as it prints), `Examples/Benchmark/SimpleStorage.lean`,
`Examples/Benchmark/Mapping.lean` (`Mapping` and `NestedMapping`) and
`Examples/Benchmark/Coin.lean` (`mint`).  What is here is what those files
do not have: `ERC20` with `msg.sender` itself, where
`Examples/Benchmark/ERC20.lean` passes it as a parameter; and `Tally`, no
benchmark, which exercises an `assignable` clause and a `payable` function
booking `msg.value`.

Not proved: `Coin.send`, whose debit-and-credit clause `sol_close` does not
close (as in `Examples/Benchmark/Coin.lean`); `ERC20.transfer`, the same; and
the benchmarks' clauses over `net(a)` (EtherWallet, Purchase, SimpleAuction).
-/
namespace Solidity.Examples.Tactics.Specs

def ERC20 : Contract := contract!{
  uint totalSupply;
  mapping(address => uint) balanceOf;
  mapping(address => mapping(address => uint)) allowance;
  requires amount >= 0 && balanceOf[msg.sender] >= amount;
  ensures \result && totalSupply == \old(totalSupply);
  ensures msg.sender != recipient -> balanceOf[msg.sender] == \old(balanceOf[msg.sender]) - amount && balanceOf[recipient] == \old(balanceOf[recipient]) + amount;
  ensures msg.sender == recipient -> balanceOf[msg.sender] == \old(balanceOf[msg.sender]);
  ensures \forall address a; a != msg.sender && a != recipient -> balanceOf[a] == \old(balanceOf[a]);
  function transfer(address recipient, uint amount) returns (bool) {
    balanceOf[msg.sender] -= amount;
    balanceOf[recipient] += amount;
    return true;
  }
  requires amount >= 0;
  ensures \result && allowance[msg.sender][spender] == amount;
  function approve(address spender, uint amount) returns (bool) {
    allowance[msg.sender][spender] = amount;
    return true;
  }
  requires amount >= 0;
  ensures balanceOf[to] == \old(balanceOf[to]) + amount && totalSupply == \old(totalSupply) + amount;
  function _mint(address to, uint amount) {
    balanceOf[to] += amount;
    totalSupply += amount;
  }
}

section
local instance : InContract := ⟨ERC20⟩

open scoped Scoped
/-- `approve(spender, amount)`: `ensures \result && allowance[msg.sender][spender] == amount`. -/
theorem erc_approve : ⊨ spec!{ approve } := by sol_spec
set_option maxHeartbeats 1000000 in
/-- `_mint(to, amount)`: the balance and the supply both up by `amount`. -/
theorem erc_mint : ⊨ spec!{ _mint } := by sol_spec
end

def Tally : Contract := contract!{
  uint count;
  uint total;
  mapping(address => uint) seen;
  ensures count == \old(count) + 1;
  assignable count;
  function inc() public {
    count += 1;
  }
  ensures seen[msg.sender] == 1;
  assignable seen[msg.sender];
  function mark() public {
    seen[msg.sender] = 1;
  }
  requires net(msg.sender) + msg.value >= 0;
  ensures net(msg.sender) == \old(net(msg.sender)) + msg.value;
  assignable \nothing;
  function pay() public payable {
  }
}

section
local instance : InContract := ⟨Tally⟩

open scoped Scoped
/-! `pay()`'s obligation: `msg.value` is booked to the sender's ledger entry
in front of the call, `\old(net(msg.sender))` reads the snapshot `oldNet`,
and `assignable \nothing` owes every word of the storage where it was.  The
`requires` says that the sum is a `uint`, which the `ensures` reads it as. -/

/--
info: dl{
  (msg.value >= 0 ∧ net(msg.sender) + msg.value >= 0) →
    { old := storage ‖ oldNet := net ‖ net := store(net, at(msg.sender), net(msg.sender) + msg.value) ‖
        selfBalance := selfBalance + msg.value }
      [ pay(); ]
        (net(msg.sender) = net(oldNet, msg.sender) + msg.value ∧
            find(storage, count) = find(old, count) ∧
              find(storage, total) = find(old, total) ∧
                (∀ uint k1; find(storage, seen[k1]) = find(old, seen[k1]))) } : Fml Tally []
-/
#guard_msgs in #check spec!{ pay }

/-- `inc()`: `assignable count`, so `total` and every `seen[k]` are kept. -/
theorem tally_inc : ⊨ spec!{ inc } := by sol_spec
/-- `mark()`: `assignable seen[msg.sender]`, so every other key is kept. -/
theorem tally_mark : ⊨ spec!{ mark } := by sol_spec
/-- `pay()`, `payable`: the sender's ledger entry up by `msg.value`, the
storage untouched. -/
theorem tally_pay : ⊨ spec!{ pay } := by sol_spec
end

/-! ## Returns by name

The obligation's call returns to its targets, `T result; result = f(x̄);`
(solkey's `result = f(x̄)@C;`, `functionBodyExpand`'s), and an `ensures` may
name a return: the one return of `inc` is `result`, the two of `order` are
`result_lo` and `result_hi` (`SpecCompiler.resultVariable`). -/

def Ordered : Contract := contract!{
  uint total;
  ensures r == x + 1;
  function inc(uint x) returns (uint r) {
    r = x + 1;
  }
  ensures lo <= hi;
  function order(uint x, uint y) returns (uint lo, uint hi) {
    if (x < y) { return (x, y); }
    return (y, x);
  }
}

section
local instance : InContract := ⟨Ordered⟩

open scoped Scoped

/--
info: dl{
  ((0 <= x ∧ x <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) ∧
        (0 <= y ∧ y <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) ∧
          msg.value = 0) →
    [ uint result_lo; uint result_hi; (result_lo, result_hi) = order(x, y); ] result_lo <= result_hi } : Fml Ordered []
-/
#guard_msgs in #check spec!{ order }

/-- `inc(x)`: its named return `r` is `result`. -/
theorem ordered_inc : ⊨ spec!{ inc } := by sol_spec
/-- `order(x, y)`: `lo <= hi` of the two returns. -/
theorem ordered_order : ⊨ spec!{ order } := by sol_spec
end

/-! The `this` adapter must preserve the existing name-resolution priority,
including intrinsic inputs that Solidity itself would not admit. -/
private def selfResolution {C : Contract} (ctx : SpecCtx C) : Option String :=
  (SpecExpr.term C ctx (.name "this")).toOption.map fun (_, term) => term.key

private def selfContext : SpecCtx { vars := [] } :=
  { storage := .storage, ensures := true, locals := [], result := none }

example : spec!(uint(7)) = SpecExpr.uintLit 7 := rfl
#guard !(spec!(uint(7))).isNum
#guard !(SpecExpr.term { vars := [] } { selfContext with locals := [("x", .int)] }
  (spec!(uint(1) + x))).isOk
#guard !(SpecExpr.term { vars := [] } selfContext
  (spec!(uint(1) && true))).isOk
#guard !(SpecExpr.term { vars := [] } selfContext (.uintLit (2 ^ 256))).isOk

private def unsignedContext : SpecCtx { vars := [] } :=
  { selfContext with locals := [("x", .uint)] }

#guard !(SpecExpr.term { vars := [] } unsignedContext (spec!(-x))).isOk
#guard !(SpecExpr.term { vars := [] } selfContext (spec!(-true))).isOk
#guard (SpecExpr.fml { vars := [] } unsignedContext (spec!(net(msg.sender) == -x))).isOk
#guard (SpecExpr.fml { vars := [] } unsignedContext (spec!(-x == net(msg.sender)))).isOk
#guard (SpecExpr.fml { vars := [] } selfContext (spec!(net(msg.sender) == -4))).isOk
#guard !(SpecExpr.term { vars := [] } { selfContext with locals := [("x", .int)] }
  (spec!(net(msg.sender) + -x))).isOk

/-- Invalid nested ledger clauses must fail without repeating an already
selected integer context exponentially. -/
private def invalidLedgerNest : Nat → SpecExpr
  | 0 => spec!(true)
  | n + 1 => .binop .add (spec!(net(msg.sender))) (invalidLedgerNest n)

#guard !(SpecExpr.term { vars := [] } selfContext (invalidLedgerNest 20)).isOk
#guard !(SpecExpr.term { vars := [] } selfContext (invalidLedgerNest 20) true).isOk

/-- Invalid ledger addresses reset their operands' context; negating the
ledger read must not cause that invalid operand to be compiled again. -/
private def invalidLedgerAddressNest (negate : Bool) : Nat → SpecExpr
  | 0 => spec!(true)
  | n + 1 =>
    let rhs : SpecExpr := .net (invalidLedgerAddressNest negate n)
    .binop .add (spec!(net(msg.sender))) (if negate then .unop .neg rhs else rhs)

#guard !(SpecExpr.term { vars := [] } selfContext (invalidLedgerAddressNest false 20)).isOk
#guard !(SpecExpr.term { vars := [] } selfContext (invalidLedgerAddressNest true 20)).isOk
#guard !(SpecExpr.term { vars := [] } selfContext (invalidLedgerAddressNest false 20) true).isOk
#guard !(SpecExpr.term { vars := [] } selfContext (invalidLedgerAddressNest true 20) true).isOk

#guard selfResolution selfContext == some (NTerm.env (C := { vars := [] }) .selfAddress).key
#guard selfResolution { selfContext with locals := [("this", .uint)] } ==
  some (NTerm.pv (C := { vars := [] }) (.ofName "this")).key
#guard selfResolution { selfContext with rets := [("this", "result_ret", .uint)] } ==
  some (NTerm.pv (C := { vars := [] }) (.ofName "result_ret")).key
#guard (selfResolution { selfContext with refs := [("this", .alias (.array (.prim .uint)))] }).isNone
#guard selfResolution ({ storage := .storage, ensures := true, locals := [], result := none } :
  SpecCtx { vars := [("this", .prim .uint)] }) ==
    some (NTerm.find (C := { vars := [("this", .prim .uint)] }) .storage (.root "this")).key

def LedgerNegation : Contract := contract!{
  ensures -net(msg.sender) == 0 - net(msg.sender);
  function ledger() public pure { }
  requires net(msg.sender) == value;
  ensures -net(msg.sender) == -value;
  function unsigned(uint value) public pure { }
  requires net(msg.sender) == -value;
  ensures -value == net(msg.sender);
  function reversed(uint value) public pure { }
}

section
local instance : InContract := ⟨LedgerNegation⟩
open scoped Scoped

/-- `ledger()`: negation is unbounded integer subtraction from zero. -/
theorem ledger_negation : ⊨ spec!{ ledger } := by sol_spec
/-- `unsigned(value)`: the unsigned negand widens beside the ledger integer. -/
theorem unsigned_negation : ⊨ spec!{ unsigned } := by sol_spec
/-- `reversed(value)`: the ledger context also reaches the left operand. -/
theorem reversed_negation : ⊨ spec!{ reversed } := by sol_spec
end

end Solidity.Examples.Tactics.Specs
