import Solidity.Calculus.Spec

/-!
# Specifications: clauses as obligations

A contract here carries `@custom:key` clauses where the NatSpec lines stand
(`requires e;`, `ensures e;`, `assignable l;` above the function).
`spec!{f}` is the obligation solkey's `SolidityProblemSynthesizer` builds for
`f` (`Calculus/Spec.lean`), and `sol_spec` proves it.

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
            (find(old, count) = find(old, count) → find(storage, count) = find(old, count)) ∧
              (find(old, total) = find(old, total) → find(storage, total) = find(old, total)) ∧
                (∀ uint k1;
                    find(old, seen[k1]) = find(old, seen[k1]) →
                      find(storage, seen[k1]) = find(old, seen[k1]))) } : Fml Tally
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

/--
info: dl{
  ((0 <= x ∧ x <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) ∧
        (0 <= y ∧ y <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) ∧
          msg.value = 0) →
    [ uint result_lo; uint result_hi; (result_lo, result_hi) = order(x, y); ] result_lo <= result_hi } : Fml Ordered
-/
#guard_msgs in #check spec!{ order }

/-- `inc(x)`: its named return `r` is `result`. -/
theorem ordered_inc : ⊨ spec!{ inc } := by sol_spec
/-- `order(x, y)`: `lo <= hi` of the two returns. -/
theorem ordered_order : ⊨ spec!{ order } := by sol_spec
end

end Solidity.Examples.Tactics.Specs
