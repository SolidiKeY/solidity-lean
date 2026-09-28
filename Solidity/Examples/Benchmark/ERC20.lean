import Solidity.Calculus.DecideComplete

/-!
# ERC20, from solkey's benchmark

Source: solkey's `keyext.solidity.examples/benchmark/ERC20.sol`, which is
Solidity by Example's ERC20
(<https://github.com/Cyfrin/solidity-by-example.github.io>, commit
`5bcdca0239409d7336a07b66a6fca8d0bcc710e6`, `contracts/src/app/erc20/ERC20.sol`),
here in its **published** form: `returns (bool)` with `return true;`, and
`mint`/`burn` calling the internal `_mint`/`_burn`, which are inlined.

Changes from the published text:

* `msg.sender` is not in this stream's syntax: it is a parameter of the
  function that reads it (`sender` of `transfer` and `approve`, `caller` of
  `transferFrom`), the hack the benchmark's README lists for it.  With
  `msg.sender` in the language the parameter goes.
* `emit Transfer(…)`/`emit Approval(…)` and the event declarations are
  dropped (events are another stream's), as solkey's port drops them.
* `address` is `uint`, as the interpreter reads it; `external` and
  `internal` are dropped (every function is internal and inlined).
* `name`, `symbol`, `decimals` and the constructor that sets them are
  dropped: solkey skips the constructor (`@custom:key skip`), and no
  specification reads them.
* `from` is a Lean keyword: `_burn`'s and `burn`'s parameter is `holder`.
* No `import`, no `is IERC20`.

Each `@custom:key` specification is an obligation below, proved.  A
postcondition is `[ … ]`: a run that reverts (a short balance or
allowance, an overflow) satisfies it, as KeY's `ensures` under its
precondition, which here only rules the revert out; `\old(e)` is a local
read before the call.  The frame condition's `\forall address a` is a free
name, which the formula reads as a parameter in scope everywhere.
-/

namespace Solidity.Examples.Benchmark.ERC20

/-- ERC20, with `msg.sender` passed as a parameter. -/
def ERC20 : Contract := contract!{
  uint totalSupply;
  mapping(uint => uint) balanceOf;
  mapping(uint => mapping(uint => uint)) allowance;
  function transfer(uint sender, uint recipient, uint amount) returns (bool) {
    balanceOf[sender] -= amount;
    balanceOf[recipient] += amount;
    return true;
  }
  function approve(uint sender, uint spender, uint amount) returns (bool) {
    allowance[sender][spender] = amount;
    return true;
  }
  function transferFrom(uint caller, uint sender, uint recipient, uint amount) returns (bool) {
    allowance[sender][caller] -= amount;
    balanceOf[sender] -= amount;
    balanceOf[recipient] += amount;
    return true;
  }
  function _mint(uint to, uint amount) {
    balanceOf[to] += amount;
    totalSupply += amount;
  }
  function _burn(uint holder, uint amount) {
    balanceOf[holder] -= amount;
    totalSupply -= amount;
  }
  function mint(uint to, uint amount) { _mint(to, amount); }
  function burn(uint holder, uint amount) { _burn(holder, amount); }
}

local instance : InContract := ⟨ERC20⟩

/-! ## `transfer` -/

set_option maxHeartbeats 2000000 in
/-- `ensures \result && totalSupply == \old(totalSupply)`. -/
theorem transfer_result :
    ⊨ dl!{ [ uint t0 = totalSupply; bool ok = transfer(s, r, amount); uint t1 = totalSupply; ]
      (ok == true ∧ t1 == t0) } := by
  sol_symex
  sol_decide

set_option maxHeartbeats 2000000 in
/-- `ensures msg.sender != recipient -> balanceOf[msg.sender] ==
\old(balanceOf[msg.sender]) - amount && balanceOf[recipient] ==
\old(balanceOf[recipient]) + amount`. -/
theorem transfer_moves :
    ⊨ dl!{ s != r → [ uint b0 = balanceOf[s]; uint c0 = balanceOf[r];
      bool ok = transfer(s, r, amount); uint b1 = balanceOf[s]; uint c1 = balanceOf[r]; ]
      (b1 + amount == b0 ∧ c1 == c0 + amount) } := by
  sol_symex
  sol_decide

set_option maxHeartbeats 2000000 in
/-- `ensures msg.sender == recipient -> balanceOf[msg.sender] ==
\old(balanceOf[msg.sender])`. -/
theorem transfer_self :
    ⊨ dl!{ [ uint b0 = balanceOf[s]; bool ok = transfer(s, s, amount); uint b1 = balanceOf[s]; ]
      b1 == b0 } := by
  sol_symex
  sol_decide

set_option maxHeartbeats 2000000 in
/-- `ensures \forall address a; a != msg.sender && a != recipient ->
balanceOf[a] == \old(balanceOf[a])`. -/
theorem transfer_frame :
    ⊨ dl!{ a != s ∧ a != r → [ uint x0 = balanceOf[a]; bool ok = transfer(s, r, amount);
      uint x1 = balanceOf[a]; ] x1 == x0 } := by
  sol_symex
  sol_decide

/-! ## `approve` -/

set_option maxHeartbeats 2000000 in
/-- `ensures \result && allowance[msg.sender][spender] == amount`. -/
theorem approve_sets :
    ⊨ dl!{ [ bool ok = approve(s, p, amount); uint x = allowance[s][p]; ]
      (ok == true ∧ x == amount) } := by
  sol_symex
  sol_decide

/-! ## `transferFrom` -/

set_option maxHeartbeats 2000000 in
/-- `ensures \result && totalSupply == \old(totalSupply)` and
`allowance[sender][msg.sender] == \old(allowance[sender][msg.sender]) - amount`. -/
theorem transferFrom_allowance :
    ⊨ dl!{ [ uint t0 = totalSupply; uint w0 = allowance[s][c];
      bool ok = transferFrom(c, s, r, amount); uint t1 = totalSupply; uint w1 = allowance[s][c]; ]
      (ok == true ∧ t1 == t0 ∧ w1 + amount == w0) } := by
  sol_symex
  sol_decide

set_option maxHeartbeats 2000000 in
/-- `ensures sender != recipient -> balanceOf[sender] ==
\old(balanceOf[sender]) - amount && balanceOf[recipient] ==
\old(balanceOf[recipient]) + amount`. -/
theorem transferFrom_moves :
    ⊨ dl!{ s != r → [ uint b0 = balanceOf[s]; uint c0 = balanceOf[r];
      bool ok = transferFrom(c, s, r, amount); uint b1 = balanceOf[s]; uint c1 = balanceOf[r]; ]
      (b1 + amount == b0 ∧ c1 == c0 + amount) } := by
  sol_symex
  sol_decide

set_option maxHeartbeats 2000000 in
/-- `ensures sender == recipient -> balanceOf[sender] == \old(balanceOf[sender])`. -/
theorem transferFrom_self :
    ⊨ dl!{ [ uint b0 = balanceOf[s]; bool ok = transferFrom(c, s, s, amount);
      uint b1 = balanceOf[s]; ] b1 == b0 } := by
  sol_symex
  sol_decide

/-! ## `mint` and `burn`: an internal call inlined in an external one -/

set_option maxHeartbeats 2000000 in
/-- `ensures balanceOf[to] == \old(balanceOf[to]) + amount && totalSupply ==
\old(totalSupply) + amount`: `mint` calls `_mint`, both inlined. -/
theorem mint_adds :
    ⊨ dl!{ [ uint b0 = balanceOf[t]; uint t0 = totalSupply; mint(t, amount);
      uint b1 = balanceOf[t]; uint t1 = totalSupply; ]
      (b1 == b0 + amount ∧ t1 == t0 + amount) } := by
  sol_symex
  sol_decide

set_option maxHeartbeats 2000000 in
/-- `ensures balanceOf[from] == \old(balanceOf[from]) - amount && totalSupply
== \old(totalSupply) - amount`. -/
theorem burn_subtracts :
    ⊨ dl!{ [ uint b0 = balanceOf[h]; uint t0 = totalSupply; burn(h, amount);
      uint b1 = balanceOf[h]; uint t1 = totalSupply; ]
      (b1 + amount == b0 ∧ t1 + amount == t0) } := by
  sol_symex
  sol_decide

end Solidity.Examples.Benchmark.ERC20
