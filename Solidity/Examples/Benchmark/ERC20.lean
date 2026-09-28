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

Each `@custom:key` specification is an obligation below, proved; an
`ensures` of two conjuncts under a premise is two obligations.  A
postcondition is `[ … ]`: a run that reverts (a short balance or
allowance, an overflow) satisfies it, as KeY's `ensures` under its
precondition, which here only rules the revert out; `\old(e)` is a local
read before the call.  The frame condition's `\forall address a` is a free
name, which the formula reads as a parameter in scope everywhere.  The
arithmetic is the specification's own (`b1 == b0 - amount`, not
`b1 + amount == b0`): `⊨` ranges over storages whose words need not be in
range, and there the second form overflows.
-/

namespace Solidity.Examples.Benchmark.ERC20

/-- ERC20, with `msg.sender` passed as a parameter. -/
def ERC20 : Contract := contract!{
  uint totalSupply;
  mapping(uint => uint) balanceOf;
  mapping(uint => mapping(uint => uint)) allowance;
  -- `sender` is `msg.sender`, a parameter until the language has it
  function transfer(uint sender, uint recipient, uint amount) returns (bool) {
    balanceOf[sender] -= amount;
    balanceOf[recipient] += amount;
    -- `emit Transfer(msg.sender, recipient, amount);` dropped: events
    return true;
  }
  -- `sender` is `msg.sender`
  function approve(uint sender, uint spender, uint amount) returns (bool) {
    allowance[sender][spender] = amount;
    -- `emit Approval(msg.sender, spender, amount);` dropped: events
    return true;
  }
  -- `caller` is `msg.sender`
  function transferFrom(uint caller, uint sender, uint recipient, uint amount) returns (bool) {
    allowance[sender][caller] -= amount;
    balanceOf[sender] -= amount;
    balanceOf[recipient] += amount;
    -- `emit Transfer(sender, recipient, amount);` dropped: events
    return true;
  }
  function _mint(uint to, uint amount) {
    balanceOf[to] += amount;
    totalSupply += amount;
    -- `emit Transfer(address(0), to, amount);` dropped: events
  }
  function _burn(uint holder, uint amount) {
    balanceOf[holder] -= amount;
    totalSupply -= amount;
    -- `emit Transfer(from, address(0), amount);` dropped: events
  }
  function mint(uint to, uint amount) { _mint(to, amount); }
  function burn(uint holder, uint amount) { _burn(holder, amount); }
}

local instance : InContract := ⟨ERC20⟩

/-! ## `transfer` -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `ensures \result && totalSupply == \old(totalSupply)`. -/
theorem transfer_result :
    ⊨ dl!{ [ uint t0 = totalSupply; bool ok = transfer(s, r, amount); uint t1 = totalSupply; ]
      (ok == true ∧ t1 == t0) } := by
  sol_symex
  sol_decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `ensures msg.sender != recipient -> balanceOf[msg.sender] ==
\old(balanceOf[msg.sender]) - amount && …`. -/
theorem transfer_moves_sender :
    ⊨ dl!{ s != r → [ uint b0 = balanceOf[s]; bool ok = transfer(s, r, amount);
      uint b1 = balanceOf[s]; ] b1 == b0 - amount } := by
  sol_symex
  sol_decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `ensures msg.sender != recipient -> … && balanceOf[recipient] ==
\old(balanceOf[recipient]) + amount`. -/
theorem transfer_moves_recipient :
    ⊨ dl!{ s != r → [ uint c0 = balanceOf[r]; bool ok = transfer(s, r, amount);
      uint c1 = balanceOf[r]; ] c1 == c0 + amount } := by
  sol_symex
  sol_decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `ensures msg.sender == recipient -> balanceOf[msg.sender] ==
\old(balanceOf[msg.sender])`. -/
theorem transfer_self :
    ⊨ dl!{ [ uint b0 = balanceOf[s]; bool ok = transfer(s, s, amount); uint b1 = balanceOf[s]; ]
      b1 == b0 } := by
  sol_symex
  sol_decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `ensures \forall address a; a != msg.sender && a != recipient ->
balanceOf[a] == \old(balanceOf[a])`. -/
theorem transfer_frame :
    ⊨ dl!{ a != s ∧ a != r → [ uint x0 = balanceOf[a]; bool ok = transfer(s, r, amount);
      uint x1 = balanceOf[a]; ] x1 == x0 } := by
  sol_symex
  sol_decide

/-! ## `approve` -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `ensures \result && allowance[msg.sender][spender] == amount`. -/
theorem approve_sets :
    ⊨ dl!{ [ bool ok = approve(s, p, amount); uint x = allowance[s][p]; ]
      (ok == true ∧ x == amount) } := by
  sol_symex
  sol_decide

/-! ## `transferFrom`

Three writes take the reduced formula past `simp`'s default step bound, in
the step of `sol_decide` that unfolds it: `sol_decide_big` is the same
steps with the bound raised. -/

open Solidity.Decide Semantics SemanticsProperties in
/-- `sol_decide`'s steps (`Calculus/DecideComplete.lean`), with `simp`'s
step bound raised in the unfolding. -/
local macro "sol_decide_big" : tactic => `(tactic| (
    refine (Fml.valid_iff_reduce _ (by decide)).2 ?_
    sol_reduce
    refine (LFml.valid_iff_cons _ (by decide)).2 ?_
    sol_reads
    intro σ o hc
    sol_cons_split hc
    sol_decide_splitA
    all_goals
      set_option linter.unusedSimpArgs false in
      simp (config := { maxSteps := 2000000 }) only [LFml.holdsA_tt, LFml.holdsA_not,
        LFml.holdsA_and, LFml.holdsA_imp, LFml.holdsA_eq, LTerm.evalA_lit, LTerm.evalA_binop,
        LTerm.evalA_unop, LTerm.evalA_ite, LTerm.evalA_find, LTerm.evalA_has, LTerm.evalA_kmap,
        LTerm.evalA_len, LTerm.evalA_sok, LTerm.evalA_pok, LTerm.evalA_seq, LTerm.evalA_orElse,
        LTerm.evalA_kite, LTerm.evalA_zero, LTerm.evalA_err, LTerm.evalA_var, LPath.evalA,
        LPath.consA, zeroV_int, zeroV_bool, orElseR_ok, orElseR_error, close_rw, forall_eq',
        List.cons_append, List.nil_append, Obs.find_eq_ok, Obs.has_eq_ok, Obs.test_map_eq_ok,
        Obs.test_fixed_eq_ok, Obs.len_eq_ok, and_assoc, *] at *
    all_goals first | omega | grind))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `ensures \result && totalSupply == \old(totalSupply)`. -/
theorem transferFrom_result :
    ⊨ dl!{ [ uint t0 = totalSupply; bool ok = transferFrom(c, s, r, amount); uint t1 = totalSupply; ]
      (ok == true ∧ t1 == t0) } := by
  sol_symex
  sol_decide

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
/-- `ensures allowance[sender][msg.sender] ==
\old(allowance[sender][msg.sender]) - amount`. -/
theorem transferFrom_allowance :
    ⊨ dl!{ [ uint w0 = allowance[s][c]; bool ok = transferFrom(c, s, r, amount);
      uint w1 = allowance[s][c]; ] w1 == w0 - amount } := by
  sol_symex
  sol_decide_big

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
/-- `ensures sender != recipient -> balanceOf[sender] ==
\old(balanceOf[sender]) - amount && …`. -/
theorem transferFrom_moves_sender :
    ⊨ dl!{ s != r → [ uint b0 = balanceOf[s]; bool ok = transferFrom(c, s, r, amount);
      uint b1 = balanceOf[s]; ] b1 == b0 - amount } := by
  sol_symex
  sol_decide_big

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
/-- `ensures sender != recipient -> … && balanceOf[recipient] ==
\old(balanceOf[recipient]) + amount`. -/
theorem transferFrom_moves_recipient :
    ⊨ dl!{ s != r → [ uint c0 = balanceOf[r]; bool ok = transferFrom(c, s, r, amount);
      uint c1 = balanceOf[r]; ] c1 == c0 + amount } := by
  sol_symex
  sol_decide_big

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
/-- `ensures sender == recipient -> balanceOf[sender] == \old(balanceOf[sender])`. -/
theorem transferFrom_self :
    ⊨ dl!{ [ uint b0 = balanceOf[s]; bool ok = transferFrom(c, s, s, amount);
      uint b1 = balanceOf[s]; ] b1 == b0 } := by
  sol_symex
  sol_decide_big

/-! ## `mint` and `burn`: an internal call inlined in an external one -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `ensures balanceOf[to] == \old(balanceOf[to]) + amount && totalSupply ==
\old(totalSupply) + amount`: `mint` calls `_mint`, both inlined. -/
theorem mint_adds :
    ⊨ dl!{ [ uint b0 = balanceOf[t]; uint t0 = totalSupply; mint(t, amount);
      uint b1 = balanceOf[t]; uint t1 = totalSupply; ]
      (b1 == b0 + amount ∧ t1 == t0 + amount) } := by
  sol_symex
  sol_decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `ensures balanceOf[from] == \old(balanceOf[from]) - amount && totalSupply
== \old(totalSupply) - amount`. -/
theorem burn_subtracts :
    ⊨ dl!{ [ uint b0 = balanceOf[h]; uint t0 = totalSupply; burn(h, amount);
      uint b1 = balanceOf[h]; uint t1 = totalSupply; ]
      (b1 == b0 - amount ∧ t1 == t0 - amount) } := by
  sol_symex
  sol_decide

end Solidity.Examples.Benchmark.ERC20
