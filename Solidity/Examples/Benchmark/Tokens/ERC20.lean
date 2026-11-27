import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# ERC20 accounting obligations

Source: <https://raw.githubusercontent.com/Cyfrin/solidity-by-example.github.io/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/app/erc20/ERC20.sol>.
The executable accounting functions follow the published source, including its
unrestricted mint/burn policy. As in the parent benchmark, interface inheritance,
events, descriptive name/symbol/decimals fields and their initializing
constructor are omitted; external/internal
visibility is erased. Unlike that port, msg.sender remains msg.sender.

The natural global invariant is totalSupply = the mathematical finite-support
sum of balanceOf over all addresses, for storage reachable from zero-initialized
balances and supply. Arbitrary typed mappings need not have finite support.
This invariant is UNKNOWN: the specification language
has quantifiers but no finite-support mapping sum. This is not replaced by a
fixed-address sum or assumed as a new axiom. A sum term with extensional
write/debit/credit laws is needed before its preservation can be stated here.

The clauses below specify successful executions (box obligations). They do not
prove that a call succeeds: checked arithmetic may revert. In particular there
is no claim of overflow freedom for every input. Successful calls must retain
uint bounds; proving non-reversion from sufficient balance, allowance and
recipient headroom remains UNKNOWN and requires a diamond specification.

Verdicts: transfer, _mint, _burn, mint and burn proved with all clauses and
frames. approve and transferFrom are UNKNOWN: their guarded two-key allowance
frames remain after sol_prove (nested path-disjointness/save-read closure).
The complete typed obligations remain below. The supply sum and successful-call
no-overflow obligations above remain UNKNOWN.
-/
namespace Solidity.Examples.Benchmark.Tokens.ERC20

def ERC20 : Contract := contract!{
  uint totalSupply;
  mapping(address => uint) balanceOf;
  mapping(address => mapping(address => uint)) allowance;

  requires balanceOf[msg.sender] >= amount;
  ensures \result && totalSupply == \old(totalSupply);
  ensures msg.sender != recipient -> balanceOf[msg.sender] == \old(balanceOf[msg.sender]) - amount && balanceOf[recipient] == \old(balanceOf[recipient]) + amount;
  ensures msg.sender == recipient -> balanceOf[msg.sender] == \old(balanceOf[msg.sender]);
  ensures \forall address a; a != msg.sender && a != recipient -> balanceOf[a] == \old(balanceOf[a]);
  assignable balanceOf[msg.sender], balanceOf[recipient];
  function transfer(address recipient, uint amount) returns (bool) {
    balanceOf[msg.sender] -= amount;
    balanceOf[recipient] += amount;
    return true;
  }

  ensures \result && allowance[msg.sender][spender] == amount;
  ensures totalSupply == \old(totalSupply);
  ensures \forall address a; balanceOf[a] == \old(balanceOf[a]);
  assignable allowance[msg.sender][spender];
  function approve(address spender, uint amount) returns (bool) {
    allowance[msg.sender][spender] = amount;
    return true;
  }

  requires balanceOf[sender] >= amount && allowance[sender][msg.sender] >= amount;
  ensures \result && totalSupply == \old(totalSupply);
  ensures allowance[sender][msg.sender] == \old(allowance[sender][msg.sender]) - amount;
  ensures sender != recipient -> balanceOf[sender] == \old(balanceOf[sender]) - amount && balanceOf[recipient] == \old(balanceOf[recipient]) + amount;
  ensures sender == recipient -> balanceOf[sender] == \old(balanceOf[sender]);
  ensures \forall address a; a != sender && a != recipient -> balanceOf[a] == \old(balanceOf[a]);
  assignable allowance[sender][msg.sender], balanceOf[sender], balanceOf[recipient];
  function transferFrom(address sender, address recipient, uint amount) returns (bool) {
    allowance[sender][msg.sender] -= amount;
    balanceOf[sender] -= amount;
    balanceOf[recipient] += amount;
    return true;
  }

  ensures balanceOf[to] == \old(balanceOf[to]) + amount && totalSupply == \old(totalSupply) + amount;
  ensures \forall address a; a != to -> balanceOf[a] == \old(balanceOf[a]);
  assignable balanceOf[to], totalSupply;
  function _mint(address to, uint amount) {
    balanceOf[to] += amount;
    totalSupply += amount;
  }
  requires balanceOf[holder] >= amount && totalSupply >= amount;
  ensures balanceOf[holder] == \old(balanceOf[holder]) - amount && totalSupply == \old(totalSupply) - amount;
  ensures \forall address a; a != holder -> balanceOf[a] == \old(balanceOf[a]);
  assignable balanceOf[holder], totalSupply;
  function _burn(address holder, uint amount) {
    balanceOf[holder] -= amount;
    totalSupply -= amount;
  }
  ensures balanceOf[to] == \old(balanceOf[to]) + amount && totalSupply == \old(totalSupply) + amount;
  ensures \forall address a; a != to -> balanceOf[a] == \old(balanceOf[a]);
  assignable balanceOf[to], totalSupply;
  function mint(address to, uint amount) { _mint(to, amount); }
  requires balanceOf[holder] >= amount && totalSupply >= amount;
  ensures balanceOf[holder] == \old(balanceOf[holder]) - amount && totalSupply == \old(totalSupply) - amount;
  ensures \forall address a; a != holder -> balanceOf[a] == \old(balanceOf[a]);
  assignable balanceOf[holder], totalSupply;
  function burn(address holder, uint amount) { _burn(holder, amount); }
}

local instance : InContract := ⟨ERC20⟩
open scoped Scoped

/-- UNKNOWN: complete approve effect and guarded two-key allowance frame. -/
def spec_approve := spec!{ approve }

/-- PROVED: full transfer clauses, including aliases and quantified frame. -/
theorem transfer_obligation : ⊢ spec!{ transfer } := by
  sol_prove
/-- UNKNOWN: allowance debit followed by transfer accounting. -/
def transferFrom_obligation := spec!{ transferFrom }
/-- PROVED: balance/supply increase and frame. -/
theorem mintCore_obligation : ⊢ spec!{ _mint } := by
  sol_prove
/-- PROVED: balance/supply decrease and frame. -/
theorem burnCore_obligation : ⊢ spec!{ _burn } := by
  sol_prove
/-- PROVED: inlined mint preserves the same full clauses. -/
theorem mint_obligation : ⊢ spec!{ mint } := by
  sol_prove
/-- PROVED: inlined burn preserves the same full clauses. -/
theorem burn_obligation : ⊢ spec!{ burn } := by
  sol_prove

/-- Proved part of approve: result and written allowance, with full clauses retained above. -/
theorem approve_writtenSlot : ⊢ dl!{ [ bool ok = approve(spender, amount); ]
    ok == true && allowance[msg.sender][spender] == amount } := by
  sol_prove

end Solidity.Examples.Benchmark.Tokens.ERC20
