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
is no claim of overflow freedom for every input. The diamonds below specify
normal termination from valid words, funds and arithmetic headroom: approve
is proved; the other six remain UNKNOWN at checked-update definedness
and range propagation through successive storage saves.

Verdicts: transfer, _mint, _burn, mint and burn proved with all clauses and
frames. approve and transferFrom are UNKNOWN: their guarded two-key allowance
frames remain after sol_prove (nested path-disjointness/save-read closure).
The complete typed obligations remain below. The supply sum and six remaining
normal-termination/no-overflow obligations remain UNKNOWN.
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

/-! ## Successful calls under word-range and headroom conditions

These natural diamond obligations supplement the unchanged box clauses. Each
requires valid argument/key words, valid accessed storage words, zero value for
a nonpayable call, and sufficient arithmetic headroom. Self-transfers need no
recipient headroom beyond the original word bound. This specifies actual normal
termination, rather than concluding no-overflow from a vacuous reverting box.
Diamond verdicts: approve proved; transfer, transferFrom, _mint, _burn, mint
and burn UNKNOWN at checked-update definedness/range propagation through
successive storage saves. Each complete diamond remains stated below.
-/

/-- PROVED below: a valid allowance write returns normally. -/
def approve_noOverflow_obligation : Fml ERC20 [] := dl!{
  msg.value == 0 ∧ 0 <= msg.sender ∧ msg.sender <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 ∧
    0 <= spender ∧ spender <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 ∧ 0 <= amount ∧ amount <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 →
  ⟨ bool ok = approve(spender, amount); ⟩ ok == true }

/-- UNKNOWN: transfer succeeds with sender funds and recipient headroom. -/
def transfer_noOverflow_obligation : Fml ERC20 [] := dl!{
  msg.value == 0 ∧ 0 <= msg.sender ∧ msg.sender <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 ∧
    0 <= recipient ∧ recipient <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 ∧ 0 <= amount ∧ amount <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 ∧
    balanceOf[msg.sender] >= amount ∧ balanceOf[msg.sender] <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 ∧
    0 <= balanceOf[recipient] ∧ balanceOf[recipient] <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 ∧
    (msg.sender == recipient ∨ balanceOf[recipient] <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 - amount) →
  ⟨ bool ok = transfer(recipient, amount); ⟩ ok == true }

/-- UNKNOWN: delegated transfer also has sufficient allowance. -/
def transferFrom_noOverflow_obligation : Fml ERC20 [] := dl!{
  msg.value == 0 ∧ 0 <= msg.sender ∧ msg.sender <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 ∧
    0 <= sender ∧ sender <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 ∧ 0 <= recipient ∧ recipient <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 ∧
    0 <= amount ∧ amount <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 ∧
    allowance[sender][msg.sender] >= amount ∧ allowance[sender][msg.sender] <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 ∧
    balanceOf[sender] >= amount ∧ balanceOf[sender] <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 ∧
    0 <= balanceOf[recipient] ∧ balanceOf[recipient] <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 ∧
    (sender == recipient ∨ balanceOf[recipient] <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 - amount) →
  ⟨ bool ok = transferFrom(sender, recipient, amount); ⟩ ok == true }

/-- UNKNOWN: both mint additions fit in a word. -/
def mintCore_noOverflow_obligation : Fml ERC20 [] := dl!{
  msg.value == 0 ∧ 0 <= to ∧ to <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 ∧ 0 <= amount ∧ amount <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 ∧
    0 <= balanceOf[to] ∧ balanceOf[to] <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 - amount ∧
    0 <= totalSupply ∧ totalSupply <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 - amount →
  ⟨ _mint(to, amount); ⟩ true }

/-- UNKNOWN: both burn subtractions stay nonnegative. -/
def burnCore_noOverflow_obligation : Fml ERC20 [] := dl!{
  msg.value == 0 ∧ 0 <= holder ∧ holder <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 ∧ 0 <= amount ∧ amount <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 ∧
    balanceOf[holder] >= amount ∧ balanceOf[holder] <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 ∧
    totalSupply >= amount ∧ totalSupply <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 →
  ⟨ _burn(holder, amount); ⟩ true }

/-- UNKNOWN: the public mint wrapper has the same headroom contract. -/
def mint_noOverflow_obligation : Fml ERC20 [] := dl!{
  msg.value == 0 ∧ 0 <= to ∧ to <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 ∧ 0 <= amount ∧ amount <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 ∧
    0 <= balanceOf[to] ∧ balanceOf[to] <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 - amount ∧
    0 <= totalSupply ∧ totalSupply <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 - amount →
  ⟨ mint(to, amount); ⟩ true }

/-- UNKNOWN: the public burn wrapper has the same funds contract. -/
def burn_noOverflow_obligation : Fml ERC20 [] := dl!{
  msg.value == 0 ∧ 0 <= holder ∧ holder <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 ∧ 0 <= amount ∧ amount <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 ∧
    balanceOf[holder] >= amount ∧ balanceOf[holder] <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 ∧
    totalSupply >= amount ∧ totalSupply <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 →
  ⟨ burn(holder, amount); ⟩ true }

/-- Normal termination of approve under the complete stated word-range conditions. -/
theorem approve_noOverflow : ⊢ approve_noOverflow_obligation := by
  sol_prove







end Solidity.Examples.Benchmark.Tokens.ERC20
