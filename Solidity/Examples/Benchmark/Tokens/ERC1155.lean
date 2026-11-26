import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# ERC1155 batch accounting, including repeated token IDs

Source: OpenZeppelin 5.0.2,
<https://raw.githubusercontent.com/OpenZeppelin/openzeppelin-contracts/dbb6104ce834628e473d2173bbc9d47f81a9eec3/contracts/token/ERC1155/ERC1155.sol>.
These are the base contract's balance/approval getters, approval setter and
internal `_update`, which upstream explicitly separates from receiver acceptance.
Metadata, balanceOfBatch, safe-transfer/mint/burn wrappers and acceptance callbacks
are omitted, not replaced by a receiver assumption. Events and their sole-use
operator local are erased. `_msgSender()` is msg.sender; `from` is holder;
custom-error branches become require (no claim about revert payloads).
`unsafeMemoryAccess(i)` becomes indexing: the loop guard and equal lengths
supply the source's bounds. Storage update order and unchecked subtraction stay.

Natural full batch effect, UNKNOWN: let S(t,i) be the mathematical sum of
values[j] for 0 <= j < i with ids[j] = t. For nonzero, distinct holder/to,
B_i(t,holder) = B_0(t,holder) - S(t,i) and
B_i(t,to) = B_0(t,to) + S(t,i); other accounts are unchanged. A zero holder with nonzero recipient
mints; nonzero holder with zero recipient burns; both zero is a no-op. Equal
nonzero holder/to leaves balances unchanged after each iteration. In particular duplicate IDs accumulate; a
single per-index debit/credit postcondition would be false and is not used.
The full prefix invariant needs a filtered finite-sum term and its extend law,
absent from SpecExpr. The loop's expressible bound and the expressible final
frames remain below; they do not substitute for this UNKNOWN sum obligation.
Verdicts: balanceOf and isApprovedForAll proved; both approval setters are
UNKNOWN (guarded two-key mapping frames). _update is UNKNOWN: even loop entry
needs memory-array length nonnegativity, before the missing sum/frame invariant.
No theorem here asserts receiver acceptance or guaranteed non-reversion.
-/
namespace Solidity.Examples.Benchmark.Tokens.ERC1155

def ERC1155 : Contract := contract!{
  mapping(uint => mapping(address => uint)) _balances;
  mapping(address => mapping(address => bool)) _operatorApprovals;
  ensures \result == _balances[id][account];
  assignable \nothing;
  function balanceOf(address account, uint id) returns (uint) {
    return _balances[id][account];
  }
  ensures \result == _operatorApprovals[account][operator];
  assignable \nothing;
  function isApprovedForAll(address account, address operator) returns (bool) {
    return _operatorApprovals[account][operator];
  }
  ensures _operatorApprovals[owner][operator] == approved && operator != address(0);
  assignable _operatorApprovals[owner][operator];
  function _setApprovalForAll(address owner, address operator, bool approved) {
    require(operator != address(0));
    _operatorApprovals[owner][operator] = approved;
  }
  ensures _operatorApprovals[msg.sender][operator] == approved && operator != address(0);
  assignable _operatorApprovals[msg.sender][operator];
  function setApprovalForAll(address operator, bool approved) {
    _setApprovalForAll(msg.sender, operator, approved);
  }
  ensures ids.length == values.length;
  ensures \forall uint t; _balances[t][address(0)] == \old(_balances[t][address(0)]);
  ensures \forall uint t; \forall address a; a != holder && a != to -> _balances[t][a] == \old(_balances[t][a]);
  ensures holder == to -> \forall uint t; _balances[t][holder] == \old(_balances[t][holder]);
  assignable _balances[*][*];
  function _update(address holder, address to, uint[] memory ids, uint[] memory values) {
    require(ids.length == values.length);
    /// @custom:key invariant i <= ids.length
    /// @custom:key decreases ids.length - i
    for (uint i = 0; i < ids.length; ++i) {
      uint id = ids[i];
      uint value = values[i];
      if (holder != address(0)) {
        uint fromBalance = _balances[id][holder];
        require(fromBalance >= value);
        unchecked { _balances[id][holder] = fromBalance - value; }
      }
      if (to != address(0)) { _balances[id][to] += value; }
    }
  }
}
local instance : InContract := ⟨ERC1155⟩
open scoped Scoped

/-- PROVED: balance getter and storage frame. -/
theorem balance_obligation : ⊢ spec!{ balanceOf } := by
  sol_prove
/-- PROVED: approval getter and storage frame. -/
theorem approved_obligation : ⊢ spec!{ isApprovedForAll } := by
  sol_prove
/-- UNKNOWN: internal approval setter and frame. -/
def setCore_obligation := spec!{ _setApprovalForAll }
/-- UNKNOWN: approval setter and frame. -/
def set_obligation := spec!{ setApprovalForAll }
/-- UNKNOWN: expressible batch frames; full aggregate effect is also unknown. -/
def batchFrame_obligation := spec!{ _update }
end Solidity.Examples.Benchmark.Tokens.ERC1155
