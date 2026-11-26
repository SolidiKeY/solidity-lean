import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# ERC721 ownership and approval accounting

Source: <https://raw.githubusercontent.com/Cyfrin/solidity-by-example.github.io/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/app/erc721/ERC721.sol>.
This is the published non-safe accounting core: interface declarations,
supportsInterface, events and the two safeTransferFrom receiver-callback wrappers
are omitted. No assertion about safe receiver acceptance follows from this
module. `from` is renamed `holder`; visibility is erased as in the benchmark.
The unused postfix decrement is spelled `-= 1` to avoid Lean comment syntax.
The helper's call, authorization checks, balance changes, owner update and
approval deletion retain source order. A token's single owner slot expresses
ownership uniqueness; transfer frames every other owner slot. Consistency of
balances with the cardinality of owned token IDs is a separate UNKNOWN aggregate
invariant, requiring a finite-support count term.

Verdicts: ownerOf, balanceOf, approve, getApproved, transferFrom, _mint and
_burn proved. setApprovalForAll is UNKNOWN (guarded two-key mapping frame);
_isApprovedOrOwner is UNKNOWN (short-circuit Boolean equivalence). The complete
clauses remain as obligation definitions for these two functions. A box permits revert, including
arithmetic failure, and does not prove mint or transfer succeeds.
-/
namespace Solidity.Examples.Benchmark.Tokens.ERC721

def ERC721 : Contract := contract!{
  mapping(uint => address) _ownerOf;
  mapping(address => uint) _balanceOf;
  mapping(uint => address) _approvals;
  mapping(address => mapping(address => bool)) isApprovedForAll;

  ensures \result == _ownerOf[id] && \result != address(0);
  assignable \nothing;
  function ownerOf(uint id) returns (address owner) {
    owner = _ownerOf[id];
    require(owner != address(0));
  }
  ensures \result == _balanceOf[owner];
  assignable \nothing;
  function balanceOf(address owner) returns (uint) {
    require(owner != address(0));
    return _balanceOf[owner];
  }
  ensures isApprovedForAll[msg.sender][operator] == approved;
  assignable isApprovedForAll[msg.sender][operator];
  function setApprovalForAll(address operator, bool approved) {
    isApprovedForAll[msg.sender][operator] = approved;
  }
  ensures _approvals[id] == spender;
  assignable _approvals[id];
  function approve(address spender, uint id) {
    address owner = _ownerOf[id];
    require(msg.sender == owner || isApprovedForAll[owner][msg.sender]);
    _approvals[id] = spender;
  }
  ensures \result == _approvals[id] && _ownerOf[id] != address(0);
  assignable \nothing;
  function getApproved(uint id) returns (address) {
    require(_ownerOf[id] != address(0));
    return _approvals[id];
  }
  ensures \result == (spender == owner || isApprovedForAll[owner][spender] || spender == _approvals[id]);
  assignable \nothing;
  function _isApprovedOrOwner(address owner, address spender, uint id) returns (bool) {
    return spender == owner || isApprovedForAll[owner][spender] || spender == _approvals[id];
  }
  ensures _ownerOf[id] == to && _approvals[id] == address(0);
  ensures \forall address a; _ownerOf[id] == a -> a == to;
  ensures holder != to -> _balanceOf[holder] == \old(_balanceOf[holder]) - 1 && _balanceOf[to] == \old(_balanceOf[to]) + 1;
  ensures holder == to -> _balanceOf[holder] == \old(_balanceOf[holder]);
  assignable _balanceOf[holder], _balanceOf[to], _ownerOf[id], _approvals[id];
  function transferFrom(address holder, address to, uint id) {
    require(holder == _ownerOf[id]);
    require(to != address(0));
    require(_isApprovedOrOwner(holder, msg.sender, id));
    _balanceOf[holder] -= 1;
    _balanceOf[to]++;
    _ownerOf[id] = to;
    delete _approvals[id];
  }
  ensures _ownerOf[id] == to && to != address(0);
  ensures _balanceOf[to] == \old(_balanceOf[to]) + 1;
  assignable _balanceOf[to], _ownerOf[id];
  function _mint(address to, uint id) {
    require(to != address(0));
    require(_ownerOf[id] == address(0));
    _balanceOf[to]++;
    _ownerOf[id] = to;
  }
  ensures _ownerOf[id] == address(0) && _approvals[id] == address(0);
  ensures _balanceOf[\old(_ownerOf[id])] == \old(_balanceOf[_ownerOf[id]]) - 1;
  assignable _balanceOf[_ownerOf[id]], _ownerOf[id], _approvals[id];
  function _burn(uint id) {
    address owner = _ownerOf[id];
    require(owner != address(0));
    _balanceOf[owner] -= 1;
    delete _ownerOf[id];
    delete _approvals[id];
  }
}
local instance : InContract := ⟨ERC721⟩
open scoped Scoped

/-- PROVED: owner getter and storage frame. -/
theorem ownerOf_obligation : ⊢ spec!{ ownerOf } := by
  sol_prove
/-- PROVED: balance getter and storage frame. -/
theorem balanceOf_obligation : ⊢ spec!{ balanceOf } := by
  sol_prove
/-- UNKNOWN: operator approval and frame. -/
def operator_obligation := spec!{ setApprovalForAll }
/-- PROVED: authorized single-token approval and frame. -/
theorem approve_obligation : ⊢ spec!{ approve } := by
  sol_prove
/-- PROVED: approval getter and existence check. -/
theorem getApproved_obligation : ⊢ spec!{ getApproved } := by
  sol_prove
/-- UNKNOWN: authorization helper truth value. -/
def authorized_obligation := spec!{ _isApprovedOrOwner }
/-- PROVED: ownership uniqueness, approval clearing, balances and frame. -/
theorem transfer_obligation : ⊢ spec!{ transferFrom } := by
  sol_prove
/-- PROVED: fresh ownership and balance increase. -/
theorem mint_obligation : ⊢ spec!{ _mint } := by
  sol_prove
/-- PROVED: owner/approval deletion and former owner balance decrease. -/
theorem burn_obligation : ⊢ spec!{ _burn } := by
  sol_prove
end Solidity.Examples.Benchmark.Tokens.ERC721
