import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# OpenZeppelin ERC721Burnable ownership and approval deletion

Sources (OpenZeppelin 4.9.6):
<https://raw.githubusercontent.com/OpenZeppelin/openzeppelin-contracts/dc44c9f1a4c3b10af99492eed84f83ed244203f6/contracts/token/ERC721/extensions/ERC721Burnable.sol>
and the same commit's `contracts/token/ERC721/ERC721.sol`.
Base getters/authorization and _burn are inlined; repeated pure owner reads
are coalesced with no intervening effects. Empty base hooks, events,
inheritance and descriptive metadata/constructor are omitted. No derived hook
or receiver behavior is claimed. Authorization precedes approval deletion,
unchecked balance decrement and owner deletion, in the source order.

Natural full spec: only the owner/approved caller can successfully burn an
existing token; ownership and approval are cleared, the former owner's count
is decremented, and other slots are framed. The unchecked zero-count case is
retained explicitly, rather than adding a balance >= 1 premise. A reachable
owner-count aggregate would exclude it, but that count term/laws are UNKNOWN.
The full burn verdict is UNKNOWN: guarded wrapped-subtraction/old-owner
normalization remains after sol_prove. All natural clauses remain below.
The owner/approval-clearing component is proved separately.
-/
namespace Solidity.Examples.Benchmark.Tokens.ERC721Burnable

def ERC721Burnable : Contract := contract!{
  mapping(uint => address) _owners;
  mapping(address => uint) _balances;
  mapping(uint => address) _tokenApprovals;
  mapping(address => mapping(address => bool)) _operatorApprovals;
  ensures \old(_owners[id]) != address(0);
  ensures \old(_owners[id]) == msg.sender || \old(_operatorApprovals[_owners[id]][msg.sender]) || \old(_tokenApprovals[id]) == msg.sender;
  ensures _owners[id] == address(0) && _tokenApprovals[id] == address(0);
  ensures \old(_balances[_owners[id]]) >= 1 -> _balances[\old(_owners[id])] == \old(_balances[_owners[id]]) - 1;
  ensures \old(_balances[_owners[id]]) == 0 -> _balances[\old(_owners[id])] == 115792089237316195423570985008687907853269984665640564039457584007913129639935;
  assignable _tokenApprovals[id], _balances[_owners[id]], _owners[id];
  function burn(uint id) {
    address owner = _owners[id];
    require(owner != address(0));
    require(msg.sender == owner || _operatorApprovals[owner][msg.sender] || _tokenApprovals[id] == msg.sender);
    delete _tokenApprovals[id];
    unchecked { _balances[owner] -= 1; }
    delete _owners[id];
  }
}
local instance : InContract := ⟨ERC721Burnable⟩
open scoped Scoped
/-- UNKNOWN: authorization, deletion, exact word count effect and frame. -/
def burn_obligation := spec!{ burn }
/-- Component only: burning clears owner and token approval, including unchecked count cases. -/
theorem burn_clears : ⊢ dl!{ [ burn(id); ]
  (_owners[id] == 0 ∧ _tokenApprovals[id] == 0) } := by
  sol_prove

end Solidity.Examples.Benchmark.Tokens.ERC721Burnable
