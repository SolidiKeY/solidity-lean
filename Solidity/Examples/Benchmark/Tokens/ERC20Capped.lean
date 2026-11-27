import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# OpenZeppelin ERC20Capped accounting

Sources (OpenZeppelin 4.9.6):
<https://raw.githubusercontent.com/OpenZeppelin/openzeppelin-contracts/dc44c9f1a4c3b10af99492eed84f83ed244203f6/contracts/token/ERC20/extensions/ERC20Capped.sol>
and the same commit's `contracts/token/ERC20/ERC20.sol`.
The parent mint body is inlined after the cap check, preserving its checked
supply addition and unchecked balance addition. Empty base hooks, events,
inheritance and descriptive metadata/its constructor are omitted; no derived
hook behavior or deployed ABI is asserted. Immutable is read as a storage root,
as the surface language does; no ordinary function writes it.

The natural spec covers the constructor, cap getter, capped supply increase,
exact word balance effect and storage frame. Both balance-addition cases are
retained for arbitrary typed stores: a zero-initialized reachable ERC20 balance
cannot exceed totalSupply, but that finite-support sum invariant is still
UNKNOWN, not added as a premise to make an unchecked addition prove.
Verdicts: constructor and cap proved; _mint UNKNOWN at guarded wrapped-add
normalization and its frame. The complete mint clauses remain below;
the cap-bound component is proved separately and does not replace them.
-/
namespace Solidity.Examples.Benchmark.Tokens.ERC20Capped

def ERC20Capped : Contract := contract!{
  uint immutable _cap;
  uint _totalSupply;
  mapping(address => uint) _balances;
  ensures _cap == cap_ && _cap > 0 && _totalSupply == 0;
  ensures \forall address a; _balances[a] == 0;
  constructor(uint cap_) { require(cap_ > 0); _cap = cap_; }
  ensures \result == _cap;
  assignable \nothing;
  function cap() returns (uint) { return _cap; }
  ensures account != address(0) && _totalSupply == \old(_totalSupply) + amount && _totalSupply <= _cap;
  ensures \old(_balances[account]) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 - amount -> _balances[account] == \old(_balances[account]) + amount;
  ensures \old(_balances[account]) > 115792089237316195423570985008687907853269984665640564039457584007913129639935 - amount -> _balances[account] == \old(_balances[account]) - (115792089237316195423570985008687907853269984665640564039457584007913129639935 - amount) - 1;
  assignable _totalSupply, _balances[account];
  function _mint(address account, uint amount) {
    require(_totalSupply + amount <= cap());
    require(account != address(0));
    _totalSupply += amount;
    unchecked { _balances[account] += amount; }
  }
}
local instance : InContract := ⟨ERC20Capped⟩
open scoped Scoped
/-- PROVED: cap initialization and zero supply/balances. -/
theorem constructor_obligation : ⊢ spec!{ constructor } := by
  sol_prove
/-- PROVED: cap getter and full frame. -/
theorem cap_obligation : ⊢ spec!{ cap } := by
  sol_prove
/-- UNKNOWN: cap, exact word effect and full frame. -/
def mint_obligation := spec!{ _mint }
/-- Component only: a successful capped mint stays below its cap. -/
theorem mint_capBound : ⊢ dl!{ [ _mint(account, amount); ] _totalSupply <= _cap } := by
  sol_prove

end Solidity.Examples.Benchmark.Tokens.ERC20Capped
