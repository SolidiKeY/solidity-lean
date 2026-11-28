import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Capped supply (OpenZeppelin 5.0.2 `ERC20Capped`)

Sources (OpenZeppelin 5.0.2):
<https://raw.githubusercontent.com/OpenZeppelin/openzeppelin-contracts/dbb6104ce834628e473d2173bbc9d47f81a9eec3/contracts/token/ERC20/extensions/ERC20Capped.sol>
and the same commit's `contracts/token/ERC20/ERC20.sol` (`_update`, `_mint`). `from` is a Lean keyword: the parameter is `from_`.
Unlike the 4.9.6 port (`Benchmark/Tokens/ERC20Capped.lean`), the cap is
checked *after* the base `_update` has run, on the new supply, and only on
the mint path (`from == address(0)`); `super._update` is inlined at the head
of the override. Custom-error reverts are `revert();`, `totalSupply()` and
`cap()` reads of their slots; events, metadata and inheritance are omitted.

Natural spec: a mint path never leaves the supply above the cap; a mint to a
nonzero account adds exactly `value` to the supply, credits the account
(stated under `balance <= supply`, the instance of the supply-sum invariant
that rules out the unchecked wrap) and leaves every other balance.

Verdicts: constructor, cap proved; _update and _mint UNKNOWN (cap bound
next to unchecked saves, wrapped credit); mint supply and frame proved.
-/
namespace Solidity.Examples.Benchmark.TokenExtensions.CappedSupply

def ERC20Capped : Contract := contract!{
  uint immutable _cap;
  uint _totalSupply;
  mapping(address => uint) _balances;
  ensures _cap == cap_ && _cap > 0;
  constructor(uint cap_) {
    if (cap_ == 0) {
      revert();
    }
    _cap = cap_;
  }
  ensures \result == _cap;
  function cap() returns (uint) { return _cap; }
  ensures from_ == address(0) -> _totalSupply <= _cap;
  ensures from_ == address(0) && to != address(0) -> _totalSupply == \old(_totalSupply) + value;
  function _update(address from_, address to, uint value) {
    if (from_ == address(0)) {
      _totalSupply += value;
    } else {
      uint fromBalance = _balances[from_];
      if (fromBalance < value) {
        revert();
      }
      unchecked {
        _balances[from_] = fromBalance - value;
      }
    }
    if (to == address(0)) {
      unchecked {
        _totalSupply -= value;
      }
    } else {
      unchecked {
        _balances[to] += value;
      }
    }
    if (from_ == address(0)) {
      uint maxSupply = cap();
      uint supply = _totalSupply;
      if (supply > maxSupply) {
        revert();
      }
    }
  }
  ensures account != address(0) && _totalSupply == \old(_totalSupply) + value && _totalSupply <= _cap;
  ensures \old(_balances[account]) <= \old(_totalSupply) -> _balances[account] == \old(_balances[account]) + value;
  ensures \forall address a; a != account -> _balances[a] == \old(_balances[a]);
  function _mint(address account, uint value) {
    if (account == address(0)) {
      revert();
    }
    _update(address(0), account, value);
  }
}
local instance : InContract := ⟨ERC20Capped⟩
open scoped Scoped

/-- PROVED: a zero cap reverts; the cap is stored. -/
theorem constructor_obligation : ⊢ spec!{ constructor } := by
  sol_prove
/-- PROVED: the getter returns the cap. -/
theorem cap_obligation : ⊢ spec!{ cap } := by
  sol_prove
/-- UNKNOWN: on the mint-and-burn branch (`from_ == to == address(0)`) the
leaf binds `se10 := se11 -% se3` and saves it; the goal
`find(storage, _totalSupply) <= find(storage, _cap)` follows from the cap
check `se6 > se5 = false` read back from that save, but does not close. -/
def update_obligation := spec!{ _update }
/-- UNKNOWN: the wrapped balance credit `se14 +% se5`, and the cap bound
(`mint_capBound`); supply and frame are proved in `mint_supplyFrame`. -/
def mint_obligation := spec!{ _mint }
/-- UNKNOWN component: the cap bound; the leaf has the cap check
`find(storage, _totalSupply) > find(storage, _cap) = false` after the `+%`
balance save and the inlined `cap()`, and stays open. -/
def mint_capBound : Fml ERC20Capped [] := dl!{ [ _mint(account, value); ] _totalSupply <= _cap }
/-- PROVED component: nonzero receiver, exact supply increase, frame. -/
theorem mint_supplyFrame : ⊢ dl!{
    t0 == _totalSupply && a0 == _balances[a] && a != account →
    [ _mint(account, value); ] account != 0 && _totalSupply == t0 + value && _balances[a] == a0 } := by
  sol_prove

end Solidity.Examples.Benchmark.TokenExtensions.CappedSupply
