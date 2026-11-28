import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
/-!
# Burnable (OpenZeppelin 5.0.2 `ERC20Burnable`)

Sources (OpenZeppelin 5.0.2): <https://raw.githubusercontent.com/OpenZeppelin/openzeppelin-contracts/dbb6104ce834628e473d2173bbc9d47f81a9eec3/contracts/token/ERC20/extensions/ERC20Burnable.sol>
and the same commit's `token/ERC20/ERC20.sol` (`_update`, `_burn`,
`_spendAllowance`, `_approve`). Unlike the 4.9.6 port
(`Benchmark/Tokens/ERC20Burnable.lean`) burning runs through the 5.x
`_update(account, address(0), value)` hub. Custom-error reverts are `revert();`;
`from` is `from_`; the event flag, events and inheritance are omitted.
Natural spec: `burn`/`burnFrom` debit holder and supply by `value` (under
`balance <= supply`, the supply-sum instance that rules out the unchecked
wrap), touch no other balance; `burnFrom` spends a finite allowance only.
Verdicts: _approve proved; _spendAllowance, _burn, burn, burnFrom UNKNOWN at
guarded unchecked subtractions; burn frame and infinite allowance proved.
-/
namespace Solidity.Examples.Benchmark.TokenExtensions.Burnable
def ERC20Burnable : Contract := contract!{
  uint _totalSupply;
  mapping(address => uint) _balances;
  mapping(address => mapping(address => uint)) _allowances;
  function _update(address from_, address to, uint value) {
    if (from_ == address(0)) { _totalSupply += value; } else {
      uint fromBalance = _balances[from_];
      if (fromBalance < value) { revert(); }
      unchecked { _balances[from_] = fromBalance - value; }
    }
    if (to == address(0)) { unchecked { _totalSupply -= value; } }
    else { unchecked { _balances[to] += value; } }
  }
  ensures owner != address(0) && spender != address(0) && _allowances[owner][spender] == value;
  function _approve(address owner, address spender, uint value) {
    if (owner == address(0)) { revert(); }
    if (spender == address(0)) { revert(); }
    _allowances[owner][spender] = value;
  }
  ensures \old(_allowances[owner][spender]) == 115792089237316195423570985008687907853269984665640564039457584007913129639935 -> _allowances[owner][spender] == 115792089237316195423570985008687907853269984665640564039457584007913129639935;
  ensures \old(_allowances[owner][spender]) != 115792089237316195423570985008687907853269984665640564039457584007913129639935 -> _allowances[owner][spender] == \old(_allowances[owner][spender]) - value;
  function _spendAllowance(address owner, address spender, uint value) {
    uint currentAllowance = _allowances[owner][spender];
    if (currentAllowance != 115792089237316195423570985008687907853269984665640564039457584007913129639935) {
      if (currentAllowance < value) { revert(); }
      unchecked { _approve(owner, spender, currentAllowance - value); }
    }
  }
  ensures account != address(0) && \old(_balances[account]) >= value;
  ensures \old(_balances[account]) <= \old(_totalSupply) -> _balances[account] == \old(_balances[account]) - value && _totalSupply == \old(_totalSupply) - value;
  ensures \forall address a; a != account -> _balances[a] == \old(_balances[a]);
  function _burn(address account, uint value) {
    if (account == address(0)) { revert(); }
    _update(account, address(0), value);
  }
  ensures msg.sender != address(0) && \old(_balances[msg.sender]) >= value;
  ensures \old(_balances[msg.sender]) <= \old(_totalSupply) -> _balances[msg.sender] == \old(_balances[msg.sender]) - value && _totalSupply == \old(_totalSupply) - value;
  ensures \forall address a; a != msg.sender -> _balances[a] == \old(_balances[a]);
  function burn(uint value) {
    _burn(msg.sender, value);
  }
  ensures account != address(0) && \old(_balances[account]) >= value;
  ensures \old(_balances[account]) <= \old(_totalSupply) -> _balances[account] == \old(_balances[account]) - value && _totalSupply == \old(_totalSupply) - value;
  ensures \forall address a; a != account -> _balances[a] == \old(_balances[a]);
  ensures \old(_allowances[account][msg.sender]) == 115792089237316195423570985008687907853269984665640564039457584007913129639935 -> _allowances[account][msg.sender] == 115792089237316195423570985008687907853269984665640564039457584007913129639935;
  ensures \old(_allowances[account][msg.sender]) != 115792089237316195423570985008687907853269984665640564039457584007913129639935 -> _allowances[account][msg.sender] == \old(_allowances[account][msg.sender]) - value;
  function burnFrom(address account, uint value) {
    _spendAllowance(account, msg.sender, value);
    _burn(account, value);
  }
}
local instance : InContract := ⟨ERC20Burnable⟩
open scoped Scoped
/-- PROVED: both addresses checked, the slot written. -/
theorem approve_obligation : ⊢ spec!{ _approve } := by sol_prove
/-- UNKNOWN: the finite branch saves `currentAllowance -% value` (guarded). -/
def spendAllowance_obligation := spec!{ _spendAllowance }
/-- UNKNOWN: the leaf saves `se9 -% se8` and `se16 -% se8` (guarded), and stays open. -/
def burnCore_obligation := spec!{ _burn }
/-- UNKNOWN: as `_burn`, inlined; the frame is `burn_frame`. -/
def burn_obligation := spec!{ burn }
/-- UNKNOWN: as `_burn` and `_spendAllowance`; see `burnFrom_infinite`. -/
def burnFrom_obligation := spec!{ burnFrom }
/-- PROVED component: no other balance changes. -/
theorem burn_frame : ⊢ dl!{
    a0 == _balances[a] && a != msg.sender → [ burn(value); ] _balances[a] == a0 } := by sol_prove
/-- PROVED component: an infinite allowance is not spent. -/
theorem burnFrom_infinite : ⊢ dl!{ _allowances[account][msg.sender] == 115792089237316195423570985008687907853269984665640564039457584007913129639935 →
    [ burnFrom(account, value); ] _allowances[account][msg.sender] == 115792089237316195423570985008687907853269984665640564039457584007913129639935 } := by sol_prove

end Solidity.Examples.Benchmark.TokenExtensions.Burnable
