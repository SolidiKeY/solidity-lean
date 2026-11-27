import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# OpenZeppelin ERC20Burnable, including infinite allowance

Sources (OpenZeppelin 4.9.6):
<https://raw.githubusercontent.com/OpenZeppelin/openzeppelin-contracts/dc44c9f1a4c3b10af99492eed84f83ed244203f6/contracts/token/ERC20/extensions/ERC20Burnable.sol>
and the same commit's `contracts/token/ERC20/ERC20.sol`.
The base allowance getter and _approve checks/write are inlined in
_spendAllowance; the _burn body is retained. `_msgSender()` is msg.sender.
Empty base hooks, events, inheritance and descriptive metadata/constructor are
omitted; no behavior of derived hook overrides is claimed. The all-ones
allowance sentinel and the unchecked source operations are not simplified away.

Natural spec: burn debits the holder and supply; burnFrom additionally spends
finite allowance, preserving infinite allowance. Full frames and the exact
unchecked supply-underflow case are retained for arbitrary typed stores.
On initialized reachable stores, the supply sum prevents that underflow, but
this global aggregate remains UNKNOWN (missing finite-support sum term/laws).
No supply >= amount premise is inserted to hide the unchecked source case.
All four complete functions are UNKNOWN: _spendAllowance retains a guarded
two-key mapping frame; _burn/burn/burnFrom retain wrapped-subtraction leaves
(and burnFrom its allowance frame). Complete clauses are retained below.
The infinite-allowance component is proved separately.
-/
namespace Solidity.Examples.Benchmark.Tokens.ERC20Burnable

def ERC20Burnable : Contract := contract!{
  uint _totalSupply;
  mapping(address => uint) _balances;
  mapping(address => mapping(address => uint)) _allowances;
  ensures \old(_allowances[owner][spender]) == 115792089237316195423570985008687907853269984665640564039457584007913129639935 -> _allowances[owner][spender] == 115792089237316195423570985008687907853269984665640564039457584007913129639935;
  ensures \old(_allowances[owner][spender]) != 115792089237316195423570985008687907853269984665640564039457584007913129639935 -> _allowances[owner][spender] == \old(_allowances[owner][spender]) - amount;
  assignable _allowances[owner][spender];
  function _spendAllowance(address owner, address spender, uint amount) {
    uint currentAllowance = _allowances[owner][spender];
    if (currentAllowance != 115792089237316195423570985008687907853269984665640564039457584007913129639935) {
      require(currentAllowance >= amount);
      unchecked {
        require(owner != address(0));
        require(spender != address(0));
        _allowances[owner][spender] = currentAllowance - amount;
      }
    }
  }
  ensures account != address(0) && _balances[account] == \old(_balances[account]) - amount;
  ensures \old(_totalSupply) >= amount -> _totalSupply == \old(_totalSupply) - amount;
  ensures \old(_totalSupply) < amount -> _totalSupply == 115792089237316195423570985008687907853269984665640564039457584007913129639935 - (amount - \old(_totalSupply)) + 1;
  assignable _balances[account], _totalSupply;
  function _burn(address account, uint amount) {
    require(account != address(0));
    uint accountBalance = _balances[account];
    require(accountBalance >= amount);
    unchecked {
      _balances[account] = accountBalance - amount;
      _totalSupply -= amount;
    }
  }
  ensures msg.sender != address(0) && _balances[msg.sender] == \old(_balances[msg.sender]) - amount;
  ensures \old(_totalSupply) >= amount -> _totalSupply == \old(_totalSupply) - amount;
  ensures \old(_totalSupply) < amount -> _totalSupply == 115792089237316195423570985008687907853269984665640564039457584007913129639935 - (amount - \old(_totalSupply)) + 1;
  assignable _balances[msg.sender], _totalSupply;
  function burn(uint amount) { _burn(msg.sender, amount); }
  ensures account != address(0) && _balances[account] == \old(_balances[account]) - amount;
  ensures \old(_totalSupply) >= amount -> _totalSupply == \old(_totalSupply) - amount;
  ensures \old(_totalSupply) < amount -> _totalSupply == 115792089237316195423570985008687907853269984665640564039457584007913129639935 - (amount - \old(_totalSupply)) + 1;
  ensures \old(_allowances[account][msg.sender]) == 115792089237316195423570985008687907853269984665640564039457584007913129639935 -> _allowances[account][msg.sender] == 115792089237316195423570985008687907853269984665640564039457584007913129639935;
  ensures \old(_allowances[account][msg.sender]) != 115792089237316195423570985008687907853269984665640564039457584007913129639935 -> _allowances[account][msg.sender] == \old(_allowances[account][msg.sender]) - amount;
  assignable _balances[account], _totalSupply, _allowances[account][msg.sender];
  function burnFrom(address account, uint amount) {
    _spendAllowance(account, msg.sender, amount);
    _burn(account, amount);
  }
}
local instance : InContract := ⟨ERC20Burnable⟩
open scoped Scoped
/-- UNKNOWN: finite spend versus infinite allowance and frame. -/
def allowance_obligation := spec!{ _spendAllowance }
/-- UNKNOWN: balance debit and exact unchecked supply effect. -/
def burnCore_obligation := spec!{ _burn }
/-- UNKNOWN: caller burn and full frame. -/
def burn_obligation := spec!{ burn }
/-- UNKNOWN: delegated burn, allowance sentinel and full frame. -/
def burnFrom_obligation := spec!{ burnFrom }
/-- Component only: infinite allowance is not spent, without excluding zero addresses. -/
theorem infiniteAllowance : ⊢ dl!{
  _allowances[owner][spender] == 115792089237316195423570985008687907853269984665640564039457584007913129639935 →
  [ _spendAllowance(owner, spender, amount); ] _allowances[owner][spender] == 115792089237316195423570985008687907853269984665640564039457584007913129639935 } := by
  sol_prove

end Solidity.Examples.Benchmark.Tokens.ERC20Burnable
