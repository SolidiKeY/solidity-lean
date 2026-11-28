import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
/-!
# OpenZeppelin `increaseAllowance` / `decreaseAllowance`

Source: <https://raw.githubusercontent.com/OpenZeppelin/openzeppelin-contracts/dc44c9f1a4c3b10af99492eed84f83ed244203f6/contracts/token/ERC20/ERC20.sol> (OpenZeppelin 4.9.6: `allowance`,
`increaseAllowance`, `decreaseAllowance`, `_approve`). `_msgSender()` is
`msg.sender`; events, the rest of the token and inheritance are omitted; the
increase is checked, the decrease unchecked after its `require`, as published.
Natural spec: the caller's allowance for `spender` moves by exactly the delta,
both addresses are nonzero, and no other allowance changes.
Verdicts: allowance, _approve proved; increaseAllowance UNKNOWN as one
obligation (disjunctive frame), every clause proved as a component;
decreaseAllowance UNKNOWN at the guarded unchecked subtraction, frames proved.
-/
namespace Solidity.Examples.Benchmark.TokenExtensions.AllowanceDelta
def AllowanceDelta : Contract := contract!{
  mapping(address => mapping(address => uint)) _allowances;
  ensures \result == _allowances[owner][spender];
  function allowance(address owner, address spender) returns (uint) { return _allowances[owner][spender]; }
  ensures owner != address(0) && spender != address(0) && _allowances[owner][spender] == amount;
  function _approve(address owner, address spender, uint amount) {
    require(owner != address(0));
    require(spender != address(0));
    _allowances[owner][spender] = amount;
  }
  ensures \result && msg.sender != address(0) && spender != address(0);
  ensures _allowances[msg.sender][spender] == \old(_allowances[msg.sender][spender]) + addedValue;
  ensures \forall address o; \forall address s; o != msg.sender || s != spender -> _allowances[o][s] == \old(_allowances[o][s]);
  function increaseAllowance(address spender, uint addedValue) returns (bool) {
    address owner = msg.sender;
    uint current = allowance(owner, spender);
    _approve(owner, spender, current + addedValue);
    return true;
  }
  requires _allowances[msg.sender][spender] >= subtractedValue;
  ensures \result && msg.sender != address(0) && spender != address(0);
  ensures _allowances[msg.sender][spender] == \old(_allowances[msg.sender][spender]) - subtractedValue;
  ensures \forall address o; \forall address s; o != msg.sender || s != spender -> _allowances[o][s] == \old(_allowances[o][s]);
  function decreaseAllowance(address spender, uint subtractedValue) returns (bool) {
    address owner = msg.sender;
    uint currentAllowance = allowance(owner, spender);
    require(currentAllowance >= subtractedValue);
    unchecked { _approve(owner, spender, currentAllowance - subtractedValue); }
    return true;
  }
}
local instance : InContract := ⟨AllowanceDelta⟩
open scoped Scoped
/-- PROVED: the getter returns the slot. -/
theorem allowance_obligation : ⊢ spec!{ allowance } := by sol_prove
/-- PROVED: `_approve` checks both addresses and writes the slot. -/
theorem approve_obligation : ⊢ spec!{ _approve } := by sol_prove
/-- UNKNOWN as one obligation: the frame premise `o != msg.sender || s != spender`
needs a case split; every clause is proved by the components below. -/
def increaseAllowance_obligation := spec!{ increaseAllowance }
/-- UNKNOWN: the guarded unchecked write leaves `se5 -% se2` (`se5 >= se2` known)
against `… - subtractedValue`; its two frame cases are proved below. -/
def decreaseAllowance_obligation := spec!{ decreaseAllowance }
/-- PROVED component: result, nonzero addresses, exact increase. -/
theorem increaseAllowance_effect : ⊢ dl!{ l0 == _allowances[msg.sender][spender] →
    [ bool ok = increaseAllowance(spender, addedValue); ]
      ok == true && msg.sender != 0 && spender != 0 && _allowances[msg.sender][spender] == l0 + addedValue } := by sol_prove
/-- PROVED component: another owner's allowances are unchanged. -/
theorem increaseAllowance_frameOwner : ⊢ dl!{ x0 == _allowances[o][s] && o != msg.sender →
    [ bool ok = increaseAllowance(spender, addedValue); ] _allowances[o][s] == x0 } := by sol_prove
/-- PROVED component: the caller's allowances to other spenders are unchanged. -/
theorem increaseAllowance_frameSpender : ⊢ dl!{ x0 == _allowances[o][s] && s != spender →
    [ bool ok = increaseAllowance(spender, addedValue); ] _allowances[o][s] == x0 } := by sol_prove
/-- PROVED component: another owner's allowances are unchanged. -/
theorem decreaseAllowance_frameOwner : ⊢ dl!{ x0 == _allowances[o][s] && o != msg.sender →
    [ bool ok = decreaseAllowance(spender, subtractedValue); ] _allowances[o][s] == x0 } := by sol_prove
/-- PROVED component: the caller's allowances to other spenders are unchanged. -/
theorem decreaseAllowance_frameSpender : ⊢ dl!{ x0 == _allowances[o][s] && s != spender →
    [ bool ok = decreaseAllowance(spender, subtractedValue); ] _allowances[o][s] == x0 } := by sol_prove

end Solidity.Examples.Benchmark.TokenExtensions.AllowanceDelta
