import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Role-gated mint (OpenZeppelin `ERC20PresetMinterPauser.mint`)

Sources (OpenZeppelin 4.9.6):
<https://raw.githubusercontent.com/OpenZeppelin/openzeppelin-contracts/dc44c9f1a4c3b10af99492eed84f83ed244203f6/contracts/token/ERC20/presets/ERC20PresetMinterPauser.sol>
(`mint`), the same commit's `contracts/access/AccessControl.sol`
(`hasRole`, `getRoleAdmin`, `grantRole` with `onlyRole`, `_grantRole`) and
`contracts/token/ERC20/ERC20.sol` (`_mint`, empty hooks dropped).

Changes: `bytes32` role ids are `uint` words (no hashing; `MINTER_ROLE` is
the parameter-free getter `minterRole()` of a stored word written once), and
`RoleData`'s two fields are two mappings `_members[role][account]` and
`_admin[role]`. Events, pausing, enumeration and inheritance are omitted.

Natural spec: only a holder of the minter role mints; a mint adds `amount`
to the supply and to `to`'s balance and touches no other balance; granting
needs the role's admin role and makes `account` a member.

Verdicts: hasRole, _grantRole, grantRole proved; _mint and mint UNKNOWN at
the unchecked credit, every other clause (role guard, supply, frame) proved.
-/
namespace Solidity.Examples.Benchmark.TokenExtensions.RoleMint

def RoleMint : Contract := contract!{
  uint _minterRole;
  mapping(uint => mapping(address => bool)) _members;
  mapping(uint => uint) _admin;
  uint _totalSupply;
  mapping(address => uint) _balances;
  ensures \result == _members[role][account];
  function hasRole(uint role, address account) returns (bool) {
    return _members[role][account];
  }
  ensures \result == _admin[role];
  function getRoleAdmin(uint role) returns (uint) {
    return _admin[role];
  }
  ensures _members[role][account];
  function _grantRole(uint role, address account) {
    bool has = hasRole(role, account);
    if (!has) {
      _members[role][account] = true;
    }
  }
  ensures _members[_admin[role]][msg.sender] && _members[role][account];
  function grantRole(uint role, address account) {
    uint adminRole = getRoleAdmin(role);
    bool ok = hasRole(adminRole, msg.sender);
    require(ok);
    _grantRole(role, account);
  }
  ensures account != address(0) && _totalSupply == \old(_totalSupply) + amount;
  ensures \old(_balances[account]) <= \old(_totalSupply) -> _balances[account] == \old(_balances[account]) + amount;
  ensures \forall address a; a != account -> _balances[a] == \old(_balances[a]);
  function _mint(address account, uint amount) {
    require(account != address(0));
    _totalSupply += amount;
    unchecked {
      _balances[account] += amount;
    }
  }
  ensures \old(_members[_minterRole][msg.sender]);
  ensures to != address(0) && _totalSupply == \old(_totalSupply) + amount;
  ensures \old(_balances[to]) <= \old(_totalSupply) -> _balances[to] == \old(_balances[to]) + amount;
  ensures \forall address a; a != to -> _balances[a] == \old(_balances[a]);
  function mint(address to, uint amount) {
    bool ok = hasRole(_minterRole, msg.sender);
    require(ok);
    _mint(to, amount);
  }
}
local instance : InContract := ⟨RoleMint⟩
open scoped Scoped

/-- PROVED: `hasRole` reads the membership slot. -/
theorem hasRole_obligation : ⊢ spec!{ hasRole } := by
  sol_prove
/-- PROVED: after `_grantRole` the account is a member. -/
theorem grantRoleCore_obligation : ⊢ spec!{ _grantRole } := by
  sol_prove
/-- PROVED: `grantRole` needs the admin role and makes the account a member. -/
theorem grantRole_obligation : ⊢ spec!{ grantRole } := by
  sol_prove
/-- UNKNOWN: the unchecked credit leaves `se5 +% se2` against
`find(old, _balances[account]) + amount` under `balance <= supply`: no closer
rewrites a wrapped addition known not to wrap to `+`. Every other clause is
proved in `mintCore_supplyFrame`. -/
def mintCore_obligation := spec!{ _mint }
/-- UNKNOWN: the same wrapped credit, through the inlined `_mint`; every
other clause, the role guard included, is proved in `mint_gated`. -/
def mint_obligation := spec!{ mint }

/-- PROVED component: `_mint`'s supply, nonzero receiver and frame. -/
theorem mintCore_supplyFrame : ⊢ dl!{
    t0 == _totalSupply && a0 == _balances[a] && a != account →
    [ _mint(account, amount); ] account != 0 && _totalSupply == t0 + amount && _balances[a] == a0 } := by
  sol_prove
/-- UNKNOWN component: the credit under `balance <= supply`, at the `+%` leaf. -/
def mintCore_credit : Fml RoleMint [] := dl!{
    b0 == _balances[account] && b0 <= _totalSupply →
    [ _mint(account, amount); ] _balances[account] == b0 + amount }
/-- PROVED component: only a minter mints; supply, receiver and frame. -/
theorem mint_gated : ⊢ dl!{
    t0 == _totalSupply && a0 == _balances[a] && a != to →
    [ mint(to, amount); ] _members[_minterRole][msg.sender] == true && to != 0 && _totalSupply == t0 + amount && _balances[a] == a0 } := by
  sol_prove

end Solidity.Examples.Benchmark.TokenExtensions.RoleMint
