import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: `OZOwnable2Step`

Source: <https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/contracts/real-world/OZOwnable2Step.sol>
(solkey's flattening of OpenZeppelin v5.0.0 `access/Ownable2Step.sol` and
`access/Ownable.sol`).  Not `Governance/Ownable.lean` (v4.9.6, one step):
this one has the pending owner and `acceptOwnership`.

Changes: only the spelling of `contract!{ … }` (a branch is a block ending
in `;`) and solkey's `@custom:key` clauses written above the functions they
annotate.  `_transferOwnership` is declared before the constructor, since a
function calls only the functions declared before it; the modifier is
inlined (`Examples/Benchmark/Syntax.lean`).

Verdicts: see the theorems.
-/

namespace Solidity.Examples.Benchmark.SolkeyOz.OZOwnable2Step

/-- `OZOwnable2Step.sol` with solkey's clauses. -/
def OZOwnable2Step : Contract := contract!{
  address private _owner;
  address private _pendingOwner;
  function _transferOwnership(address newOwner) internal virtual {
    delete _pendingOwner;
    _owner = newOwner;
  }
  ensures initialOwner != address(0) && _owner == initialOwner && _pendingOwner == address(0);
  constructor(address initialOwner) {
    if (initialOwner == address(0)) {
      revert();
    };
    _transferOwnership(initialOwner);
  }
  modifier onlyOwner() {
    if (_owner != msg.sender) {
      revert();
    };
    _;
  }
  ensures o == _owner && _owner == \old(_owner);
  function owner() public view virtual returns (address o) {
    return _owner;
  }
  function _checkOwner() internal view virtual {
    if (owner() != msg.sender) {
      revert();
    };
  }
  ensures \old(_owner) == msg.sender && _owner == address(0) && _pendingOwner == address(0);
  function renounceOwnership() public virtual onlyOwner {
    _transferOwnership(address(0));
  }
  ensures p == _pendingOwner && _pendingOwner == \old(_pendingOwner);
  function pendingOwner() public view virtual returns (address p) {
    return _pendingOwner;
  }
  ensures \old(_owner) == msg.sender && _owner == \old(_owner) && _pendingOwner == newOwner;
  function transferOwnership(address newOwner) public virtual onlyOwner {
    _pendingOwner = newOwner;
  }
  ensures \old(_pendingOwner) == msg.sender && _owner == msg.sender && _pendingOwner == address(0);
  function acceptOwnership() public virtual {
    address sender = msg.sender;
    if (pendingOwner() != sender) {
      revert();
    };
    _transferOwnership(sender);
  }
}

local instance : InContract := ⟨OZOwnable2Step⟩

open scoped Scoped

/-- `ensures initialOwner != address(0) && _owner == initialOwner && _pendingOwner == address(0)`. -/
theorem spec_constructor : ⊢ spec!{ constructor } := by
  sol_prove

/-- `ensures o == _owner && _owner == \old(_owner)`. -/
theorem spec_owner : ⊢ spec!{ owner } := by
  sol_prove

/-- `ensures \old(_owner) == msg.sender && _owner == address(0) && _pendingOwner == address(0)`. -/
theorem spec_renounceOwnership : ⊢ spec!{ renounceOwnership } := by
  sol_prove

/-- `ensures p == _pendingOwner && _pendingOwner == \old(_pendingOwner)`. -/
theorem spec_pendingOwner : ⊢ spec!{ pendingOwner } := by
  sol_prove

/-- `ensures \old(_owner) == msg.sender && _owner == \old(_owner) && _pendingOwner == newOwner`. -/
theorem spec_transferOwnership : ⊢ spec!{ transferOwnership } := by
  sol_prove

/-- `ensures \old(_pendingOwner) == msg.sender && _owner == msg.sender && _pendingOwner == address(0)`. -/
theorem spec_acceptOwnership : ⊢ spec!{ acceptOwnership } := by
  sol_prove

end Solidity.Examples.Benchmark.SolkeyOz.OZOwnable2Step
