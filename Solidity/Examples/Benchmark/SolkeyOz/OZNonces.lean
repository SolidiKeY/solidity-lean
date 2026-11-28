import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
/-!
# Benchmark: `OZNonces`
Source: <https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/contracts/real-world/OZNonces.sol>
(solkey's port of OpenZeppelin v5.0.0 `utils/Nonces.sol`, made concrete with
the public wrappers `useNonce` and `useCheckedNonce`).
Changes: the mapping's key name `account` is dropped (`contract!{ … }` reads
no key name); `return _nonces[owner]++;` inside `unchecked` is spelled out as
what it does, `uint256 n0 = _nonces[owner]; _nonces[owner] = n0 + 1; return
n0;` (still unchecked), since `contract!{ … }` refuses `++` inside an
expression in an `unchecked` block; otherwise only the spelling of `contract!{ … }` (a branch is a
block ending in `;`) and solkey's `@custom:key` clauses written above the functions they
annotate.
Verdicts: `nonces`, `useNonce`: proved (`useNonce`'s unchecked `+ 1` leaves a
wrapping `+%` in its leaf, closed by `sol_leaf`, `sol_close`, found by
`sol_prove?`).  `useCheckedNonce`: unknown.  Its clause is true (the
`requires` keeps the unchecked `+ 1` below `2^256 - 1`, and a run that does
not revert has `nonce == current`), but no leaf tactic `sol_auto` tries closes
its leaf: the wrapping `se8 +% 1` together with the Boolean binding
`{ se10 := se4 != se5 }, se10 = false` that carries `nonce == current`.  The
obligation is kept below as a `def`.
-/
namespace Solidity.Examples.Benchmark.SolkeyOz.OZNonces
/-- `OZNonces.sol` with solkey's clauses. -/
def OZNonces : Contract := contract!{
  invariant \forall address a; _nonces[a] >= 0;
  mapping(address => uint256) private _nonces;
  ensures n == _nonces[owner] && _nonces[owner] == \old(_nonces[owner]);
  function nonces(address owner) public view virtual returns (uint256 n) { return _nonces[owner]; }
  function _useNonce(address owner) internal virtual returns (uint256) {
    unchecked { uint256 n0 = _nonces[owner]; _nonces[owner] = n0 + 1; return n0; }
  }
  function _useCheckedNonce(address owner, uint256 nonce) internal virtual {
    uint256 current = _useNonce(owner);
    if (nonce != current) { revert(); };
  }
  requires _nonces[owner] < 115792089237316195423570985008687907853269984665640564039457584007913129639935;
  ensures n == \old(_nonces[owner]) && _nonces[owner] == \old(_nonces[owner]) + 1;
  ensures \forall address a; a != owner -> _nonces[a] == \old(_nonces[a]);
  function useNonce(address owner) public returns (uint256 n) { return _useNonce(owner); }
  requires _nonces[owner] < 115792089237316195423570985008687907853269984665640564039457584007913129639935;
  ensures nonce == \old(_nonces[owner]) && _nonces[owner] == \old(_nonces[owner]) + 1;
  ensures \forall address a; a != owner -> _nonces[a] == \old(_nonces[a]);
  function useCheckedNonce(address owner, uint256 nonce) public { _useCheckedNonce(owner, nonce); }
}
local instance : InContract := ⟨OZNonces⟩
open scoped Scoped
/-- `ensures n == _nonces[owner] && _nonces[owner] == \old(_nonces[owner])`. -/
theorem spec_nonces : ⊢ spec!{ nonces } := by sol_prove
/-- `requires _nonces[owner] < 2^256 - 1`, `ensures n == \old(_nonces[owner]) &&
_nonces[owner] == \old(_nonces[owner]) + 1` and the frame. -/
theorem spec_useNonce : ⊢ spec!{ useNonce } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close
/-- UNKNOWN: `ensures nonce == \old(_nonces[owner]) && _nonces[owner] ==
\old(_nonces[owner]) + 1` and the frame; the leaf keeps `se8 +% 1` under
`_nonces[owner] < 2^256 - 1` (no closer for the wrapping add with the Boolean `!=` binding). -/
def useCheckedNonce_obligation := spec!{ useCheckedNonce }
end Solidity.Examples.Benchmark.SolkeyOz.OZNonces
