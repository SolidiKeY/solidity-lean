import Solidity.Calculus.Closers
import Solidity.Tools.Counterexample

/-!
# solkey open problems: `SolcPayments`

Source: <https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/semantics/open/SolcPayments.sol>.
Changes: `receive() external payable { ++fy; }` is left out (`contract!` has no `receive`);
`@custom:key skip` is `skip;`.  A function solkey tags `@custom:key box` or specifies has the obligation `spec!{f}`; an untagged
one solkey's diamond, `msg.value == 0 → wt(storage) → ⟨ f(); ⟩ true`.  A payable function's `msg.value` is below the ether supply.
`⊢` reads a call without callbacks: a call to another address keeps the caller's storage, and a
`try` on `address(this)` runs the callee.
-/

namespace Solidity.Examples.SolkeyOpen.SolcPayments

def SolcPayments : Contract := contract!{
  uint x;
  uint y;
  uint fy;
  int ix;
  bool lock;
  address payable recipient;
  skip;
  function gOne(bool b) external pure returns (uint) { require(b); return 13; }
  skip;
  function uf(bool b, uint p, uint q) external pure returns (uint) { require(b); return p - q; }
  skip;
  function setIx() external { ix = 42; }
  skip;
  function getIx() external view returns (int) { return ix; }
  skip;
  function id(int v) external pure returns (int) { return v; }
  skip;
  function noop() external pure { }
  function msgSenderRange() public view { assert(msg.sender >= address(0)); }
  function msgValueArith() public payable {
    uint lhs = (5 + msg.value + msg.value) - (4 + msg.value);
    assert(lhs > 0);
  }
  function msgValueRange() public payable { assert(msg.value >= 0); }
  function lockedNoValue() internal view { bool l = lock; require(l == false); assert(msg.value == 0); }
  function msgValueNonPayable() public { lock = false; lockedNoValue(); lock = true; }
  function requireNoValue() internal view { require(msg.value == 0); }
  function nonPayableRequireHolds() public view { requireNoValue(); }
  function tryCatchExactReturn(address p, uint q) public pure {
    require(p == 0x00000000000000000000000000000000DeaDBeef && q == 1);
    bool flag = q == 1;
    uint r = 0;
    try SolcPayments(payable(p)).gOne(flag) returns (uint a) { r = a; } catch { r = 9; }
    assert(r == 13);
  }
  function trySuccessRunsCallee(address p) public {
    require(p == 0x00000000000000000000000000000000DeaDBeef);
    ix = 0;
    try SolcPayments(payable(p)).setIx() { int r = ix; assert(r == 42); }
    catch (bytes memory) { int r = ix; assert(r == 0); }
  }
  function trySuccessKeepsStorageUnsound(address p) public {
    require(p == 0x00000000000000000000000000000000DeaDBeef);
    ix = 0;
    try SolcPayments(payable(p)).setIx() { int r = ix; assert(r == 0); } catch (bytes memory) { }
  }
  function tryMultipleCatchClausesSuccess(address p) public {
    require(p == 0x00000000000000000000000000000000DeaDBeef);
    ix = 1;
    bool success = false;
    try SolcPayments(payable(p)).setIx() { success = true; int r = ix; assert(r == 42); }
    catch Error(string memory) { } catch (bytes memory) { }
    int s = ix;
    assert((success && s == 42) || (!success && s == 1));
  }
  function tryNestedGetter(address p) public view {
    require(p == 0x00000000000000000000000000000000DeaDBeef);
    int y2 = 42;
    bool success = false;
    try SolcPayments(payable(p)).getIx() returns (int v) {
      y2 = v;
      try SolcPayments(payable(p)).getIx() returns (int w) { success = true; y2 = w; } catch { }
    } catch { }
    int cur = ix;
    assert(!success || y2 == cur);
  }
  function postinc() internal returns (int) { ix += 1; return ix; }
  function tryArgumentSideEffect(address p) public {
    require(p == 0x00000000000000000000000000000000DeaDBeef);
    ix = 0;
    try SolcPayments(payable(p)).id(postinc()) { int r = ix; assert(r == 1); } catch (bytes memory) { }
  }
  function callWithoutCodeReverts() public { SolcPayments(payable(address(0))).noop(); assert(false); }
  function callRunsReceive(address p) public {
    require(p == 0x00000000000000000000000000000000DeaDBeef);
    fy = 0;
    (bool ok, ) = payable(p).call{value: 0}("");
    uint r = fy;
    assert(ok && r == 1);
  }
  function callKeepsStorageUnsound(address p) public {
    require(p == 0x00000000000000000000000000000000DeaDBeef);
    fy = 0;
    (bool ok, ) = payable(p).call{value: 0}("");
    uint r = fy;
    assert(r == 0);
  }
  function transferUnfundedReverts() public { recipient.transfer(1); assert(false); }
}

local instance : InContract := ⟨SolcPayments⟩
open scoped Scoped

/-- `msg.sender >= address(0)`.  Proved. -/
theorem total_msgSenderRange : ⊢ dl!{ msg.value == 0 → wt(storage) → ⟨ msgSenderRange(); ⟩ true } := by sol_prove
/-- `(5 + v + v) - (4 + v) > 0` for `v = msg.value`.  Proved (the leaves by `sol_close`). -/
theorem total_msgValueArith : ⊢ dl!{ msg.value < 340282366920938463463374607431768211456 → wt(storage) → ⟨ msgValueArith(); ⟩ true } := by
  sol_prove
  all_goals (sol_leaf; sol_close)
/-- `msg.value >= 0`.  Proved. -/
theorem total_msgValueRange : ⊢ dl!{ msg.value < 340282366920938463463374607431768211456 → wt(storage) → ⟨ msgValueRange(); ⟩ true } := by sol_prove
/-- `msg.value == 0` in a function that is not `payable`.  Proved. -/
theorem total_msgValueNonPayable : ⊢ dl!{ msg.value == 0 → wt(storage) → ⟨ msgValueNonPayable(); ⟩ true } := by sol_prove
/-- `require(msg.value == 0)` does not revert.  Proved. -/
theorem total_nonPayableRequireHolds : ⊢ dl!{ msg.value == 0 → wt(storage) → ⟨ nonPayableRequireHolds(); ⟩ true } := by sol_prove
/-- Unknown: `sol_prove` leaves it, `sol_leaf; sol_close` does not close it and `sol_refute` finds no witness.  The success leaf is
`∀ uint se5, p != this, se4 := se5 ⟹ se4 == 13` (the foreign callee's value is unconstrained) and the
`catch` leaf `se4 := 9 ⟹ se4 == 13`: false leaves, a refutation whose witness (`p == 0xDeaDBeef`) the
search does not draw. -/
def tryCatchExactReturn_obligation : Fml SolcPayments [] := spec!{ tryCatchExactReturn }
/-- Unknown: `sol_prove` leaves it, `sol_leaf; sol_close` does not close it and `sol_refute` finds no witness.  Leaf: `p != this,
storage := save(storage, ix, 0), se2 := find(storage, ix) ⟹ se2 == 42` (false: a foreign callee
keeps the caller's storage). -/
def trySuccessRunsCallee_obligation : Fml SolcPayments [] := spec!{ trySuccessRunsCallee }
/-- Unknown: `sol_prove` leaves it, `sol_leaf; sol_close` does not close it and `sol_refute` finds no witness.  Leaf: `p == this,
storage := save(storage, ix, 42), se2 := find(storage, ix) ⟹ se2 == 0`: false where the contract is
deployed at `p`, the unsoundness solkey notes ("closes in KeY but fails on the EVM"); the model runs
the callee there. -/
def trySuccessKeepsStorageUnsound_obligation : Fml SolcPayments [] := spec!{ trySuccessKeepsStorageUnsound }
/-- Unknown: `sol_prove` leaves it, `sol_leaf; sol_close` does not close it and `sol_refute` finds no witness.  Leaf: `p != this,
storage := save(storage, ix, 1), se3 := find(storage, ix) ⟹ se3 == 42` (false, as above). -/
def tryMultipleCatchClausesSuccess_obligation : Fml SolcPayments [] := spec!{ tryMultipleCatchClausesSuccess }
/-- Unknown: `sol_prove` leaves it, `sol_leaf; sol_close` does not close it and `sol_refute` finds no witness.  Leaf: `∀ int se4, ∀ int se5,
p != this, se2 := se5, se6 := find(storage, ix) ⟹ se2 == se6`: a foreign getter's value is not linked
to `ix`. -/
def tryNestedGetter_obligation : Fml SolcPayments [] := spec!{ tryNestedGetter }
/-- The argument `postinc()` runs once, before the call: `ix == 1` on success.  Proved. -/
theorem spec_tryArgumentSideEffect : ⊢ spec!{ tryArgumentSideEffect } := by sol_prove
-- Unknown: an external call outside `try` is refused by the front end (solkey: "has no rule").
/-- error: Solidity elaboration failed: SolcPayments is not a function declared before this one -/
#guard_msgs in #check spec!{ callWithoutCodeReverts }
/-- Unknown: `sol_prove` leaves it, `sol_leaf; sol_close` does not close it and `sol_refute` finds no witness.  Leaves:
`storage := save(storage, fy, 0), { pay(p,0) ‖ ok := true }, se3 := find(storage, fy) ⟹ se3 == 1` and
the failed send's `ok == false ⟹ false`: the call keeps the storage and may fail, and the contract
here has no `receive` to run. -/
def callRunsReceive_obligation : Fml SolcPayments [] := spec!{ callRunsReceive }
/-- Proved, in the reading without callbacks and of a contract without `receive`: the call keeps the
caller's storage, so `fy == 0`.  It does not decide solkey's case ("closes in KeY but fails on the
EVM", where the call to the contract itself runs `receive`). -/
theorem spec_callKeepsStorageUnsound : ⊢ spec!{ callKeepsStorageUnsound } := by sol_prove
/-- Refuted: in a state where the transfer returns, `assert(false)` fails (solkey: the contract's
own balance is not tracked, so the transfer is not known to revert). -/
example : ¬ (⊢ spec!{ transferUnfundedReverts }) := by sol_refute

end Solidity.Examples.SolkeyOpen.SolcPayments
