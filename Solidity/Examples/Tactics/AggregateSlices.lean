import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.Close

/-! Calldata slice bounds and indices retain their evaluation positions. -/
namespace Solidity.Examples.Tactics.AggregateSlices
open Semantics
open scoped Scoped

def Views : Contract := contract!{
  function effects(uint[] calldata xs) returns (uint r) {
    uint k = 0; uint[] calldata t = xs[k++:k++ + 1];
    r = t[(k++ - 2)]; assert(k == 3);
  }
  function earlierOperand(uint[] calldata xs) returns (uint r) {
    uint[] calldata t = xs[0:2]; uint k = 0;
    r = k++ + t[k]; assert(k == 1);
  }
  function inlineEarlier(uint[] calldata xs) returns (uint r) {
    uint k = 0; r = k++ + xs[k:2][0];
  }
  function rebound(uint[] calldata xs, uint[] calldata ys) returns (uint r) {
    uint[] calldata t = xs[0:1]; xs = ys; r = t[0];
  }
  function skipped(uint[] calldata xs) returns (bool r) {
    uint[] calldata t = xs[0:0]; r = false && t[0] == 1;
  }
  function huge(uint[] calldata xs) public returns (uint r) {
    uint[] calldata t = xs[1:2]; r = t[type(uint).max];
  }
  function decodeTuple(bytes calldata data) returns (uint r) {
    (uint x, uint y) = abi.decode(data[4:], (uint, uint)); r = x + y;
  }
  function all(uint[] calldata xs) returns (uint r) { uint[] calldata t = xs[:]; r = t[0]; }
  function shadow(uint[] calldata xs) returns (uint r) {
    uint[] calldata t = xs[0:1];
    { uint[] memory t = new uint[](1); t[0] = 17; r = t[0]; }
  }
  function shadowTuple(uint[] calldata xs) returns (uint r) {
    uint[] calldata t = xs[0:1]; { (uint t, uint z) = (3, 4); r = t + z; }
  }
  function hugeLocal() public returns (uint r) {
    uint[] memory a = new uint[](3); uint[] calldata t = a[1:2]; r = t[type(uint).max];
  }
  function nested(uint[] calldata xs) returns (uint r) {
    uint[] calldata t = xs[1:3]; r = t[1:][0];
  }
}
local instance : InContract := ⟨Views⟩

private def successful := sol{
  uint[] memory a = new uint[](3); a[0] = 5; a[1] = 7; a[2] = 9;
  uint[] memory b = new uint[](1); b[0] = 11;
  uint x = effects(a); assert(x == 5);
  uint y = earlierOperand(a); assert(y == 5);
  uint z = inlineEarlier(a); assert(z == 5);
  uint w = rebound(a, b); assert(w == 5);
  bool s = skipped(a); assert(!s);
  uint n = nested(a); assert(n == 9);
  uint sh = shadow(a); assert(sh == 17);
  uint st = shadowTuple(a); assert(st == 7);
  uint al = all(a); assert(al == 5);
  bytes memory data = abi.encodeWithSelector(bytes4(0x12345678), 7, 9);
  uint dt = decodeTuple(data); assert(dt == 16);
}
/-- Successful slice reads, including bound/index effects and rebinding. -/
theorem successful_run : (Prog.run (State.init Views) successful).isOk = true := by decide +kernel

private def hugeIndex := sol{
  uint[] memory a = new uint[](3); uint x = huge(a);
}
/-- A huge relative index fails without evaluating offset plus index. -/
theorem huge_run : (Prog.run (State.init Views) hugeIndex).isOk = false := by decide +kernel

private def caughtHuge := sol{
  uint[] memory a = new uint[](3); uint code = 0;
  try this.hugeLocal() returns (uint r) { code = 99; }
    catch Panic(uint c) { code = c; } catch { code = 98; }
  assert(code == 50);
}
/-- The invalid relative index retains the catchable bounds panic 0x32. -/
theorem caughtHuge_run : (Prog.run
    { State.init Views with tx := { selfAddress := ⟨7, rfl⟩ } } caughtHuge).isOk = true := by decide +kernel

private def viaIRViews : Contract := { Views with evalOrder := .viaIR }
private def viaIRRun := sol[viaIRViews]{
  uint[] memory a = new uint[](2); a[0] = 5; a[1] = 7;
  uint y = earlierOperand(a); assert(y == 7);
  uint z = inlineEarlier(a); assert(z == 7);
}
/-- The same effects follow the contract's selected binary evaluation order. -/
theorem viaIR_run : (Prog.run (State.init viaIRViews) viaIRRun).isOk = true := by decide +kernel

end Solidity.Examples.Tactics.AggregateSlices
