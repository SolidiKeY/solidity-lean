import Solidity.Tools.Upstream
import Solidity.Syntax.Inlined

/-! Pipeline controls for modifier slot lifetime. These are kernel-checked
run equalities, separate from the upstream runner's runtime observations. -/
namespace Solidity.Tests.ModifierFrames
open Solidity Semantics

private def Legacy : Contract := contract!{
  uint total;
  enum E { A, B }
  uint[] data;
  uint[] other;
  modifier repeatCount(uint count) { for (uint i = 0; i < count; ++i) { _; } }
  modifier maybeTwice(bool twice) { if (twice) { _; } _; }
  modifier twice() { _; _; }
  modifier afterBody() { _; total += 10; }
  modifier skipBody(bool skip) { if (!skip) { _; } }
  modifier observe(uint a) { total = total * 10 + a; _; }
  modifier input(uint a) { _; }
  modifier stop(uint a) { if (a == 0) { _; } }
  function assignedReturn() input(++x) input(++y) returns (uint x, uint y) {}
  function assignedSkipped() stop(++x) returns (uint x) {}
  function loop() repeatCount(10) returns (uint r) { r += 1; }
  function multi(bool b) maybeTwice(b) returns (uint r) { r += 1; }
  function parameter(uint a) twice returns (uint r) { r = a++; }
  function nested() twice twice returns (uint r) { r += 1; }
  function skips() twice skipBody(true) returns (uint r) { r += 1; }
  function early() afterBody twice returns (uint r) { total++; r++; return r; }
  function argument(uint a) twice observe(a++) returns (uint r) { r = a; }
  function memoryAlias(uint[] memory a) twice returns (uint r) { a[0]++; r = a[0]; a = new uint[](1); }
  function narrow(uint8 a) twice returns (uint8 r) { r = a++; }
  function pair() twice returns (uint a, bool b) { a++; b = !b; }
  function packed(E e) twice returns (uint r) { r = abi.encodePacked(e).length; }
  function packedArray(E[] memory e) twice returns (uint r) { r = abi.encodePacked(e).length; }
  function stringLength(string memory s) twice returns (uint r) { r = bytes(s).length; }
  function inc(uint a) pure returns (uint r) { r = a + 1; }
  function invoke(function (uint) pure returns (uint) h) twice returns (uint r) { r = h(7); }
  function functionSlot() returns (uint r) { r = invoke(inc); }
  function storageWork(uint[] storage a) twice returns (uint r) { a[0]++; r = a[0]; a = other; }
  function storageAlias() returns (uint r) { data.push(); other.push(); r = storageWork(data); }
  function memRet() twice returns (uint[] memory r) { r = new uint[](1); r[0] = 7; }
  function memoryReturn() returns (uint r) { uint[] memory a = memRet(); r = a[0]; }

}
private def IR : Contract := { Legacy with evalOrder := .viaIR }

private def check (C : Contract) (code : List RawStmt) (want : List Int) : IO Unit := do
  let .ok ⟨_, P⟩ := elabProgS C code | throw (IO.userError "lowering failed")
  let .ok o := Prog.runF 1000 P (State.init C) | throw (IO.userError "execution did not succeed")
  let got := (Solidity.Tools.localVals (P.outNames []) o.st.env).filterMap fun (name, v) =>
    if !["r", "t", "a", "b"].contains (toString name) then none else
    match v with | .uint n => some n.1 | .bool b => some (if b then 1 else 0) | _ => none
  unless got == want do throw (IO.userError s!"expected {want}, got {got}")

#eval check IR (sol_raw!{ uint r = multi(false); }) [1]
#eval check Legacy (sol_raw!{ uint r = multi(false); }) [1]
#eval check IR (sol_raw!{ uint r = parameter(0); }) [0]
#eval check Legacy (sol_raw!{ uint r = parameter(0); }) [1]
#eval check IR (sol_raw!{ uint r = nested(); }) [1]
#eval check Legacy (sol_raw!{ uint r = nested(); }) [4]
#eval check IR (sol_raw!{ uint r = skips(); }) [0]
#eval check Legacy (sol_raw!{ uint r = skips(); }) [0]
#eval check IR (sol_raw!{ uint r = early(); uint t = total; }) [12,1]
#eval check Legacy (sol_raw!{ uint r = early(); uint t = total; }) [12,2]
#eval check IR (sol_raw!{ uint r = argument(1); uint t = total; }) [11,2]
#eval check Legacy (sol_raw!{ uint r = argument(1); uint t = total; }) [12,3]
#eval check IR (sol_raw!{ uint[] memory a = new uint[](1); uint r = memoryAlias(a); uint t = a[0]; }) [2,2]
#eval check Legacy (sol_raw!{ uint[] memory a = new uint[](1); uint r = memoryAlias(a); uint t = a[0]; }) [1,1]
#eval check IR (sol_raw!{ uint8 r = narrow(254); }) [254]
-- Legacy's second increment overflows. It must not become a successful result.
#eval (do
  let .ok ⟨_, P⟩ := elabProgS Legacy (sol_raw!{ uint8 r = narrow(254); })
    | throw (IO.userError "lowering failed")
  unless (Prog.runF 1000 P (State.init Legacy)).halt? == some .revert do
    throw (IO.userError "expected overflow revert") : IO Unit)
#eval check IR (sol_raw!{ (uint a, bool b) = pair(); }) [1,1]
#eval check Legacy (sol_raw!{ (uint a, bool b) = pair(); }) [0,2]


#eval check IR (sol_raw!{ uint r = packed(E.B); }) [1]
#eval check Legacy (sol_raw!{ uint r = packed(E.B); }) [1]
#eval check IR (sol_raw!{ E[] memory e = new E[](1); uint r = packedArray(e); }) [32]
#eval check IR (sol_raw!{ uint r = stringLength("abc"); }) [3]
#eval check IR (sol_raw!{ uint r = functionSlot(); }) [8]
#eval check IR (sol_raw!{ uint r = storageAlias(); }) [2]
#eval check Legacy (sol_raw!{ uint r = storageAlias(); }) [1]
#eval check IR (sol_raw!{ uint r = memoryReturn(); }) [7]
#eval check Legacy (sol_raw!{ uint r = memoryReturn(); }) [7]

#eval check IR (sol_raw!{ (uint a, uint b) = assignedReturn(); }) [1,1]
#eval check Legacy (sol_raw!{ (uint a, uint b) = assignedReturn(); }) [1,1]
#eval check IR (sol_raw!{ uint r = assignedSkipped(); }) [0]
#eval check Legacy (sol_raw!{ uint r = assignedSkipped(); }) [1]

-- Operand order and modifier slot lifetime are independent controls.
#eval check { Legacy with evalOrder := { binaryLeftToRight := true } }
  (sol_raw!{ uint r = multi(true); }) [2]
#eval check { Legacy with evalOrder := { modifierFrames := true } }
  (sol_raw!{ uint r = multi(true); }) [1]

private def StorageLegacy : Contract := contract!{
  uint[] a;
  modifier once() { _; }
  function get() once returns (uint[] storage r) { r = a; }
}
private def StorageIR : Contract := { StorageLegacy with evalOrder := .viaIR }
/-- info: viaIR modifier frames with storage returns are not supported -/
#guard_msgs in
#eval match elabProgS StorageIR (sol_raw!{ uint[] storage r = get(); }) with
  | .error msg => IO.println msg
  | .ok _ => throw (IO.userError "storage-return exclusion disappeared")

end Solidity.Tests.ModifierFrames
