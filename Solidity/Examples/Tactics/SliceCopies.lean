import Solidity.Calculus.Surface
import Solidity.Calculus.Close
import Solidity.Calculus.Closers
import Solidity.Semantics.RunFuel

/-! Flat slice values allocate independent memory, then use ordinary frames,
ABI/hash builtins and memory-to-storage copying. No new core representation. -/
namespace Solidity.Examples.Tactics.SliceCopies
open Semantics
open scoped Scoped

/-- A finite execution certificate proves the same observation of the
unbounded typed run, provided divergence cannot satisfy the observation. -/
theorem observe_run_of_fuel {C : Contract} {Γ Δ : Ctx}
    (P : Prog C Γ Δ) (σ : State C Γ) (n : Nat)
    (observe : TRes (Out C σ.H Δ) → Bool)
    (hd : observe (.error .diverge) = false)
    (h : observe (Prog.runF n P σ) = true) : observe (Prog.run σ P) = true := by
  have hn : Prog.runF n P σ ≠ .error .diverge := by
    intro he
    rw [he, hd] at h
    cases h
  change observe (P.runR σ) = true
  rw [← (Prog.runF_approx n P σ).eq hn]
  exact h

def Copies : Contract := contract!{
  uint[] stored; uint[][] rows; struct Pair { uint value; }
  enum Kind { One, Two }
  function read(uint[] calldata v) returns (uint r) { r = v[0] + v.length; }
  function mutate(uint[] memory v) returns (uint r) { v[0] = 99; r = v.length; }
  function echo(uint[] calldata xs) returns (uint[] memory r) { r = xs[1:3]; }
  function copies(uint[] calldata xs) {
    uint[] calldata v = xs[1:4];
    uint[] memory a = v[0:2]; uint[] memory b = v;
    a[0] = 21; b[1] = 31;
    assert(xs[1] == 5 && v[1] == 7 && a[1] == 7 && b[0] == 5);
    uint k = 0; uint[] memory e = xs[k++:k++ + 1];
    assert(k == 2 && e.length == 2 && e[0] == 3 && e[1] == 5);
    uint[] memory empty = xs[2:2]; assert(empty.length == 0);
  }
  function passing(uint[] calldata xs) {
    uint[] calldata v = xs[1:3];
    uint a = read(v); uint b = read(xs[1:3]); assert(a == 7 && b == 7);
    uint c = mutate(v); uint d = mutate(xs[1:3]); assert(c == 2 && d == 2);
    uint[] memory returned = echo(xs); returned[0] = 43;
    assert(v[0] == 5 && xs[1] == 5 && returned[1] == 7);
  }
  function storageCopy(uint[] calldata xs) {
    uint[] calldata v = xs[1:3]; stored = v; rows.push(xs[1:3]);
    stored[0] = 81; rows[0][1] = 82;
    assert(v[0] == 5 && v[1] == 7 && stored.length == 2 && rows[0][0] == 5);
  }
  function hashes(bytes calldata data) {
    bytes calldata v = data[1:4]; bytes memory m = v; m[0] = 0x78;
    bytes32 h = keccak256(v); bytes32 expected = keccak256("abc"); assert(h == expected);
    bytes32 s = sha256(data[1:4]); bytes32 se = sha256("abc"); assert(s == se);
    bytes20 r = ripemd160(v); bytes20 re = ripemd160("abc"); assert(r == re);
    assert(v[0] == 0x61 && m[0] == 0x78);
  }
  function narrow(uint8[] calldata xs, bool[] calldata flags, bytes2[] calldata pairs) {
    uint8[] memory n = xs[1:]; bool[] memory b = flags[1:]; bytes2[] memory p = pairs[1:];
    n[0] = 1; b[0] = false; p[0] = 0x5678;
    assert(xs[1] == 255 && flags[1] && pairs[1] == 0x1234);
  }
  function aliases(Pair calldata p, uint[2] calldata xs) {
    Pair calldata q = p; Pair calldata r = q;
    uint[2] calldata ys = xs; uint[2] calldata zs = ys;
    assert(q.value == p.value && r.value == p.value && ys[1] == xs[1] && zs[1] == xs[1]);
  }
  function bounds(uint[] calldata xs) returns (uint[] memory r) { r = xs[2:1]; }
  function falsePost(uint[] calldata xs) {
    uint[] memory m = xs[1:2]; m[0] = 99; assert(xs[1] == 99);
  }
  function lazy(uint[] calldata xs) returns (bool r) {
    r = false && mutate(xs[9:10]) == 0;
  }
}
/- A memory-returning identity must not hide calldata aliases, including
through another call or an assignment inside a fresh-returning call. -/
private def AliasReturn : Contract := contract!{
  function identity(uint[] memory a) returns (uint[] memory r) { r = a; }
  function forward(uint[] memory a) returns (uint[] memory r) { r = identity(a); }
  function fresh(uint[] calldata a) returns (uint[] memory r) { r = a[0:1]; }
}
#guard (calldataCheck AliasReturn.funs 8 ["xs"] [] (sol_raw!{
  uint[] memory y = identity(xs); y[0] = 1;
})).isOk == false
#guard (calldataCheck AliasReturn.funs 8 ["xs"] [] (sol_raw!{
  uint[] memory y = forward(xs); y[0] = 1;
})).isOk == false
#guard (calldataCheck AliasReturn.funs 8 ["xs"] [] [
  .declMemory (.array (.named "uint")) "alias" none,
  .declMemory (.array (.named "uint")) "y" (some (.call "fresh" [
    .assign (.name "alias") (.name "xs")])),
  .assign (.index (.name "alias") (.num 0)) (.num 1)]).isOk == false

-- Memory reassignment cannot manufacture a calldata origin, even nested.
#guard ((sol_raw!{
  xs = m; uint[] calldata v = xs;
}) |> fun body => (RawStmt.sliceViews body ["xs"]).any fun statement =>
  statement.exprs.any fun e => e.any fun
    | .call "#sliceRefused" _ => true | _ => false)
#guard ((RawStmt.sliceViews [
  .eval [.assign (.name "xs") (.name "m")],
  .declMemory (.array (.named "uint")) "v" (some (.call "#sliceBind" [.name "xs"]))] ["xs"]).any fun statement =>
  statement.exprs.any fun e => e.any fun
    | .call "#sliceRefused" _ => true | _ => false)

#guard ((RawStmt.sliceViews [
  .assign (.index (.assign (.name "xs") (.name "ys")) (.num 0)) (.num 1)]
    ["xs", "ys"]).any fun statement =>
  statement.exprs.any fun e => e.any fun
    | .call "#sliceRefused" _ => true | _ => false)

#guard ((RawStmt.sliceViews [
  .assign (.index (.ternary (.name "choose") (.name "xs") (.name "ys")) (.num 0)) (.num 1)]
    ["xs", "ys"]).any fun statement =>
  statement.exprs.any fun e => e.any fun
    | .call "#sliceRefused" _ => true | _ => false)


local instance : InContract := ⟨Copies⟩

private def copiesInput := sol{
  uint[] memory a = new uint[](4); a[0] = 3; a[1] = 5; a[2] = 7; a[3] = 9;
  copies(a);
}
/-- Solidity `memory a = v[0:2]; memory b = v;` has the expected successful execution. -/
theorem copies_run : (Prog.run (State.init Copies) copiesInput).isOk = true := by
  apply observe_run_of_fuel copiesInput (State.init Copies) 8 (fun r => r.isOk) rfl
  decide +kernel

private def passingInput := sol{
  uint[] memory a = new uint[](4); a[0] = 3; a[1] = 5; a[2] = 7; a[3] = 9;
  passing(a);
}
/-- Solidity `read(v); mutate(v); echo(xs);` has the expected successful execution. -/
theorem passing_run : (Prog.run (State.init Copies) passingInput).isOk = true := by
  apply observe_run_of_fuel passingInput (State.init Copies) 8 (fun r => r.isOk) rfl
  decide +kernel

private def storageInput := sol{
  uint[] memory a = new uint[](4); a[0] = 3; a[1] = 5; a[2] = 7; a[3] = 9;
  storageCopy(a);
}
/-- Solidity `stored = v; rows.push(xs[1:3]);` has the expected successful execution. -/
theorem storage_run : (Prog.run (State.init Copies) storageInput).isOk = true := by
  apply observe_run_of_fuel storageInput (State.init Copies) 8 (fun r => r.isOk) rfl
  decide +kernel

private def lazyInput := sol{
  uint[] memory a = new uint[](4); a[0] = 3; a[1] = 5; a[2] = 7; a[3] = 9;
  bool skipped = lazy(a); assert(!skipped);
}
/-- Solidity `false && mutate(xs[9:10]) == 0` has the expected successful execution. -/
theorem lazy_run : (Prog.run (State.init Copies) lazyInput).isOk = true := by
  apply observe_run_of_fuel lazyInput (State.init Copies) 8 (fun r => r.isOk) rfl
  decide +kernel


private def hashInput := sol{
  bytes memory b = hex"0061626300"; hashes(b);
}
/-- Solidity `keccak256(v)`, `sha256(data[1:4])`, `ripemd160(v)` hash only the view. -/
theorem hashes_run : (Prog.run (State.init Copies) hashInput).isOk = true := by
  apply observe_run_of_fuel hashInput (State.init Copies) 8 (fun r => r.isOk) rfl
  decide +kernel

private def narrowInput := sol{
  uint8[] memory a = new uint8[](2); a[1] = 255;
  bool[] memory b = new bool[](2); b[1] = true;
  bytes2[] memory c = new bytes2[](2); c[1] = 0x1234; narrow(a, b, c);
}
/-- Solidity `uint8[]`, `bool[]`, `bytes2[]` copies keep widths and identities. -/
theorem narrow_run : (Prog.run (State.init Copies) narrowInput).isOk = true := by
  apply observe_run_of_fuel narrowInput (State.init Copies) 8 (fun r => r.isOk) rfl
  decide +kernel

private def invalidRange := sol{
  uint[] memory a = new uint[](3); uint[] memory b = bounds(a);
}
/-- Solidity `xs[2:1]` fails before allocating its result. -/
theorem invalidRange_run : (match Prog.run (State.init Copies) invalidRange with
    | .error .revert => true | _ => false) = true := by
  apply observe_run_of_fuel invalidRange (State.init Copies) 8
    (fun r => match r with | .error .revert => true | _ => false) rfl
  decide +kernel

private def falseAlias := sol{
  uint[] memory a = new uint[](3); a[1] = 5; falsePost(a);
}
/-- Solidity `m[0] = 99` does not change calldata; asserting that it did fails. -/
theorem falseAlias_run : (match Prog.run (State.init Copies) falseAlias with
    | .error .panic => true | _ => false) = true := by
  apply observe_run_of_fuel falseAlias (State.init Copies) 8
    (fun r => match r with | .error .panic => true | _ => false) rfl
  decide +kernel

private def aliasInput := sol{
  Pair memory p = Pair(17); uint[2] memory a = [uint(1), 2]; aliases(p, a);
}
/-- Solidity struct and fixed-array calldata locals keep their ordinary alias path. -/
theorem aliases_run : (Prog.run (State.init Copies) aliasInput).isOk = true := by
  apply observe_run_of_fuel aliasInput (State.init Copies) 8 (fun r => r.isOk) rfl
  decide +kernel

-- An ordinary calldata declaration needs an actual calldata origin.
-- These standalone memory programs have no calldata parameters.
#guard (elabProgS Copies (sol_raw!{
  uint[] memory a = new uint[](2); uint[] calldata v = a; v[0] = 1;
})).isOk == false
#guard (elabProgS Copies (sol_raw!{
  Pair memory p = Pair(0); Pair calldata q = p; q.value = 1;
})).isOk == false

/-- A memory parameter cannot acquire calldata location by a local spelling. -/
def MemoryOrigin : Contract := contract!{
  function bad(uint[] memory a) {
    uint[] calldata v = a; v[0] = 99;
  }
}
#guard (elabProgS MemoryOrigin (sol_raw!{
  uint[] memory a = new uint[](2); bad(a);
})).isOk == false

/-- Ordinary aliases retain origin transitively, and their writes are refused.
An inner alias also cannot establish a name in the following outer scope. -/
def ReadonlyOrigins : Contract := contract!{
  struct Pair { uint value; }
  function arrayWrite(uint[] calldata xs) {
    uint[] calldata v = xs; uint[] calldata w = v; w[0] = 99;
  }
  function structWrite(Pair calldata p) {
    Pair calldata q = p; Pair calldata r = q; r.value = 99;
  }
  function fixedWrite(uint[2] calldata xs) {
    uint[2] calldata ys = xs; uint[2] calldata zs = ys; zs[0] = 99;
  }
  function scopeExit(uint[] calldata xs) {
    { uint[] calldata v = xs; }
    uint[] calldata w = v;
  }
  function unstable(uint[][] calldata xs, uint k) {
    uint[] calldata v = xs[k++];
  }
}
#guard ["arrayWrite", "structWrite", "fixedWrite", "scopeExit", "unstable"].all fun name =>
  (lookupBy name ReadonlyOrigins.funs).any fun declaration =>
    (sliceRefusal? declaration.body).isSome
#guard (elabProgS ReadonlyOrigins (sol_raw!{
  uint[] memory a = new uint[](2); arrayWrite(a);
})).isOk == false

-- Read-only targets and descriptor rebinding must fail admission.
#guard (elabProgS Copies (sol_raw!{
  uint[] memory a = new uint[](2); uint[] calldata v = a[:]; v[0] = 1;
})).isOk == false
#guard (elabProgS Copies (sol_raw!{
  uint[] memory a = new uint[](2); uint[] calldata v = a[:]; v = a;
})).isOk == false
-- Inline slices are read-only lvalues too, before hidden-base hoisting.
#guard (elabProgS Copies (sol_raw!{
  uint[] memory a = new uint[](2); a[:][0] = 1;
})).isOk == false
#guard (elabProgS Copies (sol_raw!{
  uint[] memory a = new uint[](2); a[:][0]++;
})).isOk == false
#guard (elabProgS Copies (sol_raw!{
  uint[] memory a = new uint[](2); delete a[:][0];
})).isOk == false
-- A slice read inside an otherwise writable target is still admitted.
#guard (elabProgS Copies (sol_raw!{
  uint[] memory a = new uint[](3); a[a[1:2].length] = 7;
})).isOk
-- Reference-element copies must not introduce shallow writable aliases.
#guard (elabProgS Copies (sol_raw!{
  uint[][] memory a = new uint[][](2); uint[][] memory b = a[:];
})).isOk == false
-- Nominal enum elements are refused rather than silently erased to uint.
#guard (elabProgS Copies (sol_raw!{
  Kind[] memory a = new Kind[](2); Kind[] memory b = a[:];
})).isOk == false
-- A narrow memory element type cannot silently become uint256.
#guard (elabProgS Copies (sol_raw!{
  uint8[] memory a = new uint8[](2); uint[] memory b = a[:];
})).isOk == false
-- Only explicit slice materialization is an RO-origin barrier.
#guard (calldataCheck [] 8 ["xs"] [] (sol_raw!{
  uint[] memory m = xs[:]; m[0] = 1;
})).isOk
#guard (calldataCheck [] 8 ["xs"] [] (sol_raw!{
  uint[] memory m = xs; m[0] = 1;
})).isOk == false

end Solidity.Examples.Tactics.SliceCopies
