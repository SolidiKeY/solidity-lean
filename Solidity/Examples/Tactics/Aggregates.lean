import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.Close

/-!
# Fixed memory literals and local reference tuples

These checks exercise the intrinsic interpreter independently of symbolic
execution, including negative assertions and reference identity.
-/

namespace Solidity.Examples.Tactics.Aggregates
open Semantics
open scoped Scoped

def Arrays : Contract := contract!{
  uint[] values;
  uint[4] tail;
  uint[1] cell;
  uint[][] rows;
  uint8[][] narrowRows;
  function getRows() internal returns (uint8[][] storage r) { return narrowRows; }
  function touchRows(uint[2] memory m) internal returns (uint[][] storage r) { m[0] = 9; return rows; }
  function change() internal returns (uint[1] storage r) {
    cell[0] = 9; return cell;
  }
  function changeMem(uint[1] memory c) internal returns (uint[1] memory r) {
    c[0] = 9; return c;
  }
}
local instance : InContract := ⟨Arrays⟩

private def numeric := sol{
  uint16[2] memory m = [1, 256];
  assert(m.length == 2); assert(m[0] == 1); assert(m[1] == 256);
  bool[2] memory b = [true, false]; assert(b[0]); assert(!b[1]);
  bytes2[2] memory bs = [bytes2(hex"0102"), bytes2(hex"0304")];
  assert(bs[1] == bytes2(hex"0304"));
}
example : (Prog.run (State.init Arrays) numeric).isOk = true := by decide +kernel

private def copies := sol{
  values.push(8); values.push(8); values.push(8);
  uint[2] memory m = [uint(1), 2];
  values = m; tail = m; rows.push(m); m[0] = 7;
  values.push();
  assert(values.length == 3); assert(values[0] == 1); assert(values[2] == 0);
  assert(tail[3] == 0); assert(rows[0][1] == 2);
}
example : (Prog.run (State.init Arrays) copies).isOk = true := by decide +kernel

private def storageElements := sol{
  cell[0] = 1;
  uint[1][2] memory a = [cell, change()];
  assert(a[0][0] == 1); assert(a[1][0] == 9);
}
example : (Prog.run (State.init Arrays) storageElements).isOk = true := by decide +kernel

private def memoryElements := sol{
  uint[1] memory c = [uint(1)];
  uint[1][2] memory a = [c, changeMem(c)];
  assert(a[0][0] == 9); assert(a[1][0] == 9);
}
example : (Prog.run (State.init Arrays) memoryElements).isOk = true := by decide +kernel

private def memoryTuple := sol{
  uint[1] memory a = [uint(1)]; uint[1] memory b = [uint(2)];
  (a, b) = (b, a);
  assert(a[0] == 2); assert(b[0] == 1);
}
example : (Prog.run (State.init Arrays) memoryTuple).isOk = true := by decide +kernel

private def wrong := sol{ uint[2] memory a = [uint(1), 2]; assert(a[1] == 3); }
example : (Prog.run (State.init Arrays) wrong).isOk = false := by decide +kernel

private def bounds := sol{ uint[1] memory a = [uint(1)]; uint k = 1; uint x = a[k]; }
example : (Prog.run (State.init Arrays) bounds).isOk = false := by decide +kernel

private def storageTuple := sol{
  tail[0] = 1; cell[0] = 2;
  uint[4] storage a = tail; uint[4] storage b = tail;
  uint[1] storage c = cell; uint[1] storage d = cell;
  (a, b, c, d) = (b, a, d, c);
  a[1] = 7; assert(b[1] == 7); c[0] = 8; assert(d[0] == 8);
}
example : (Prog.run (State.init Arrays) storageTuple).isOk = true := by decide +kernel

private def nested := sol{
  uint[2][2] memory a = [[uint(1), 2], [uint(3), 4]];
  assert(a[1][0] == 3);
}
example : (Prog.run (State.init Arrays) nested).isOk = true := by decide +kernel

/-- Reading a literal element is proved for every initial typed state. -/
theorem literal_valid : ⊨ᶠ dl!{ [uint16[2] memory m = [1, 256];] m[1] == 256 } := by
  sol_symex; sol_decide

/-- error: Solidity elaboration failed: mv1 has narrow positions ·[] 8 bits wide where ·[] 16 bits wide are expected: solc converts no reference type to one of another element type -/
#guard_msgs in
private def targetCannotTypeLiteral := sol{ uint16[2] memory m = [1, 2]; }

/-- error: Solidity elaboration failed: inline array elements uint8 and int8 have no common type -/
#guard_msgs in
private def mixedSigns := sol{ int8[2] memory m = [uint8(1), int8(2)]; }

/-- error: Solidity elaboration failed: an inline array literal is not an assignment or delete target -/
#guard_msgs in
private def literalLvalue := sol{ [uint(1), 2] = [uint(3), 4]; }

private def literalIndex := sol{
  uint[1] memory a = [uint(0)]; a[[uint(0)][0]] = 7;
  assert(a[0] == 7); delete a[[uint(0)][0]]; assert(a[0] == 0);
  [uint(1)][0] = 7; delete [uint(1)][0]; [uint(1)][0] += 7;
  uint x = [uint(1)][0]++; assert(x == 1);
}
example : (Prog.run (State.init Arrays) literalIndex).isOk = true := by decide +kernel

/-- info: false -/
#guard_msgs in
#eval (calldataCheck [] 8 ["xs"] [] (sol_raw!{
    (a, n) = (b, 0); (b, n) = (c, 0); (c, n) = (d, 0);
    (d, n) = (e, 0); (e, n) = (xs, 0); a[0] = 7;
  })).isOk

/-- info: false -/
#guard_msgs in
#eval (calldataCheck [] 8 ["xs"] [] (sol_raw!{
    (a, b) = ((m = xs), b); m[0] = 7;
  })).isOk

private def deferredCopies := sol{
  uint8[1] memory n = [uint8(3)]; getRows().push(n); getRows().push([uint8(4)]);
  uint[2] memory m = [uint(1), 2]; touchRows(m).push(m);
  assert(narrowRows[0][0] == 3); assert(narrowRows[1][0] == 4);
  assert(rows[0][0] == 9);
}
example : (Prog.run (State.init Arrays) deferredCopies).isOk = true := by decide +kernel

/-- error: Solidity elaboration failed: a storage copy would narrow an integer element -/
#guard_msgs in
private def narrowingPush := sol{ narrowRows.push([uint(256)]); }

/-- error: Solidity elaboration failed: a storage copy would narrow an integer element -/
#guard_msgs in
private def narrowingDeferredPush := sol{ getRows().push([uint(256)]); }

/-- info: false -/
#guard_msgs in
#eval (calldataCheck [] 8 ["xs"] [] (sol_raw!{
    uint[][1] memory a = [(m[0] = xs)]; m[0][0] = 7;
  })).isOk

end Solidity.Examples.Tactics.Aggregates
