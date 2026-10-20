import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Inspect

/-!
# `bytesN`, `bytes` and `string`

Neither is a type of the syntax (`docs/semantic-gaps.md`, "Bytes and
strings"): a `bytesN` is a `uint` of `8N` bits holding its bytes read
big-endian, the value solc's `uintN(b)` gives, so `bytes2 b = "ab"` holds
`0x6162`; what solc does differently from a `uint8N` (a conversion between
sizes, an index, `.length`, a literal, an implicit widening) the elaborator
rewrites before the statement (`bytesPure`, `Syntax/Elab.lean`).  A
postcondition reads a `bytesN` as that number.

* §1 — `bytesN`: literals, comparisons, bitwise operators, indexing,
  `.length`, conversions;
* §2 — `bytesN` in state variables, arrays, mapping keys and functions.
-/

namespace Solidity.Examples.Tactics.Bytes

local instance : InContract := ⟨StandardExample⟩

open scoped Scoped

/-! ## 1 · `bytesN` values -/

/-- A string literal is left-aligned: `"a"` at `bytes2` is `0x6100`; `hex"…"`
spells the bytes. -/
theorem literals : ⊨ dl!{ ⟨ bytes2 a = "a"; bytes2 b = "ab"; bytes2 c = hex"6162"; ⟩
    a == 24832 && b == 24930 && c == 24930 } := by
  sol_symex
  sol_close

/-- Comparison is lexicographic on the bytes: `"ab" < "b"` at `bytes2`. -/
theorem compare : ⊨ dl!{ ⟨ bytes2 a = "ab"; bytes2 b = "b"; bool lt = a < b; bool eq = a == "ab"; ⟩
    lt == true && eq == true } := by
  sol_symex
  sol_close

/-- `b[i]` is the byte `i` from the left, a `bytes1`; `.length` is `N`. -/
theorem index : ⊨ dl!{ ⟨ bytes2 b = "ab"; bytes1 x = b[0]; bytes1 y = b[1]; uint l = b.length; ⟩
    x == 97 && y == 98 && l == 2 } := by
  sol_symex
  sol_close

/-- At an index that is not a literal, the byte is read through a shift. -/
theorem indexVar : ⊨ dl!{ ⟨ bytes2 b = "ab"; uint i = 1; bytes1 y = b[i]; ⟩ y == 98 } := by
  sol_symex
  sol_decide

/-- An index out of range reverts, as an array's does. -/
theorem indexOutOfRange : ⊨ dl!{ [ bytes2 b = "ab"; uint i = 2; bytes1 x = b[i]; ] false } := by
  sol_symex
  sol_close

example : ¬ (⊨ dl!{ ⟨ bytes2 b = "ab"; uint i = 2; bytes1 x = b[i]; ⟩ true }) :=
  fun h => Modality.afterRunTR_diamond_fail (h (State.init _)) (by decide +kernel)

/-- A conversion to a shorter `bytesM` keeps the left bytes, to a longer one
pads on the right; an implicit widening pads too. -/
theorem conversions : ⊨ dl!{ ⟨ bytes2 b = "ab"; bytes1 s = bytes1(b); bytes4 w = bytes4(b);
    bytes4 v = b; ⟩ s == 97 && w == 1633812480 && v == 1633812480 } := by
  sol_symex
  sol_close

/-- `uintM` and `bytesN` of the same size convert as the number. -/
theorem toUint : ⊨ dl!{ ⟨ bytes2 b = "ab"; uint16 u = uint16(b); bytes2 c = bytes2(u); ⟩
    u == 24930 && c == b } := by
  sol_symex
  sol_close

/-- Bitwise operators act on the bytes: `~` at `bytes1`, `<<` cut to the
size, `&`. -/
theorem bitwise : ⊨ dl!{ ⟨ bytes1 a = hex"0f"; bytes1 n = ~a; bytes2 b = "ab"; bytes2 l = b << 8;
    bytes2 m = b & hex"ff00"; ⟩ n == 240 && l == 25088 && m == 24832 } := by
  sol_symex
  sol_close

/-! ## 2 · `bytesN` inside types and functions

A state variable, an element, a mapping's key and a parameter carry the
marker beside their width (`Contract.widths`: `id#bytes`). -/

/-- A contract with `bytesN` in its state and functions. -/
def Tags : Contract := contract!{
  bytes4 id;
  bytes32 root;
  bytes2[] codes;
  mapping(bytes32 => uint) votes;
  mapping(uint => bytes2) names;
  function first(bytes4 x) returns (bytes1 r) { r = x[0]; }
  function widen(bytes2 x) returns (bytes4 r) { r = x; }
}

example : Tags.widths =
    [("id", 32), ("id#bytes", 4), ("root#bytes", 32), ("codes[]", 16), ("codes[]#bytes", 2),
     ("votes{}#bytes", 32), ("names[]", 16), ("names[]#bytes", 2)] := rfl

/-- A state variable, and a mapping's value of `bytes2`. -/
theorem stateVar : ⊨ dl[Tags]{ ⟨ id = "abcd"; bytes1 c = id[3]; ⟩ c == 100 } := by
  sol_symex
  sol_close

theorem element : ⊨ dl[Tags]{ ⟨ names[1] = "xy"; bytes1 d = names[1][1]; ⟩ d == 121 } := by
  sol_symex
  sol_close

/-- A literal key at `bytes32` is left-aligned too. -/
theorem mappingKey : ⊨ dl[Tags]{ ⟨ votes["a"] = 1; bytes32 k = "a"; uint v = votes[k]; ⟩ v == 1 } := by
  sol_symex
  sol_close

/-- A parameter and a return: `first("abcd")` is `"a"`, `widen("ab")` pads. -/
theorem functions : ⊨ dl[Tags]{ ⟨ bytes1 r = first("abcd"); bytes4 w = widen("ab"); ⟩
    r == 97 && w == 1633812480 } := by
  sol_symex
  sol_close

/-! ## 3 · `bytes` and `string`

A `bytes1[]`: a `uint[]` whose elements are 8 bits wide and marked `bytes1`
(`dynBytesRows`), in memory and in storage alike, `string` the same.  A
literal where one stands is a fresh memory array of its bytes. -/

/-- A literal in memory: its length and its bytes. -/
theorem memoryLiteral : ⊨ dl!{ ⟨ bytes memory b = "abc"; uint l = b.length; bytes1 c = b[1]; ⟩
    l == 3 && c == 98 } := by
  sol_symex
  sol_decide

/-- `bytes(s)` of a `string` is the same array; an element written takes a
`bytes1`. -/
theorem stringToBytes : ⊨ dl!{ ⟨ string memory s = "hi"; bytes memory b = bytes(s); b[0] = "H";
    bytes1 c = b[0]; uint l = b.length; ⟩ c == 72 && l == 2 } := by
  sol_symex
  sol_decide

/-- An index past the end reverts. -/
theorem memoryOutOfRange : ⊨ dl!{ [ bytes memory b = new bytes(2); bytes1 c = b[2]; ] false } := by
  sol_symex
  sol_decide

/-- A contract with `bytes` and `string` in storage and in its functions. -/
def Texts : Contract := contract!{
  bytes data;
  string name;
  function len(string memory s) returns (uint n) { n = bytes(s).length; }
  function hello() returns (string memory r) { r = "hello"; }
}

example : Texts.widths =
    [("data[]", 8), ("data[]#bytes", 1), ("name[]", 8), ("name[]#bytes", 1)] := rfl

/-- A literal copied to storage, then pushed to and popped. -/
theorem storagePushPop : ⊨ dl[Texts]{ ⟨ data = "ab"; data.push("c"); uint l = data.length;
    bytes1 z = data[2]; data.pop(); uint m = data.length; ⟩ l == 3 && z == 99 && m == 2 } := by
  sol_symex
  sol_decide

/-- A `string` parameter and return, in memory. -/
theorem stringFunctions : ⊨ dl[Texts]{ ⟨ uint n = len("abcd"); string memory h = hello();
    uint k = bytes(h).length; ⟩ n == 4 && k == 5 } := by
  sol_symex
  sol_decide

/-- `delete` empties a `string` in storage. -/
theorem deleteString : ⊨ dl[Texts]{ ⟨ name = "x"; delete name; uint l = bytes(name).length; ⟩
    l == 0 } := by
  sol_symex
  sol_decide

end Solidity.Examples.Tactics.Bytes
