import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Inspect
import Solidity.Tools.Run

/-!
# `keccak256`, `abi.*`, `concat` and string-keyed mappings

`keccak256` is an uninterpreted function of the bytes (`keccakOf`,
`Semantics/Heap.lean`; `docs/semantic-gaps.md`, "Hashing and the ABI"): a
proof knows only that equal bytes hash equal, and the closer sees that of
one byte string read twice (`keccak256(memory, b)`, the same term).
`abi.encode`, `abi.encodePacked`, `string.concat` and `bytes.concat` are
fresh memory `bytes` of solc's layout, written byte by byte (`abiEncode`,
`Syntax/Elab.lean`), and `abi.decode` reads words back, reverting on a value
out of its type's range.  A `mapping(string => V)` is keyed by the hash.

* §1 — `keccak256`;
* §2 — `abi.encode`, `abi.encodePacked`, `abi.decode`;
* §3 — `string.concat`, `bytes.concat`;
* §4 — a mapping keyed by `string`.
-/

namespace Solidity.Examples.Tactics.Hashing

local instance : InContract := ⟨StandardExample⟩

open scoped Scoped

/-! ## 1 · `keccak256` -/

/-- One byte string hashed twice: the same value, the hash a function. -/
theorem hashTwice : ⊨ dl!{ [ bytes memory b = "ab"; bytes32 h = keccak256(b);
    bytes32 g = keccak256(b); ] h == g } := by
  sol_symex
  sol_decide

/-- A `string` hashed through `bytes(s)`, the identity. -/
theorem hashString : ⊨ dl!{ [ string memory s = "ab"; bytes32 h = keccak256(bytes(s));
    bytes32 g = keccak256(bytes(s)); ] h == g } := by
  sol_symex
  sol_decide

/-! ## 2 · The ABI -/

/-- `abi.encode(uint, bool)`: two words, big-endian. -/
theorem encodeLayout : ⊨ dl!{ ⟨ bytes memory e = abi.encode(258, true); uint l = e.length;
    bytes1 a = e[30]; bytes1 b = e[31]; bytes1 c = e[63]; bytes1 z = e[0]; ⟩
    l == 64 && a == 1 && b == 2 && c == 1 && z == 0 } := by
  sol_symex
  sol_decide

/-- `abi.encodePacked`: each value in its own width, a `bytes2` left-aligned. -/
theorem encodePacked : ⊨ dl!{ ⟨ uint16 x = 258; bytes2 t = "ab";
    bytes memory e = abi.encodePacked(x, true, t); uint l = e.length;
    bytes1 a = e[0]; bytes1 b = e[1]; bytes1 c = e[2]; bytes1 d = e[3]; ⟩
    l == 5 && a == 1 && b == 2 && c == 1 && d == 97 } := by
  sol_symex
  sol_decide

/-- The ABI run: `#run` evaluates what a symbolic proof of 32-byte words
would take minutes over (each word read byte by byte). -/
def Codec : Contract := contract!{
  function roundtrip() returns (uint a, bool c) {
    bytes memory e = abi.encode(258, true);
    (a, c) = abi.decode(e, (uint, bool));
  }
  function signed() returns (int8 a) {
    int8 x = -2;
    a = abi.decode(abi.encode(x), (int8));
  }
  function badBool() returns (bool c) {
    bytes memory e = abi.encode(2);
    c = abi.decode(e, (bool));
  }
  function shortData() returns (uint a) {
    bytes memory e = abi.encodePacked(uint8(1));
    a = abi.decode(e, (uint));
  }
  function dynamic() returns (uint l, bytes1 b) {
    bytes memory e = abi.encode(7, "hi");
    l = e.length;
    b = e[97];
  }
  function concat() returns (uint l, bytes1 y) {
    string memory s = string.concat("ab", "cde");
    bytes memory t = bytes.concat("x", "yz");
    l = bytes(s).length;
    y = t[1];
  }
}

-- `abi.decode` reads back what `abi.encode` wrote.
/--
info: ok
returns (258, true)
-/
#guard_msgs in #run Codec.roundtrip()

-- An `int8` is sign-extended and read back.
/--
info: ok
returns -2
-/
#guard_msgs in #run Codec.signed()

-- A word out of `bool`'s range, and data shorter than a word, revert.
/-- info: revert -/
#guard_msgs in #run Codec.badBool()

/-- info: revert -/
#guard_msgs in #run Codec.shortData()

-- A byte string: its offset in the head, its length and bytes in the tail,
-- padded to a word: `abi.encode(7, "hi")` is 128 bytes, `"i"` at 97.
/--
info: ok
returns (128, 105)
-/
#guard_msgs in #run Codec.dynamic()

-- `string.concat` and `bytes.concat`: the bytes one after the other.
/--
info: ok
returns (5, 121)
-/
#guard_msgs in #run Codec.concat()

/-! ## 4 · A mapping keyed by `string` -/

/-- `mapping(string => uint)`: a `mapping(uint => uint)` keyed by the hash
(`hashKeyRows`). -/
def Names : Contract := contract!{
  mapping(string => uint) ids;
}

example : Names.widths = [("ids{}#hash", 1)] := rfl

/-- Set and read back under one key. -/
theorem setGet : ⊨ dl[Names]{ [ string memory k = "alice"; ids[k] = 7; uint v = ids[k]; ] v == 7 } := by
  sol_symex
  sol_decide

end Solidity.Examples.Tactics.Hashing
