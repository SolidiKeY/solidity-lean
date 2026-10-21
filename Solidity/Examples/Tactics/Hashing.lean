import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Inspect

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

#exit

/-- `abi.decode` reads back what `abi.encode` wrote. -/
theorem decodeRoundtrip : ⊨ dl!{ ⟨ bytes memory e = abi.encode(5, true);
    (uint a, bool c) = abi.decode(e, (uint, bool)); ⟩ a == 5 && c == true } := by
  sol_symex
  sol_decide

/-- A word out of `bool`'s range does not decode: the run reverts. -/
theorem decodeBadBool : ⊨ dl!{ [ bytes memory e = abi.encode(2); bool c = abi.decode(e, (bool)); ]
    false } := by
  sol_symex
  sol_decide

/-! ## 3 · `concat` -/

/-- `string.concat` and `bytes.concat`: the bytes one after the other. -/
theorem concat : ⊨ dl!{ ⟨ string memory s = string.concat("ab", "cde"); uint l = bytes(s).length;
    bytes memory b = bytes.concat("x", "yz"); bytes1 y = b[1]; ⟩ l == 5 && y == 121 } := by
  sol_symex
  sol_decide

/-! ## 4 · A mapping keyed by `string` -/

/-- `mapping(string => uint)`: a `mapping(uint => uint)` keyed by the hash
(`hashKeyRows`). -/
def Names : Contract := contract!{
  mapping(string => uint) ids;
}

example : Names.widths = [("ids{}#hash", 1)] := rfl

/-- Set and read back under one key. -/
theorem setGet : ⊨ dl[Names]{ ⟨ string memory k = "alice"; ids[k] = 7; uint v = ids[k]; ⟩ v == 7 } := by
  sol_symex
  sol_decide

end Solidity.Examples.Tactics.Hashing
