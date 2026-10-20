import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Inspect

/-!
# `keccak256`, `abi.*`, `concat` and string-keyed mappings

`keccak256` is an uninterpreted function of the bytes (`keccakOf`,
`Semantics/Heap.lean`; `docs/semantic-gaps.md`, "Hashing and the ABI"): a
proof knows only that equal bytes hash equal.  `abi.encode`,
`abi.encodePacked`, `string.concat` and `bytes.concat` are fresh memory
`bytes` of solc's layout, written byte by byte (`abiEncode`,
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
theorem hashTwice : ⊨ dl!{ ⟨ bytes memory b = "ab"; bytes32 h = keccak256(b);
    bytes32 g = keccak256(b); ⟩ h == g } := by
  sol_symex
  sol_close

/-! ## 2 · The ABI -/

/-- `abi.encode(uint, bool)`: two words, big-endian. -/
theorem encodeLayout : ⊨ dl!{ ⟨ bytes memory e = abi.encode(258, true); uint l = e.length;
    bytes1 a = e[30]; bytes1 b = e[31]; bytes1 c = e[63]; bytes1 z = e[0]; ⟩
    l == 64 && a == 1 && b == 2 && c == 1 && z == 0 } := by
  sol_symex
  sol_decide

end Solidity.Examples.Tactics.Hashing
