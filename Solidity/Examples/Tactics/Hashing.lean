import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Inspect
import Solidity.Tools.Run

/-!
# `keccak256`, `abi.*`, `concat` and string-keyed mappings

`keccak256` is Keccak-256 of the bytes (`keccakBytes`,
`Semantics/Heap.lean`, computed by `Keccak.lean`; `docs/semantic-gaps.md`,
"Hashing and the ABI"), kept from unfolding: the closers read a hash as an
atom, equal bytes hashing equal (`keccak256(memory, b)` of one byte string
read twice, the same term), and a proof evaluates the hash of literal bytes
in the kernel (`decide +kernel`).
`abi.encode`, `abi.encodePacked`, `string.concat` and `bytes.concat` are
fresh memory `bytes` of solc's layout, written byte by byte (`abiEncode`,
`Syntax/Elab.lean`), and `abi.decode` reads words back, reverting on a value
out of its type's range.  A `mapping(string => V)` is keyed by the hash.

* §1 — `keccak256`, its value computed (`#run`, `decide +kernel`);
* §2 — `abi.encode`, `abi.encodePacked` proved; `abi.decode`, a dynamic
  encoding and the `concat`s run (`#run`);
* §3 — a mapping keyed by `string`.
-/

namespace Solidity.Examples.Tactics.Hashing

local instance : InContract := ⟨StandardExample⟩

open scoped Scoped

/-! ## 1 · `keccak256` -/

/-- One byte string hashed twice: the same value, the hash a function.
Under the box: `sol_decide` reads a hash as an atom, and does not show that
one of a memory it wrote returns (`docs/semantic-gaps.md`, "Hashing and
the ABI"). -/
theorem hashTwice : ⊨ dl!{ [ bytes memory b = "ab"; bytes32 h = keccak256(b);
    bytes32 g = keccak256(b); ] h == g } := by
  sol_symex
  sol_decide

/-- A `string` hashed through `bytes(s)`, the identity. -/
theorem hashString : ⊨ dl!{ [ string memory s = "ab"; bytes32 h = keccak256(bytes(s));
    bytes32 g = keccak256(bytes(s)); ] h == g } := by
  sol_symex
  sol_decide

/-- The hash is Keccak-256: of `"abc"`, by evaluation in the kernel (well
under a second for an input of one block). -/
theorem keccakAbc : (keccakBytes [97, 98, 99]).1 =
    0x4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45 := by
  decide +kernel

/-- So a selector hashed at run time is the one the elaborator folds:
`bytes4(keccak256("f(uint256)"))` is `this.f.selector`, `0xb3de648b`. -/
def Sel : Contract := contract!{
  function f(uint x) returns (uint r) { r = x; }
  function sel() returns (bool same, uint s) {
    bytes4 h = bytes4(keccak256("f(uint256)"));
    s = uint32(h);
    same = h == this.f.selector;
  }
}

/--
info: ok
returns (true, 3017696395)
-/
#guard_msgs in #run Sel.sel()

#guard Keccak.selector "f(uint256)" == 0xb3de648b

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

/-- More of the ABI: a selector before the arguments, an `address` and an
enum packed at their own widths, arrays and structs, a `bytes` decoded. -/
def Codec2 : Contract := contract!{
  enum E { A, B, C }
  struct Pt { uint x; bool y; }
  function g(uint x, address a) { }
  function withSelector() returns (uint l, bytes1 b0, bytes1 b35) {
    bytes memory e = abi.encodeWithSelector(bytes4(0x12345678), 7);
    l = e.length; b0 = e[0]; b35 = e[35];
  }
  function withSignature() returns (uint l, bytes1 b0, bytes1 b3) {
    bytes memory e = abi.encodeWithSignature("transfer(address,uint256)", 9, 5);
    l = e.length; b0 = e[0]; b3 = e[3];
  }
  function withCall() returns (uint l, bytes1 b0, bytes1 b67) {
    bytes memory e = abi.encodeCall(g, (4, 8));
    l = e.length; b0 = e[0]; b67 = e[67];
  }
  function packedWidths() returns (uint l, bytes1 a, bytes1 c) {
    address x = 7;
    bytes memory e = abi.encodePacked(x, E.C);
    l = e.length; a = e[19]; c = e[20];
  }
  function arrays() returns (uint l, bytes1 off, bytes1 n, bytes1 b, uint pl) {
    uint[] memory xs = new uint[](2);
    xs[0] = 5; xs[1] = 6;
    bytes memory e = abi.encode(xs);
    l = e.length; off = e[31]; n = e[63]; b = e[127];
    pl = abi.encodePacked(xs).length;
  }
  function structs() returns (uint l, bytes1 x, bytes1 y) {
    Pt memory p;
    p.x = 3; p.y = true;
    bytes memory e = abi.encode(p);
    l = e.length; x = e[31]; y = e[63];
  }
  function decodeBytes() returns (uint a, uint l, bytes1 c) {
    bytes memory e = abi.encode(7, "hi");
    bytes memory b;
    (a, b) = abi.decode(e, (uint, bytes));
    l = b.length; c = b[1];
  }
  function decodeOutOfRange() returns (uint l) {
    bytes memory e = abi.encode(1000);
    bytes memory b = abi.decode(e, (bytes));
    l = b.length;
  }
}

-- `abi.encodeWithSelector`: the selector's four bytes, then the words
/--
info: ok
returns (36, 18, 7)
-/
#guard_msgs in #run Codec2.withSelector()

-- `abi.encodeWithSignature`: a literal signature's selector, `0xa9059cbb`
/--
info: ok
returns (68, 169, 187)
-/
#guard_msgs in #run Codec2.withSignature()

-- `abi.encodeCall(g, (…))`: `g(uint256,address)`'s selector, solc's
-- `0xa4394e36` (the `address` read off its marker)
/--
info: ok
returns (68, 164, 8)
-/
#guard_msgs in #run Codec2.withCall()

-- `abi.encodePacked` of an `address` takes 20 bytes, of an enum one
/--
info: ok
returns (21, 7, 2)
-/
#guard_msgs in #run Codec2.packedWidths()

-- a dynamic array: its offset, length and words; packed, its words alone
/--
info: ok
returns (128, 32, 2, 6, 64)
-/
#guard_msgs in #run Codec2.arrays()

-- a struct of values: its members' words in the head
/--
info: ok
returns (64, 3, 1)
-/
#guard_msgs in #run Codec2.structs()

-- `abi.decode` of `bytes`: the offset, the length, the bytes
/--
info: ok
returns (7, 2, 105)
-/
#guard_msgs in #run Codec2.decodeBytes()

-- an offset past the data reverts, as solc's decoder does
/-- info: revert -/
#guard_msgs in #run Codec2.decodeOutOfRange()

/-- **A symbolic word written byte by byte, read back**: `abi.encodePacked`
writes `uint8(x >> 8k)` per byte; the closer reads a byte back (`x >> 0` as
`x`, `(t % m) % n` and `((t % 2^m) >> j) % 2^w` narrowed) and reassembles
Horner's `r * 256 + b` (`hornerU?`, `Calculus/Closer.lean`, Lean only). -/
def Packed : Contract := contract!{
  function addressLast(address a) {
    bytes memory e = abi.encodePacked(a);
    assert(uint8(e[19]) == uint8(uint160(a)));
  }
  function addressFirst(address a) {
    bytes memory e = abi.encodePacked(a);
    assert(uint8(e[0]) == uint8(uint160(a) >> 152));
  }
  function wordReassembled(uint a) {
    bytes memory e = abi.encodePacked(uint64(a));
    uint r = uint8(e[0]); r = r * 256 + uint8(e[1]); r = r * 256 + uint8(e[2]); r = r * 256 + uint8(e[3]); r = r * 256 + uint8(e[4]); r = r * 256 + uint8(e[5]); r = r * 256 + uint8(e[6]); r = r * 256 + uint8(e[7]);
    assert(r == a % 18446744073709551616);
  }
}

section Packed

local instance : InContract := ⟨Packed⟩

theorem addressLast : ⊨ spec!{addressLast} := by
  sol_symex
  sol_decide

theorem addressFirst : ⊨ spec!{addressFirst} := by
  sol_symex
  sol_decide

/-- Eight bytes reassembled; twenty (an `address`) are past `Seq.closeSize`. -/
theorem wordReassembled : ⊨ spec!{wordReassembled} := by
  sol_symex
  sol_decide

end Packed

/-! ## 3 · A mapping keyed by `string` -/

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
