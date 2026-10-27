import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Run
import Solidity.ERC7201

/-!
# ABI and ERC-7201 regressions

Execution pins include noncanonical layouts accepted by Solidity's decoder,
malformed lengths checked before allocation, source ABI types, and UTF-8.
The byte roundtrip theorem is over every admitted input, not a concrete run.
-/

namespace Solidity.Examples.Tactics.AbiFeatures
open scoped Scoped

set_option maxRecDepth 2048

/-- The OpenZeppelin ERC20 namespace, evaluated from the ERC-7201 formula. -/
theorem erc20_namespace : (ERC7201.root ([111, 112, 101, 110, 122, 101, 112, 112, 101, 108, 105, 110, 46, 115, 116, 111, 114, 97, 103, 101, 46, 69, 82, 67, 50, 48] : List UInt8)).val =
    0x52c63247e1f47db19d5ce0460030c497f067ca4cebf71ba98eeadabe20bace00 := by
  have first : Keccak.keccak256Nat (([111, 112, 101, 110, 122, 101, 112, 112, 101, 108, 105, 110, 46, 115, 116, 111, 114, 97, 103, 101, 46, 69, 82, 67, 50, 48] : List UInt8).map UInt8.toNat) =
      82915213839719001205248582274697999438556962381091881013640795084694332245503 := by
    decide +kernel
  simp only [ERC7201.root, first, ERC7201.align]
  decide +kernel

/-- An empty identifier is valid; it is not a zero namespace. -/
theorem empty_namespace : (ERC7201.root []).val =
    0x4318a0031e4d2f411be9017543511db04d79cf580aaff6bae7539a4a49eacc00 := by
  decide +kernel

/-- UTF-8 bytes, rather than code points or a double UTF-8 encoding. -/
theorem utf8_namespace : (ERC7201.root ([195, 169] : List UInt8)).val =
    0x8209567c5747803e22c4b2eb04f9225604d2ac46762f9b6727bd697cc008a000 := by
  have first : Keccak.keccak256Nat (([195, 169] : List UInt8).map UInt8.toNat) =
      105402001111089681679568048549521299118097946430040143869324989827683005334386 := by
    decide +kernel
  simp only [ERC7201.root, first, ERC7201.align]
  decide +kernel

/-- Source operations used by the lowered builtins. -/
def Codec : Contract := contract!{
  function g(bytes2 x) returns (bytes2 y) { y = x; }
  function referenceFunction(uint[] memory xs) returns (uint y) { y = xs.length; }
  function directReferenceValue() returns (bool ok) {
    bytes memory e = abi.encode(this.referenceFunction);
    bytes memory p = abi.encodePacked(this.referenceFunction);
    ok = e.length == 32 && p.length == 24 && e[23] == p[23] && uint8(e[31]) == 0;
  }
  function f(uint x) returns (uint y) { y = x; }
  function fixedLiteral() returns (uint n, uint a, uint b, uint z) {
    bytes memory e = abi.encodeCall(this.g, ("ab"));
    n = e.length; a = uint8(e[4]); b = uint8(e[5]); z = uint8(e[35]);
  }
  function externalValue() returns (bool ok) {
    function (uint) external returns (uint) h = this.f;
    bytes memory e = abi.encode(h);
    bytes memory p = abi.encodePacked(h);
    ok = e.length == 32 && p.length == 24 && e[23] == p[23] &&
      uint8(e[24]) == 0 && uint8(e[31]) == 0;
  }
  function directValue() returns (bool ok) {
    bytes memory e = abi.encode(this.f);
    bytes memory p = abi.encodePacked(this.f);
    ok = e.length == 32 && p.length == 24 && e[23] == p[23] &&
      uint8(e[24]) == 0 && uint8(e[31]) == 0;
  }
  function shadowedScalar(uint f) returns (uint n) {
    bytes memory e = abi.encode(f); n = e.length;
  }
  function shadowedFunction() returns (uint a, uint b, uint x) {
    function (uint) external returns (uint) g = this.f;
    bytes memory e = abi.encodeCall(g, (7));
    a = uint8(e[0]); b = uint8(e[3]); x = uint8(e[35]);
  }
  function memberShadowScalar(uint f) returns (uint a, uint b, uint x) {
    bytes memory e = abi.encodeCall(this.f, (7));
    a = uint8(e[0]); b = uint8(e[3]); x = uint8(e[35]);
  }
  function memberShadowFunction() returns (uint a, uint b, uint x) {
    function (bytes2) external returns (bytes2) f = this.g;
    bytes memory e = abi.encodeCall(this.f, (7));
    a = uint8(e[0]); b = uint8(e[3]); x = uint8(e[35]);
  }
  function receiverOverflow(uint x) returns (uint n) {
    checked { bytes memory e = abi.encodeCall((x + 1).f, (7)); n = e.length; }
  }
  function unusedBuiltin() returns (uint n) {
    abi.encodeCall(this.f, (7)); n = 1;
  }
  function widenedBytes() returns (uint a, uint b) {
    bytes1 x = "a";
    bytes memory e = abi.encodeCall(this.g, (x));
    a = uint8(e[4]); b = uint8(e[5]);
  }
  function unicodeSelector() returns (uint a, uint b, uint c, uint d, bool same) {
    string memory s = "é()";
    bytes memory e = abi.encodeWithSignature("é()", 7);
    bytes memory r = abi.encodeWithSignature(s, 7);
    a = uint8(e[0]); b = uint8(e[1]); c = uint8(e[2]); d = uint8(e[3]);
    same = e[0] == r[0] && e[1] == r[1] && e[2] == r[2] && e[3] == r[3];
  }
  function namespaceValue() returns (uint a, uint b, uint low) {
    string memory s = "abc";
    a = erc7201(s); b = erc7201("abc"); low = a % 256;
  }
  function byteRoundtrip(uint8 x) {
    require(x < 256);
    uint8 y = abi.decode(abi.encode(x), (uint8));
    assert(y == x);
  }
  function nestedPrefix() returns (uint n, uint off, uint val) {
    uint[][] memory xs = new uint[][](1);
    xs[0] = new uint[](1); xs[0][0] = 7;
    bytes memory e = abi.encodeWithSelector(bytes4(0x12345678), xs, 9);
    n = e.length; off = uint8(e[35]); val = uint8(e[195]);
  }
  function hugeNestedHead() returns (uint n) {
    bytes memory e = abi.encode(32, type(uint).max);
    uint[][] memory xs = abi.decode(e, (uint[][])); n = xs.length;
  }
  function hugeBytes() returns (uint n) {
    bytes memory e = abi.encode(32, type(uint).max);
    bytes memory b = abi.decode(e, (bytes)); n = b.length;
  }
  function badSigned() returns (int8 x) { x = abi.decode(abi.encode(255), (int8)); }
  function badPadding() returns (bytes1 x) { x = abi.decode(abi.encode(1), (bytes1)); }
  function unaligned() returns (uint n) {
    bytes memory e = new bytes(65); e[31] = bytes1(33);
    bytes memory b = abi.decode(e, (bytes)); n = b.length;
  }
  function overlapping() returns (uint n) {
    bytes memory b = abi.decode(abi.encode(0), (bytes)); n = b.length;
  }
}

/-- info: ok
returns (36, 97, 98, 0) -/
#guard_msgs in #run Codec.fixedLiteral()
/-- info: ok
returns true -/
#guard_msgs in #run Codec.externalValue()
/-- info: ok
returns true -/
#guard_msgs in #run Codec.directValue()
/-- info: ok
returns true -/
#guard_msgs in #run Codec.directReferenceValue()
/-- info: ok
returns 32 -/
#guard_msgs in #run Codec.shadowedScalar(7)
/-- info: ok
returns (179, 139, 7) -/
#guard_msgs in #run Codec.shadowedFunction()
/-- info: ok
returns (179, 139, 7) -/
#guard_msgs in #run Codec.memberShadowScalar(0)
/-- info: ok
returns (179, 139, 7) -/
#guard_msgs in #run Codec.memberShadowFunction()
/-- info: ok
returns 1 -/
#guard_msgs in #run Codec.unusedBuiltin()
/-- info: panic (an `assert` failed) -/
#guard_msgs in #run Codec.receiverOverflow(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
/-- info: ok
returns 36 -/
#guard_msgs in #run Codec.receiverOverflow(0)
/-- info: ok
returns (97, 0) -/
#guard_msgs in #run Codec.widenedBytes()
/-- info: ok
returns (78, 69, 207, 137, true) -/
#guard_msgs in #run Codec.unicodeSelector()
/-- info: ok
returns (89080316084849266924113458916420441381095493738250323500559816430735688691456, 89080316084849266924113458916420441381095493738250323500559816430735688691456, 0) -/
#guard_msgs in #run Codec.namespaceValue()
/-- info: ok
returns (196, 64, 7) -/
#guard_msgs in #run Codec.nestedPrefix()
/-- info: revert -/
#guard_msgs in #run Codec.hugeNestedHead()
/-- info: revert -/
#guard_msgs in #run Codec.hugeBytes()
/-- info: revert -/
#guard_msgs in #run Codec.badSigned()
/-- info: revert -/
#guard_msgs in #run Codec.badPadding()
/-- info: ok
returns 0 -/
#guard_msgs in #run Codec.unaligned()
/-- info: ok
returns 0 -/
#guard_msgs in #run Codec.overlapping()

/-- Invalid discarded calls use the same source-kind check as assigned values. -/
def BadDiscarded : Contract := contract!{
  function invalid() { bytes.concat(string.concat("a")); }
}
/-- error: #run: bytes.concat takes bytes or fixed bytes -/
#guard_msgs in #run BadDiscarded.invalid()

-- Refuse narrowing and wrong primitive kinds before ABI marking erases types.
#guard (encodeCallArg Codec [("x", .val .uint 24 [("#bytes", 3)])]
  "bytes2" (.name "x")).toOption.isNone
#guard (encodeCallArg Codec [("x", .val .uint 256)] "uint8" (.name "x")).toOption.isNone
#guard (encodeCallArg Codec [("x", .val .uint 256)] "bool" (.name "x")).toOption.isNone
#guard (encodeCallArg Codec [("x", .val .bool 256)] "uint256" (.name "x")).toOption.isNone
#guard (encodeCallArg Codec [("x", .val .uint 256)] "bytes2" (.name "x")).toOption.isNone
#guard (bytesPure Codec [] (.call "bytes.concat" [.call "string.concat" [RawExpr.bytesLit [97]]])).toOption.isNone

#guard (encodeCallArg Codec [] "bytes" (.call "bytes" [RawExpr.bytesLit [97]])).isOk
#guard (encodeCallArg Codec [("x", .mem (.array (.prim .uint)) (dynBytesRowsOf "bytes"))] "string" (.call "string" [.name "x"])).isOk
#guard (encodeCallArg Codec [("x", .val .uint 192 [("#function(uint)externalreturns(uint)", 1)])] "function(uint)externalreturns(uint)" (.name "x")).isOk
#guard (encodeCallArg Codec [("x", .val .uint 192 [("#function(bool)externalreturns(bool)", 1)])] "function(uint)externalreturns(uint)" (.name "x")).toOption.isNone

#guard abiFnType "function(uint[][3])externalreturns((uint,int[]))" ==
  "function(uint256[][3])externalreturns((uint256,int256[]))"
#guard (encodeCallArg Codec [("x", .val .uint 192 [("#function(uint256[])externalreturns(uint256)", 1)])] "function(uint[])externalreturns(uint)" (.name "x")).isOk

#guard (fnPure Codec [("x", .val .uint 24 [("#bytes", 3)])]
  (.call "abi.encodeCall" [.field (.name "this") "g", .tuple [.name "x"]])).toOption.isNone

local instance : InContract := ⟨Codec⟩

/-- `abi.decode(abi.encode(x), (uint8)) == x` for every in-range byte. -/
theorem byte_roundtrip : ⊨ᶠ spec!{byteRoundtrip} := by
  sol_symex
  sol_decide

end Solidity.Examples.Tactics.AbiFeatures
