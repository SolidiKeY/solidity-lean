import Solidity.Semantics.Value

/-!
# Revert data

What a revert returns to its caller (`docs/semantic-gaps.md`, "Revert
data"): bytes.  `require(c, "m")` and `revert("m")` return
`abi.encodeWithSelector(0x08c379a0, "m")` (`Error(string)`), a panic
`Panic(uint256)` (`0x4e487b71`) and its code, `revert E(a, b)` `E`'s selector
and `abi.encode(a, b)`.  A `catch Error(string memory r)` decodes the first
(`decodeError`), a `catch Panic(uint c)` the second (`decodePanic`).

`Error`'s and `Panic`'s selectors are Solidity's fixed values; with
`keccak256` uninterpreted (`keccakBytes`) the model cannot compute a custom
error's, so `customSelector` is an uninterpreted function of the signature:
two signatures have different selectors only under a premise that says so,
as two inputs of `keccak256` hash apart only under one.
-/

namespace Solidity.Semantics

/-- Revert data: the bytes a revert returns. -/
abbrev RevertData := List UInt8

/-- `bytes4(keccak256("Error(string)"))`. -/
def errorSelector : List UInt8 := [0x08, 0xc3, 0x79, 0xa0]

/-- `bytes4(keccak256("Panic(uint256)"))`. -/
def panicSelector : List UInt8 := [0x4e, 0x48, 0x7b, 0x71]

/-- A compiled stand-in for `customSelector`, only so that `#run` tells
signatures apart; it is not Keccak, and no proof sees it. -/
def customSelectorStandIn (sig : String) : UInt32 :=
  sig.foldl (fun h c => (h ^^^ c.toNat.toUInt32) * 16777619) 2166136261

/-- A custom error's selector, `bytes4(keccak256(sig))`: uninterpreted. -/
@[implemented_by customSelectorStandIn]
opaque customSelector : String → UInt32

/-- A selector's four bytes, big-endian. -/
def selectorBytes (s : UInt32) : List UInt8 :=
  [(s >>> 24).toUInt8, (s >>> 16).toUInt8, (s >>> 8).toUInt8, s.toUInt8]

/-- `n` as a 32-byte big-endian ABI word (modulo `2^256`). -/
def wordBytes (n : Nat) : List UInt8 :=
  (List.range 32).map fun i => (n / 256 ^ (31 - i) % 256).toUInt8

/-- Bytes read big-endian as a number. -/
def bytesNat (bs : List UInt8) : Nat :=
  bs.foldl (fun a b => a * 256 + b.toNat) 0

/-- Bytes padded with zeros to a multiple of 32. -/
def pad32 (bs : List UInt8) : List UInt8 :=
  bs ++ List.replicate ((32 - bs.length % 32) % 32) 0

/-- `abi.encodeWithSelector(Error.selector, s)`: the selector, the offset
`32`, the length, the bytes padded. -/
def encodeError (s : List UInt8) : RevertData :=
  errorSelector ++ wordBytes 32 ++ wordBytes s.length ++ pad32 s

/-- `abi.encodeWithSelector(Panic.selector, c)`. -/
def encodePanic (c : Nat) : RevertData :=
  panicSelector ++ wordBytes c

/-- The reason `catch Error(string memory r)` binds: data with `Error`'s
selector whose string decodes (its offset and length inside the data);
`none` otherwise, where the `try` goes on to the catch-all. -/
def decodeError (d : RevertData) : Option (List UInt8) :=
  if d.take 4 = errorSelector then
    let body := d.drop 4
    let off := bytesNat (body.take 32)
    let rest := body.drop off
    if body.length < 32 || rest.length < 32 then none else
    let len := bytesNat (rest.take 32)
    let s := (rest.drop 32).take len
    if s.length = len then some s else none
  else none

/-- The code `catch Panic(uint c)` binds: data that is `Panic`'s selector
and one word. -/
def decodePanic (d : RevertData) : Option Word :=
  if d.take 4 = panicSelector ∧ d.length = 36 then
    let n := bytesNat (d.drop 4)
    if h : n < 2 ^ 256 then some ⟨n, by
      simp only [PrimTy.inRange, decide_eq_true_eq]
      exact ⟨Int.natCast_nonneg n, Int.ofNat_lt.mpr h⟩⟩
    else none
  else none

/-- A reason encoded decodes back. -/
example : decodeError (encodeError [0x62, 0x6f, 0x6f, 0x6d]) = some [0x62, 0x6f, 0x6f, 0x6d] := by
  decide

end Solidity.Semantics
