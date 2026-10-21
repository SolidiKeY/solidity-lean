import Solidity.Keccak

/-!
# Revert data as bytes

The byte layouts of revert data (`docs/semantic-gaps.md`, "Revert data"),
with nothing but Lean's core below them, so that the elaborator writes a
`revert("m")`'s data (`Syntax/Elab.lean`) and the run reads it
(`Semantics/RevertData.lean`) by the same functions.  `require(c, "m")` and
`revert("m")` return `abi.encodeWithSelector(0x08c379a0, "m")`
(`Error(string)`), a panic `Panic(uint256)` (`0x4e487b71`) and its code.

`Error`'s and `Panic`'s selectors are Solidity's fixed values; a custom
error's is computed as solc computes it, the first four bytes of the
Keccak-256 of its canonical signature (`customSelector`, `Keccak.lean`).
-/

namespace Solidity.Semantics

/-- Revert data: the bytes a revert returns. -/
abbrev RevertData := List UInt8

/-- `bytes4(keccak256("Error(string)"))`. -/
def errorSelector : List UInt8 := [0x08, 0xc3, 0x79, 0xa0]

/-- `bytes4(keccak256("Panic(uint256)"))`. -/
def panicSelector : List UInt8 := [0x4e, 0x48, 0x7b, 0x71]

/-- A custom error's selector, `bytes4(keccak256(sig))`. -/
def customSelector (sig : String) : UInt32 := UInt32.ofNat (Keccak.selector sig)

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

/-- A reason encoded decodes back. -/
example : decodeError (encodeError [0x62, 0x6f, 0x6f, 0x6d]) = some [0x62, 0x6f, 0x6f, 0x6d] := by
  decide

end Solidity.Semantics
