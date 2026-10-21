/-!
# Keccak-256, computed

The elaborator folds a function selector as solc does: the first four bytes
of the Keccak-256 of the function's canonical signature (`this.f.selector`,
`abi.encodeWithSignature("f(uint256)", …)`; `docs/semantic-gaps.md`,
"Function types" and "Hashing and the ABI").  This is that hash, the
original Keccak (padding `0x01`, not SHA-3's `0x06`), over bytes.  Only
elaboration runs it: no proof reads it, and the hash a program computes at
run time stays the uninterpreted `keccakBytes` (`Semantics/Heap.lean`).
-/

namespace Solidity.Keccak

/-- The round constants. -/
def roundConsts : Array UInt64 := #[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- The rotation offsets, by lane `x + 5 y`. -/
def rotations : Array UInt64 := #[
  0, 1, 62, 28, 27,
  36, 44, 6, 55, 20,
  3, 10, 43, 25, 39,
  41, 45, 15, 21, 8,
  18, 2, 61, 56, 14]

def rotl (x n : UInt64) : UInt64 := if n == 0 then x else (x <<< n) ||| (x >>> (64 - n))

/-- One round of Keccak-f[1600] on the 25 lanes. -/
def round (a : Array UInt64) (rc : UInt64) : Array UInt64 := Id.run do
  let lane (i : Nat) : UInt64 := a[i]!
  -- θ
  let c : Array UInt64 := (Array.range 5).map fun x =>
    lane x ^^^ lane (x + 5) ^^^ lane (x + 10) ^^^ lane (x + 15) ^^^ lane (x + 20)
  let d : Array UInt64 := (Array.range 5).map fun x => c[(x + 4) % 5]! ^^^ rotl c[(x + 1) % 5]! 1
  let a1 : Array UInt64 := (Array.range 25).map fun i => lane i ^^^ d[i % 5]!
  -- ρ and π
  let mut b : Array UInt64 := Array.replicate 25 0
  for x in [0:5] do
    for y in [0:5] do
      b := b.set! (y + 5 * ((2 * x + 3 * y) % 5)) (rotl a1[x + 5 * y]! rotations[x + 5 * y]!)
  -- χ
  let a2 : Array UInt64 := (Array.range 25).map fun i =>
    let x := i % 5
    let y := i / 5
    b[i]! ^^^ ((~~~ b[(x + 1) % 5 + 5 * y]!) &&& b[(x + 2) % 5 + 5 * y]!)
  -- ι
  pure (a2.set! 0 (a2[0]! ^^^ rc))

def permute (a : Array UInt64) : Array UInt64 :=
  roundConsts.foldl round a

/-- A lane of eight bytes, little-endian. -/
def laneOf (bs : List UInt8) : UInt64 :=
  bs.foldr (fun b acc => (acc <<< 8) ||| b.toUInt64) 0

/-- The sponge at rate 136 bytes, its first 32 bytes out, the message padded
with the domain byte `ds` (`0x01` Keccak's, `0x06` SHA-3's). -/
def sponge (ds : UInt8) (msg : List UInt8) : List UInt8 := Id.run do
  let rate := 136
  let padLen := rate - msg.length % rate
  let pad : List UInt8 :=
    if padLen == 1 then [ds ||| 0x80] else [ds] ++ List.replicate (padLen - 2) 0 ++ [0x80]
  let data := (msg ++ pad).toArray
  let mut st : Array UInt64 := Array.replicate 25 0
  for blk in [0:data.size / rate] do
    for i in [0:rate / 8] do
      let o := blk * rate + 8 * i
      st := st.set! i (st[i]! ^^^ laneOf (data.extract o (o + 8)).toList)
    st := permute st
  let mut out : List UInt8 := []
  for i in [0:4] do
    let w := st[i]!
    out := out ++ (List.range 8).map fun j => (w >>> (8 * j).toUInt64).toUInt8
  pure out

/-- Keccak-256 of `msg`, its 32 bytes. -/
def keccak256 (msg : List UInt8) : List UInt8 := sponge 0x01 msg

/-- Keccak-256 of a string's UTF-8 bytes, as a number. -/
def keccak256Str (s : String) : Nat :=
  (keccak256 s.toUTF8.toList).foldl (fun n b => 256 * n + b.toNat) 0

/-- The selector of a canonical signature, `transfer(address,uint256)`. -/
def selector (sig : String) : Nat := keccak256Str sig / 2 ^ 224

#guard keccak256Str "" ==
    0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470
#guard selector "transfer(address,uint256)" == 0xa9059cbb
#guard keccak256Str "abc" ==
    0x4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45
-- the permutation over two blocks and at a block's edge, through SHA3-256
-- (the same sponge, its domain byte `0x06`)
#guard (sponge 0x06 (List.replicate 200 97)).foldl (fun n b => 256 * n + b.toNat) 0 ==
    0xcce34485baf2bf2aca99b94833892a4f52896d3d153f7b840cc4f9fe695f1387
#guard (sponge 0x06 (List.replicate 136 97)).foldl (fun n b => 256 * n + b.toNat) 0 ==
    0x3fc5559f14db8e453a0a3091edbd2bc25e11528d81c66fa570a4efdcc2695ee1

end Solidity.Keccak
