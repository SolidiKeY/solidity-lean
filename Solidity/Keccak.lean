/-!
# Keccak-256, computed

The elaborator folds a function selector as solc does: the first four bytes
of the Keccak-256 of the function's canonical signature (`this.f.selector`,
`abi.encodeWithSignature("f(uint256)", …)`; `docs/semantic-gaps.md`,
"Function types" and "Hashing and the ABI").  This is that hash, the
original Keccak (padding `0x01`, not SHA-3's `0x06`), over bytes.  It is
also the hash a program computes at run time (`keccakBytes`,
`Semantics/Heap.lean`), so a folded selector and a hashed signature are one
number, and the kernel evaluates the hash of literal bytes
(`decide +kernel`).
-/

namespace Solidity.Keccak

/-- The round constants. -/
def roundConsts : List Nat := [
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- The rotation offsets, by lane `x + 5 y`. -/
def rotations : List Nat := [
  0, 1, 62, 28, 27,
  36, 44, 6, 55, 20,
  3, 10, 43, 25, 39,
  41, 45, 15, 21, 8,
  18, 2, 61, 56, 14]

/-- The lanes are `Nat`s below `2^64` and the state a list of 25 of them, so
that the kernel evaluates the hash of literal bytes (`decide +kernel`): every
recursion is structural and every operation one the kernel computes on
numerals (`Nat` arithmetic, shifts, `&&&`, `|||`, `^^^`). -/
def mask64 : Nat := 2 ^ 64 - 1

def rotl (x n : Nat) : Nat :=
  if n = 0 then x else ((x <<< n) &&& mask64) ||| (x >>> (64 - n))

/-- One round of Keccak-f[1600] on the 25 lanes. -/
def round (a : List Nat) (rc : Nat) : List Nat :=
  let lane (i : Nat) : Nat := a.getD i 0
  -- θ
  let c : List Nat := (List.range 5).map fun x =>
    lane x ^^^ lane (x + 5) ^^^ lane (x + 10) ^^^ lane (x + 15) ^^^ lane (x + 20)
  let d : List Nat := (List.range 5).map fun x =>
    c.getD ((x + 4) % 5) 0 ^^^ rotl (c.getD ((x + 1) % 5) 0) 1
  let a1 : List Nat := (List.range 25).map fun i => lane i ^^^ d.getD (i % 5) 0
  -- ρ and π
  let b : List Nat := (List.range 25).foldl (fun b i =>
      let x := i % 5
      let y := i / 5
      b.set (y + 5 * ((2 * x + 3 * y) % 5)) (rotl (a1.getD i 0) (rotations.getD i 0)))
    (List.replicate 25 0)
  -- χ
  let a2 : List Nat := (List.range 25).map fun i =>
    let x := i % 5
    let y := i / 5
    b.getD i 0 ^^^ ((mask64 - b.getD ((x + 1) % 5 + 5 * y) 0) &&& b.getD ((x + 2) % 5 + 5 * y) 0)
  -- ι
  a2.set 0 (a2.getD 0 0 ^^^ rc)

def permute (a : List Nat) : List Nat :=
  roundConsts.foldl round a

/-- A lane of eight bytes, little-endian. -/
def laneOf (bs : List Nat) : Nat :=
  bs.foldr (fun b acc => (acc <<< 8) ||| b) 0

/-- Absorb the padded message, a block of 136 bytes (17 lanes) at a time;
`k` bounds the blocks. -/
def absorb : Nat → List Nat → List Nat → List Nat
  | 0, st, _ => st
  | k + 1, st, data =>
    if data.isEmpty then st else
      let blk := data.take 136
      let lanes : List Nat := (List.range 17).map fun i => laneOf ((blk.drop (8 * i)).take 8)
      absorb k (permute ((List.range 25).map fun i => st.getD i 0 ^^^ lanes.getD i 0))
        (data.drop 136)

/-- The sponge at rate 136 bytes, its first 32 bytes out, the message padded
with the domain byte `ds` (`0x01` Keccak's, `0x06` SHA-3's). -/
def sponge (ds : Nat) (msg : List Nat) : List Nat :=
  let rate := 136
  let padLen := rate - msg.length % rate
  let pad : List Nat :=
    if padLen = 1 then [ds ||| 0x80] else [ds] ++ List.replicate (padLen - 2) 0 ++ [0x80]
  let data := msg ++ pad
  let st := absorb (data.length / rate) (List.replicate 25 0) data
  ((st.take 4).map fun w => (List.range 8).map fun j => (w >>> (8 * j)) % 256).flatten

/-- Keccak-256 of `msg` (bytes below `256`), its 32 bytes. -/
def keccak256 (msg : List Nat) : List Nat := sponge 0x01 msg

/-- Big-endian bytes as a number. -/
def ofBytes (bs : List Nat) : Nat := bs.foldl (fun n b => 256 * n + b) 0

/-- Keccak-256 of `msg` as a number, below `2^256`. -/
def keccak256Nat (msg : List Nat) : Nat := ofBytes (keccak256 msg)

/-- Keccak-256 of a string's UTF-8 bytes, as a number. -/
def keccak256Str (s : String) : Nat :=
  keccak256Nat (s.toUTF8.toList.map UInt8.toNat)

/-- The selector of a canonical signature, `transfer(address,uint256)`. -/
def selector (sig : String) : Nat := keccak256Str sig / 2 ^ 224

#guard keccak256Str "" ==
    0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470
#guard selector "transfer(address,uint256)" == 0xa9059cbb
#guard keccak256Str "abc" ==
    0x4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45
-- the permutation over two blocks and at a block's edge, through SHA3-256
-- (the same sponge, its domain byte `0x06`)
#guard ofBytes (sponge 0x06 (List.replicate 200 97)) ==
    0xcce34485baf2bf2aca99b94833892a4f52896d3d153f7b840cc4f9fe695f1387
#guard ofBytes (sponge 0x06 (List.replicate 136 97)) ==
    0x3fc5559f14db8e453a0a3091edbd2bc25e11528d81c66fa570a4efdcc2695ee1

end Solidity.Keccak
