/-!
# SHA-256 and RIPEMD-160, computed

solc's `sha256(bytes memory b)` and `ripemd160(bytes memory b)` call the
EVM's precompiles at addresses `2` and `3`, which compute the standard hashes
of the bytes.  These are those hashes, written as `Keccak.lean` writes
Keccak-256: over `Nat`s, words below `2^32`, every recursion structural, so
that the kernel evaluates the hash of literal bytes (`decide +kernel`) and
`#run` computes the real value (`docs/semantic-gaps.md`, "Hashing and the
ABI").  The program-level functions are `sha256Bytes` and `ripemd160Bytes`
(`Semantics/Heap.lean`), `@[irreducible]` as `keccakBytes` is.
-/

namespace Solidity.Hashes

def mask32 : Nat := 2 ^ 32 - 1

def add32 (a b : Nat) : Nat := (a + b) % 2 ^ 32

def not32 (x : Nat) : Nat := mask32 - x % 2 ^ 32

def rotr32 (x n : Nat) : Nat :=
  if n = 0 then x else ((x >>> n) ||| (x <<< (32 - n))) &&& mask32

def rotl32 (x n : Nat) : Nat :=
  if n = 0 then x else ((x <<< n) &&& mask32) ||| (x >>> (32 - n))

/-- Big-endian bytes of `x`, `n` of them. -/
def beBytes (n x : Nat) : List Nat := (List.range n).reverse.map fun i => (x >>> (8 * i)) % 256

/-- Little-endian bytes of `x`, `n` of them. -/
def leBytes (n x : Nat) : List Nat := (List.range n).map fun i => (x >>> (8 * i)) % 256

/-- Big-endian bytes as a number. -/
def ofBytes (bs : List Nat) : Nat := bs.foldl (fun n b => 256 * n + b) 0

/-- The message padded as MD4 and its successors pad: `0x80`, zeros to `56`
modulo `64`, the length in bits on eight bytes (`le`: little-endian). -/
def pad (le : Bool) (msg : List Nat) : List Nat :=
  let zeros := (119 - msg.length % 64) % 64
  let len := 8 * msg.length
  msg ++ [0x80] ++ List.replicate zeros 0 ++ (if le then leBytes 8 len else beBytes 8 len)

/-- The 64-byte blocks of padded data; `k` bounds them. -/
def blocks : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | k + 1, data => if data.isEmpty then [] else data.take 64 :: blocks k (data.drop 64)

/-! ## SHA-256 (FIPS 180-4) -/

def shaK : List Nat := [
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def shaH0 : List Nat := [
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- The message schedule of one block: its sixteen words, then 48 more. -/
def shaSchedule (blk : List Nat) : List Nat :=
  let w0 : List Nat := (List.range 16).map fun i => ofBytes ((blk.drop (4 * i)).take 4)
  (List.range 48).foldl (fun w t =>
    let i := t + 16
    let x := w.getD (i - 15) 0
    let y := w.getD (i - 2) 0
    let s0 := rotr32 x 7 ^^^ rotr32 x 18 ^^^ (x >>> 3)
    let s1 := rotr32 y 17 ^^^ rotr32 y 19 ^^^ (y >>> 10)
    w ++ [add32 (add32 (w.getD (i - 16) 0) s0) (add32 (w.getD (i - 7) 0) s1)]) w0

/-- One block compressed into the eight words. -/
def shaBlock (h : List Nat) (blk : List Nat) : List Nat :=
  let w := shaSchedule blk
  let v := (List.range 64).foldl (fun (v : List Nat) t =>
    let a := v.getD 0 0
    let b := v.getD 1 0
    let c := v.getD 2 0
    let d := v.getD 3 0
    let e := v.getD 4 0
    let f := v.getD 5 0
    let g := v.getD 6 0
    let hh := v.getD 7 0
    let S1 := rotr32 e 6 ^^^ rotr32 e 11 ^^^ rotr32 e 25
    let ch := (e &&& f) ^^^ (not32 e &&& g)
    let t1 := add32 (add32 (add32 hh S1) (add32 ch (shaK.getD t 0))) (w.getD t 0)
    let S0 := rotr32 a 2 ^^^ rotr32 a 13 ^^^ rotr32 a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := add32 S0 maj
    [add32 t1 t2, a, b, c, add32 d t1, e, f, g]) h
  (List.range 8).map fun i => add32 (h.getD i 0) (v.getD i 0)

/-- SHA-256 of `msg` (bytes below `256`), its 32 bytes. -/
def sha256 (msg : List Nat) : List Nat :=
  let data := pad false msg
  let h := (blocks (data.length / 64) data).foldl shaBlock shaH0
  (h.map (beBytes 4)).flatten

/-- SHA-256 of `msg` as a number, below `2^256`. -/
def sha256Nat (msg : List Nat) : Nat := ofBytes (sha256 msg)

/-! ## RIPEMD-160 (Dobbertin, Bosselaers, Preneel) -/

def rmdR : List Nat := [
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
  7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
  3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12,
  1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
  4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13]

def rmdR' : List Nat := [
  5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12,
  6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
  15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13,
  8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
  12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11]

def rmdS : List Nat := [
  11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8,
  7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
  11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5,
  11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
  9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6]

def rmdS' : List Nat := [
  8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6,
  9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11,
  9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5,
  15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8,
  8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11]

def rmdK : List Nat := [0x00000000, 0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xa953fd4e]

def rmdK' : List Nat := [0x50a28be6, 0x5c4dd124, 0x6d703ef3, 0x7a6d76e9, 0x00000000]

/-- The boolean function of round `j / 16`. -/
def rmdF (j x y z : Nat) : Nat :=
  match j / 16 with
  | 0 => x ^^^ y ^^^ z
  | 1 => (x &&& y) ||| (not32 x &&& z)
  | 2 => (x ||| not32 y) ^^^ z
  | 3 => (x &&& z) ||| (y &&& not32 z)
  | _ => x ^^^ (y ||| not32 z)

/-- One line's 80 steps over the five words `[a, b, c, d, e]`; the right
line reads the functions in reverse order. -/
def rmdLine (right : Bool) (x : List Nat) (v : List Nat) : List Nat :=
  (List.range 80).foldl (fun (v : List Nat) j =>
    let a := v.getD 0 0
    let b := v.getD 1 0
    let c := v.getD 2 0
    let d := v.getD 3 0
    let e := v.getD 4 0
    let f := if right then rmdF (79 - j) b c d else rmdF j b c d
    let r := if right then rmdR'.getD j 0 else rmdR.getD j 0
    let s := if right then rmdS'.getD j 0 else rmdS.getD j 0
    let k := if right then rmdK'.getD (j / 16) 0 else rmdK.getD (j / 16) 0
    let t := add32 (rotl32 (add32 (add32 a f) (add32 (x.getD r 0) k)) s) e
    [e, t, b, rotl32 c 10, d]) v

/-- One block compressed into the five words. -/
def rmdBlock (h : List Nat) (blk : List Nat) : List Nat :=
  let x : List Nat := (List.range 16).map fun i =>
    ((blk.drop (4 * i)).take 4).foldr (fun b acc => (acc <<< 8) ||| b) 0
  let l := rmdLine false x h
  let r := rmdLine true x h
  let g (i : Nat) (u : List Nat) : Nat := u.getD (i % 5) 0
  [add32 (g 1 h) (add32 (g 2 l) (g 3 r)), add32 (g 2 h) (add32 (g 3 l) (g 4 r)),
    add32 (g 3 h) (add32 (g 4 l) (g 0 r)), add32 (g 4 h) (add32 (g 0 l) (g 1 r)),
    add32 (g 0 h) (add32 (g 1 l) (g 2 r))]

def rmdH0 : List Nat := [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0]

/-- RIPEMD-160 of `msg` (bytes below `256`), its 20 bytes. -/
def ripemd160 (msg : List Nat) : List Nat :=
  let data := pad true msg
  let h := (blocks (data.length / 64) data).foldl rmdBlock rmdH0
  (h.map (leBytes 4)).flatten

/-- RIPEMD-160 of `msg` as a number, below `2^160`. -/
def ripemd160Nat (msg : List Nat) : Nat := ofBytes (ripemd160 msg)

private def str (s : String) : List Nat := s.toUTF8.toList.map UInt8.toNat

#guard sha256Nat [] == 0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
#guard sha256Nat (str "abc") ==
    0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
-- two blocks: the padding past the first block's end
#guard sha256Nat (str "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") ==
    0x248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1
#guard ripemd160Nat [] == 0x9c1185a5c5e9fc54612808977ee8f548b2258d31
#guard ripemd160Nat (str "abc") == 0x8eb208f7e05d987a9b044a8e98c6b087f15a0bfc
#guard ripemd160Nat (str "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") ==
    0x12a053384a9c0c88e405a06c27dcf49ada62eb2b

end Solidity.Hashes
