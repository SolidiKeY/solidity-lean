import Solidity.Precompiles.Field
import Solidity.Secp256k1

/-!
# Frontier's precompiles: `ECRECOVER` (0x01), `SHA256` (0x02), `RIPEMD160` (0x03), `IDENTITY` (0x04)

The three hashes reuse the approved fixed functions (`Solidity/Hashes.lean`,
`Solidity/Secp256k1.lean`) and add the precompiles' framing, as Osaka's
execution specification frames them:

- **`ECRECOVER`** reads 128 bytes (zero-padded) as `h, v, r, s`; it returns
  the recovered address as a 32-byte word, or *no* bytes when `v ∉ {27, 28}`,
  `r` or `s` is outside `[1, n)`, or recovery fails.  It never halts
  exceptionally; 3000 gas.
- **`SHA256`** returns the 32-byte digest; `60 + 12·words` gas.
- **`RIPEMD160`** returns the 20-byte digest left-padded to 32;
  `600 + 120·words` gas.
- **`IDENTITY`** returns its input; `15 + 3·words` gas.

None of the four fails on any input (`*_isSome`); the three linear gas
formulas grow with the input (`*Gas_mono`).
-/

namespace Solidity.Precompiles

open Solidity.Roadmap.Evm (Bytes)

def ecrecoverGas (_ : Bytes) : Nat := 3000

/-- `ECRECOVER` (0x01). -/
def ecrecover (d : Bytes) : Option Bytes :=
  some <| match Secp256k1.recover (readNat d 0 32) (readNat d 32 32) (readNat d 64 32)
      (readNat d 96 32) with
    | some a => word a.val
    | none => []

def sha256Gas (d : Bytes) : Nat := 60 + 12 * words d.length

/-- `SHA256` (0x02). -/
def sha256 (d : Bytes) : Option Bytes := some ((Hashes.sha256 (d.map UInt8.toNat)).map Nat.toUInt8)

def ripemd160Gas (d : Bytes) : Nat := 600 + 120 * words d.length

/-- `RIPEMD160` (0x03). -/
def ripemd160 (d : Bytes) : Option Bytes := some (word (Hashes.ripemd160Nat (d.map UInt8.toNat)))

def identityGas (d : Bytes) : Nat := 15 + 3 * words d.length

/-- `IDENTITY` (0x04). -/
def identity (d : Bytes) : Option Bytes := some d

theorem ecrecover_isSome (d : Bytes) : (ecrecover d).isSome := rfl
theorem sha256_isSome (d : Bytes) : (sha256 d).isSome := rfl
theorem ripemd160_isSome (d : Bytes) : (ripemd160 d).isSome := rfl
theorem identity_eq (d : Bytes) : identity d = some d := rfl

theorem words_mono {m n : Nat} (h : m ≤ n) : words m ≤ words n :=
  Nat.div_le_div_right (Nat.add_le_add_right h 31)

theorem sha256Gas_mono {d e : Bytes} (h : d.length ≤ e.length) : sha256Gas d ≤ sha256Gas e :=
  Nat.add_le_add_left (Nat.mul_le_mul_left 12 (words_mono h)) 60

theorem ripemd160Gas_mono {d e : Bytes} (h : d.length ≤ e.length) :
    ripemd160Gas d ≤ ripemd160Gas e :=
  Nat.add_le_add_left (Nat.mul_le_mul_left 120 (words_mono h)) 600

theorem identityGas_mono {d e : Bytes} (h : d.length ≤ e.length) : identityGas d ≤ identityGas e :=
  Nat.add_le_add_left (Nat.mul_le_mul_left 3 (words_mono h)) 15

/-! ## Vectors (Osaka's execution specification) -/

#guard ecrecover (ofHex "c4179c5a26cda29e689fe027ee5f5e4e085b30ad136bcc4808cf982380607110000000000000000000000000000000000000000000000000000000000000001b60a33eea03a29c01e5bf251d76ed7bd817e46666faa8ea703d95b7648da367576136d40d487f83644b470554781141106cefbdf3324e63a49b1ef6c49e2368de") == some (ofHex "0000000000000000000000002c7536e3605d9c16a7a3d7b1898e529396a65c23")
#guard ecrecoverGas (ofHex "c4179c5a26cda29e689fe027ee5f5e4e085b30ad136bcc4808cf982380607110000000000000000000000000000000000000000000000000000000000000001b60a33eea03a29c01e5bf251d76ed7bd817e46666faa8ea703d95b7648da367576136d40d487f83644b470554781141106cefbdf3324e63a49b1ef6c49e2368de") == 3000
#guard ecrecover (ofHex "c4179c5a26cda29e689fe027ee5f5e4e085b30ad136bcc4808cf982380607110000000000000000000000000000000000000000000000000000000000000001d60a33eea03a29c01e5bf251d76ed7bd817e46666faa8ea703d95b7648da367576136d40d487f83644b470554781141106cefbdf3324e63a49b1ef6c49e2368de") == some (ofHex "")
#guard ecrecoverGas (ofHex "c4179c5a26cda29e689fe027ee5f5e4e085b30ad136bcc4808cf982380607110000000000000000000000000000000000000000000000000000000000000001d60a33eea03a29c01e5bf251d76ed7bd817e46666faa8ea703d95b7648da367576136d40d487f83644b470554781141106cefbdf3324e63a49b1ef6c49e2368de") == 3000
#guard ecrecover (ofHex "c4179c5a26cda29e689fe027ee5f5e4e085b30ad136bcc4808cf982380607110000000000000000000000000000000000000000000000000000000000000001b60a33eea03a29c01e5bf251d76ed7bd817e46666faa8ea703d95b7648da36757ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff") == some (ofHex "")
#guard ecrecoverGas (ofHex "c4179c5a26cda29e689fe027ee5f5e4e085b30ad136bcc4808cf982380607110000000000000000000000000000000000000000000000000000000000000001b60a33eea03a29c01e5bf251d76ed7bd817e46666faa8ea703d95b7648da36757ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff") == 3000
#guard ecrecover (ofHex "c4179c5a26cda29e689fe027ee5f5e4e085b30ad136bcc4808cf982380607110000000000000000000000000000000000000000000000000000000000000001b60a33eea03a29c01e5bf251d76ed7bd817e46666faa8ea703d95b7648da367576136d40d") == some (ofHex "0000000000000000000000000731edd08692e8f4709d476fe0869404489237ce")
#guard ecrecoverGas (ofHex "c4179c5a26cda29e689fe027ee5f5e4e085b30ad136bcc4808cf982380607110000000000000000000000000000000000000000000000000000000000000001b60a33eea03a29c01e5bf251d76ed7bd817e46666faa8ea703d95b7648da367576136d40d") == 3000
#guard ecrecover (ofHex "") == some (ofHex "")
#guard ecrecoverGas (ofHex "") == 3000
#guard sha256 (ofHex "") == some (ofHex "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
#guard sha256Gas (ofHex "") == 60
#guard sha256 (ofHex "616263") == some (ofHex "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
#guard sha256Gas (ofHex "616263") == 72
#guard sha256 (ofHex "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f60616263") == some (ofHex "bce0aff19cf5aa6a7469a30d61d04e4376e4bbf6381052ee9e7f33925c954d52")
#guard sha256Gas (ofHex "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f60616263") == 108
#guard ripemd160 (ofHex "") == some (ofHex "0000000000000000000000009c1185a5c5e9fc54612808977ee8f548b2258d31")
#guard ripemd160Gas (ofHex "") == 600
#guard ripemd160 (ofHex "616263") == some (ofHex "0000000000000000000000008eb208f7e05d987a9b044a8e98c6b087f15a0bfc")
#guard ripemd160Gas (ofHex "616263") == 720
#guard ripemd160 (ofHex "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f60616263") == some (ofHex "0000000000000000000000008ae5d2e6b1f3a514257f2469b637454931844aeb")
#guard ripemd160Gas (ofHex "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f60616263") == 1080
#guard identity (ofHex "") == some (ofHex "")
#guard identityGas (ofHex "") == 15
#guard identity (ofHex "616263") == some (ofHex "616263")
#guard identityGas (ofHex "616263") == 18
#guard identity (ofHex "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20") == some (ofHex "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20")
#guard identityGas (ofHex "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20") == 21

end Solidity.Precompiles
