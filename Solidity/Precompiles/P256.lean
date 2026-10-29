import Solidity.Precompiles.Field

/-!
# `P256VERIFY` (0x100) at Osaka

EIP-7951: ECDSA verification over secp256r1 (NIST P-256), as Osaka's
execution specification (`p256verify.py`) runs it.  The input is exactly
160 bytes: the message hash `h`, the signature `r, s` and the public key
`qx, qy`, each a 32-byte big-endian word.

- **Never fails.**  A malformed input (another length, `r` or `s` outside
  `[1, n)`, a coordinate at or above `p`, the key `(0, 0)` or off the curve)
  and an invalid signature both return *no* bytes; a valid signature
  returns the word `1` (`p256Verify_isSome`).
- **Gas**: 6900.

The check is the textbook one: with `s₁ = s⁻¹ mod n`,
`R = (h·s₁)·G + (r·s₁)·Q` must be finite with `R.x ≡ r (mod n)`.
-/

namespace Solidity.Precompiles.P256

open Solidity.Roadmap.Evm (Bytes)

/-- The base field's prime. -/
def p : Nat := 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
/-- The group order. -/
def n : Nat := 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551

instance : NeZero p := ⟨by decide⟩

abbrev Fp := Fin p

/-- `y² = x³ - 3·x + b`. -/
def curve : Curve Fp :=
  ⟨Fin.ofNat p (p - 3), Fin.ofNat p 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B⟩

/-- The standard generator. -/
def generator : Pt Fp :=
  .aff (Fin.ofNat p 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296)
       (Fin.ofNat p 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5)

#guard curve.onCurve generator
#guard curve.mul n generator == .inf

/-- A public key: a finite point of the curve. -/
abbrev Key := { Q : Pt Fp // Q ≠ .inf ∧ curve.onCurve Q = true }

/-- The key `(qx, qy)`, if well formed: coordinates below `p`, not
`(0, 0)`, on the curve. -/
def decodeKey (qx qy : Nat) : Option Key :=
  if hx : qx < p then if hy : qy < p then
    if h : (qx ≠ 0 ∨ qy ≠ 0) ∧ curve.onCurve (.aff ⟨qx, hx⟩ ⟨qy, hy⟩) = true then
      some ⟨.aff ⟨qx, hx⟩ ⟨qy, hy⟩, nofun, h.2⟩
    else none
  else none else none

/-- The ECDSA check of `(r, s)` on hash `h` by key `Q`. -/
def verify (h r s : Nat) (Q : Key) : Bool :=
  let s₁ := powMod s (n - 2) n
  match curve.add (curve.mul (h * s₁ % n) generator) (curve.mul (r * s₁ % n) Q.1) with
  | .inf => false
  | .aff x _ => x.val % n == r

def gas (_ : Bytes) : Nat := 6900

/-- `P256VERIFY` (0x100). -/
def p256Verify (d : Bytes) : Option Bytes :=
  some <|
    if d.length ≠ 160 then [] else
    let r := readNat d 32 32
    let s := readNat d 64 32
    if r = 0 ∨ n ≤ r ∨ s = 0 ∨ n ≤ s then [] else
    match decodeKey (readNat d 96 32) (readNat d 128 32) with
    | none => []
    | some Q => if verify (readNat d 0 32) r s Q then word 1 else []

theorem p256Verify_isSome (d : Bytes) : (p256Verify d).isSome := rfl

/-! ## Vectors (signed by `cryptography`, run by Osaka's execution specification) -/

#guard p256Verify (ofHex "bc691003939b33f22ac89afc39417969b3240c6fba15b987c3e9a576cdb15b0b93a3a1686593b7b992cae7fc2dd19983412beb4ff1c7c7d4a8fdc719a0de44c7ebfafd96902a95743fcfbd59f10fffdaae2cc7dc3af7a5a60dc655a3639802c9471c3e758c4904285bba7e53118ed0f524adeb0757d25bd2f8e7b0d76dfa714cdd520f7aca8a8b917acc37f51de8f0c9bbe3ad858382e702dc25a12d09f7a858") == some (ofHex "0000000000000000000000000000000000000000000000000000000000000001")
#guard gas (ofHex "bc691003939b33f22ac89afc39417969b3240c6fba15b987c3e9a576cdb15b0b93a3a1686593b7b992cae7fc2dd19983412beb4ff1c7c7d4a8fdc719a0de44c7ebfafd96902a95743fcfbd59f10fffdaae2cc7dc3af7a5a60dc655a3639802c9471c3e758c4904285bba7e53118ed0f524adeb0757d25bd2f8e7b0d76dfa714cdd520f7aca8a8b917acc37f51de8f0c9bbe3ad858382e702dc25a12d09f7a858") == 6900
#guard p256Verify (ofHex "bc691003939b33f22ac89afc39417969b3240c6fba15b987c3e9a576cdb15b0b93a3a1686593b7b992cae7fc2dd19983412beb4ff1c7c7d4a8fdc719a0de44c7ebfafd96902a95743fcfbd59f10fffdaae2cc7dc3af7a5a60dc655a3639802c9471c3e758c4904285bba7e53118ed0f524adeb0757d25bd2f8e7b0d76dfa714cdd520f7aca8a8b917acc37f51de8f0c9bbe3ad858382e702dc25a12d09f7a85800") == some (ofHex "")
#guard gas (ofHex "bc691003939b33f22ac89afc39417969b3240c6fba15b987c3e9a576cdb15b0b93a3a1686593b7b992cae7fc2dd19983412beb4ff1c7c7d4a8fdc719a0de44c7ebfafd96902a95743fcfbd59f10fffdaae2cc7dc3af7a5a60dc655a3639802c9471c3e758c4904285bba7e53118ed0f524adeb0757d25bd2f8e7b0d76dfa714cdd520f7aca8a8b917acc37f51de8f0c9bbe3ad858382e702dc25a12d09f7a85800") == 6900
#guard p256Verify (ofHex "bc691003939b33f22ac89afc39417969b3240c6fba15b987c3e9a576cdb15b0b93a3a1686593b7b992cae7fc2dd19983412beb4ff1c7c7d4a8fdc719a0de44c7140502686fd56a8cc03042a60ef000250eba32d16c1ff8dee5f3751f98cb2288471c3e758c4904285bba7e53118ed0f524adeb0757d25bd2f8e7b0d76dfa714cdd520f7aca8a8b917acc37f51de8f0c9bbe3ad858382e702dc25a12d09f7a858") == some (ofHex "0000000000000000000000000000000000000000000000000000000000000001")
#guard gas (ofHex "bc691003939b33f22ac89afc39417969b3240c6fba15b987c3e9a576cdb15b0b93a3a1686593b7b992cae7fc2dd19983412beb4ff1c7c7d4a8fdc719a0de44c7140502686fd56a8cc03042a60ef000250eba32d16c1ff8dee5f3751f98cb2288471c3e758c4904285bba7e53118ed0f524adeb0757d25bd2f8e7b0d76dfa714cdd520f7aca8a8b917acc37f51de8f0c9bbe3ad858382e702dc25a12d09f7a858") == 6900
#guard p256Verify (ofHex "bc691003939b33f22ac89afc39417969b3240c6fba15b987c3e9a576cdb15b0b93a3a1686593b7b992cae7fc2dd19983412beb4ff1c7c7d4a8fdc719a0de44c7ebfafd96902a95743fcfbd59f10fffdaae2cc7dc3af7a5a60dc655a3639802ca471c3e758c4904285bba7e53118ed0f524adeb0757d25bd2f8e7b0d76dfa714cdd520f7aca8a8b917acc37f51de8f0c9bbe3ad858382e702dc25a12d09f7a858") == some (ofHex "")
#guard gas (ofHex "bc691003939b33f22ac89afc39417969b3240c6fba15b987c3e9a576cdb15b0b93a3a1686593b7b992cae7fc2dd19983412beb4ff1c7c7d4a8fdc719a0de44c7ebfafd96902a95743fcfbd59f10fffdaae2cc7dc3af7a5a60dc655a3639802ca471c3e758c4904285bba7e53118ed0f524adeb0757d25bd2f8e7b0d76dfa714cdd520f7aca8a8b917acc37f51de8f0c9bbe3ad858382e702dc25a12d09f7a858") == 6900
#guard p256Verify (ofHex "bc691003939b33f22ac89afc39417969b3240c6fba15b987c3e9a576cdb15b0b93a3a1686593b7b992cae7fc2dd19983412beb4ff1c7c7d4a8fdc719a0de44c70000000000000000000000000000000000000000000000000000000000000000471c3e758c4904285bba7e53118ed0f524adeb0757d25bd2f8e7b0d76dfa714cdd520f7aca8a8b917acc37f51de8f0c9bbe3ad858382e702dc25a12d09f7a858") == some (ofHex "")
#guard gas (ofHex "bc691003939b33f22ac89afc39417969b3240c6fba15b987c3e9a576cdb15b0b93a3a1686593b7b992cae7fc2dd19983412beb4ff1c7c7d4a8fdc719a0de44c70000000000000000000000000000000000000000000000000000000000000000471c3e758c4904285bba7e53118ed0f524adeb0757d25bd2f8e7b0d76dfa714cdd520f7aca8a8b917acc37f51de8f0c9bbe3ad858382e702dc25a12d09f7a858") == 6900
#guard p256Verify (ofHex "bc691003939b33f22ac89afc39417969b3240c6fba15b987c3e9a576cdb15b0b93a3a1686593b7b992cae7fc2dd19983412beb4ff1c7c7d4a8fdc719a0de44c7ebfafd96902a95743fcfbd59f10fffdaae2cc7dc3af7a5a60dc655a3639802c900000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000") == some (ofHex "")
#guard gas (ofHex "bc691003939b33f22ac89afc39417969b3240c6fba15b987c3e9a576cdb15b0b93a3a1686593b7b992cae7fc2dd19983412beb4ff1c7c7d4a8fdc719a0de44c7ebfafd96902a95743fcfbd59f10fffdaae2cc7dc3af7a5a60dc655a3639802c900000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000") == 6900
#guard p256Verify (ofHex "bc691003939b33f22ac89afc39417969b3240c6fba15b987c3e9a576cdb15b0b93a3a1686593b7b992cae7fc2dd19983412beb4ff1c7c7d4a8fdc719a0de44c7ebfafd96902a95743fcfbd59f10fffdaae2cc7dc3af7a5a60dc655a3639802c9471c3e758c4904285bba7e53118ed0f524adeb0757d25bd2f8e7b0d76dfa714cdd520f7aca8a8b917acc37f51de8f0c9bbe3ad858382e702dc25a12d09f7a859") == some (ofHex "")
#guard gas (ofHex "bc691003939b33f22ac89afc39417969b3240c6fba15b987c3e9a576cdb15b0b93a3a1686593b7b992cae7fc2dd19983412beb4ff1c7c7d4a8fdc719a0de44c7ebfafd96902a95743fcfbd59f10fffdaae2cc7dc3af7a5a60dc655a3639802c9471c3e758c4904285bba7e53118ed0f524adeb0757d25bd2f8e7b0d76dfa714cdd520f7aca8a8b917acc37f51de8f0c9bbe3ad858382e702dc25a12d09f7a859") == 6900
#guard p256Verify (ofHex "00691003939b33f22ac89afc39417969b3240c6fba15b987c3e9a576cdb15b0b93a3a1686593b7b992cae7fc2dd19983412beb4ff1c7c7d4a8fdc719a0de44c7ebfafd96902a95743fcfbd59f10fffdaae2cc7dc3af7a5a60dc655a3639802c9471c3e758c4904285bba7e53118ed0f524adeb0757d25bd2f8e7b0d76dfa714cdd520f7aca8a8b917acc37f51de8f0c9bbe3ad858382e702dc25a12d09f7a858") == some (ofHex "")
#guard gas (ofHex "00691003939b33f22ac89afc39417969b3240c6fba15b987c3e9a576cdb15b0b93a3a1686593b7b992cae7fc2dd19983412beb4ff1c7c7d4a8fdc719a0de44c7ebfafd96902a95743fcfbd59f10fffdaae2cc7dc3af7a5a60dc655a3639802c9471c3e758c4904285bba7e53118ed0f524adeb0757d25bd2f8e7b0d76dfa714cdd520f7aca8a8b917acc37f51de8f0c9bbe3ad858382e702dc25a12d09f7a858") == 6900

end Solidity.Precompiles.P256
