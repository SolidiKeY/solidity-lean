import Solidity.Backend.Environment.Crypto

/-!
# ERC-7201 executable slice

Two actual memory KECCAK256 instructions, wrapping subtraction and an exact
big-endian MSTORE word. SHR/SHL clear the low byte without inventing a hash
instruction. The scratch interval is caller-owned and may overlap the consumed
input (the first hash precedes its write). Source-object allocation and the
pinned EVM/gas correspondence are outside this instruction-slice certificate.
-/
namespace Solidity.Backend.Environment

def predecessorWord (bs : List UInt8) : Word :=
  wrap ((digest bs).1.toNat + 2 ^ 256 - 1)

def namespacePreimage (bs : List UInt8) : List UInt8 :=
  Semantics.wordBytes (predecessorWord bs).1.toNat

theorem namespace_preimage (bs : List UInt8) :
    namespacePreimage bs = Semantics.wordBytes
      (ERC7201.predecessor (Keccak.keccak256Nat (bs.map UInt8.toNat))).val := by
  simp only [namespacePreimage, predecessorWord, wrap_nat, digest, lenU,
    Int.toNat_natCast, ERC7201.predecessor]

theorem wordBytes_length (n : Nat) : (Semantics.wordBytes n).length = 32 := by
  simp only [Semantics.wordBytes, List.length_map, List.length_range]

def clearByte (w : Word) : Word := wrap ((wrap (w.1.toNat / 256)).1.toNat * 256)

theorem clearByte_value (w : Word) : (clearByte w).1 = (w.1.toNat / 256 * 256 : Nat) := by
  have hw : 0 ≤ w.1 ∧ w.1 < ((2 ^ 256 : Nat) : Int) := of_decide_eq_true w.2
  have hn : w.1.toNat < 2 ^ 256 := by omega
  have hq : w.1.toNat / 256 < 2 ^ 256 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn
  have hp : w.1.toNat / 256 * 256 < 2 ^ 256 := Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hn
  simp only [clearByte, wrap_nat, Nat.mod_eq_of_lt hq]
  simp only [wrap, lenU, Nat.mod_eq_of_lt hp]

/-- The exact numeric root formula, using the existing implementation read-only. -/
theorem root_value (bs : List UInt8) :
    (ERC7201.root bs).val =
      Keccak.keccak256Nat ((namespacePreimage bs).map UInt8.toNat) / 256 * 256 := by
  have h : Keccak.keccak256Nat ((namespacePreimage bs).map UInt8.toNat) < 2 ^ 256 :=
    keccak_bound (namespacePreimage bs)
  rw [namespace_preimage] at h
  simp only [ERC7201.root, ERC7201.align, Nat.mod_eq_of_lt h, namespace_preimage]

/-- Clearing the low byte of the second actual digest is exactly the committed
ERC7201.root; no collision/injectivity or disjointness premise is used. -/
theorem namespace_result (bs : List UInt8) :
    clearByte (digest (namespacePreimage bs)) =
      lenU (ERC7201.root bs).val (ERC7201.root bs).isLt := by
  apply Subtype.ext
  rw [clearByte_value, digest_nat, ← root_value]
  rfl

def namespaceSuffix (scratch : W256) : List Instr :=
  [.op .SUB, push256 scratch, .op .MSTORE] ++
    keccakCode scratch ⟨32, by decide⟩ ++
    [constant 1 ⟨8, by decide⟩, .op .SHR, constant 1 ⟨8, by decide⟩, .op .SHL]

def namespaceCode (offset length scratch : W256) : List Instr :=
  [constant 1 ⟨1, by decide⟩] ++ keccakCode offset length ++ namespaceSuffix scratch

/-- Exact intermediate word and byte preimage for the second KECCAK. -/
theorem namespace_suffix_correct (scratch : W256) (bs : List UInt8) (s : Slice) :
    runCrypto (namespaceSuffix scratch)
      { s with stack := digest bs :: lenU 1 (by decide) :: s.stack } =
    some ⟨clearByte (digest (namespacePreimage bs)) :: s.stack,
      writeBytes s.memory scratch.val (namespacePreimage bs)⟩ := by
  simp only [namespaceSuffix, List.cons_append, List.nil_append, runCrypto,
    cryptoStep_constant, push256, Option.bind_some]
  simp only [cryptoStep, lenU, Int.toNat_natCast, Option.bind_some]
  change runCrypto (keccakCode scratch ⟨32, by decide⟩ ++
      [constant 1 ⟨8, by decide⟩, .op .SHR, constant 1 ⟨8, by decide⟩, .op .SHL])
      ⟨s.stack, writeBytes s.memory scratch.val (namespacePreimage bs)⟩ = _
  rw [runCrypto_append, keccak_correct]
  have hr : readMemory (writeBytes s.memory scratch.val (namespacePreimage bs)) scratch.val 32 =
      namespacePreimage bs := by
    simpa only [namespacePreimage, wordBytes_length] using
      read_written (namespacePreimage bs) scratch.val s.memory
  simp only [hr, Option.bind_some, runCrypto, cryptoStep_constant]
  simp only [cryptoStep, lenU, Int.toNat_natCast, Option.bind_some]
  rfl

/-- Full local instruction-slice certificate, arbitrary input bytes/memory/tail.
The caller must supply gas/stack room and an owned scratch interval; the exact
nonwrapping resource interval is recorded separately in NamespaceInput. -/
theorem namespace_correct (offset length scratch : W256) (s : Slice) :
    runCrypto (namespaceCode offset length scratch) s =
      some ⟨lenU (ERC7201.root (readMemory s.memory offset.val length.val)).val
          (ERC7201.root (readMemory s.memory offset.val length.val)).isLt :: s.stack,
        writeBytes s.memory scratch.val
          (namespacePreimage (readMemory s.memory offset.val length.val))⟩ := by
  simp only [namespaceCode, runCrypto_append]
  simp only [runCrypto, cryptoStep_constant, Option.bind_some]
  rw [keccak_correct]
  simp only [Option.bind_some, namespace_suffix_correct, namespace_result]

structure NamespaceInput (s : Slice) (offset length scratch : W256) (bs : List UInt8) : Prop where
  inputFits : offset.val + length.val ≤ 2 ^ 256
  scratchFits : scratch.val + 32 ≤ 2 ^ 256
  bytes : readMemory s.memory offset.val length.val = bs

/-- Resolved source namespace bytes produce the exact existing root. -/
theorem namespace_source (offset length scratch : W256) (s : Slice) (bs : List UInt8)
    (input : NamespaceInput s offset length scratch bs) :
    runCrypto (namespaceCode offset length scratch) s =
      some ⟨lenU (ERC7201.root bs).val (ERC7201.root bs).isLt :: s.stack,
        writeBytes s.memory scratch.val (namespacePreimage bs)⟩ := by
  rw [namespace_correct, input.bytes]

end Solidity.Backend.Environment
