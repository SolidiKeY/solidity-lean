import Solidity.Backend.Environment.ByteConstants
import Solidity.Storage.HashedKeccak
import Solidity.ERC7201
import Solidity.Precompiles.Basic

/-!
# Executable cryptographic instruction slices

KECCAK256 reads byte-addressed memory, never a symbolic hash instruction.
The argument memory is related to the existing intrinsic heap explicitly.
PUSH/SUB/MSTORE/SHR/SHL suffice for ERC-7201's exact two preimages. Existing
precompile computations are reused read-only; STATICCALL execution, output
copying, gas/failure handling and whole-world composition remain open.
-/
namespace Solidity.Backend.Environment

abbrev W256 := Fin (2 ^ 256)

theorem keccak_bound (bs : List UInt8) : Keccak.keccak256Nat (bs.map UInt8.toNat) < 2 ^ 256 := by
  have hb := Storage.keccak256_bytes (bs.map UInt8.toNat)
  have h1 := Storage.ofBytes_lt hb.1
  have h2 : 256 ^ (Keccak.keccak256 (bs.map UInt8.toNat)).length ≤ 256 ^ 32 :=
    Nat.pow_le_pow_right (by decide) hb.2
  change Keccak.ofBytes (Keccak.keccak256 (bs.map UInt8.toNat)) < 2 ^ 256
  have he : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
  omega

def digest (bs : List UInt8) : Word := lenU (Keccak.keccak256Nat (bs.map UInt8.toNat)) (keccak_bound bs)

theorem digest_nat (bs : List UInt8) :
    (digest bs).1.toNat = Keccak.keccak256Nat (bs.map UInt8.toNat) := by
  simp only [digest, lenU, Int.toNat_natCast]

def wireBytes (bs : List Int) : List UInt8 := bs.map fun b => UInt8.ofNat (b.toNat % 256)

theorem wireBytes_values (bs : List Int) :
    (wireBytes bs).map UInt8.toNat = bs.map (fun b => b.toNat % 256) := by
  simp only [wireBytes, List.map_map]
  apply List.map_congr_left
  intro b _
  simp only [Function.comp_apply, UInt8.toNat_ofNat', Nat.mod_mod]

/-- The intrinsic Keccak value is the actual computed word, with no new hash
premise. Its defensive out-of-range branch is unreachable by the committed bound. -/
theorem source_digest (bs : List Int) : keccakBytes bs = digest (wireBytes bs) := by
  have h := keccak_bound (wireBytes bs)
  rw [wireBytes_values] at h
  apply Subtype.ext
  simp only [keccakBytes, dif_pos h, digest, lenU, wireBytes_values]

/-- Word interpretation shared with G06's concrete fixed-function instance. -/
theorem digest_fixed (bs : List UInt8) : digest bs |>.1.toNat = Roadmap.Evm.keccakWord bs := by
  simp only [digest, lenU, Int.toNat_natCast, Roadmap.Evm.keccakWord,
    Nat.mod_eq_of_lt (keccak_bound bs)]

def wrap (n : Nat) : Word := lenU (n % 2 ^ 256) (Nat.mod_lt _ (by decide))

theorem wrap_nat (n : Nat) : (wrap n).1.toNat = n % 2 ^ 256 := by
  simp only [wrap, lenU, Int.toNat_natCast]

def cryptoStep : Instr → Slice → Option Slice
  | .push _ imm, s => some { s with stack := uintOfNat (ofBytesBE imm.toList) :: s.stack }
  | .op .KECCAK256, { stack := off :: len :: tail, memory := m } =>
      some ⟨digest (readMemory m off.1.toNat len.1.toNat) :: tail, m⟩
  | .op .SUB, { stack := a :: b :: tail, memory := m } =>
      some ⟨wrap (a.1.toNat + 2 ^ 256 - b.1.toNat) :: tail, m⟩
  | .op .MSTORE, { stack := off :: value :: tail, memory := m } =>
      some ⟨tail, writeBytes m off.1.toNat (Semantics.wordBytes value.1.toNat)⟩
  | .op .SHR, { stack := shift :: value :: tail, memory := m } =>
      some ⟨wrap (value.1.toNat / 2 ^ shift.1.toNat) :: tail, m⟩
  | .op .SHL, { stack := shift :: value :: tail, memory := m } =>
      some ⟨wrap (value.1.toNat * 2 ^ shift.1.toNat) :: tail, m⟩
  | _, _ => none

def runCrypto : List Instr → Slice → Option Slice
  | [], s => some s
  | i :: code, s => (cryptoStep i s).bind (runCrypto code)

theorem runCrypto_append (a b : List Instr) (s : Slice) :
    runCrypto (a ++ b) s = (runCrypto a s).bind (runCrypto b) := by
  induction a generalizing s with
  | nil => rfl
  | cons i a ih =>
    simp only [List.cons_append, runCrypto, Option.bind_assoc]
    cases cryptoStep i s with
    | none => rfl
    | some t => exact ih t

theorem cryptoStep_constant (width : Fin 33) (v : Fin (256 ^ width.val)) (s : Slice) :
    cryptoStep (constant width v) s =
      some { s with stack := lenU v.val (constant_bound width v) :: s.stack } := by
  simp only [constant, cryptoStep, ofBytesBE_toBytesBE _ _ v.isLt,
    uintOfNat_eq_lenU (constant_bound width v)]

def push256 (v : W256) : Instr := constant 32 ⟨v.val, v.isLt⟩

def keccakCode (offset length : W256) : List Instr :=
  [push256 length, push256 offset, .op .KECCAK256]

/-- Exact byte/preimage and stack-tail law for executable KECCAK256. -/
theorem keccak_correct (offset length : W256) (s : Slice) :
    runCrypto (keccakCode offset length) s =
      some { s with stack := digest (readMemory s.memory offset.val length.val) :: s.stack } := by
  simp only [keccakCode, push256, runCrypto, cryptoStep_constant, Option.bind_some]
  simp only [cryptoStep, lenU, Int.toNat_natCast, Option.bind_some]

/-- Nonwrapping representation of one already-evaluated argument's exact bytes.
The surrounding memory compiler owns allocation and source-object layout. -/
structure HashInput (s : Slice) (offset length : W256) (bs : List Int) : Prop where
  fits : offset.val + length.val ≤ 2 ^ 256
  bytes : readMemory s.memory offset.val length.val = wireBytes bs

/-- The existing memory path is evaluated once, before the target hash. The
source oracle, ledger, locals and heap are unrestricted except exact argument
representation. Failure never becomes successful target hashing. -/
theorem intrinsic_keccak {C : Contract} {Γ : Ctx} {R : RefTy}
    (σ : State C Γ) (b : MPath C Γ (.ref R)) (r : HRef σ.H R)
    (evaluated : b.mvalT σ = .ok r) (offset length : W256) (s : Slice)
    (input : HashInput s offset length (MObj.words R (σ.heap.get r))) :
    Val.evalT σ (.hash .keccak b rfl : Val C Γ .uint) = .ok (σ.heap.hash .keccak r) ∧
    runCrypto (keccakCode offset length) s =
      some { s with stack := σ.heap.hash .keccak r :: s.stack } := by
  constructor
  · change (b.mvalT σ >>= fun r => pure (σ.heap.hash .keccak r)) = _
    rw [evaluated]
    rfl
  · rw [keccak_correct, input.bytes, ← source_digest]
    rfl

/-- Preserve failed argument resolution as its exact intrinsic halt. -/
theorem intrinsic_hash_failure {C : Contract} {Γ : Ctx} {R : RefTy}
    (σ : State C Γ) (b : MPath C Γ (.ref R)) (k : HashKind) (halt : THalt)
    (failed : b.mvalT σ = .error halt) :
    Val.evalT σ (.hash k b rfl : Val C Γ .uint) = .error halt := by
  change (b.mvalT σ >>= fun r => pure (σ.heap.hash k r)) = _
  rw [failed]
  rfl

/-- Existing read-only precompile computations; no world-code oracle is used. -/
def precompileResult (k : HashKind) (bs : List UInt8) : Option (List UInt8) :=
  match k with
  | .keccak => none
  | .sha256 => Precompiles.sha256 bs
  | .ripemd160 => Precompiles.ripemd160 bs
  | .ecrecover => Precompiles.ecrecover bs

def precompileAddress : HashKind → Option W256
  | .keccak => none
  | .sha256 => some ⟨2, by decide⟩
  | .ripemd160 => some ⟨3, by decide⟩
  | .ecrecover => some ⟨1, by decide⟩

/-- Actual STATICCALL operand prefix. GAS is only forwarding machinery and is
not exposed as a source observation. Return memory must be zero initialized
for ecrecover's empty result. Call success/failure and loading the return word
are intentionally left to the reserved CALL/precompile composition work. -/
def precompilePrefix (address inputOffset inputLength outputOffset : W256) : List Instr :=
  [push256 ⟨32, by decide⟩, push256 outputOffset, push256 inputLength,
   push256 inputOffset, push256 address]

def precompileCode (address inputOffset inputLength outputOffset : W256) : List Instr :=
  precompilePrefix address inputOffset inputLength outputOffset ++
    [.op .GAS, .op .STATICCALL, .op .POP, push256 outputOffset, .op .MLOAD]

theorem precompile_operands (address inputOffset inputLength outputOffset : W256) (s : Slice) :
    runCrypto (precompilePrefix address inputOffset inputLength outputOffset) s =
      some ⟨[lenU address.val address.isLt, lenU inputOffset.val inputOffset.isLt,
        lenU inputLength.val inputLength.isLt, lenU outputOffset.val outputOffset.isLt,
        lenU 32 (by decide)] ++ s.stack, s.memory⟩ := by
  simp only [precompilePrefix, push256, runCrypto, cryptoStep_constant, Option.bind_some]
  rfl

/-- Builtin lowering is executable bytecode, selected only after the intrinsic
argument path resolves. No invented symbolic crypto instruction is returned. -/
def builtinCode (k : HashKind) (offset length output : W256) : List Instr :=
  match precompileAddress k with
  | none => keccakCode offset length
  | some address =>
      if k = .ecrecover ∧ length.val ≠ 128 then [constant 0 ⟨0, by decide⟩]
      else precompileCode address offset length output

def lowerHash {C : Contract} {Γ : Ctx} {R : RefTy}
    (σ : State C Γ) (b : MPath C Γ (.ref R)) (k : HashKind)
    (offset output : W256) : TRes (List Instr) := do
  let r ← b.mvalT σ
  pure (builtinCode k offset
    ⟨(MObj.words R (σ.heap.get r)).length % 2 ^ 256, Nat.mod_lt _ (by decide)⟩ output)

theorem lowerHash_failure {C : Contract} {Γ : Ctx} {R : RefTy}
    (σ : State C Γ) (b : MPath C Γ (.ref R)) (k : HashKind) (offset output : W256)
    (halt : THalt) (failed : b.mvalT σ = .error halt) :
    lowerHash σ b k offset output = .error halt := by
  unfold lowerHash
  rw [failed]
  rfl

theorem HashInput.length_eq {s : Slice} {offset length : W256} {bs : List Int}
    (h : HashInput s offset length bs) : bs.length = length.val := by
  have e := congrArg List.length h.bytes
  simp only [readMemory, wireBytes, List.length_map, List.length_range] at e
  exact e.symm

theorem lowerHash_success {C : Contract} {Γ : Ctx} {R : RefTy}
    (σ : State C Γ) (b : MPath C Γ (.ref R)) (r : HRef σ.H R)
    (evaluated : b.mvalT σ = .ok r) (k : HashKind) (offset length output : W256)
    (s : Slice) (input : HashInput s offset length (MObj.words R (σ.heap.get r))) :
    lowerHash σ b k offset output = .ok (builtinCode k offset length output) := by
  unfold lowerHash
  rw [evaluated]
  change Except.ok (builtinCode k offset _ output) = _
  have e : (⟨(MObj.words R (σ.heap.get r)).length % 2 ^ 256,
      Nat.mod_lt _ (by decide)⟩ : W256) = length := by
    apply Fin.ext
    change (MObj.words R (σ.heap.get r)).length % 2 ^ 256 = length.val
    rw [input.length_eq, Nat.mod_eq_of_lt length.isLt]
  rw [e]

theorem ecrecover_wrong_length (bs : List Int) (h : bs.length ≠ 128) :
    HashKind.apply .ecrecover bs = uintOfNat 0 := by
  simp only [HashKind.apply, ecrecoverBytes, List.length_map, h, false_and, if_false]

/-- Read-only precompile input is the very same byte sequence, in order. -/
theorem precompile_preimage (s : Slice) (offset length : W256) (bs : List Int)
    (h : HashInput s offset length bs) (k : HashKind) :
    precompileResult k (readMemory s.memory offset.val length.val) =
      precompileResult k (wireBytes bs) := by rw [h.bytes]

end Solidity.Backend.Environment
