import Solidity.Backend.Assembler
import Solidity.Backend.Environment.Observations

/-!
# Typed metadata constants and byte alignment

Reuse committed ABI declaration metadata and assembler big-endian immediates.
The intrinsic frontend stores selectors as low numeric uints. ABI bytes4 uses
left alignment separately; confusing these conventions is observably wrong.
This module does not resolve declarations, assume selector uniqueness, or accept
raw msg.sig/code observations. Resource conditions are those of Observations.
-/
namespace Solidity.Backend.Environment

/-- A typed constant always fits its actual PUSH width. -/
def constant (width : Fin 33) (value : Fin (256 ^ width.val)) : Instr :=
  .push width (toBytesBE width.val value.val)

/-- Independent PUSH meaning: read immediate bytes big-endian, zero extend.
This evaluator is only the PUSH slice; other instructions are refused. -/
def pushStep : Instr → List Word → Option (List Word)
  | .push _ imm, tail => some (uintOfNat (ofBytesBE imm.toList) :: tail)
  | _, _ => none

theorem constant_bound (width : Fin 33) (value : Fin (256 ^ width.val)) :
    value.val < 2 ^ 256 := by
  have hp : 256 ^ width.val ≤ 256 ^ 32 :=
    Nat.pow_le_pow_right (by decide) (by omega : width.val ≤ 32)
  have he : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
  omega

/-- Exact bytes, zero extension, and arbitrary stack-tail preservation. -/
theorem constant_correct (width : Fin 33) (value : Fin (256 ^ width.val))
    (tail : List Word) :
    pushStep (constant width value) tail =
      some (lenU value.val (constant_bound width value) :: tail) := by
  simp only [constant, pushStep, ofBytesBE_toBytesBE _ _ value.isLt,
    uintOfNat_eq_lenU (constant_bound width value)]

/-- Explicit truncation at a chosen metadata width, including PUSH0. -/
def truncateCode (width : Fin 33) (value : Nat) : Instr :=
  constant width ⟨value % 256 ^ width.val, Nat.mod_lt _ (Nat.pow_pos (by decide))⟩

theorem truncate_correct (width : Fin 33) (value : Nat) (tail : List Word) :
    pushStep (truncateCode width value) tail =
      some (uintOfNat (value % 256 ^ width.val) :: tail) := by
  simp only [truncateCode, constant, pushStep,
    ofBytesBE_toBytesBE _ _ (Nat.mod_lt _ (Nat.pow_pos (by decide)))]

/-- Increasing the PUSH width only zero extends a bounded value. -/
theorem zero_extension (small large : Fin 33) (n : Nat)
    (hs : n < 256 ^ small.val) (hl : n < 256 ^ large.val) (tail : List Word) :
    pushStep (constant small ⟨n, hs⟩) tail =
      pushStep (constant large ⟨n, hl⟩) tail := by
  simp only [constant, pushStep, ofBytesBE_toBytesBE _ _ hs,
    ofBytesBE_toBytesBE _ _ hl]

/-- Read the committed canonical selector, never a generated model name. -/
def metadataSelector (d : SourceFunction) : Option (Fin (2 ^ 32)) :=
  match d.callable with
  | .abi _ _ s => s
  | .getter s => some s
  | _ => none

/-- Missing canonical ABI metadata is refused; signatures are not guessed. -/
def declarationCode (d : SourceFunction) : Option Instr :=
  (metadataSelector d).map fun s => constant 4 ⟨s.val, by
    have h := s.isLt
    change s.val < 4294967296
    exact h⟩

def selectorCode (s : Fin (2 ^ 32)) : Instr :=
  constant 4 ⟨s.val, by have h := s.isLt; change s.val < 4294967296; exact h⟩

def selectorWord (s : Fin (2 ^ 32)) : Word := lenU s.val (by have h := s.isLt; omega)

theorem selector_correct (s : Fin (2 ^ 32)) (tail : List Word) :
    pushStep (selectorCode s) tail = some (selectorWord s :: tail) :=
  constant_correct _ _ tail

/-- ABI encoding of a bytes4, unlike its intrinsic numeric value. -/
def selectorAbiValue (s : Fin (2 ^ 32)) : Fin (256 ^ 32) :=
  ⟨s.val * 2 ^ 224, by have h := s.isLt; change s.val * 2 ^ 224 < 2 ^ 256; omega⟩

def selectorAbiCode (s : Fin (2 ^ 32)) : Instr := constant 32 (selectorAbiValue s)

theorem selector_alignment (s : Fin (2 ^ 32)) :
    (selectorAbiValue s).val / 2 ^ 224 = s.val ∧
    (selectorAbiValue s).val % 2 ^ 224 = 0 := by
  exact ⟨Nat.mul_div_left _ (by decide : 0 < (2 : Nat) ^ 224), Nat.mul_mod_left _ _⟩

/-- Actual bytes of the ABI immediate read to the left-aligned value. -/
theorem selector_abi_bytes (s : Fin (2 ^ 32)) :
    ofBytesBE (toBytesBE 32 (selectorAbiValue s).val).toList = s.val * 2 ^ 224 :=
  ofBytesBE_toBytesBE _ _ (selectorAbiValue s).isLt

/-- Generic bytesN source metadata: low numeric value, no lossy Int conversion. -/
def metadataBytes (width : Fin 33) (v : Fin (256 ^ width.val)) : Instr := constant width v

/-- Function receiver identities remain bounded to 160 bits and zero extended. -/
def addressCode (a : Address) : Instr :=
  constant 20 ⟨a.1.1.toNat, by have h := a.2; change a.1.1.toNat < 2 ^ 160; omega⟩

theorem address_correct (a : Address) (tail : List Word) :
    pushStep (addressCode a) tail = some (a.1 :: tail) := by
  rw [show addressCode a = constant 20 _ from rfl, constant_correct]
  congr 2
  apply Subtype.ext
  exact Int.toNat_of_nonneg (of_decide_eq_true a.1.2).1

/-- The existing source external-function representation: address above selector.
No new function-value IR is introduced. -/
def packedFunction (a : Address) (s : Fin (2 ^ 32)) : Fin (256 ^ 24) :=
  ⟨a.1.1.toNat * 2 ^ 32 + s.val, by
    have ha := a.2
    have hs := s.isLt
    change a.1.1.toNat * 2 ^ 32 + s.val < 2 ^ 192
    omega⟩

def functionCode (a : Address) (s : Fin (2 ^ 32)) : Instr := constant 24 (packedFunction a s)

theorem function_projections (a : Address) (s : Fin (2 ^ 32)) :
    (packedFunction a s).val / 2 ^ 32 = a.1.1.toNat ∧
    (packedFunction a s).val % 2 ^ 32 = s.val := by
  have hs := s.isLt
  dsimp only [packedFunction]
  omega

theorem function_correct (a : Address) (s : Fin (2 ^ 32)) (tail : List Word) :
    pushStep (functionCode a s) tail =
      some (lenU (packedFunction a s).val (constant_bound 24 _) :: tail) :=
  constant_correct _ _ tail

/-- Declaration resolution precedes this boundary. Exactly the supplied,
bounded metadata selector is emitted. -/
theorem declaration_correct (d : SourceFunction) (s : Fin (2 ^ 32))
    (resolved : metadataSelector d = some s) (tail : List Word) :
    declarationCode d = some (selectorCode s) ∧
    pushStep (selectorCode s) tail = some (selectorWord s :: tail) := by
  constructor
  · simp only [declarationCode, resolved, Option.map_some]
    rfl
  · exact selector_correct s tail

/-- Integer type-bound metadata retains its intrinsic signedness. The target
word uses the committed ABI two's-complement operation, not a Nat cast of a
possibly negative source value. -/
def typedConstant {p : PrimTy} (value : p.Denote) : Instr :=
  let word := PrimTy.toWord value
  constant 32 ⟨word.1.toNat, by
    have h := of_decide_eq_true word.2
    change word.1.toNat < 2 ^ 256
    omega⟩

theorem typed_constant_correct {p : PrimTy} (value : p.Denote) (tail : List Word) :
    pushStep (typedConstant value) tail = some (PrimTy.toWord value :: tail) := by
  unfold typedConstant
  rw [constant_correct]
  congr 2
  apply Subtype.ext
  exact Int.toNat_of_nonneg (of_decide_eq_true (PrimTy.toWord value).2).1

theorem typed_literal_intrinsic {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (p : PrimTy) (n : Int) (inRange : p.inRange n = true) (tail : List Word) :
    Val.evalT σ (.simple (.lit n inRange) : Val C Γ p) = .ok (PrimTy.ofLit p n inRange) ∧
    pushStep (typedConstant (PrimTy.ofLit p n inRange)) tail =
      some (PrimTy.toWord (PrimTy.ofLit p n inRange) :: tail) :=
  ⟨rfl, typed_constant_correct _ tail⟩

/-- Metadata literals agree with the pre-existing typed literal denotation. -/
theorem selector_intrinsic {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (s : Fin (2 ^ 32)) (tail : List Word) :
    Val.evalT σ (.simple (.lit (selectorWord s).1 (selectorWord s).2) : Val C Γ .uint) =
      .ok (selectorWord s) ∧
    pushStep (selectorCode s) tail = some (selectorWord s :: tail) :=
  ⟨rfl, selector_correct s tail⟩

end Solidity.Backend.Environment
