import Solidity.Backend.Environment.Metadata

/-!
# Byte-valued metadata instruction slices

A target-only, byte-addressed memory view for exact metadata materialization.
This does not replace intrinsic source state/heap or the reserved EVM memory
compiler. Only PUSH and MSTORE8 are interpreted, without gas/stack exceptions.
The caller owns the written interval; all other memory is framed.
-/
namespace Solidity.Backend.Environment

abbrev Memory := Nat → UInt8

structure Slice where
  stack : List Word
  memory : Memory

def writeByte (m : Memory) (offset : Nat) (b : UInt8) : Memory :=
  fun i => if i = offset then b else m i

def writeBytes : Memory → Nat → List UInt8 → Memory
  | m, _, [] => m
  | m, offset, b :: bs => writeBytes (writeByte m offset b) (offset + 1) bs

/-- MSTORE8 takes offset first, then the low byte of its value. -/
def dataStep : Instr → Slice → Option Slice
  | .push _ imm, s => some { s with stack := uintOfNat (ofBytesBE imm.toList) :: s.stack }
  | .op .MSTORE8, { stack := offset :: value :: tail, memory := m } =>
      some ⟨tail, writeByte m offset.1.toNat (UInt8.ofNat value.1.toNat)⟩
  | _, _ => none

def runData : List Instr → Slice → Option Slice
  | [], s => some s
  | i :: code, s => (dataStep i s).bind (runData code)

theorem runData_append (a b : List Instr) (s : Slice) :
    runData (a ++ b) s = (runData a s).bind (runData b) := by
  induction a generalizing s with
  | nil => rfl
  | cons i a ih =>
    simp only [List.cons_append, runData, Option.bind_assoc]
    cases dataStep i s with
    | none => rfl
    | some t => exact ih t

theorem dataStep_constant (width : Fin 33) (v : Fin (256 ^ width.val)) (s : Slice) :
    dataStep (constant width v) s =
      some { s with stack := lenU v.val (constant_bound width v) :: s.stack } := by
  simp only [constant, dataStep, ofBytesBE_toBytesBE _ _ v.isLt,
    uintOfNat_eq_lenU (constant_bound width v)]

/-- One real PUSH1/PUSH32/MSTORE8 byte store. Offsets wrap only in selection;
materialize_correct below proves wrapping is absent in the owned interval. -/
def byteCode (offset : Fin (2 ^ 256)) (b : UInt8) : List Instr :=
  [constant 1 ⟨b.toNat, by have h : b.toNat < 256 := b.toNat_lt; exact h⟩,
   constant 32 ⟨offset.val, by have h : offset.val < 2 ^ 256 := offset.isLt; exact h⟩, .op .MSTORE8]

theorem byteCode_correct (offset : Fin (2 ^ 256)) (b : UInt8) (s : Slice) :
    runData (byteCode offset b) s =
      some { s with memory := writeByte s.memory offset.val b } := by
  simp only [byteCode, runData, dataStep_constant, Option.bind_some]
  simp only [dataStep, lenU, Int.toNat_natCast, UInt8.ofNat_toNat, Option.bind_some]

/-- Statically resolved bytes (including UTF-8 type names) become executable
stores, rather than a symbolic byte-string instruction. -/
def materialize : Nat → List UInt8 → List Instr
  | _, [] => []
  | offset, b :: bs => byteCode ⟨offset % 2 ^ 256, Nat.mod_lt _ (by decide)⟩ b ++
      materialize (offset + 1) bs

theorem materialize_correct (bs : List UInt8) (offset : Nat) (s : Slice)
    (fits : offset + bs.length ≤ 2 ^ 256) :
    runData (materialize offset bs) s =
      some { s with memory := writeBytes s.memory offset bs } := by
  induction bs generalizing offset s with
  | nil => rfl
  | cons b bs ih =>
    have ho : offset < 2 ^ 256 := by simp only [List.length_cons] at fits; omega
    have hn : offset + 1 + bs.length ≤ 2 ^ 256 := by
      simp only [List.length_cons] at fits
      omega
    simp only [materialize, runData_append, byteCode_correct, Nat.mod_eq_of_lt ho,
      Option.bind_some, ih _ _ hn, writeBytes]

/-- A UTF-8 name constant is bytes, with no claim that this function resolves
its declaration. The importer supplies the resolved name before this boundary. -/
def nameCode (resolvedName : String) (offset : Nat) : List Instr :=
  materialize offset resolvedName.toUTF8.data.toList

theorem name_correct (name : String) (offset : Nat) (s : Slice)
    (fits : offset + name.toUTF8.data.toList.length ≤ 2 ^ 256) :
    runData (nameCode name offset) s =
      some { s with memory := writeBytes s.memory offset name.toUTF8.data.toList } :=
  materialize_correct _ _ _ fits

/-- No byte outside the written interval changes. -/
theorem writeBytes_frame (bs : List UInt8) (offset i : Nat) (m : Memory)
    (outside : i < offset ∨ offset + bs.length ≤ i) :
    writeBytes m offset bs i = m i := by
  induction bs generalizing offset m with
  | nil => rfl
  | cons b bs ih =>
    have hi : i ≠ offset := by simp only [List.length_cons] at outside; omega
    have hn : i < offset + 1 ∨ offset + 1 + bs.length ≤ i := by
      simp only [List.length_cons] at outside
      omega
    rw [writeBytes, ih _ _ hn]
    exact if_neg hi

/-- Every materialized byte is observed in its original order. -/
theorem writeBytes_at (bs : List UInt8) (offset j : Nat) (m : Memory)
    (inside : j < bs.length) : writeBytes m offset bs (offset + j) = bs[j] := by
  induction bs generalizing offset j m with
  | nil => simp only [List.length_nil] at inside; omega
  | cons b bs ih =>
    cases j with
    | zero =>
      change writeBytes (writeByte m offset b) (offset + 1) bs offset = b
      rw [writeBytes_frame bs (offset + 1) offset _ (Or.inl (by omega))]
      exact if_pos rfl
    | succ j =>
      have hj : j < bs.length := by simp only [List.length_cons] at inside; omega
      rw [writeBytes, show offset + (j + 1) = offset + 1 + j by omega]
      exact ih _ _ _ hj

def readMemory (m : Memory) (offset length : Nat) : List UInt8 :=
  (List.range length).map fun i => m (offset + i)

theorem read_written (bs : List UInt8) (offset : Nat) (m : Memory) :
    readMemory (writeBytes m offset bs) offset bs.length = bs := by
  apply List.ext_getElem
  · simp only [readMemory, List.length_map, List.length_range]
  · intro i _ hi
    simp only [readMemory, List.getElem_map, List.getElem_range,
      writeBytes_at bs offset i m hi]

end Solidity.Backend.Environment
