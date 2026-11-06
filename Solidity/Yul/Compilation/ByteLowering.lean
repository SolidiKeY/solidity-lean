import Solidity.Yul.Compilation.ClzLowering

/-! Compiler output over existing standard bit-vector extraction. This is not
a second source Yul builtin table, AST or state. Actual source/driver bindings
remain separate obligations. Big-endian index0 selects the high byte. -/
namespace Solidity.Yul.Compilation
open Backend Scalar

/-- Existing standard extraction, widened back to the target word. -/
def byteWindow (shift : Nat) (value : Word) : Word :=
  (value.extractLsb' shift 8).zeroExtend 256

theorem byteWindow_mask (shift : Nat) (value : Word) :
    (value >>> shift) &&& (255 : Word) = byteWindow shift value := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, byteWindow,
    BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat]
  change (value.toNat >>> shift) &&& (2 ^ 8 - 1) =
    ((value.toNat >>> shift) % 2 ^ 8) % 2 ^ 256
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact (Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide : 0 < 2 ^ 8))
    (by decide : 2 ^ 8 < 2 ^ 256))).symm

/-- Compiler result specification using standard extraction, not source semantics.
The complete index word is tested before choosing its big-endian bit window. -/
def indexedByteWindow (index value : Word) : Word :=
  if index.toNat < 32 then byteWindow (8 * (31 - index.toNat)) value else 0

private def byteShift : BinarySelection := (selectBinaryOpcode .SHR).getD selectDiv
private def byteLess : BinarySelection := (selectBinaryOpcode .LT).getD selectAdd

/-- The guarded pure expansion may evaluate its arithmetic eagerly. No source
call/effect/nondeterminism is accepted by this total-expression interface. -/
def byteExpression : LoweredExpr 2 (fun l => indexedByteWindow l[0] l[1]) :=
  let index := lowerLocal (n := 2) ⟨0, by decide⟩
  let value := lowerLocal (n := 2) ⟨1, by decide⟩
  let shift := lowerBinary selectMul (lowerSmallLiteral 8)
    (lowerBinary selectSub (lowerSmallLiteral 31) index)
  let raw := lowerBinary selectMul (lowerBinary byteLess index (lowerSmallLiteral 32))
    (lowerBinary selectAnd (lowerBinary byteShift shift value) (lowerSmallLiteral 255))
  raw.congr (by
    intro locals
    change flag (decide (locals[0].toNat < 32)) *
      ((if ((8 : Word) * ((31 : Word) - locals[0])).toNat < 256
        then locals[1] >>> ((8 : Word) * ((31 : Word) - locals[0])).toNat else 0) &&& 255) =
      indexedByteWindow locals[0] locals[1]
    unfold indexedByteWindow
    by_cases hi : locals[0].toNat < 32
    · have order : locals[0] ≤ (31 : Word) := by
        rw [BitVec.le_def]
        change locals[0].toNat ≤ 31
        omega
      have small : 8 * (31 - locals[0].toNat) < 256 := by omega
      have count : ((8 : Word) * ((31 : Word) - locals[0])).toNat =
          8 * (31 - locals[0].toNat) := by
        rw [BitVec.toNat_mul, BitVec.toNat_sub_of_le order]
        change (8 * (31 - locals[0].toNat)) % 2 ^ 256 = _
        exact Nat.mod_eq_of_lt (Nat.lt_trans small (by decide : 256 < 2 ^ 256))
      simp only [flag, hi, decide_true, ite_true]
      rw [count, if_pos small]
      exact (BitVec.one_mul _).trans (byteWindow_mask (8 * (31 - locals[0].toNat)) locals[1])
    · simp only [flag, hi, decide_false, Bool.false_eq_true, ite_false]
      exact BitVec.zero_mul)

/-- Explicit emitted output, linked to the actual compiler by selected below. -/
def byteExpressionCode : Program :=
  [pushByte 255, readSlot ⟨2, by decide⟩, readSlot ⟨2, by decide⟩,
   pushByte 31, .op .SUB, pushByte 8, .op .MUL, .op .SHR, .op .AND,
   pushByte 32, readSlot ⟨2, by decide⟩, .op .LT, .op .MUL]

theorem byteExpression_selected : byteExpression.code 0 = some byteExpressionCode := rfl

/-- The actual result replaces the two copied input operands. This is an inline
primitive slice, not a V12 call/return-address convention. -/
def byteExpansion : Program := byteExpressionCode ++
  (writeSlot ⟨1, by decide⟩ ++ popPrefix 1)

theorem byteExpansion_run (index value : Word) (tail : Stack) :
    run byteExpansion (index :: value :: tail) =
      some (indexedByteWindow index value :: tail) := by
  apply run_comp (byteExpression.correct 0 byteExpressionCode byteExpression_selected
    #v[index, value] #v[] tail)
  rfl

private theorem pair_words (input : Vector Word 2) : input.toList = [input[0], input[1]] := by
  apply List.ext_getElem
  · exact Vector.length_toList
  · intro i hi hj
    have h : i = 0 ∨ i = 1 := by simp only [Vector.length_toList] at hi; omega
    rcases h with h | h <;> subst i <;>
      simp only [Vector.getElem_toList, List.getElem_cons_zero, List.getElem_cons_succ]

def byteAritySlice : AritySlice 2 1 (fun input => #v[indexedByteWindow input[0] input[1]]) where
  code := byteExpansion
  correct := by
    intro input tail
    rw [pair_words]
    exact byteExpansion_run _ _ tail

/-- Argument lowering reuses the real arity-indexed compiler. Complete original
locals, newer prefix and caller are outside the copied operand frame. -/
def lowerByte {n : Nat} {index value : Vector Word n → Word}
    (a : LoweredExpr n index) (b : LoweredExpr n value) :
    LoweredExpr n (fun locals => indexedByteWindow (index locals) (value locals)) :=
  let args := lowerArgCons a (lowerArgCons b (lowerNoArgs n))
  let compiled := lowerInline args byteAritySlice
  { code := compiled.code
    correct := by
      intro depth p selected locals newer tail
      exact compiled.correct depth p selected locals newer tail }

/-- Trace admissibility includes entry and exit; it does not assert operand
existence at height1. The execution theorem separately supplies two operands. -/
theorem byteExpansion_bound_iff (height : Int) :
    stackBound byteExpansion height = true ↔ 1 ≤ height ∧ height + 4 ≤ 1024 := by
  simp only [byteExpansion, byteExpressionCode, writeSlot, popPrefix, readSlot,
    pushByte, List.cons_append, List.nil_append, stackBound, heightTrace,
    stackDelta, numericDelta, unary, binary, ternary, Option.isSome_none,
    Option.isSome_some, Bool.false_eq_true, if_false, if_true, List.all_cons,
    List.all_nil, Bool.and_true, Bool.and_eq_true, safeHeight, decide_eq_true_eq]
  constructor <;> intro bound <;> omega

theorem byteExpansion_size : size byteExpansion = 20 := rfl

theorem byteExpansion_delta : ((byteExpansion.map stackDelta).sum : Int) = -1 := rfl

#print axioms byteExpansion_bound_iff
#print axioms byteExpansion_size
#print axioms byteExpansion_run
#print axioms lowerByte
#print axioms byteWindow_mask
#print axioms byteExpression
end Solidity.Yul.Compilation
