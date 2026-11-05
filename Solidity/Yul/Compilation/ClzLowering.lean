import Solidity.Yul.Compilation.OpcodeLowering

/-! Expand CLZ into existing supported primitive code. The specification is
stdlib BitVec.clz, not a second Yul word semantics. No native CLZ transition,
source admission, fetched execution or gas bound is asserted here. -/
namespace Solidity.Yul.Compilation
open Backend Scalar

/-- Compact compiler-internal constants; this never truncates an arbitrary
source word, since the input itself is intrinsically UInt8. -/
def lowerSmallLiteral {n : Nat} (byte : UInt8) :
    LoweredExpr n (fun _ => BitVec.ofNat 256 byte.toNat) where
  code := fun _ => some [pushByte byte]
  correct := by
    intro depth p selected locals newer tail
    cases selected
    simp only [run, step_pushByte, Option.bind_some]

private theorem word_bit_mask (x : Word) (i : Fin 256) :
    (1#256) &&& (x >>> i.val) = if x.getLsbD i.val then (1#256) else (0#256) := by
  have oneAt (j : Nat) : (1#256).getLsbD j = decide (j = 0) := by
    rw [BitVec.getLsbD_one]
    rfl
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  by_cases hz : j = 0
  · subst j
    cases hb : x.getLsbD i.val <;>
      simp only [BitVec.getLsbD_and, oneAt, BitVec.getLsbD_ushiftRight,
        Nat.add_zero, hb, Bool.false_eq_true, ite_false, ite_true, BitVec.getLsbD_zero,
        decide_true, Bool.true_and]
  · cases hb : x.getLsbD i.val <;>
      simp only [BitVec.getLsbD_and, oneAt, hz, decide_false, Bool.false_and,
        Bool.false_eq_true, ite_false, ite_true, BitVec.getLsbD_zero]

private def shrSelection : BinarySelection := (selectBinaryOpcode .SHR).getD selectDiv

private def bitExpression (i : Fin 256) :
    LoweredExpr 2 (fun l => (1#256) &&& (l[1] >>> i.val)) :=
  let raw := lowerBinary selectAnd (lowerSmallLiteral 1)
    (lowerBinary shrSelection (lowerSmallLiteral (UInt8.ofNat i.val))
      (lowerLocal ⟨1, by decide⟩))
  raw.congr (by
    intro locals
    have count : (BitVec.ofNat 256 (UInt8.ofNat i.val).toNat).toNat = i.val := by
      rw [BitVec.toNat_ofNat, UInt8.toNat_ofNat', Nat.mod_eq_of_lt i.isLt,
        Nat.mod_eq_of_lt (Nat.lt_trans i.isLt (by decide : 256 < 2 ^ 256))]
    change (1#256) &&& (if (BitVec.ofNat 256 (UInt8.ofNat i.val).toNat).toNat < 256
      then locals[1] >>> (BitVec.ofNat 256 (UInt8.ofNat i.val).toNat).toNat else 0) = _
    rw [count, if_pos i.isLt])

/-- Overwrite the accumulator when this bit is set. Ascending bit steps
therefore leave the count belonging to the highest set bit. -/
def clzStepExpression (i : Fin 256) : LoweredExpr 2
    (fun l => if l[1].getLsbD i.val then BitVec.ofNat 256 (255 - i.val) else l[0]) :=
  let bit := bitExpression i
  let raw := lowerBinary selectAdd
    (lowerBinary selectMul (lowerBinary selectSub (lowerSmallLiteral 1) bit)
      (lowerLocal ⟨0, by decide⟩))
    (lowerBinary selectMul (lowerSmallLiteral (UInt8.ofNat (255 - i.val))) bit)
  raw.congr (by
    intro locals
    have small : 255 - i.val < 256 := by omega
    change ((1#256) - ((1#256) &&& (locals[1] >>> i.val))) * locals[0] +
      BitVec.ofNat 256 (UInt8.ofNat (255 - i.val)).toNat *
        ((1#256) &&& (locals[1] >>> i.val)) = _
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt small, word_bit_mask]
    cases hb : locals[1].getLsbD i.val <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, BitVec.sub_zero,
        BitVec.sub_self, BitVec.one_mul, BitVec.zero_mul, BitVec.mul_zero,
        BitVec.mul_one, BitVec.zero_add, BitVec.add_zero])

def clzStep (i : Fin 256) : LoweredStmt 2
    (fun l => l.set 0 (if l[1].getLsbD i.val then BitVec.ofNat 256 (255 - i.val) else l[0])
      (by decide)) :=
  lowerAssign ⟨0, by decide⟩ (clzStepExpression i)

/-- Explicit executable output avoids re-normalizing proof-carrying compiler
records for each concrete bit. Equality with generated code is checked below. -/
def clzStepCode (i : Fin 256) : Program :=
  [readSlot ⟨1, by decide⟩, pushByte (UInt8.ofNat i.val), .op .SHR, pushByte 1, .op .AND,
   pushByte (UInt8.ofNat (255 - i.val)), .op .MUL,
   readSlot ⟨1, by decide⟩, readSlot ⟨3, by decide⟩,
   pushByte (UInt8.ofNat i.val), .op .SHR, pushByte 1, .op .AND,
   pushByte 1, .op .SUB, .op .MUL, .op .ADD] ++ writeSlot ⟨0, by decide⟩

theorem clzStep_selected (i : Fin 256) : (clzStep i).code 0 = some (clzStepCode i) := rfl

theorem clzStep_run (i : Fin 256) (accumulator x : Word) (tail : Stack) :
    run (clzStepCode i) (accumulator :: x :: tail) =
      some ((if x.getLsbD i.val then BitVec.ofNat 256 (255 - i.val) else accumulator) :: x :: tail) :=
  (clzStep i).correct 0 (clzStepCode i) (clzStep_selected i) #v[accumulator, x] #v[] tail

/-- Finite compiler recursion, not a source execution fuel or new budget. -/
def clzScanCode : (count : Nat) → count ≤ 256 → Program
  | 0, _ => []
  | count + 1, bound => clzScanCode count (by omega) ++ clzStepCode ⟨count, by omega⟩

theorem clzScanCode_run (count : Nat) (bound : count ≤ 256) (x : Word) (tail : Stack) :
    run (clzScanCode count bound) ((256 : Word) :: x :: tail) =
      some ((if count = 0 then 256 else x.clzAuxRec (count - 1)) :: x :: tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [clzScanCode]
    apply run_comp (ih (by omega))
    rw [clzStep_run]
    cases count with
    | zero => rfl
    | succ count => rfl

def clzExpansion : Program := [pushWord 256] ++ clzScanCode 256 (by decide) ++
  writeSlot ⟨0, by decide⟩

/-- Exact full-word CLZ result over an arbitrary untouched caller stack. -/
theorem clzExpansion_run (x : Word) (tail : Stack) :
    run clzExpansion (x :: tail) = some (x.clz :: tail) := by
  apply run_comp (p := [pushWord 256] ++ clzScanCode 256 (by decide))
    (q := writeSlot ⟨0, by decide⟩)
  · apply run_comp (p := [pushWord 256]) (q := clzScanCode 256 (by decide))
      (t := (256 : Word) :: x :: tail)
    · simp only [run, step_pushWord, Option.bind_some]
    · exact clzScanCode_run 256 (by decide) x tail
  · change run (writeSlot ⟨0, by decide⟩) (x.clz :: x :: tail) = _
    rfl

/-- Expression lowering consumes only the copied argument word. The original
local vector/newer prefix/caller all remain exact, including dirty high bits. -/
def lowerClzExpanded {n : Nat} {value : Vector Word n → Word}
    (argument : LoweredExpr n value) : LoweredExpr n (fun locals => (value locals).clz) where
  code := fun depth => (argument.code depth).map (fun p => p ++ clzExpansion)
  correct := by
    intro depth p selected locals newer tail
    cases ha : argument.code depth with
    | none => simp only [ha, Option.map_none] at selected; cases selected
    | some code =>
      simp only [ha, Option.map_some] at selected
      cases selected
      exact run_comp (argument.correct depth code ha locals newer tail)
        (clzExpansion_run (value locals) (newer.toList ++ (locals.toList ++ tail)))

#print axioms clzStep_run
#print axioms clzScanCode_run
#print axioms clzExpansion_run
#print axioms lowerClzExpanded
#print axioms lowerSmallLiteral
#print axioms word_bit_mask
#print axioms clzStepExpression
end Solidity.Yul.Compilation
