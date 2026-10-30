import Solidity.Backend.Scalar.SignedDivision
import Solidity.Backend.Scalar.SignedMul

/-! Two distinct signed-division exceptional classes at the explicit
instruction-test/observation boundary. No generic revert-byte emitter is assumed. -/
namespace Solidity.Backend.Scalar

def signedDivOverflowTest : Program :=
  [.op (.DUP ⟨0, by decide⟩), pushWord (encodeValue .int minimumInt), .op .EQ,
   .op (.DUP ⟨2, by decide⟩), pushWord (BitVec.ofInt 256 (-1)), .op .EQ, .op .AND]

theorem signedDivOverflowTest_correct (a b : PrimTy.int.Denote) (tail : Stack) :
    run signedDivOverflowTest (encodeValue .int a :: encodeValue .int b :: tail) =
      some (flag (decide (a.val = minimumInt.val ∧ b.val = -1)) ::
        encodeValue .int a :: encodeValue .int b :: tail) := by
  change run (pushWord (encodeValue .int minimumInt) :: _)
    (encodeValue .int a :: encodeValue .int a :: encodeValue .int b :: tail) = _
  rw [run, step_pushWord]
  change run (pushWord (BitVec.ofInt 256 (-1)) :: _)
    (encodeValue .int b :: flag (encodeValue .int minimumInt == encodeValue .int a) ::
      encodeValue .int a :: encodeValue .int b :: tail) = _
  rw [run, step_pushWord]
  let minusOne : PrimTy.int.Denote := ⟨-1, by decide⟩
  change some ((flag (encodeValue .int minusOne == encodeValue .int b) &&&
      flag (encodeValue .int minimumInt == encodeValue .int a)) ::
      encodeValue .int a :: encodeValue .int b :: tail) = _
  rw [flag_and, encode_int_beq, encode_int_beq, ← Bool.decide_and]
  have he : (minusOne.val = b.val ∧ minimumInt.val = a.val) ↔
      (a.val = minimumInt.val ∧ b.val = -1) := by
    change (-1 = b.val ∧ minimumInt.val = a.val) ↔ _
    omega
  simp only [he]

/-- A tested continuation retains operands for the next independent slice. -/
def guardedNext (test : Program) (failure : List UInt8)
    (next : Stack → Option (Except (List UInt8) Stack)) (st : Stack) :
    Option (Except (List UInt8) Stack) := do
  let tested ← run test st
  match tested with
  | f :: operands => if f == 0 then next operands else some (.error failure)
  | [] => none

theorem guardedNext_zero (n : Fin 16) (st : Stack) (a : Word)
    (failure : List UInt8) (next : Stack → Option (Except (List UInt8) Stack))
    (ha : st[n.val]? = some a) :
    guardedNext (zeroTest n) failure next st =
      if a == 0 then some (.error failure) else next st := by
  unfold guardedNext
  rw [zeroTest_correct n st a ha]
  cases h : a == 0 <;> rfl

def signedDivExecute (st : Stack) : Option (Except (List UInt8) Stack) :=
  guardedNext (zeroTest ⟨1, by decide⟩) divisionFailure
    (guarded signedDivOverflowTest [.op .SDIV] overflowFailure) st

def signedDivOutcome (a b : PrimTy.int.Denote) (tail : Stack) : Except (List UInt8) Stack :=
  if b.val = 0 then .error divisionFailure
  else checkedOutcome .int (BinOp.evalT .div (p := .int) rfl a b) tail

theorem int_div_correct (a b : PrimTy.int.Denote) (tail : Stack) :
    signedDivExecute (encodeValue .int a :: encodeValue .int b :: tail) =
      some (signedDivOutcome a b tail) := by
  rw [signedDivExecute, guardedNext_zero ⟨1, by decide⟩ _ (encodeValue .int b) _ _ rfl,
    int_word_zero]
  by_cases hb : b.val = 0
  · simp only [hb, decide_true, if_true, signedDivOutcome]
  · simp only [hb, decide_false, Bool.false_eq_true, if_false, signedDivOutcome]
    unfold guarded
    rw [signedDivOverflowTest_correct]
    change (if flag (decide (a.val = minimumInt.val ∧ b.val = -1)) == 0 then
      (run [.op .SDIV] (encodeValue .int a :: encodeValue .int b :: tail)).map Except.ok
      else some (.error overflowFailure)) = _
    by_cases hn : a.val = minimumInt.val ∧ b.val = -1
    · rw [if_neg (show ¬ flag (decide (a.val = minimumInt.val ∧ b.val = -1)) == 0 from by
        rw [show decide (a.val = minimumInt.val ∧ b.val = -1) = true from decide_eq_true hn]
        decide)]
      rw [int_div_exception a b hn.1 hn.2]
      rfl
    · have hf : flag (decide (a.val = minimumInt.val ∧ b.val = -1)) == 0 := by
        rw [show decide (a.val = minimumInt.val ∧ b.val = -1) = false from decide_eq_false hn]
        rfl
      rw [if_pos hf]
      have he : run [Instr.op Op.SDIV] (encodeValue PrimTy.int a :: encodeValue PrimTy.int b :: tail) =
          Option.map (fun v => encodeValue PrimTy.int v :: tail) (BinOp.div.evalT rfl a b) := int_div_body a b hb hn tail
      have hs : (BinOp.evalT .div (p := .int) rfl a b).isSome = true := by
        have hh : (run [Instr.op Op.SDIV] (encodeValue PrimTy.int a :: encodeValue PrimTy.int b :: tail)).isSome =
            (Option.map (fun v => encodeValue PrimTy.int v :: tail) (BinOp.div.evalT rfl a b)).isSome := congrArg Option.isSome he
        have hl : (run [.op .SDIV] (encodeValue .int a :: encodeValue .int b :: tail)).isSome = true := rfl
        rw [hl, Option.isSome_map] at hh
        exact hh.symm
      rw [he]
      cases hr : BinOp.evalT .div (p := .int) rfl a b with
      | none => simp only [hr] at hs; contradiction
      | some v => rfl

example : signedDivExecute [7, 0, 99] = some (.error divisionFailure) := rfl
example : signedDivExecute [encodeValue .int minimumInt, BitVec.ofInt 256 (-1), 99] =
    some (.error overflowFailure) := rfl
example : signedDivExecute [BitVec.ofInt 256 (-7), 2, 99] =
    some (.ok [BitVec.ofInt 256 (-3), 99]) := rfl


theorem int_mod_correct (a b : PrimTy.int.Denote) (tail : Stack) :
    guarded (zeroTest ⟨1, by decide⟩) [.op .SMOD] divisionFailure
      (encodeValue .int a :: encodeValue .int b :: tail) =
      some (divisionOutcome .int (BinOp.evalT .mod (p := .int) rfl a b) tail) := by
  rw [guarded_zero ⟨1, by decide⟩ _ (encodeValue .int b) _ _ rfl, int_word_zero]
  by_cases hb : b.val = 0
  · simp only [hb, decide_true, if_true, divisionOutcome, BinOp.evalT,
      BinOp.evalNum, BinOp.arithInt, Option.bind_none]
    rfl
  · simp only [hb, decide_false, Bool.false_eq_true, if_false]
    have he : run [Instr.op Op.SMOD] (encodeValue PrimTy.int a :: encodeValue PrimTy.int b :: tail) =
        Option.map (fun v => encodeValue PrimTy.int v :: tail) (BinOp.mod.evalT rfl a b) := int_mod_body a b hb tail
    have hs : (BinOp.evalT .mod (p := .int) rfl a b).isSome = true := by
      have hh : (run [Instr.op Op.SMOD] (encodeValue PrimTy.int a :: encodeValue PrimTy.int b :: tail)).isSome =
          (Option.map (fun v => encodeValue PrimTy.int v :: tail) (BinOp.mod.evalT rfl a b)).isSome := congrArg Option.isSome he
      have hl : (run [.op .SMOD] (encodeValue .int a :: encodeValue .int b :: tail)).isSome = true := rfl
      rw [hl, Option.isSome_map] at hh
      exact hh.symm
    rw [he]
    cases hr : BinOp.evalT .mod (p := .int) rfl a b with
    | none => simp only [hr] at hs; contradiction
    | some v => rfl

#print axioms int_mod_correct

#print axioms signedDivOverflowTest_correct
#print axioms guardedNext_zero
#print axioms int_div_correct
end Solidity.Backend.Scalar
