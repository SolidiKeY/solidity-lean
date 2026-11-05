import Solidity.Yul.EvmArithmetic

/-! Comparison, bitwise, shift and power agreement with the repository target.
All words, machines and stack tails are quantified. No compiler lowering or
external EVM adequacy is inferred from these operation-level equalities. -/
namespace Solidity.Yul.EvmBitwise

theorem step_and : ∀ (machine : Solidity.Evm.Machine) (x y : Solidity.Yul.Word) (tail : List Solidity.Evm.Word),
 Solidity.Evm.Instr.step .and { machine with stack := .val x :: .val y :: tail } =
 .ok { machine with stack := .val (Solidity.Yul.Pure.eval .and
   (Solidity.Yul.EvmSigned.args x y)) :: tail } 0 := by
  intro machine x y tail
  apply congrArg (fun result : Solidity.Yul.Word => Solidity.Evm.Out.ok { machine with stack := .val result :: tail } 0)
  apply Fin.ext
  change (x.val &&& y.val) = (x.val &&& y.val) % Solidity.Evm.W
  exact (Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ y.isLt)).symm

theorem step_or : ∀ (machine : Solidity.Evm.Machine) (x y : Solidity.Yul.Word) (tail : List Solidity.Evm.Word),
 Solidity.Evm.Instr.step .or { machine with stack := .val x :: .val y :: tail } =
 .ok { machine with stack := .val (Solidity.Yul.Pure.eval .or
   (Solidity.Yul.EvmSigned.args x y)) :: tail } 0 := by
  intro machine x y tail
  apply congrArg (fun result : Solidity.Yul.Word => Solidity.Evm.Out.ok { machine with stack := .val result :: tail } 0)
  apply Fin.ext
  change (x.val ||| y.val) = (x.val ||| y.val) % Solidity.Evm.W
  exact (Nat.mod_eq_of_lt (Nat.or_lt_two_pow x.isLt y.isLt)).symm

theorem step_xor : ∀ (machine : Solidity.Evm.Machine) (x y : Solidity.Yul.Word) (tail : List Solidity.Evm.Word),
 Solidity.Evm.Instr.step .xor { machine with stack := .val x :: .val y :: tail } =
 .ok { machine with stack := .val (Solidity.Yul.Pure.eval .xor
   (Solidity.Yul.EvmSigned.args x y)) :: tail } 0 := by
  intro machine x y tail
  apply congrArg (fun result : Solidity.Yul.Word => Solidity.Evm.Out.ok { machine with stack := .val result :: tail } 0)
  apply Fin.ext
  change (x.val ^^^ y.val) = (x.val ^^^ y.val) % Solidity.Evm.W
  exact (Nat.mod_eq_of_lt (Nat.xor_lt_two_pow x.isLt y.isLt)).symm

theorem step_not : ∀ (machine : Solidity.Evm.Machine) (x : Solidity.Yul.Word) (tail : List Solidity.Evm.Word),
 Solidity.Evm.Instr.step .not { machine with stack := .val x :: tail } =
 .ok { machine with stack := .val (Solidity.Yul.Pure.eval .not
   ((fun _ => x))) :: tail } 0 := by
  intro machine x tail
  apply congrArg (fun result : Solidity.Yul.Word => Solidity.Evm.Out.ok { machine with stack := .val result :: tail } 0)
  apply Fin.ext
  change (Solidity.Evm.W-1-x.val) = (Solidity.Evm.W-1-x.val) % Solidity.Evm.W
  have bound : Solidity.Evm.W-1-x.val < Solidity.Evm.W := by
    have positive := Solidity.Evm.W_pos
    omega
  exact (Nat.mod_eq_of_lt bound).symm

theorem step_lt : ∀ (machine : Solidity.Evm.Machine) (x y : Solidity.Yul.Word) (tail : List Solidity.Evm.Word),
 Solidity.Evm.Instr.step .lt { machine with stack := .val x :: .val y :: tail } =
 .ok { machine with stack := .val (Solidity.Yul.Pure.eval .lt
   (Solidity.Yul.EvmSigned.args x y)) :: tail } 0 := by
  intro machine x y tail
  apply congrArg (fun result : Solidity.Yul.Word => Solidity.Evm.Out.ok { machine with stack := .val result :: tail } 0)
  change Solidity.Evm.bword (decide (x.val < y.val)) = Solidity.Yul.truth (decide (x.val < y.val))
  generalize decide (x.val < y.val) = choice
  cases choice <;> rfl

theorem step_gt : ∀ (machine : Solidity.Evm.Machine) (x y : Solidity.Yul.Word) (tail : List Solidity.Evm.Word),
 Solidity.Evm.Instr.step .gt { machine with stack := .val x :: .val y :: tail } =
 .ok { machine with stack := .val (Solidity.Yul.Pure.eval .gt
   (Solidity.Yul.EvmSigned.args x y)) :: tail } 0 := by
  intro machine x y tail
  apply congrArg (fun result : Solidity.Yul.Word => Solidity.Evm.Out.ok { machine with stack := .val result :: tail } 0)
  change Solidity.Evm.bword (decide (y.val < x.val)) = Solidity.Yul.truth (decide (y.val < x.val))
  generalize decide (y.val < x.val) = choice
  cases choice <;> rfl

theorem step_eq : ∀ (machine : Solidity.Evm.Machine) (x y : Solidity.Yul.Word) (tail : List Solidity.Evm.Word),
 Solidity.Evm.Instr.step .eq { machine with stack := .val x :: .val y :: tail } =
 .ok { machine with stack := .val (Solidity.Yul.Pure.eval .eq
   (Solidity.Yul.EvmSigned.args x y)) :: tail } 0 := by
  intro machine x y tail
  apply congrArg (fun result : Solidity.Yul.Word => Solidity.Evm.Out.ok { machine with stack := .val result :: tail } 0)
  change Solidity.Evm.bword (decide (x.val = y.val)) = Solidity.Yul.truth (x.val == y.val)
  simp only [Solidity.Evm.bword, Solidity.Yul.truth, beq_iff_eq, decide_eq_true_eq]
  split <;> rfl

theorem step_iszero : ∀ (machine : Solidity.Evm.Machine) (x : Solidity.Yul.Word) (tail : List Solidity.Evm.Word),
 Solidity.Evm.Instr.step .iszero { machine with stack := .val x :: tail } =
 .ok { machine with stack := .val (Solidity.Yul.Pure.eval .iszero
   ((fun _ => x))) :: tail } 0 := by
  intro machine x tail
  apply congrArg (fun result : Solidity.Yul.Word => Solidity.Evm.Out.ok { machine with stack := .val result :: tail } 0)
  change Solidity.Evm.bword (decide (x.val = 0)) = Solidity.Yul.truth (x.val == 0)
  simp only [Solidity.Evm.bword, Solidity.Yul.truth, beq_iff_eq, decide_eq_true_eq]
  split <;> rfl

theorem step_shl : ∀ (machine : Solidity.Evm.Machine) (x y : Solidity.Yul.Word) (tail : List Solidity.Evm.Word),
 Solidity.Evm.Instr.step .shl { machine with stack := .val x :: .val y :: tail } =
 .ok { machine with stack := .val (Solidity.Yul.Pure.eval .shl
   (Solidity.Yul.EvmSigned.args x y)) :: tail } 0 := by
  intro machine x y tail
  apply congrArg (fun result : Solidity.Yul.Word => Solidity.Evm.Out.ok { machine with stack := .val result :: tail } 0)
  change (if x.val < 256 then Solidity.Evm.wmod (y.val * 2 ^ x.val) else Solidity.Yul.word 0) =
    (if x.val ≥ 256 then Solidity.Yul.word 0 else Solidity.Yul.word (y.val <<< x.val))
  by_cases small : x.val < 256
  · have large : ¬ x.val ≥ 256 := by omega
    simp only [if_pos small, if_neg large, Nat.shiftLeft_eq]
    rfl
  · have large : x.val ≥ 256 := by omega
    simp only [if_neg small, if_pos large]

theorem step_shr : ∀ (machine : Solidity.Evm.Machine) (x y : Solidity.Yul.Word) (tail : List Solidity.Evm.Word),
 Solidity.Evm.Instr.step .shr { machine with stack := .val x :: .val y :: tail } =
 .ok { machine with stack := .val (Solidity.Yul.Pure.eval .shr
   (Solidity.Yul.EvmSigned.args x y)) :: tail } 0 := by
  intro machine x y tail
  apply congrArg (fun result : Solidity.Yul.Word => Solidity.Evm.Out.ok { machine with stack := .val result :: tail } 0)
  change (if x.val < 256 then
    (⟨y.val / 2 ^ x.val, Nat.lt_of_le_of_lt (Nat.div_le_self _ _) y.isLt⟩ : Solidity.Yul.Word)
    else Solidity.Yul.word 0) =
    (if x.val ≥ 256 then Solidity.Yul.word 0 else Solidity.Yul.word (y.val >>> x.val))
  by_cases small : x.val < 256
  · have large : ¬ x.val ≥ 256 := by omega
    simp only [if_pos small, if_neg large, Nat.shiftRight_eq_div_pow]
    apply Fin.ext
    change y.val / 2 ^ x.val = (y.val / 2 ^ x.val) % Solidity.Evm.W
    have bound : y.val / 2 ^ x.val < Solidity.Evm.W :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) y.isLt
    exact (Nat.mod_eq_of_lt bound).symm
  · have large : x.val ≥ 256 := by omega
    simp only [if_neg small, if_pos large]

theorem step_exp : ∀ (machine : Solidity.Evm.Machine) (x y : Solidity.Yul.Word) (tail : List Solidity.Evm.Word),
 Solidity.Evm.Instr.step .exp { machine with stack := .val x :: .val y :: tail } =
 .ok { machine with stack := .val (Solidity.Yul.Pure.eval .exp
   (Solidity.Yul.EvmSigned.args x y)) :: tail } 0 := by
  intro machine x y tail
  apply congrArg (fun result : Solidity.Yul.Word => Solidity.Evm.Out.ok { machine with stack := .val result :: tail } 0)
  apply Fin.ext
  change (x.val ^ y.val) % Solidity.Evm.W = (Solidity.Yul.powWord x y.val).val
  exact (Solidity.Yul.powWord_correct x y.val).symm


/-- Pure arithmetic right shift agrees with the existing target for every count and value. -/
theorem eval_sar : ∀ (count value : Solidity.Yul.Word),
 Solidity.Yul.Pure.eval .sar (Solidity.Yul.EvmSigned.args count value) =
 Solidity.Evm.sarWord count value := by
  intro count value
  change (if count.val ≥ 256 then
    (if signed value < 0 then word (2^256-1) else word 0)
    else iword (signed value >>> count.val)) = _
  rw [EvmSigned.signed_eq_sgn]
  unfold Solidity.Evm.sarWord
  by_cases small : count.val < 256
  · have large : ¬ count.val ≥ 256 := by omega
    simp only [if_neg large,if_pos small]
    rw [Int.shiftRight_eq_div_pow]
    apply EvmSigned.iword_eq_sword
    have range := Solidity.Evm.div_pow_range count.val (Solidity.Evm.sgn_range value.isLt)
    have sizes := Solidity.Evm.W_eq
    omega
  · have large : count.val ≥ 256 := by omega
    simp only [if_pos large,if_neg small]
    by_cases negative : Solidity.Evm.sgn value.val < 0
    · simp only [if_pos negative]
      apply Fin.ext
      change (Solidity.Evm.W-1) % Solidity.Evm.W = Solidity.Evm.W-1
      exact Nat.mod_eq_of_lt (by have positive := Solidity.Evm.W_pos; omega)
    · simp only [if_neg negative]
      rfl

/-- SAR consumes two words, preserving every other machine field and an arbitrary stack tail. -/
theorem step_sar : ∀ (machine : Solidity.Evm.Machine) (count value : Solidity.Yul.Word)
 (tail : List Solidity.Evm.Word),
 Solidity.Evm.Instr.step .sar { machine with stack := .val count :: .val value :: tail } =
 .ok { machine with stack := .val (Solidity.Yul.Pure.eval .sar
   (Solidity.Yul.EvmSigned.args count value)) :: tail } 0 := by
  intro machine count value tail
  change Solidity.Evm.Out.ok
    { machine with stack := .val (Solidity.Evm.sarWord count value) :: tail } 0 = _
  rw [eval_sar]

/-- SAR faults exactly when the stack lacks two leading value words. Arbitrary
remaining words, including slots, do not affect acceptance. -/
theorem step_sar_fault_iff : ∀ (machine : Solidity.Evm.Machine),
 Solidity.Evm.Instr.step .sar machine = .fault ↔
 ¬ ∃ (count value : Solidity.Yul.Word) (tail : List Solidity.Evm.Word),
 machine.stack = .val count :: .val value :: tail := by
  intro machine
  cases h : machine.stack with
  | nil =>
    simp only [Solidity.Evm.Instr.step, h, List.nil_eq, reduceCtorEq, exists_const,
      not_false_eq_true]
  | cons first rest =>
    cases first with
    | slot slot =>
      simp only [Solidity.Evm.Instr.step, h, List.cons.injEq, reduceCtorEq, false_and,
        exists_const, not_false_eq_true]
    | val count =>
      cases rest with
      | nil =>
        simp only [Solidity.Evm.Instr.step, h, List.cons.injEq, Solidity.Evm.Word.val.injEq,
          List.nil_eq, reduceCtorEq, and_false, exists_const, not_false_eq_true]
      | cons second tail =>
        cases second with
        | val value =>
          simp only [Solidity.Evm.Instr.step, h, Solidity.Evm.Machine.next,
            reduceCtorEq, List.cons.injEq, Solidity.Evm.Word.val.injEq, exists_and_left,
            exists_eq', and_true, not_true_eq_false]
        | slot slot =>
          simp only [Solidity.Evm.Instr.step, h, List.cons.injEq,
            Solidity.Evm.Word.val.injEq, reduceCtorEq, false_and, and_false, exists_const,
            not_false_eq_true]

end Solidity.Yul.EvmBitwise
