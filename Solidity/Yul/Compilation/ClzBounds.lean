import Solidity.Yul.Compilation.ClzLowering

/-! Compositional capacity/size certificates. Scalar operand correctness and
physical capacity remain separate obligations. -/
namespace Solidity.Yul.Compilation
open Backend Scalar

theorem stackBound_comp {p q : Program} {h : Int}
    (hp : stackBound p h = true)
    (hq : stackBound q (h + (p.map stackDelta).sum) = true) :
    stackBound (p ++ q) h = true := by
  induction p generalizing h with
  | nil => simpa only [List.map_nil, List.sum_nil, Int.add_zero] using hq
  | cons i p ih =>
    change (safeHeight h && stackBound p (h + stackDelta i)) = true at hp
    change (safeHeight h && stackBound (p ++ q) (h + stackDelta i)) = true
    rw [Bool.and_eq_true] at hp ⊢
    refine ⟨hp.1, ih hp.2 ?_⟩
    simpa only [List.map_cons, List.sum_cons, Int.add_assoc] using hq

private theorem sum_append_int (a b : List Int) : (a ++ b).sum = a.sum + b.sum := by
  induction a with
  | nil => simp only [List.nil_append, List.sum_nil, Int.zero_add]
  | cons x a ih => simp only [List.cons_append, List.sum_cons, ih, Int.add_assoc]

theorem clzStep_delta (i : Fin 256) : ((clzStepCode i).map stackDelta).sum = 0 := rfl

theorem clzScan_delta (count : Nat) (bound : count ≤ 256) :
    ((clzScanCode count bound).map stackDelta).sum = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [clzScanCode, List.map_append, sum_append_int, ih, clzStep_delta]
    rfl

theorem clzStep_bound (i : Fin 256) (h : Int) (lo : 0 ≤ h) (hi : h + 4 ≤ 1024) :
    stackBound (clzStepCode i) h = true := by
  simp only [clzStepCode, readSlot, writeSlot, List.cons_append, List.nil_append,
    pushByte, stackBound, heightTrace, stackDelta, numericDelta, unary, binary, ternary,
    Option.isSome_none, Option.isSome_some, Bool.false_eq_true, if_false, if_true,
    List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, safeHeight,
    decide_eq_true_eq]
  omega

theorem clzScan_bound (count : Nat) (bound : count ≤ 256) (h : Int)
    (lo : 0 ≤ h) (hi : h + 4 ≤ 1024) : stackBound (clzScanCode count bound) h = true := by
  induction count with
  | zero =>
    simp only [clzScanCode, stackBound, heightTrace, List.all_cons, List.all_nil,
      Bool.and_true, safeHeight, decide_eq_true_eq]
    omega
  | succ count ih =>
    rw [clzScanCode]
    apply stackBound_comp (ih (by omega))
    rw [clzScan_delta, Int.add_zero]
    exact clzStep_bound _ h lo hi

/-- Expansion needs five spare words above its input height. This is an
actual stackBound certificate; successful scalar evaluation alone is weaker. -/
theorem clzExpansion_bound (h : Int) (lo : 0 ≤ h) (hi : h + 5 ≤ 1024) :
    stackBound clzExpansion h = true := by
  apply stackBound_comp (p := [pushWord 256] ++ clzScanCode 256 (by decide))
    (q := writeSlot ⟨0, by decide⟩)
  · apply stackBound_comp (p := [pushWord 256]) (q := clzScanCode 256 (by decide))
    · simp only [pushWord, stackBound, heightTrace, stackDelta, safeHeight, List.all_cons,
        List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
      omega
    · change stackBound (clzScanCode 256 (by decide)) (h + 1) = true
      exact clzScan_bound 256 (by decide) (h + 1) (by omega) (by omega)
  · rw [List.map_append, sum_append_int, clzScan_delta]
    change stackBound (writeSlot ⟨0, by decide⟩) (h + (1 + 0)) = true
    simp only [writeSlot, stackBound, heightTrace, stackDelta, safeHeight, List.all_cons,
      List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    omega
theorem clzScan_head (count : Nat) (bound : count + 1 ≤ 256) :
    ∃ rest, clzScanCode (count + 1) bound = clzStepCode ⟨0, by decide⟩ ++ rest := by
  induction count with
  | zero => exact ⟨[], rfl⟩
  | succ count ih =>
    obtain ⟨rest, eqn⟩ := ih (by omega)
    refine ⟨rest ++ clzStepCode ⟨count + 1, by omega⟩, ?_⟩
    rw [clzScanCode, eqn, List.append_assoc]

theorem clzExpansion_has_prefix : ∃ rest,
    clzExpansion = ([pushWord 256] ++ clzStepCode ⟨0, by decide⟩) ++ rest := by
  obtain ⟨rest, eqn⟩ := clzScan_head 255 (by decide)
  exact ⟨rest ++ writeSlot ⟨0, by decide⟩, by
    rw [clzExpansion, eqn]
    simp only [List.append_assoc]⟩

theorem clzExpansion_bound_iff (h : Int) :
    stackBound clzExpansion h = true ↔ 0 ≤ h ∧ h + 5 ≤ 1024 := by
  constructor
  · intro hb
    obtain ⟨rest, eqn⟩ := clzExpansion_has_prefix
    rw [eqn] at hb
    have hp := stackBound_prefix _ rest h hb
    simp only [clzStepCode, readSlot, writeSlot, List.cons_append, List.nil_append,
      pushWord, pushByte, stackBound, heightTrace, stackDelta, numericDelta,
      unary, binary, ternary, Option.isSome_none, Option.isSome_some,
      Bool.false_eq_true, if_false, if_true, List.all_cons, List.all_nil,
      Bool.and_true, Bool.and_eq_true, safeHeight, decide_eq_true_eq] at hp
    omega
  · rintro ⟨lo, hi⟩
    exact clzExpansion_bound h lo hi

theorem clzStep_size (i : Fin 256) : size (clzStepCode i) = 25 := rfl

theorem clzScan_size (count : Nat) (bound : count ≤ 256) :
    size (clzScanCode count bound) = 25 * count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [clzScanCode]
    change (List.map Instr.size (clzScanCode count _ ++ clzStepCode _)).sum = _
    rw [List.map_append, List.sum_append_nat]
    change size (clzScanCode count _) + size (clzStepCode _) = _
    rw [ih, clzStep_size]
    omega

private theorem program_size_append (p q : Program) : size (p ++ q) = size p + size q := by
  simp only [size, List.map_append, List.sum_append_nat]

theorem clzExpansion_size : size clzExpansion = 6435 := by
  unfold clzExpansion
  rw [program_size_append, program_size_append, clzScan_size]
  rfl

/-- Refusal follows from a small failing first step, not whole-program reduction. -/
theorem clzExpansion_underflow : run clzExpansion [] = none := by
  obtain ⟨rest, eqn⟩ := clzExpansion_has_prefix
  rw [eqn, run_append]
  have short : run ([pushWord 256] ++ clzStepCode ⟨0, by decide⟩) [] = none := rfl
  rw [short]
  rfl

#print axioms clzExpansion_bound_iff
#print axioms clzExpansion_size
#print axioms clzExpansion_underflow
end Solidity.Yul.Compilation
