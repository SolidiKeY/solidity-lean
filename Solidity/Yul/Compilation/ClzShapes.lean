import Solidity.Yul.Compilation.ExpressionShapes
import Solidity.Yul.Compilation.ClzLowering

/-! Operand and every-boundary capacity proofs for the EXISTING CLZ software
expansion. The fixed256-step scan is unchanged; no native CLZ transition,
word semantics, source state, resource budget or calling convention is added. -/
namespace Solidity.Yul.Compilation.ClzShapes
open Backend Scalar LabelExec

/-- Every shared concatenation boundary is checked; an entry check is not
silently dropped when the first program is empty. -/
theorem bound_append (p q : Program) (h : Int) :
    stackBound (p++q) h = (stackBound p h && stackBound q (h+(p.map stackDelta).sum)) := by
  induction p generalizing h with
  | nil =>
    simp only [List.nil_append,List.map_nil,List.sum_nil,Int.add_zero]
    cases q <;> simp only [stackBound,heightTrace,List.all_cons,List.all_nil,
      Bool.and_true,←Bool.and_assoc,Bool.and_self]
  | cons i p ih =>
    change (safeHeight h && stackBound (p++q) (h+stackDelta i)) =
      ((safeHeight h && stackBound p (h+stackDelta i)) &&
        stackBound q (h+(stackDelta i+(p.map stackDelta).sum)))
    rw [ih]
    simp only [Bool.and_assoc,Int.add_assoc]

theorem step_shape (i : Fin 256) (h : Nat) (enough : 2 ≤ h) : CodeShape (clzStepCode i) h h := by
  refine .cons (m := h+1) (.mk 2 3 ((h)-2) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+2) (.mk 0 1 ((h+1)-0) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+1) (.mk 2 1 ((h+2)-2) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+2) (.mk 0 1 ((h+1)-0) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+1) (.mk 2 1 ((h+2)-2) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+2) (.mk 0 1 ((h+1)-0) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+1) (.mk 2 1 ((h+2)-2) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+2) (.mk 2 3 ((h+1)-2) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+3) (.mk 4 5 ((h+2)-4) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+4) (.mk 0 1 ((h+3)-0) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+3) (.mk 2 1 ((h+4)-2) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+4) (.mk 0 1 ((h+3)-0) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+3) (.mk 2 1 ((h+4)-2) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+4) (.mk 0 1 ((h+3)-0) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+3) (.mk 2 1 ((h+4)-2) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+2) (.mk 2 1 ((h+3)-2) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+1) (.mk 2 1 ((h+2)-2) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+1) (.mk 2 2 ((h+1)-2) rfl (by omega) (by omega)) ?_
  refine .cons (m := h) (.mk 1 0 ((h+1)-1) rfl (by omega) (by omega)) ?_
  exact .nil h

theorem step_trace (i : Fin 256) (h : Int) : heightTrace (clzStepCode i) h = [h,h+1,h+2,h+1,h+2,h+1,h+2,h+1,h+2,h+3,h+4,h+3,h+4,h+3,h+4,h+3,h+2,h+1,h+1,h] := by
  change [h,(h)+(1),((h)+(1))+(1),(((h)+(1))+(1))+(-1),((((h)+(1))+(1))+(-1))+(1),(((((h)+(1))+(1))+(-1))+(1))+(-1),((((((h)+(1))+(1))+(-1))+(1))+(-1))+(1),(((((((h)+(1))+(1))+(-1))+(1))+(-1))+(1))+(-1),((((((((h)+(1))+(1))+(-1))+(1))+(-1))+(1))+(-1))+(1),(((((((((h)+(1))+(1))+(-1))+(1))+(-1))+(1))+(-1))+(1))+(1),((((((((((h)+(1))+(1))+(-1))+(1))+(-1))+(1))+(-1))+(1))+(1))+(1),(((((((((((h)+(1))+(1))+(-1))+(1))+(-1))+(1))+(-1))+(1))+(1))+(1))+(-1),((((((((((((h)+(1))+(1))+(-1))+(1))+(-1))+(1))+(-1))+(1))+(1))+(1))+(-1))+(1),(((((((((((((h)+(1))+(1))+(-1))+(1))+(-1))+(1))+(-1))+(1))+(1))+(1))+(-1))+(1))+(-1),((((((((((((((h)+(1))+(1))+(-1))+(1))+(-1))+(1))+(-1))+(1))+(1))+(1))+(-1))+(1))+(-1))+(1),(((((((((((((((h)+(1))+(1))+(-1))+(1))+(-1))+(1))+(-1))+(1))+(1))+(1))+(-1))+(1))+(-1))+(1))+(-1),((((((((((((((((h)+(1))+(1))+(-1))+(1))+(-1))+(1))+(-1))+(1))+(1))+(1))+(-1))+(1))+(-1))+(1))+(-1))+(-1),(((((((((((((((((h)+(1))+(1))+(-1))+(1))+(-1))+(1))+(-1))+(1))+(1))+(1))+(-1))+(1))+(-1))+(1))+(-1))+(-1))+(-1),((((((((((((((((((h)+(1))+(1))+(-1))+(1))+(-1))+(1))+(-1))+(1))+(1))+(1))+(-1))+(1))+(-1))+(1))+(-1))+(-1))+(-1))+(0),(((((((((((((((((((h)+(1))+(1))+(-1))+(1))+(-1))+(1))+(-1))+(1))+(1))+(1))+(-1))+(1))+(-1))+(1))+(-1))+(-1))+(-1))+(0))+(-1)] = _
  simp only [Int.add_assoc,Int.reduceAdd,Int.add_zero]

theorem step_capacity (i : Fin 256) (h : Int) :
    stackBound (clzStepCode i) h = true ↔ 0 ≤ h ∧ h+4 ≤ 1024 := by
  simp only [stackBound,step_trace,List.all_cons,List.all_nil,Bool.and_true,
    Bool.and_eq_true,safeHeight,decide_eq_true_eq]
  omega

theorem step_delta (i : Fin 256) : ((clzStepCode i).map stackDelta).sum = (0 : Int) := by rfl

theorem scan_shape (count : Nat) : ∀ (bound : count ≤ 256) (h : Nat), 2 ≤ h →
    CodeShape (clzScanCode count bound) h h := by
  induction count with
  | zero => intro bound h enough; exact .nil h
  | succ count ih =>
    intro bound h enough
    exact ExpressionShapes.append (ih (by omega) h enough) (step_shape ⟨count,by omega⟩ h enough)

theorem scan_delta (count : Nat) : ∀ (bound : count ≤ 256),
    ((clzScanCode count bound).map stackDelta).sum = (0 : Int) := by
  intro bound
  have actual := clzScanCode_run count bound (0 : Scalar.Word) []
  have height := run_height actual
  simp only [List.length_cons,List.length_nil] at height
  omega

theorem scan_capacity (count : Nat) : ∀ (bound : count ≤ 256) (h : Int),
    stackBound (clzScanCode count bound) h = true ↔
      match count with
      | 0 => 0 ≤ h ∧ h ≤ 1024
      | _+1 => 0 ≤ h ∧ h+4 ≤ 1024 := by
  induction count with
  | zero =>
    intro bound h
    simp only [clzScanCode,stackBound,heightTrace,List.all_cons,List.all_nil,
      Bool.and_true,safeHeight,decide_eq_true_eq]
  | succ count ih =>
    intro bound h
    rw [clzScanCode,bound_append,scan_delta,Int.add_zero,Bool.and_eq_true,ih,step_capacity]
    cases count <;> omega

private theorem initial_capacity (h : Int) :
    stackBound [pushWord 256] h = true ↔ 0 ≤ h ∧ h+1 ≤ 1024 := by
  change ([h,h+1].all safeHeight) = true ↔ _
  simp only [List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true,safeHeight,decide_eq_true_eq]
  omega

private theorem retire_capacity (h : Int) :
    stackBound (writeSlot ⟨0,by decide⟩) h = true ↔ 1 ≤ h ∧ h ≤ 1024 := by
  change ([h,h+0,(h+0)+(-1)].all safeHeight) = true ↔ _
  simp only [List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true,safeHeight,decide_eq_true_eq]
  omega

/-- An actual copied argument is required; height/capacity alone cannot
supply that operand. The full scan uses the same caller as every bit step. -/
theorem expansion_shape (h : Nat) (enough : 1 ≤ h) : CodeShape clzExpansion h h := by
  have initial : CodeShape [pushWord 256] h (h+1) :=
    .cons (.mk 0 1 h rfl (by omega) (by omega)) (.nil (h+1))
  have scan : CodeShape (clzScanCode 256 (by decide)) (h+1) (h+1) :=
    scan_shape 256 (by decide) (h+1) (by omega)
  have retire : CodeShape (writeSlot ⟨0,by decide⟩) (h+1) h :=
    .cons (m := h+1) (.mk 2 2 (h-1) rfl (by omega) (by omega))
      (.cons (.mk 1 0 h rfl (by omega) (by omega)) (.nil h))
  exact ExpressionShapes.append (ExpressionShapes.append initial scan) retire

/-- Exact every-boundary capacity for all256 emitted bit steps, including
initialization and retirement. This is not a charged/native execution bound. -/
theorem expansion_capacity (h : Int) :
    stackBound clzExpansion h = true ↔ 0 ≤ h ∧ h+5 ≤ 1024 := by
  change stackBound ([pushWord 256]++clzScanCode 256 (by decide)++writeSlot ⟨0,by decide⟩) h = true ↔ _
  rw [List.append_assoc,bound_append]
  have initialDelta : ([pushWord 256].map stackDelta).sum = (1 : Int) := rfl
  rw [initialDelta,bound_append,scan_delta,Int.add_zero]
  simp only [Bool.and_eq_true,initial_capacity,scan_capacity,retire_capacity]
  omega

/-- Existing intrinsic code packet with both operand and prefix-capacity
proofs. No fake runtime transition is supplied by this constructor. -/
def expansionCode (h : Nat) (enough : 1 ≤ h) (room : h+5 ≤ 1024) : Code h h where
  instructions := clzExpansion
  shape := expansion_shape h enough
  capacity := (expansion_capacity h).mpr ⟨by omega,by omega⟩

theorem step_length (i : Fin 256) : (clzStepCode i).length = 19 := by rfl

theorem scan_length (count : Nat) : ∀ (bound : count ≤ 256),
    (clzScanCode count bound).length = 19*count := by
  induction count with
  | zero => intro bound; rfl
  | succ count ih =>
    intro bound
    rw [clzScanCode,List.length_append,ih,step_length]
    omega

private theorem surrounded_length (count : Nat) (bound : count ≤ 256) :
    ([pushWord 256]++clzScanCode count bound++writeSlot ⟨0,by decide⟩).length = 19*count+3 := by
  simp only [List.length_append,scan_length,writeSlot,List.length_cons,List.length_nil]
  omega

theorem expansion_length : clzExpansion.length = 4867 :=
  surrounded_length 256 (by decide)

/-- Actual argument emission plus the concrete expansion yields the existing
expression shape. This helper retains its real argument-metadata premise. -/
theorem lowering_shape {n : Nat} {value : Vector Scalar.Word n → Scalar.Word}
    (argument : LoweredExpr n value)
    (argumentShape : ∀ depth p, argument.code depth = some p → CodeShape p (n+depth) (n+depth+1))
    (depth : Nat) (p : Program) (emitted : (lowerClzExpanded argument).code depth = some p) :
    CodeShape p (n+depth) (n+depth+1) := by
  change (argument.code depth).map (fun code => code++clzExpansion) = some p at emitted
  obtain ⟨code,argEmitted,same⟩ := Option.map_eq_some_iff.mp emitted
  subst p
  exact ExpressionShapes.append (argumentShape depth code argEmitted)
    (expansion_shape (n+depth+1) (by omega))
/-- info: 'Solidity.Yul.Compilation.ClzShapes.bound_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms bound_append
/-- info: 'Solidity.Yul.Compilation.ClzShapes.step_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms step_shape
/-- info: 'Solidity.Yul.Compilation.ClzShapes.step_trace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms step_trace
/-- info: 'Solidity.Yul.Compilation.ClzShapes.step_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_capacity
/-- info: 'Solidity.Yul.Compilation.ClzShapes.step_delta' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms step_delta
/-- info: 'Solidity.Yul.Compilation.ClzShapes.scan_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scan_shape
/-- info: 'Solidity.Yul.Compilation.ClzShapes.scan_delta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms scan_delta
/-- info: 'Solidity.Yul.Compilation.ClzShapes.scan_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms scan_capacity
/-- info: 'Solidity.Yul.Compilation.ClzShapes.expansion_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms expansion_shape
/-- info: 'Solidity.Yul.Compilation.ClzShapes.expansion_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms expansion_capacity
/-- info: 'Solidity.Yul.Compilation.ClzShapes.expansionCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms expansionCode
/-- info: 'Solidity.Yul.Compilation.ClzShapes.step_length' does not depend on any axioms -/
#guard_msgs in #print axioms step_length
/-- info: 'Solidity.Yul.Compilation.ClzShapes.scan_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scan_length
/-- info: 'Solidity.Yul.Compilation.ClzShapes.expansion_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms expansion_length
/-- info: 'Solidity.Yul.Compilation.ClzShapes.lowering_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lowering_shape

end Solidity.Yul.Compilation.ClzShapes
