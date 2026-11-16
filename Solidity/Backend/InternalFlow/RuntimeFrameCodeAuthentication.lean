import Solidity.Backend.InternalFlow.RuntimeFrameCodeEquality

/-! Total structural authentication of existing instruction lists, including
nested loop children. This compares code data only; it is not another machine
or execution relation. The earlier flat recognizer remains unchanged. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.CodeAuthentication
open Evm

mutual
 def instruction (left right : Instr) : Bool :=
   match left,right with
   | .loop cond body,.loop other rest => code cond other && code body rest
   | _,_ => CodeEquality.instruction left right
 termination_by sizeOf left
 decreasing_by all_goals simp_wf; all_goals omega

 def code (left right : List Instr) : Bool :=
   match left,right with
   | [],[] => true
   | first::tail,other::rest => instruction first other && code tail rest
   | _,_ => false
 termination_by sizeOf left
 decreasing_by all_goals simp_wf; all_goals omega
end

mutual
 theorem instruction_sound {left right : Instr} (same : instruction left right=true) : left=right := by
   cases shape : left <;> (try simp only [shape,instruction] at same) <;> first | exact CodeEquality.instruction_sound same | skip
   cases right <;> simp only [instruction,CodeEquality.instruction,Bool.false_eq_true] at same
   have both := Bool.and_eq_true_iff.mp same
   rw [code_sound both.1,code_sound both.2]
 termination_by sizeOf left
 decreasing_by all_goals simp_all only; all_goals simp_wf; all_goals omega

 theorem code_sound {left right : List Instr} (same : code left right=true) : left=right := by
   cases shape : left with
   | nil => cases right <;> simp only [shape,code,Bool.false_eq_true] at same <;> rfl
   | cons x xs =>
     cases right with
     | nil => simp only [shape,code,Bool.false_eq_true] at same
     | cons y ys =>
       have both := Bool.and_eq_true_iff.mp (show (instruction x y && code xs ys)=true from by simpa only [shape,code] using same)
       rw [instruction_sound both.1,code_sound both.2]
 termination_by sizeOf left
 decreasing_by all_goals simp_all only; all_goals simp_wf; all_goals omega
end

mutual
 theorem instruction_self (item : Instr) : instruction item item=true := by
   cases shape : item <;> simp only [instruction,CodeEquality.instruction,decide_true]
   rw [code_self,code_self]
   rfl
 termination_by sizeOf item
 decreasing_by all_goals simp_all only; all_goals simp_wf; all_goals omega

 theorem code_self (items : List Instr) : code items items=true := by
   cases shape : items with
   | nil => simp only [code]
   | cons x xs =>
     have first := instruction_self x
     have rest := code_self xs
     simp only [code,first,rest,Bool.true_and]
 termination_by sizeOf items
 decreasing_by all_goals simp_all only; all_goals simp_wf; all_goals omega
end

theorem common_prefix (front left right : List Instr) :
 code (front++left) (front++right)=code left right := by
 induction front with
 | nil => rfl
 | cons first rest ih =>
   simp only [List.cons_append,code,instruction_self,Bool.true_and,ih]

/-- Authentication preserves the entire existing outcome, including machine
fields, residual skip, bare revert and fault, rather than only an observer. -/
theorem run_equal {left right : List Instr} (same : code left right=true) (before : Machine) :
 run left before=run right before := by
 rw [code_sound same]

theorem suffix_equal {left right : List Instr} (same : code left right=true)
 (suffix : List Instr) (before : Machine) : run (left++suffix) before=run (right++suffix) before := by
 rw [code_sound same]

end Solidity.Backend.InternalFlow.RuntimeFrame.CodeAuthentication
