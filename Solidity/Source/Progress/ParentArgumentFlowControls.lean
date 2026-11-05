import Solidity.Source.Progress.ParentArgumentControls

/-! Earlier argument references survive later argument allocation. A failing
child propagates through the actual call before callee defaults/body start;
the source halt and input policies are retained in both pipelines. -/
namespace Solidity.Source.Progress.ParentArgumentFlowControls
open EM ParentArgumentControls
open Solidity.Lowering.P9

def doubleArgs : RConvArgs E Γ [Aty,Aty] := .cons parent rfl (.cons parent rfl .nil)
theorem double_admitted {A : Decl → Prop} : ParentArgs A doubleArgs :=
  .cons rfl (.inr rfl) (.parent ready_parent) (.cons rfl (.inr rfl) (.parent ready_parent) .nil)
def doubleReached : St E := {initial with heap:=(argumentReached.heap.alloc ⟨Aty,argumentData⟩).1}
def doubleValues : Vals E.layout [Aty,Aty] := .cons (.memRef rfl 1) (.cons (.memRef rfl 2) .nil)

theorem double_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalConvArgs (globals p fixed) frame 21 doubleArgs).run (caller,initial) =
      (.ok doubleValues,(caller,doubleReached)) := rfl
theorem double_preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalConvArgs (globals p fixed) frame 21 doubleArgs) ∧
    MemOK E seed.ty (caller,doubleReached) ∧ RValsOK E doubleReached.heap.ty doubleValues.toR := by
  have calls := WholeProgram.from_elaborate resolution actual_elaboration (globals p fixed) rfl "C" [] (checked p fixed)
  have actual := eval_parent_args_mem calls frame rfl 21 doubleArgs double_admitted seed.ty (caller,initial) caller_mem
  rw [double_run] at actual
  exact ⟨eval_parent_args_ns calls frame rfl 21 doubleArgs double_admitted,actual⟩
theorem earlier_reference_retained :
    doubleReached.heap.get 0 = seed.get 0 ∧
    doubleReached.heap.get 1 = some ⟨Aty,argumentData⟩ ∧
    doubleReached.heap.get 2 = some ⟨Aty,argumentData⟩ ∧ doubleReached.heap.next = 3 := ⟨rfl,rfl,rfl,rfl⟩

abbrev U : STy := .int .u256
abbrev PΓ : RCtx := [U,Bty]
def divide : RExpr E PΓ U := .binary .div (.local .here) (.local .here)
def guard : RExpr E PΓ .bool := .compare .lt divide (.local .here)
def panicFields : RConvArgs E PΓ [.bool,.bool] := .cons (.bool true) rfl (.cons guard rfl .nil)
def panicParent : RExpr E PΓ Aty := .inlineArray panicFields rfl
def panicArgs : RConvArgs E PΓ ps := .cons panicParent rfl .nil
def zero : Locals E.layout PΓ := .cons (.int 0 (by decide)) (.cons (.memRef rfl 0) .nil)
theorem guard_ready {A : Decl → Prop} : ReadyExpr A guard :=
  .value ⟨⟨rfl,rfl,rfl⟩,rfl,rfl⟩
    ⟨rfl,rfl,⟨.inl ⟨rfl,rfl⟩,trivial,trivial⟩,trivial⟩
theorem panic_admitted {A : Decl → Prop} : ParentArgs A panicArgs :=
  .cons rfl (.inr rfl) (.parent (.inline rfl
    (.cons rfl (.inl rfl) (.value trivial trivial)
      (.cons rfl (.inl rfl) guard_ready .nil)))) .nil
theorem zero_mem : MemOK E seed.ty (zero,initial) :=
  Preservation.relocalize entry_mem zero ⟨trivial,⟨⟨Bty,rfl,rfl⟩,trivial⟩⟩

theorem panic_checked (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (globals p fixed) frame 22 (.call d signature panicArgs)) ∧
    Hoare (MemOK E seed.ty) (evalE (globals p fixed) frame 22 (.call d signature panicArgs))
      (fun v y=>MemOK E seed.ty y ∧ RValOK E y.2.heap.ty v) (fun _ y=>MemOK E seed.ty y) :=
  parent_args_call_from_elaborate resolution actual_elaboration (globals p fixed) rfl "C" []
    (checked p fixed) frame rfl ps [Aty] ⟨d,declared,signature⟩ body
    (by rw [show frame.contract = "C" from rfl,ParentArgumentControls.dispatch];exact source_body)
    rfl rfl rfl rfl (fun τ member=>by
      simp only [List.mem_singleton] at member;subst τ;exact shape)
    ready_body panicArgs panic_admitted seed.ty 21
theorem panic_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (globals p fixed) frame 22 (.call d signature panicArgs)).run (zero,initial) =
      (.error (.revert (panicData .divZero)),(zero,initial)) := by cases p <;> rfl
theorem panic_preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (globals p fixed) frame 22 (.call d signature panicArgs)) ∧ MemOK E seed.ty (zero,initial) := by
  have joint := panic_checked p fixed
  have actual := joint.2 (zero,initial) zero_mem
  rw [panic_run] at actual
  exact ⟨joint.1,actual⟩
theorem no_callee_allocation : initial.heap.get 1 = none ∧ initial.heap.next = 1 := ⟨rfl,rfl⟩


def safeFields : RConvArgs E PΓ [.bool,.bool] :=
  .cons (.bool true) rfl (.cons (.bool false) rfl .nil)
def safeParent : RExpr E PΓ Aty := .inlineArray safeFields rfl
def lateArgs : RConvArgs E PΓ [Aty,Aty] := .cons safeParent rfl panicArgs
theorem late_admitted {A : Decl → Prop} : ParentArgs A lateArgs :=
  .cons rfl (.inr rfl) (.parent (.inline rfl
    (.cons rfl (.inl rfl) (.value trivial trivial)
      (.cons rfl (.inl rfl) (.value trivial trivial) .nil)))) panic_admitted
theorem later_panic_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalConvArgs (globals p fixed) frame 21 lateArgs).run (zero,initial) =
      (.error (.revert (panicData .divZero)),(zero,argumentReached)) := by cases p <;> rfl
theorem later_panic_preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalConvArgs (globals p fixed) frame 21 lateArgs) ∧ MemOK E seed.ty (zero,argumentReached) := by
  have calls := WholeProgram.from_elaborate resolution actual_elaboration (globals p fixed) rfl "C" [] (checked p fixed)
  have actual := eval_parent_args_mem calls frame rfl 21 lateArgs late_admitted seed.ty (zero,initial) zero_mem
  rw [later_panic_run] at actual
  exact ⟨eval_parent_args_ns calls frame rfl 21 lateArgs late_admitted,actual⟩
theorem retained_on_panic : argumentReached.heap.get 1 = some ⟨Aty,argumentData⟩ ∧
    argumentReached.heap.get 2 = none ∧ argumentReached.heap.next = 2 := ⟨rfl,rfl,rfl⟩

#print axioms double_admitted
#print axioms double_run
#print axioms double_preserved
#print axioms earlier_reference_retained
#print axioms guard_ready
#print axioms panic_admitted
#print axioms zero_mem
#print axioms panic_checked
#print axioms panic_run
#print axioms panic_preserved
#print axioms no_callee_allocation
#print axioms late_admitted
#print axioms later_panic_run
#print axioms later_panic_preserved
#print axioms retained_on_panic
end Solidity.Source.Progress.ParentArgumentFlowControls
