import Solidity.Source.Progress.ReadyArguments
import Solidity.Source.Preservation.AllocatingControls
import Solidity.Source.Preservation.MemoryProgramControls

/-! Ready reference conditionals and exact argument lists over inhabited
memory. Actual runs distinguish alias selection, fresh allocation, later-argument
panic and timeout. A checked-elaboration client retains the source-only boundary. -/
namespace Solidity.Source.Progress.ReadyExpressionControls
open EM
open Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls (E Γ seed state small frame globals)
open Preservation.AllocatingControls
  (fresh selected chooseFresh oversized grown arguments source_runs argument_run initial_mem)

theorem fresh_ready : ReadyExpr (fun _ => False) fresh := .newArray .bytes rfl (.local .here)
theorem selected_ready : ReadyExpr (fun _ => False) selected :=
  .branch (.local _) (.local _) (.same (.inr rfl) fresh_ready)
theorem arguments_ready : ReadyArgs (fun _ => False) arguments :=
  .cons _ (.inr rfl) (.local _) (.cons _ (.inr rfl) fresh_ready .nil)

theorem choice_progress_and_memory (p : Roadmap.Pipeline) :
    NS (evalE (globals p) frame 4 selected) ∧
    (MemOK E seed.ty (small,state) ∧
      RValOK E state.heap.ty (.val (.memRef rfl 0) : RVal E.layout (.bytes .memory))) ∧
    (MemOK E seed.ty (chooseFresh,grown) ∧
      RValOK E grown.heap.ty (.val (.memRef rfl 1) : RVal E.layout (.bytes .memory))) ∧
    MemOK E seed.ty (oversized,state) := by
  have joint := ready_progress_and_preservation (Preservation.NewArrayFragmentControls.calls p)
    frame rfl 4 selected selected_ready seed.ty
  have alias := joint.2 (small,state) Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.initial_mem.1
  have allocated := joint.2 (chooseFresh,state) initial_mem.1
  have panic := joint.2 (oversized,state) initial_mem.2
  rw [(source_runs p).1] at alias
  rw [(source_runs p).2.1] at allocated
  rw [(source_runs p).2.2] at panic
  exact ⟨joint.1,alias,allocated,panic⟩

theorem arguments_progress_and_memory (p : Roadmap.Pipeline) :
    NS (evalConvArgs (globals p) frame 4 arguments) ∧
    MemOK E seed.ty (small,grown) ∧
    RValsOK E grown.heap.ty
      (Vals.toR (.cons (τ := .bytes .memory) (.memRef rfl 0)
        (.cons (τ := .bytes .memory) (.memRef rfl 1) .nil))) := by
  have joint := ready_args_progress_and_preservation (Preservation.NewArrayFragmentControls.calls p)
    frame rfl 4 arguments arguments_ready seed.ty
  have actual := joint.2 (small,state) Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.initial_mem.1
  rw [argument_run] at actual
  exact ⟨joint.1,actual⟩

theorem arguments_large_run (p : Roadmap.Pipeline) :
    (evalConvArgs (globals p) frame 4 arguments).run (oversized,state) =
      (.error (.revert (panicData .alloc)),(oversized,state)) := rfl

theorem arguments_panic_preserved (p : Roadmap.Pipeline) : MemOK E seed.ty (oversized,state) := by
  have actual := (ready_args_progress_and_preservation (Preservation.NewArrayFragmentControls.calls p)
    frame rfl 4 arguments arguments_ready seed.ty).2 (oversized,state) initial_mem.2
  rw [arguments_large_run] at actual
  exact actual

theorem low_horizon (p : Roadmap.Pipeline) :
    (evalE (globals p) frame 3 selected).run (chooseFresh,state) =
      (.error .timeout,(chooseFresh,state)) := Preservation.AllocatingControls.low_horizon p

theorem literal_refused : ¬ReadyExpr (E := E) (Γ := Γ) (fun _ => False) (.str []) :=
  fun ready => Preservation.AllocatingControls.literal_not_admitted ready.allocating

#print axioms choice_progress_and_memory
#print axioms arguments_progress_and_memory
#print axioms arguments_large_run
#print axioms literal_refused
end Solidity.Source.Progress.ReadyExpressionControls

namespace Solidity.Source.Progress.ReadyExpressionControls.Program
open EM Preservation.MemoryProgramControls

def selection (flag : Bool) : RExpr E [Aty] Aty :=
  .cond (.bool flag) (.local .here)
    (.newArray (τ := Aty) rfl (.const (Q.ofInt 2)) (by decide +kernel))
def fresh : Data E.layout Aty := .array 2 (fun _ h => nomatch h) (fun _ => .val (.int 0 (by decide)))
def freshState : St E := {initial with heap := (seed.alloc ⟨Aty,fresh⟩).1}

theorem admitted (flag : Bool) : ReadyExpr (fun d => d ∈ ([] : List Decl)) (selection flag) :=
  .branch (.value trivial trivial) (.local _)
    (.newArray (.array (.int .u256) rfl rfl) _ (.value trivial trivial))

theorem checked (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (flag : Bool) :
    NS (evalE (glob p fixed) frame 5 (selection flag)) ∧
    Hoare (MemOK E seed.ty) (evalE (glob p fixed) frame 5 (selection flag))
      (fun v y => MemOK E seed.ty y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E seed.ty y) :=
  ready_from_elaborate resolution actual_elaboration (glob p fixed) rfl "Memory" [] (value_check p fixed)
    frame rfl 5 (selection flag) (admitted flag) seed.ty

theorem run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (flag : Bool) :
    (evalE (glob p fixed) frame 5 (selection flag)).run (caller,initial) =
      (.ok (.val (.memRef rfl (if flag then 0 else 1))),(caller,if flag then initial else freshState)) := by
  cases flag <;> rfl

theorem preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (flag : Bool) :
    NS (evalE (glob p fixed) frame 5 (selection flag)) ∧
    MemOK E seed.ty (caller,if flag then initial else freshState) ∧
    RValOK E (if flag then initial else freshState).heap.ty
      (.val (.memRef rfl (if flag then 0 else 1)) : RVal E.layout Aty) := by
  have actual := (checked p fixed flag).2 (caller,initial) caller_mem
  rw [run] at actual
  exact ⟨(checked p fixed flag).1,actual⟩

def parameters (flag : Bool) : RConvArgs E [Aty] [Aty,Aty] :=
  .cons (.local .here) (by decide +kernel) (.cons (selection flag) (by decide +kernel) .nil)

theorem parameters_admitted (flag : Bool) : ReadyArgs (fun d => d ∈ ([] : List Decl)) (parameters flag) :=
  .cons _ (.inr rfl) (.local _) (.cons _ (.inr rfl) (admitted flag) .nil)

theorem parameters_checked (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (flag : Bool) :
    NS (evalConvArgs (glob p fixed) frame 7 (parameters flag)) ∧
    Hoare (MemOK E seed.ty) (evalConvArgs (glob p fixed) frame 7 (parameters flag))
      (fun vs y => MemOK E seed.ty y ∧ RValsOK E y.2.heap.ty vs.toR) (fun _ y => MemOK E seed.ty y) :=
  ready_args_from_elaborate resolution actual_elaboration (glob p fixed) rfl "Memory" [] (value_check p fixed)
    frame rfl 7 (parameters flag) (parameters_admitted flag) seed.ty

theorem parameters_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (flag : Bool) :
    (evalConvArgs (glob p fixed) frame 7 (parameters flag)).run (caller,initial) =
      (.ok (.cons (.memRef rfl 0) (.cons (.memRef rfl (if flag then 0 else 1)) .nil)),
        (caller,if flag then initial else freshState)) := by cases flag <;> rfl

theorem parameters_preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (flag : Bool) :
    NS (evalConvArgs (glob p fixed) frame 7 (parameters flag)) ∧
    MemOK E seed.ty (caller,if flag then initial else freshState) ∧
    RValsOK E (if flag then initial else freshState).heap.ty
      (Vals.toR (.cons (τ := Aty) (.memRef rfl 0)
        (.cons (τ := Aty) (.memRef rfl (if flag then 0 else 1)) .nil))) := by
  have actual := (parameters_checked p fixed flag).2 (caller,initial) caller_mem
  rw [parameters_run] at actual
  exact ⟨(parameters_checked p fixed flag).1,actual⟩

#print axioms parameters_preserved
#print axioms parameters_run
#print axioms checked
#print axioms preserved
#print axioms run
end Solidity.Source.Progress.ReadyExpressionControls.Program
