import Solidity.Source.Preservation.ReferenceArguments
import Solidity.Source.Preservation.NewArrayFragmentControls

/-! Inhabited memory-expression and exact-argument witnesses in both source
pipelines. An alias branch keeps object 0; an allocating branch returns fresh
object 1. A later argument allocation keeps an earlier argument reference valid.
These are source preservation controls, not compiler/EVM observations. -/
namespace Solidity.Source.Preservation.AllocatingControls
open EM Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls

def fresh : RExpr E Γ (.bytes .memory) := .newArray rfl (.local .here) rfl
def selected : RExpr E Γ (.bytes .memory) :=
  .cond (.local (.there (.there .here))) (.local (.there .here)) (.conv fresh (.inr rfl))
def chooseFresh : Locals E.layout Γ := .cons (.int 2 (by decide))
  (.cons (.memRef rfl 0) (.cons (.bool false) .nil))
def oversized : Locals E.layout Γ := .cons (.int (2^64) (by decide))
  (.cons (.memRef rfl 0) (.cons (.bool false) .nil))
def grown : St E := {state with heap := (seed.alloc ⟨.bytes .memory, .bytes [0,0]⟩).1}
def arguments : RConvArgs E Γ [.bytes .memory, .bytes .memory] :=
  .cons (.local (.there .here)) (by decide +kernel)
    (.cons fresh (by decide +kernel) .nil)

theorem fresh_admitted : AllocatingExpr (fun _ => False) fresh :=
  .newArray rfl rfl (.local .here)
theorem selected_admitted : AllocatingExpr (fun _ => False) selected :=
  .branch (.local _) (.local _) (.same (.inr rfl) fresh_admitted)
theorem arguments_admitted : ExactArgs (fun _ => False) arguments :=
  .cons _ (.local _) (.cons _ fresh_admitted .nil)

theorem source_runs (pipeline : Roadmap.Pipeline) :
    (evalE (globals pipeline) frame 4 selected).run (small, state) =
      (.ok (.val (.memRef rfl 0)), (small, state)) ∧
    (evalE (globals pipeline) frame 4 selected).run (chooseFresh, state) =
      (.ok (.val (.memRef rfl 1)), (chooseFresh, grown)) ∧
    (evalE (globals pipeline) frame 4 selected).run (oversized, state) =
      (.error (.revert (panicData .alloc)), (oversized, state)) := ⟨rfl,rfl,rfl⟩

theorem argument_run (pipeline : Roadmap.Pipeline) :
    (evalConvArgs (globals pipeline) frame 4 arguments).run (small, state) =
      (.ok (.cons (.memRef rfl 0) (.cons (.memRef rfl 1) .nil)), (small, grown)) := rfl

theorem initial_mem : MemOK E seed.ty (chooseFresh, state) ∧ MemOK E seed.ty (oversized, state) :=
  ⟨Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.initial_mem.1,
    Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.initial_mem.2⟩

theorem preserved (pipeline : Roadmap.Pipeline) :
    MemOK E seed.ty (chooseFresh, grown) ∧
    RValOK E grown.heap.ty (.val (τ := .bytes .memory) (.memRef rfl 1)) ∧
    MemOK E seed.ty (oversized, state) := by
  have success := eval_allocating_mem (NewArrayFragmentControls.calls pipeline) frame rfl
    4 selected selected_admitted seed.ty (chooseFresh, state) initial_mem.1
  have refusal := eval_allocating_mem (NewArrayFragmentControls.calls pipeline) frame rfl
    4 selected selected_admitted seed.ty (oversized, state) initial_mem.2
  rw [(source_runs pipeline).2.1] at success
  rw [(source_runs pipeline).2.2] at refusal
  exact ⟨success.1,success.2,refusal⟩

theorem argument_references (pipeline : Roadmap.Pipeline) :
    MemOK E seed.ty (small, grown) ∧
    RValsOK E grown.heap.ty
      (Vals.toR (.cons (τ := .bytes .memory) (.memRef rfl 0)
        (.cons (τ := .bytes .memory) (.memRef rfl 1) .nil))) := by
  have actual := eval_exact_args_mem (NewArrayFragmentControls.calls pipeline) frame rfl
    4 arguments arguments_admitted seed.ty (small, state)
    Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.initial_mem.1
  rw [argument_run] at actual
  exact actual

theorem low_horizon (pipeline : Roadmap.Pipeline) :
    (evalE (globals pipeline) frame 3 selected).run (chooseFresh, state) =
      (.error .timeout, (chooseFresh, state)) := rfl

theorem literal_not_admitted : ¬ AllocatingExpr (E := E) (Γ := Γ) (fun _ => False) (.str []) := by
  intro admitted
  cases admitted with
  | value hf _ => exact hf

theorem distinct_prefix : grown.heap.get 0 = seed.get 0 ∧ grown.heap.next = 2 := ⟨rfl,rfl⟩

#print axioms preserved
#print axioms argument_references
#print axioms source_runs
#print axioms literal_not_admitted
end Solidity.Source.Preservation.AllocatingControls
