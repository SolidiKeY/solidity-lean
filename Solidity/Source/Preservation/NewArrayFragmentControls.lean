import Solidity.Source.Preservation.NewArrayFragment
import Solidity.Roadmap.V16.SSCP2.NewAllocationControls

/-! Computed local length with a live caller reference: two plus two
allocates four elements; oversized lengths and low horizons keep their halts.
These are source preservation observations, not compiler/EVM certificates. -/
namespace Solidity.Source.Preservation.NewArrayFragmentControls
open EM Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls

def lengthExpr : RExpr E Γ (.int .u256) := .binary .add (.local .here) (.local .here)
def expression : RExpr E Γ (.array .memory .bool none) := .newArray rfl lengthExpr rfl

theorem length_fragment : lengthExpr.ValFragC (fun _ => False) := ⟨rfl, rfl, rfl⟩
theorem length_operations : lengthExpr.OpsOK := ⟨.inl ⟨rfl, rfl⟩, trivial, trivial⟩
theorem calls (pipeline : Roadmap.Pipeline) : CallsOK (fun _ => False) (globals pipeline) frame.contract := by
  intro d ps rs signature impossible
  cases impossible

theorem checked (pipeline : Roadmap.Pipeline) (H : HeapTy) :
    Hoare (MemOK E H) (evalE (globals pipeline) frame 4 expression)
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) :=
  eval_new_fragment_mem (calls pipeline) frame rfl 3 H rfl lengthExpr rfl length_fragment length_operations

def four : Data E.layout (.array .memory .bool none) :=
  .array 4 (fun _ h => nomatch h) (fun _ => .val (.bool false))
def grown : St E := {state with heap := (seed.alloc ⟨.array .memory .bool none, four⟩).1}

theorem runs (pipeline : Roadmap.Pipeline) :
    (evalE (globals pipeline) frame 4 expression).run (small, state) =
      (.ok (.val (.memRef rfl 1)), (small, grown)) := by cases pipeline <;> rfl

theorem large_refused (pipeline : Roadmap.Pipeline) :
    (evalE (globals pipeline) frame 4 expression).run (huge, state) =
      (.error (.revert (panicData .alloc)), (huge, state)) := by cases pipeline <;> rfl

theorem preserved (pipeline : Roadmap.Pipeline) :
    MemOK E seed.ty (small, grown) ∧
    RValOK E grown.heap.ty (.val (τ := .array .memory .bool none) (.memRef rfl 1)) ∧
    MemOK E seed.ty (huge, state) := by
  have successful := checked pipeline seed.ty (small, state) initial_mem.1
  have refused := checked pipeline seed.ty (huge, state) initial_mem.2
  rw [runs] at successful
  rw [large_refused] at refused
  exact ⟨successful.1, successful.2, refused⟩

theorem caller_prefix : grown.heap.get 0 = seed.get 0 ∧ grown.heap.next = 2 ∧
    small.get (.there .here) = .memRef rfl 0 := ⟨rfl, rfl, rfl⟩

theorem low_horizon (pipeline : Roadmap.Pipeline) :
    (evalE (globals pipeline) frame 1 expression).run (small, state) =
      (.error .timeout, (small, state)) := rfl

theorem compound_horizon_three (pipeline : Roadmap.Pipeline) :
    (evalE (globals pipeline) frame 3 expression).run (small, state) =
      (.error .timeout, (small, state)) := by cases pipeline <;> rfl

#print axioms checked
#print axioms preserved
#print axioms runs
#print axioms large_refused
end Solidity.Source.Preservation.NewArrayFragmentControls
