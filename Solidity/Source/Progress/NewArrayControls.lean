import Solidity.Source.Progress.NewArray
import Solidity.Source.Preservation.NewArrayFragmentControls
import Solidity.Source.Preservation.MemoryProgramControls

/-! Inhabited allocation progress and exact observations. A compound length
keeps allocation panic and timeout; a missing enum default retains its named
stuck outcome outside readiness. A separate client consumes real elaboration. -/
namespace Solidity.Source.Progress.NewArrayControls
open EM
open Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls (E Γ seed state small huge frame globals initial_mem)
open Solidity.Source.Preservation.NewArrayFragmentControls
  (expression lengthExpr length_fragment length_operations calls runs large_refused low_horizon compound_horizon_three grown)

theorem progress (p : Roadmap.Pipeline) : NS (evalE (globals p) frame 4 expression) :=
  new_fragment_ns (calls p) frame rfl 3 (.array .bool rfl rfl) lengthExpr rfl length_fragment length_operations

theorem progress_and_memory (p : Roadmap.Pipeline) :
    NS (evalE (globals p) frame 4 expression) ∧
    MemOK E seed.ty (small,grown) ∧
    RValOK E grown.heap.ty (.val (.memRef rfl 1) : RVal E.layout (.array .memory .bool none)) ∧
    MemOK E seed.ty (huge,state) :=
  ⟨progress p,Preservation.NewArrayFragmentControls.preserved p⟩

theorem actual_runs (p : Roadmap.Pipeline) :
    (evalE (globals p) frame 4 expression).run (small,state) =
      (.ok (.val (.memRef rfl 1)),(small,grown)) ∧
    (evalE (globals p) frame 4 expression).run (huge,state) =
      (.error (.revert (panicData .alloc)),(huge,state)) ∧
    (evalE (globals p) frame 3 expression).run (small,state) =
      (.error .timeout,(small,state)) :=
  ⟨runs p,large_refused p,compound_horizon_three p⟩

def missing : DeclName := ⟨none,"MissingEnum"⟩
abbrev badType : STy := .array .memory (.enum missing) none

theorem still_newable : badType.newable = true := rfl
theorem missing_default : (Val.default E.layout (.enum missing)).isSome = false := rfl

theorem not_ready : ¬NewReady E badType := by
  intro ready
  have valid := NewReady.array_default ready
  rw [missing_default] at valid
  cases valid

def refused : RExpr E Γ badType := .newArray still_newable (.const (Q.ofInt 2)) (by decide +kernel)

theorem missing_default_run (p : Roadmap.Pipeline) :
    (evalE (globals p) frame 4 refused).run (small,state) =
      (.error (.stuck "new of this element type"),(small,state)) := rfl

theorem missing_default_not_ns (p : Roadmap.Pipeline) : ¬NS (evalE (globals p) frame 4 refused) := by
  intro h
  have impossible := h (small,state) "new of this element type"
  rw [missing_default_run] at impossible
  exact impossible rfl

#print axioms missing_default_not_ns
#print axioms progress
#print axioms progress_and_memory
#print axioms actual_runs
#print axioms missing_default_run
end Solidity.Source.Progress.NewArrayControls

namespace Solidity.Source.Progress.NewArrayProgramControls
open EM Preservation.MemoryProgramControls

def allocation : RExpr E [Aty] (.bytes .memory) :=
  .newArray rfl (.const (Q.ofInt 2)) (by decide +kernel)
def allocated : St E := {initial with heap := (seed.alloc ⟨.bytes .memory,.bytes [0,0]⟩).1}

theorem checked (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (glob p fixed) frame 4 allocation) ∧
    Hoare (MemOK E seed.ty) (evalE (glob p fixed) frame 4 allocation)
      (fun v y => MemOK E seed.ty y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E seed.ty y) :=
  new_from_elaborate resolution actual_elaboration (glob p fixed) rfl "Memory" [] (value_check p fixed)
    frame rfl 3 .bytes (RExpr.const (E := E) (Γ := [Aty]) (Q.ofInt 2))
      (by decide +kernel) (by trivial) (by trivial) seed.ty

theorem run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 4 allocation).run (caller,initial) =
      (.ok (.val (.memRef rfl 1)),(caller,allocated)) := rfl

theorem preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (glob p fixed) frame 4 allocation) ∧
    MemOK E seed.ty (caller,allocated) ∧
    RValOK E allocated.heap.ty (.val (.memRef rfl 1) : RVal E.layout (.bytes .memory)) := by
  have actual := (checked p fixed).2 (caller,initial) caller_mem
  rw [run] at actual
  exact ⟨(checked p fixed).1,actual⟩

#print axioms checked
#print axioms preserved
#print axioms run
end Solidity.Source.Progress.NewArrayProgramControls
