import Solidity.Source.Progress.ReadyBodyControls

/-! Direct intrinsic controls for the conditional, unchecked restoration and
reference-tuple return arms of the ready statement admission. The source-unit
control in ReadyBodyControls supplies the actual elaboration consumer. -/
namespace Solidity.Source.Progress.ReadyScopeControls
open EM ReadyBodyControls

theorem calls (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    CallsOK (fun d => d ∈ ([] : List Decl)) (glob p fixed) "Memory" :=
  Solidity.Lowering.P9.WholeProgram.from_elaborate resolution actual_elaboration
    (glob p fixed) rfl "Memory" [] (value_check p fixed)

def bools (b : Bool) : Locals E.layout [.bool] := .cons (.bool b) .nil
def branch : RStmt E [] false .body [.bool] [.bool] :=
  .ifElse (.local .here) (.block (.stmt (.declVar Aty) .nil)) .skip

theorem branch_ready : ReadyStmt (fun d => d ∈ ([] : List Decl)) [] false branch :=
  .ifElse (.local _) (.block (.stmt (.declVar Aty (.memory (.array _))) .nil))
    (.value trivial trivial)

def oneDefault : St E := {initial with heap := (seed.alloc ⟨Aty,empty⟩).1}

theorem branch_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (b : Bool) :
    (execS (glob p fixed) frame 10 0 none branch (bools b)).run (.nil,initial) =
      (.ok (.normal (bools b)),(.nil,if b then oneDefault else initial)) := by
  cases p <;> cases b <;> rfl

theorem branch_checked (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (b : Bool) :
    NSP (execS (glob p fixed) frame 10 0 none branch (bools b)) (fun o => o.esc = false) ∧
    MemOK E seed.ty ((.nil : Locals E.layout []),if b then oneDefault else initial) := by
  have progress := (ready_body_at (calls p fixed) 10).stmt frame rfl 0 none branch branch_ready
    (bools b) ⟨[.bool],[],rfl,rfl⟩
  have memory := (Preservation.memory_body_at (calls p fixed) 10).stmt frame rfl 0 none branch
    branch_ready.memory (bools b) seed.ty (.nil,initial) ⟨entry_mem,trivial,trivial⟩
  rw [branch_run] at memory
  exact ⟨NSP.weaken progress (fun _ h => h rfl),memory.1⟩

def lengthLocal : Locals E.layout [U] := .cons (.int 2 (by decide)) .nil
def uncheckedItems : RItems E [] false .body [U] [Aty,U] :=
  .unchecked (.stmt (.declVar Aty) .nil)
    (.stmt (.declInit (τ := Aty) (.newArray (τ := Aty) rfl (.local .here) rfl)
      (by decide +kernel)) .nil)

theorem unchecked_ready : ReadyItems (fun d => d ∈ ([] : List Decl)) [] false uncheckedItems :=
  .unchecked (.stmt (.declVar Aty (.memory (.array _))) .nil)
    (.stmt (.declInit _ (.inr rfl) (.newArray (.array U rfl rfl) rfl (.local _))) .nil)

def uncheckedAfter : St E :=
  {initial with heap := ((seed.alloc ⟨Aty,empty⟩).1.alloc ⟨Aty,fresh⟩).1}
def uncheckedLocals : Locals E.layout [Aty,U] := .cons (.memRef rfl 2) lengthLocal

theorem unchecked_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (execItems (glob p fixed) frame 20 0 none uncheckedItems lengthLocal).run (.nil,initial) =
      (.ok (.normal uncheckedLocals),(.nil,uncheckedAfter)) := by
  cases p <;> rfl

theorem unchecked_checked (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NSP (execItems (glob p fixed) frame 20 0 none uncheckedItems lengthLocal) (fun o => o.esc = false) ∧
    MemOK E seed.ty ((.nil : Locals E.layout []),uncheckedAfter) ∧
    LocalsOK E uncheckedAfter.heap.ty uncheckedLocals := by
  have joint := ready_items_progress_and_memory (calls p fixed) frame rfl 20 0 none
    uncheckedItems unchecked_ready lengthLocal ⟨[U],[],rfl,rfl⟩ seed.ty
  have actual := joint.2 (.nil,initial) ⟨entry_mem,trivial,trivial⟩
  rw [unchecked_run] at actual
  exact ⟨NSP.weaken joint.1 (fun _ h => h rfl),actual⟩

def tupleReturn : RStmt E [Aty] false .body [Aty] [Aty] :=
  .retTuple (.cons (.local .here) (by decide +kernel) .nil)

theorem tuple_ready : ReadyStmt (fun d => d ∈ ([] : List Decl)) [Aty] false tupleReturn :=
  .returns (.cons _ (.inr rfl) (.local _) .nil)

def referenceLocal : Locals E.layout [Aty] := .cons (.memRef rfl 0) .nil

theorem tuple_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (execS (glob p fixed) frame 10 0 none tupleReturn referenceLocal).run (.nil,initial) =
      (.ok (.ret referenceLocal),(.nil,initial)) := by
  cases p <;> rfl

theorem tuple_checked (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NSP (execS (glob p fixed) frame 10 0 none tupleReturn referenceLocal) (fun o => o.esc = false) ∧
    LocalsOK E initial.heap.ty referenceLocal := by
  have progress := (ready_body_at (calls p fixed) 10).stmt frame rfl 0 none tupleReturn tuple_ready
    referenceLocal ⟨[],[],rfl,rfl⟩
  have memory := (Preservation.memory_body_at (calls p fixed) 10).stmt frame rfl 0 none tupleReturn
    tuple_ready.memory referenceLocal seed.ty (.nil,initial) ⟨entry_mem,⟨Aty,rfl,rfl⟩,trivial⟩
  rw [tuple_run] at memory
  exact ⟨NSP.weaken progress (fun _ h => h rfl),memory.2⟩

#print axioms branch_checked
#print axioms unchecked_checked
#print axioms tuple_checked
end Solidity.Source.Progress.ReadyScopeControls
