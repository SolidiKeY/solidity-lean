import Solidity.Source.Progress.InlineArrayParents
import Solidity.Source.Preservation.MemoryProgramControls

/-! Inhabited inline-array progress over a live caller reference and a nonempty
heap. The checked-elaboration adapter is consumed in both evaluator pipelines;
exact allocation, child panic, horizon and readiness boundaries are retained. -/
namespace Solidity.Source.Progress.InlineArrayParentControls
open EM Preservation.MemoryProgramControls

def args : RConvArgs E [Aty] [.bool,.bool] :=
  .cons (.bool true) rfl (.cons (.bool false) rfl .nil)
def expression : RExpr E [Aty] (.array .memory .bool (some 2)) := .inlineArray args rfl
def data : Data E.layout (.array .memory .bool (some 2)) :=
  inlineData (.cons (.bool true) (.cons (.bool false) .nil))
def allocated : St E := {initial with heap := (seed.alloc ⟨_,data⟩).1}

theorem ready {A : Decl → Prop} : ReadyArgs A args :=
  .cons rfl (.inl rfl) (.value trivial trivial)
    (.cons rfl (.inl rfl) (.value trivial trivial) .nil)

theorem checked (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (glob p fixed) frame 10 expression) ∧
    Hoare (MemOK E seed.ty) (evalE (glob p fixed) frame 10 expression)
      (fun v y => MemOK E seed.ty y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E seed.ty y) :=
  inline_array_from_elaborate resolution actual_elaboration (glob p fixed) rfl "Memory" []
    (value_check p fixed) frame rfl 10 (σ:=.bool) (m:=2) args rfl ready seed.ty

theorem run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 10 expression).run (caller,initial) =
      (.ok (.val (.memRef rfl 1)),(caller,allocated)) := rfl

theorem preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (glob p fixed) frame 10 expression) ∧
    MemOK E seed.ty (caller,allocated) ∧
    RValOK E allocated.heap.ty (.val (.memRef rfl 1) : RVal E.layout (.array .memory .bool (some 2))) := by
  have actual := (checked p fixed).2 (caller,initial) caller_mem
  rw [run] at actual
  exact ⟨(checked p fixed).1,actual⟩

theorem prefix_and_frame :
    allocated.heap.get 0 = seed.get 0 ∧ allocated.heap.next = 2 ∧
    allocated.logs = initial.logs ∧ allocated.fnLocals = initial.fnLocals := ⟨rfl,rfl,rfl,rfl⟩

def statement : RStmt E [] false .body [Aty] [Aty] := .expr expression

theorem statement_checked (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (execS (glob p fixed) frame 11 0 none statement caller) ∧
    Hoare (fun y => MemOK E seed.ty y ∧ LocalsOK E y.2.heap.ty caller)
      (execS (glob p fixed) frame 11 0 none statement caller)
      (fun out y => MemOK E seed.ty y ∧ Preservation.OutRefsOK (E:=E) y.2.heap.ty out)
      (fun _ y => MemOK E seed.ty y) :=
  inline_array_statement_progress_and_memory
    (Solidity.Lowering.P9.WholeProgram.from_elaborate resolution actual_elaboration
      (glob p fixed) rfl "Memory" [] (value_check p fixed))
    frame rfl 11 (σ:=.bool) (m:=2) args rfl ready 0 none caller seed.ty

theorem statement_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (execS (glob p fixed) frame 11 0 none statement caller).run (L0 E,initial) =
      (.ok (.normal caller),(L0 E,allocated)) := rfl

theorem statement_preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (execS (glob p fixed) frame 11 0 none statement caller) ∧
    MemOK E seed.ty (L0 E,allocated) ∧
    Preservation.OutRefsOK (E:=E) allocated.heap.ty (.normal caller : Out E.layout [Aty] [Aty]) := by
  have actual := (statement_checked p fixed).2 (L0 E,initial) ⟨entry_mem,caller_mem.1.2⟩
  rw [statement_run] at actual
  exact ⟨(statement_checked p fixed).1,actual⟩

theorem exact_boundary (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 4 expression).run (caller,initial) =
      (.ok (.val (.memRef rfl 1)),(caller,allocated)) ∧
    (evalE (glob p fixed) frame 3 expression).run (caller,initial) =
      (.error .timeout,(caller,initial)) := ⟨rfl,rfl⟩

theorem zero_horizon (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 0 expression).run (caller,initial) =
      (.error .timeout,(caller,initial)) := rfl

def divide : RExpr E [.int .u256] (.int .u256) := .binary .div (.local .here) (.local .here)
def panicArgs : RConvArgs E [.int .u256] [.int .u256] := .cons divide rfl .nil
def panicParent : RExpr E [.int .u256] (.array .memory (.int .u256) (some 1)) :=
  .inlineArray panicArgs rfl
def zero : Locals E.layout [.int .u256] := .cons (.int 0 (by decide)) .nil

theorem divide_ready {A : Decl → Prop} : ReadyExpr A divide :=
  .value ⟨rfl,rfl,rfl⟩ ⟨.inl ⟨rfl,rfl⟩,trivial,trivial⟩
theorem panic_ready {A : Decl → Prop} : ReadyArgs A panicArgs :=
  .cons rfl (.inl rfl) divide_ready .nil

theorem child_panic_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 10 panicParent).run (zero,initial) =
      (.error (.revert (panicData .divZero)),(zero,initial)) := by cases p <;> rfl

theorem child_panic_preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (glob p fixed) frame 10 panicParent) ∧ MemOK E seed.ty (zero,initial) := by
  have joint : NS (evalE (glob p fixed) frame 10 panicParent) ∧
      Hoare (MemOK E seed.ty) (evalE (glob p fixed) frame 10 panicParent)
        (fun v y => MemOK E seed.ty y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E seed.ty y) :=
    inline_array_from_elaborate resolution actual_elaboration
      (glob p fixed) rfl "Memory" [] (value_check p fixed) frame rfl 10
      (σ:=.int .u256) (m:=1) panicArgs rfl panic_ready seed.ty
  have input : MemOK E seed.ty (zero,initial) := Preservation.relocalize entry_mem zero ⟨trivial,trivial⟩
  have actual := joint.2 (zero,initial) input
  rw [child_panic_run] at actual
  exact ⟨joint.1,actual⟩

theorem old_ready_refused : ¬ReadyExpr (fun _ => False) expression := by
  intro admitted
  cases admitted with
  | value fragment _ => exact fragment

theorem reference_elements_refused : (STy.bytes .memory).oneWord = false := rfl

#print axioms ready
#print axioms checked
#print axioms run
#print axioms preserved
#print axioms prefix_and_frame
#print axioms statement_checked
#print axioms statement_run
#print axioms statement_preserved
#print axioms exact_boundary
#print axioms zero_horizon
#print axioms divide_ready
#print axioms panic_ready
#print axioms child_panic_run
#print axioms child_panic_preserved
#print axioms old_ready_refused
#print axioms reference_elements_refused
end Solidity.Source.Progress.InlineArrayParentControls
