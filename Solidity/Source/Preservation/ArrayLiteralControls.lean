import Solidity.Source.Preservation.ArrayLiterals
import Solidity.Source.Preservation.AllocationControls

/-! Typed Boolean inline-array allocation, both pipelines, and the one-word
element boundary. -/
namespace Solidity.Source.Preservation.ArrayLiteralControls
open AllocationControls

def syn : Syn .expr := .inlineArray (.lit (.bool true)) (.cons (.lit (.bool false)) .nil)
def typed : Typed ctx syn (.array .memory .bool (some 2)) :=
  .inlineArray (.bool true) (.cons (.bool false) .nil) rfl rfl rfl
def literal : RExpr E [.bool] (.array .memory .bool (some 2)) := typed.toR

theorem literal_eq : literal = .inlineArray args rfl := rfl

def data : Data E.layout (.array .memory .bool (some 2)) :=
  inlineData (.cons (.bool true) (.cons (.bool false) .nil))

theorem literal_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 10 literal).run (.cons (.bool false) .nil, St.init E) =
    (.ok (.val (.memRef rfl 0)), (.cons (.bool false) .nil,
      {St.init E with heap := (Heap.empty.alloc ⟨_, data⟩).1})) := by cases p <;> rfl

theorem literal_mem (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (H : HeapTy) :
    Hoare (MemOK E H) (evalE (glob p fixed) frame 10 literal)
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  rw [literal_eq]
  apply evalE_inlineArray_mem
  rw [args_eq]
  exact Hoare.pure' fun _ h => ⟨h, ⟨trivial, ⟨trivial, trivial⟩⟩⟩

theorem reference_elements_refused : (STy.bytes .memory).oneWord = false := rfl

#print axioms literal_run
#print axioms literal_mem
end Solidity.Source.Preservation.ArrayLiteralControls
