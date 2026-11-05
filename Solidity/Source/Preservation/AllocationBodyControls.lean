import Solidity.Source.Preservation.MemoryBodies
import Solidity.Source.Preservation.ArrayLiteralControls
import Solidity.Source.Preservation.EncodingVariantControls

/-! Actual typed allocation nodes composed in admitted memory-body statements.
The initialized memory prefix survives struct, inline-array and ABI allocations.
Both pipelines and the encoding-head refusal boundary are retained. -/
namespace Solidity.Source.Preservation.AllocationBodyControls
open EM AllocationControls

theorem fields_admitted : ExactArgs (fun _ => False) args :=
  .cons rfl (.value trivial trivial) (.cons rfl (.value trivial trivial) .nil)

theorem constructor_admitted : BodyExpr (fun _ => False) constructor := by
  rw [constructor_eq]
  exact .structNew _ fields_admitted

theorem literal_admitted : BodyExpr (fun _ => False) ArrayLiteralControls.literal := by
  rw [ArrayLiteralControls.literal_eq]
  exact .inlineArray rfl fields_admitted

theorem packed_admitted : BodyExpr (fun _ => False) EncodingVariantControls.packed :=
  .encode .encodePacked rfl (.cons (.value trivial trivial) .nil)
theorem encoder_admitted : BodyExpr (fun _ => False) encoder :=
  .encode .encode rfl (.cons (.value trivial trivial) .nil)
theorem selector_admitted : BodyExpr (fun _ => False) EncodingVariantControls.selector :=
  .encode .encodeWithSelector rfl (.string _ (.cons (.value trivial trivial) .nil))
theorem signature_admitted : BodyExpr (fun _ => False) EncodingVariantControls.signature :=
  .encode .encodeWithSignature rfl (.string _ (.cons (.value trivial trivial) .nil))

def sequence : RStmt E [] false .body [.bool] [.bool] := .block
  (.stmt (.expr constructor) (.stmt (.expr ArrayLiteralControls.literal)
    (.stmt (.expr EncodingVariantControls.packed) .nil)))
def after : St E := {EncodingVariantControls.initial with heap :=
  (((EncodingVariantControls.initial.heap.alloc ⟨_,structData⟩).1.alloc
    ⟨_,ArrayLiteralControls.data⟩).1.alloc ⟨.bytes .memory,.bytes [1]⟩).1}

theorem sequence_admitted : MemoryStmt (fun _ => False) [] false sequence :=
  .block (.stmt (.expr constructor_admitted)
    (.stmt (.expr literal_admitted) (.stmt (.expr packed_admitted) .nil)))
theorem calls (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    CallsOK (fun _ => False) (glob p fixed) frame.contract := by
  intro d ps rs signature impossible
  cases impossible

theorem sequence_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (execS (glob p fixed) frame 16 0 none sequence (.cons (.bool false) .nil)).run
      (.nil,EncodingVariantControls.initial) =
      (.ok (.normal (.cons (.bool false) .nil)),(.nil,after)) := by cases p <;> rfl

theorem sequence_preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    MemOK E (Heap.empty : Heap E.layout).ty ((.nil : Locals E.layout []),after) ∧
      after.heap.next = 4 := by
  have valid := EncodingVariantControls.initial_mem
  have actual := (memory_body_at (calls p fixed) 16).stmt frame rfl 0 none sequence
    sequence_admitted (.cons (.bool false) .nil) (Heap.empty : Heap E.layout).ty
    (.nil,EncodingVariantControls.initial) ⟨relocalize valid .nil trivial,trivial,trivial⟩
  rw [sequence_run] at actual
  exact ⟨actual.1,rfl⟩

theorem selector_preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    MemOK E (Heap.empty : Heap E.layout).ty
      ((evalE (glob p fixed) frame 10 EncodingVariantControls.selector).run
        (.cons (.bool false) .nil,EncodingVariantControls.initial)).2 ∧
    RValOK E
      ((evalE (glob p fixed) frame 10 EncodingVariantControls.selector).run
        (.cons (.bool false) .nil,EncodingVariantControls.initial)).2.2.heap.ty
      (.val (.memRef rfl 1) : RVal E.layout (.bytes .memory)) := by
  have actual := eval_body_expr_mem (calls p fixed) frame rfl 10 _ selector_admitted
    (Heap.empty : Heap E.layout).ty _ EncodingVariantControls.initial_mem
  rw [EncodingVariantControls.selector_run] at actual ⊢
  exact actual

theorem signature_preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    MemOK E (Heap.empty : Heap E.layout).ty
      ((evalE (glob p fixed) frame 10 EncodingVariantControls.signature).run
        (.cons (.bool false) .nil,EncodingVariantControls.initial)).2 ∧
    RValOK E
      ((evalE (glob p fixed) frame 10 EncodingVariantControls.signature).run
        (.cons (.bool false) .nil,EncodingVariantControls.initial)).2.2.heap.ty
      (.val (.memRef rfl 1) : RVal E.layout (.bytes .memory)) := by
  have actual := eval_body_expr_mem (calls p fixed) frame rfl 10 _ signature_admitted
    (Heap.empty : Heap E.layout).ty _ EncodingVariantControls.initial_mem
  rw [EncodingVariantControls.signature_run] at actual ⊢
  exact actual

theorem missing_selector_boundary : AbiKind.encodeWithSelector.argsOK E.isBase [] = false := rfl
theorem missing_signature_boundary : AbiKind.encodeWithSignature.argsOK E.isBase [] = false := rfl

theorem missing_selector_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 3 (.abiEncode .encodeWithSelector
      (.nil : RArgs E [.bool] []))).run (.cons (.bool false) .nil,EncodingVariantControls.initial) =
      (.error (.stuck "abi arguments"),(.cons (.bool false) .nil,EncodingVariantControls.initial)) :=
  EncodingVariantControls.missing_selector p fixed

def freshBytes : RExpr E [.bool] (.bytes .memory) :=
  .newArray rfl (.const (Q.ofInt 2)) (by decide +kernel)
def hugeBytes : RExpr E [.bool] (.bytes .memory) :=
  .newArray rfl (.const (Q.ofInt (2^64))) (by decide +kernel)
def nested : RExpr E [.bool] (.bytes .memory) :=
  .abiEncode .encodePacked (.cons freshBytes .nil)
def failingTail : RExpr E [.bool] (.bytes .memory) :=
  .abiEncode .encodePacked (.cons freshBytes (.cons hugeBytes .nil))
def childAfter : St E := {EncodingVariantControls.initial with heap :=
  (EncodingVariantControls.initial.heap.alloc ⟨.bytes .memory,.bytes [0,0]⟩).1}
def nestedAfter : St E := {childAfter with heap :=
  (childAfter.heap.alloc ⟨.bytes .memory,.bytes [0,0]⟩).1}

theorem nested_admitted : BodyExpr (fun _ => False) nested :=
  .encode .encodePacked rfl (.cons (.newArray rfl _ (.value trivial trivial)) .nil)
theorem tail_admitted : BodyExpr (fun _ => False) failingTail :=
  .encode .encodePacked rfl (.cons (.newArray rfl _ (.value trivial trivial))
    (.cons (.newArray rfl _ (.value trivial trivial)) .nil))

theorem nested_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 12 nested).run (.cons (.bool false) .nil,EncodingVariantControls.initial) =
      (.ok (.val (.memRef rfl 2)),(.cons (.bool false) .nil,nestedAfter)) := by cases p <;> rfl

theorem tail_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 12 failingTail).run (.cons (.bool false) .nil,EncodingVariantControls.initial) =
      (.error (.revert (panicData .alloc)),(.cons (.bool false) .nil,childAfter)) := by cases p <;> rfl

theorem nested_preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (MemOK E (Heap.empty : Heap E.layout).ty (.cons (.bool false) .nil,nestedAfter) ∧
      RValOK E nestedAfter.heap.ty (.val (.memRef rfl 2) : RVal E.layout (.bytes .memory))) ∧
    MemOK E (Heap.empty : Heap E.layout).ty (.cons (.bool false) .nil,childAfter) := by
  have success := eval_body_expr_mem (calls p fixed) frame rfl 12 _ nested_admitted
    (Heap.empty : Heap E.layout).ty _ EncodingVariantControls.initial_mem
  have failure := eval_body_expr_mem (calls p fixed) frame rfl 12 _ tail_admitted
    (Heap.empty : Heap E.layout).ty _ EncodingVariantControls.initial_mem
  rw [nested_run] at success
  rw [tail_run] at failure
  exact ⟨success,failure⟩

#print axioms nested_preserved
#print axioms nested_run
#print axioms tail_run
#print axioms sequence_preserved
#print axioms selector_preserved
#print axioms signature_preserved
#print axioms sequence_run
#print axioms missing_selector_run
end Solidity.Source.Preservation.AllocationBodyControls
