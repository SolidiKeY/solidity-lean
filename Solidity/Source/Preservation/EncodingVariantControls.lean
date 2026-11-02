import Solidity.Source.Preservation.EncodingVariants
import Solidity.Source.Preservation.AllocationControls
import Solidity.Source.Preservation.CallerReferenceControls

/-! Actual Typed.toR encoding variants, both pipelines, an inhabited nonempty
heap, complete caller/state observations and missing-head named refusals.
The `*_mem` preservation triples are stated for an arbitrary heap typing. -/
namespace Solidity.Source.Preservation.EncodingVariantControls
open AllocationControls

def packedSyn : Syn .expr := .call (.member (.ident "abi") "encodePacked")
  (.positional (.cons (.lit (.bool true)) .nil))
def packedTyped : Typed ctx packedSyn (.bytes .memory) :=
  .abiEncode rfl rfl (.cons (.bool true) .nil) rfl
def packed : RExpr E [.bool] (.bytes .memory) := packedTyped.toR

def selectorSyn : Syn .expr := .call (.member (.ident "abi") "encodeWithSelector")
  (.positional (.cons (.lit (.hexStr [1,2,3,4])) (.cons (.lit (.bool true)) .nil)))
def selectorTyped : Typed ctx selectorSyn (.bytes .memory) :=
  .abiEncode rfl rfl (.cons (.hexStr [1,2,3,4]) (.cons (.bool true) .nil)) rfl
def selector : RExpr E [.bool] (.bytes .memory) := selectorTyped.toR

def signatureSyn : Syn .expr := .call (.member (.ident "abi") "encodeWithSignature")
  (.positional (.cons (.lit (.str [102,40,41])) (.cons (.lit (.bool true)) .nil)))
def signatureTyped : Typed ctx signatureSyn (.bytes .memory) :=
  .abiEncode rfl rfl (.cons (.str [102,40,41]) (.cons (.bool true) .nil)) rfl
def signature : RExpr E [.bool] (.bytes .memory) := signatureTyped.toR

def initial : St E := CallerReferenceControls.original

theorem initial_mem : MemOK E (Heap.empty : Heap E.layout).ty
    (.cons (.bool false) .nil, initial) :=
  relocalize (CallerReferenceControls.caller_valid (E := E)) _ ⟨trivial, trivial⟩

theorem packed_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 10 packed).run (.cons (.bool false) .nil, initial) =
    (.ok (.val (.memRef rfl 1)), (.cons (.bool false) .nil,
      {initial with heap := (initial.heap.alloc ⟨.bytes .memory, .bytes [1]⟩).1})) := by cases p <;> rfl

theorem selector_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 10 selector).run (.cons (.bool false) .nil, initial) =
    (.ok (.val (.memRef rfl 1)), (.cons (.bool false) .nil,
      {initial with heap := (initial.heap.alloc ⟨.bytes .memory, .bytes ([1,2,3,4] ++ encoded)⟩).1})) := by cases p <;> rfl

theorem signature_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 10 signature).run (.cons (.bool false) .nil, initial) =
    (.ok (.val (.memRef rfl 1)), (.cons (.bool false) .nil,
      {initial with heap := (initial.heap.alloc ⟨.bytes .memory,
        .bytes ((wordBytes (fixed.hash [102,40,41])).take 4 ++ encoded)⟩).1})) := by cases p <;> rfl

def selArgs : RArgs E [.bool] [.stringLit [1,2,3,4], .bool] := .cons (.str [1,2,3,4]) (.cons (.bool true) .nil)
def sigArgs : RArgs E [.bool] [.stringLit [102,40,41], .bool] := .cons (.str [102,40,41]) (.cons (.bool true) .nil)

theorem packed_mem (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (H : HeapTy) :
    Hoare (MemOK E H) (evalE (glob p fixed) frame 10 packed)
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  change Hoare _ (evalE _ _ _ (.abiEncode .encodePacked (.cons (.bool true) .nil))) _ _
  apply evalE_encodePacked_mem
  rw [encoder_args_eq]
  exact Hoare.pure' fun _ h => h

theorem selector_mem (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (H : HeapTy) :
    Hoare (MemOK E H) (evalE (glob p fixed) frame 10 selector)
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  change Hoare _ (evalE _ _ _ (.abiEncode .encodeWithSelector selArgs)) _ _
  apply evalE_encodeWithSelector_mem _ _ _ _ rfl
  have ha : evalArgs (glob p fixed) frame 9 selArgs = pure (.cons (.strLit [1,2,3,4]) (.cons (.val (.bool true)) .nil)) := by cases p <;> rfl
  rw [ha]
  exact Hoare.pure' fun _ h => h

theorem signature_mem (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (H : HeapTy) :
    Hoare (MemOK E H) (evalE (glob p fixed) frame 10 signature)
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  change Hoare _ (evalE _ _ _ (.abiEncode .encodeWithSignature sigArgs)) _ _
  apply evalE_encodeWithSignature_mem
  have ha : evalArgs (glob p fixed) frame 9 sigArgs = pure (.cons (.strLit [102,40,41]) (.cons (.val (.bool true)) .nil)) := by cases p <;> rfl
  rw [ha]
  exact Hoare.pure' fun _ h => h

theorem missing_selector (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 3 (.abiEncode .encodeWithSelector (.nil : RArgs E [.bool] []))).run
      (.cons (.bool false) .nil, initial) = (.error (.stuck "abi arguments"), (.cons (.bool false) .nil, initial)) := by cases p <;> rfl

theorem missing_signature (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 3 (.abiEncode .encodeWithSignature (.nil : RArgs E [.bool] []))).run
      (.cons (.bool false) .nil, initial) = (.error (.stuck "abi arguments"), (.cons (.bool false) .nil, initial)) := by cases p <;> rfl

#print axioms packed_mem
#print axioms selector_mem
#print axioms signature_mem
#print axioms selector_run
#print axioms signature_run
end Solidity.Source.Preservation.EncodingVariantControls
