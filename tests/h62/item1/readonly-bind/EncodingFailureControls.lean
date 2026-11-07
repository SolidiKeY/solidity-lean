import Solidity.Lowering.Readonly.CaptureFailures
import Solidity.Source.SemanticsExamples

/-! Guards against losing the encoding-failure branch after successful actual
receiver, value and argument evaluation. The allocated array is a typed memory
reference; the current encoder explicitly refuses its non-word representation.
This is an evaluator failure fixture, not a compiler-success or ABI adequacy claim. -/
namespace Solidity.H62.ReadonlyBind.EncodingFailureControls
open Solidity.Source Solidity.Source.SemanticsExamples
open Solidity.Lowering.Readonly

def arrayTy : STy := .array .memory .bool none

def declaration : Decl :=
  ⟨.function, "arrayCall", some "C", false,
    fn "arrayCall" (.cons (.param (.array (.elem .bool) .none)
      (some .memory) (some "xs")) .nil) .nil⟩

theorem signature : declaration.fnSig EB = some ([arrayTy], []) := rfl

def before : Locals EB.layout [arrayTy] × St EB :=
  (.cons (.memRef rfl sB.heap.next) .nil,
    { sB with heap := (sB.heap.alloc ⟨arrayTy,
      .array 1 (fun _ h => nomatch h) (fun _ => .val (.bool true))⟩).1 })

def arguments : RConvArgs EB [arrayTy] [arrayTy] :=
  .cons (.local .here) (by decide) .nil

def values : Vals EB.layout [arrayTy] :=
  .cons (.memRef rfl sB.heap.next) .nil

/-- The argument points to an allocated array, rather than a dangling reference. -/
theorem allocated : before.2.heap.get sB.heap.next = some
    ⟨arrayTy, .array 1 (fun _ h => nomatch h) (fun _ => .val (.bool true))⟩ := rfl

/-- All input hypotheses of `CaptureFailures.encoding_failed` hold together
for this one actual source computation, before code admission or callee entry. -/
theorem joint_capture :
    (evalE (Γ := [arrayTy]) (GB answerOnly) FC 6 (.this "C")).run before =
      (.ok (.val (.contract FC.this)), before) ∧
    (evalE (Γ := [arrayTy]) (GB answerOnly) FC 6 (lit 0)).run before =
      (.ok (.val (.int 0 (by decide))), before) ∧
    (evalConvArgs (GB answerOnly) FC 6 arguments).run before = (.ok values, before) ∧
    (encodeVals FC 6 false values.toR).run before =
      (.error (.stuck "not ABI-encodable"), before) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem encoding_failure :
    (evalE (GB answerOnly) FC 7
      (.extCall (.this "C") declaration signature (lit 0) arguments)).run before =
      (.error (.stuck "not ABI-encodable"), before) := by
  exact CaptureFailures.encoding_failed (GB answerOnly) FC 6 declaration signature
    (.this "C") (lit 0) arguments FC.this 0 (by decide) values
    before before before before before (.stuck "not ABI-encodable")
    joint_capture.1 joint_capture.2.1 joint_capture.2.2.1 joint_capture.2.2.2

end Solidity.H62.ReadonlyBind.EncodingFailureControls
