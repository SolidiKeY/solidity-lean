import Solidity.Lowering.Readonly.SourceDispatchEffects
import Solidity.Lowering.Readonly.SourceLoopControls
import Solidity.Lowering.Readonly.SourceHistoryBase

/-! Actual dispatch observations retain decoding/payability refusals and dirty
callee failure. No child-frame rollback or native adequacy is inferred. -/
namespace Solidity.Lowering.Readonly.SourceDispatchControls
open Solidity.Source Solidity.Source.SemanticsExamples
open SourceHistory
def global := GB (fun _ => .answer (.success []))
def run (mode : Bool) (input : Solidity.Roadmap.Bytes) (fuel : Nat := 30) :=
  (dispatch global {FC with static := mode} fuel input).run (L0 EB, sB)
def cb := selOf "cb()"
def g := selOf "g()"
def poke := selOf "poke()"
theorem ordinary_callback : (run false cb).1 = .ok [] ∧ readX (run false cb).2.2 = some 4 := by constructor <;> first | rfl | decide
theorem static_callback_refused : (run true cb).1 = .error (.revert []) := by rfl
theorem static_callback_kept : readX (run true cb).2.2 = some 3 := by decide
theorem value_return : (run false g).1 = .ok (wordBytes (word 12)) := by rfl
theorem ordinary_storage_changed : readX (run false g).2.2 = some 5 := by decide
theorem ordinary_false_preservation : readX (run false g).2.2 ≠ some 3 := by decide
theorem callee_revert_dirty : (run false poke).1 = .error (.revert []) ∧ readX (run false poke).2.2 = some 1 := by constructor <;> first | rfl | decide
theorem short_arguments : (run false (selOf "callOut(address)")).1 = .error (.revert []) := by rfl
theorem short_arguments_kept : readX (run false (selOf "callOut(address)")).2.2 = some 3 := by decide
theorem absent_special : (run true []).1 = .error (.revert []) := by rfl
theorem nonpayable :
    ((dispatch global {FC with value := word 1} 30 cb).run (L0 EB, sB)).1 = .error (.revert []) := by rfl
theorem zero_timeout : (run true cb 0).1 = .error .timeout := by rfl
theorem selected_at_zero :
    Effect true (dispatch global {FC with static := true} 1 cb) := by
  apply dispatch_function_succ global {FC with static := true} 0 (at_zero global) cb
    (⟨.function, "cb", some "C", false, fn "cb" .nil .nil⟩)
  · rfl
  · decide
end Solidity.Lowering.Readonly.SourceDispatchControls
