import Solidity.Lowering.V08.BoolErrorCompleteness

namespace Solidity.Lowering.V08.LiteralFailureBoolStatement
open Solidity Source Backend

/-- Exact architectural span for the already compiled constant Boolean family.
This is an auxiliary address bound, never a source admission predicate. -/
theorem fits_iff_span {E : Env} (global : Glob E) (error : Decl) (bits : List Bool) (offset : Nat) :
 Failure.Fits offset (BoolErrorLowering.payload global error bits) ↔
 offset + 4 + 32 * bits.length ≤ Failure.wordLimit := by
 rw [Failure.Fits,BoolErrorLowering.payload_length]
 have aligned : Failure.wordLimit = 32 * (Failure.wordLimit / 32) := by decide +kernel
 constructor
 · intro fits
   omega
 · intro span
   exact ⟨by omega,by omega,by omega⟩

theorem fits_at_end {E : Env} (global : Glob E) (error : Decl) (bits : List Bool)
 (room : 4 + 32 * bits.length ≤ Failure.wordLimit) :
 Failure.Fits (Failure.wordLimit - (4 + 32 * bits.length)) (BoolErrorLowering.payload global error bits) := by
 apply (fits_iff_span global error bits _).mpr
 omega

theorem not_fits_one_past {E : Env} (global : Glob E) (error : Decl) (bits : List Bool)
 (room : 4 + 32 * bits.length ≤ Failure.wordLimit) :
 ¬ Failure.Fits (Failure.wordLimit - (4 + 32 * bits.length) + 1) (BoolErrorLowering.payload global error bits) := by
 rw [fits_iff_span]
 omega

theorem bounded_lowered {E : Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
 (extra offset : Nat) (error : Decl) (bits : List Bool)
 (typed : error.paramTys E = some (BoolErrorLowering.types bits))
 (locals : Locals E.layout Γ) (state : St E) (suffix : Backend.Program) (machine : Failure.Slice.Machine)
 (span : offset + 4 + 32 * bits.length ≤ Failure.wordLimit)
 (stack : machine.stack.length+2 ≤ 1024) :
 (execS global frame (bits.length+extra+4) 0 none (BoolErrorLowering.statement error bits typed) locals).run (Source.L0 E,state) =
  (.error (.revert (BoolErrorLowering.payload global error bits)),(Source.L0 E,state)) ∧
 Failure.Slice.checkedRun
  ((BoolErrorStatement.emitStatement global offset (BoolErrorLowering.statement (Γ:=Γ) error bits typed)).getD [] ++ suffix) machine =
  some ({machine with memory := (Failure.Slice.putBytes machine.memory offset (BoolErrorLowering.payload global error bits))},
   some (.revert (BoolErrorLowering.payload global error bits))) :=
 ⟨BoolErrorLowering.source_run global frame extra error bits typed locals state,
  BoolErrorCompleteness.emitted_complete (Γ:=Γ) global offset error bits typed suffix machine
   ((fits_iff_span global error bits offset).mpr span) stack⟩

theorem bounded_frame {E : Env} {Γ : RCtx} (global : Glob E) (offset probe : Nat)
 (error : Decl) (bits : List Bool) (typed : error.paramTys E = some (BoolErrorLowering.types bits))
 (suffix : Backend.Program) (machine : Failure.Slice.Machine)
 (span : offset + 4 + 32 * bits.length ≤ Failure.wordLimit)
 (stack : machine.stack.length+2 ≤ 1024)
 (outside : probe < offset ∨ offset + 4 + 32 * bits.length ≤ probe) :
 Failure.Slice.checkedRun
  ((BoolErrorStatement.emitStatement global offset (BoolErrorLowering.statement (Γ:=Γ) error bits typed)).getD [] ++ suffix) machine =
  some ({machine with memory := (Failure.Slice.putBytes machine.memory offset (BoolErrorLowering.payload global error bits))},
   some (.revert (BoolErrorLowering.payload global error bits))) ∧
 Failure.Slice.putBytes machine.memory offset (BoolErrorLowering.payload global error bits) probe = machine.memory probe := by
 constructor
 · exact BoolErrorCompleteness.emitted_complete (Γ:=Γ) global offset error bits typed suffix machine
    ((fits_iff_span global error bits offset).mpr span) stack
 · apply Failure.Slice.putBytes_frame
   rw [BoolErrorLowering.payload_length]
   omega

end Solidity.Lowering.V08.LiteralFailureBoolStatement
