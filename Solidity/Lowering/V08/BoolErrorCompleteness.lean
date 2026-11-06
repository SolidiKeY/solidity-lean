import Solidity.Lowering.V08.BoolErrorStatement

/-! Completeness for the explicitly supported literal family. This is not an
all-profile admission theorem: arbitrary runtime boolean expressions remain
outside this particular partial emitter. -/
namespace Solidity.Lowering.V08.BoolErrorCompleteness
open Solidity Source Backend BoolErrorStatement

theorem arguments_complete {E : Env} {Γ : RCtx} (bits : List Bool) :
 ∃ view, literalArgs (BoolErrorLowering.arguments (E:=E) (Γ:=Γ) bits) = some view ∧
 view.bits = bits := by
 induction bits with
 | nil => exact ⟨_,rfl,rfl⟩
 | cons bit bits ih =>
   obtain ⟨view,selected,same⟩ := ih
   simp only [BoolErrorLowering.arguments, literalArgs,
     LiteralFailureLowering.boolLiteral, selected]
   exact ⟨_,rfl,congrArg (List.cons bit) same⟩

theorem emit_complete {E : Env} {Γ : RCtx} (global : Glob E) (offset : Nat)
 (error : Decl) (bits : List Bool)
 (typed : error.paramTys E = some (BoolErrorLowering.types bits)) :
 emitStatement global offset (BoolErrorLowering.statement (Γ:=Γ) error bits typed) =
 some (BoolErrorLowering.emit global error bits offset) := by
 obtain ⟨view,selected,same⟩ := arguments_complete (E:=E) (Γ:=Γ) bits
 obtain ⟨found,types,identity⟩ := view
 change found = bits at same
 cases same
 simp only [emitStatement, BoolErrorLowering.statement, statementView, selected,
   Option.map_some]

theorem emitted_complete {E : Env} {Γ : RCtx} (global : Glob E) (offset : Nat)
 (error : Decl) (bits : List Bool)
 (typed : error.paramTys E = some (BoolErrorLowering.types bits))
 (suffix : Backend.Program) (machine : Failure.Slice.Machine)
 (fits : Failure.Fits offset (BoolErrorLowering.payload global error bits))
 (stack : machine.stack.length + 2 ≤ 1024) :
 Failure.Slice.checkedRun
  ((emitStatement global offset (BoolErrorLowering.statement (Γ:=Γ) error bits typed)).getD [] ++ suffix) machine =
 some ({machine with memory := Failure.Slice.putBytes machine.memory offset (BoolErrorLowering.payload global error bits)},
  some (.revert (BoolErrorLowering.payload global error bits))) := by
 simp only [emit_complete, Option.getD_some]
 exact BoolErrorLowering.emitted_run global error bits offset suffix machine fits stack

end Solidity.Lowering.V08.BoolErrorCompleteness
