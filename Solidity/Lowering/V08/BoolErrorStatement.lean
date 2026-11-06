import Solidity.Lowering.V08.BoolErrorLowering
import Solidity.Lowering.V08.LiteralFailureLowering

/-! An executable selector on actual existing typed statements for the closed
boolean-literal custom-error family. The views certify syntax identity only;
no new AST, evaluator, admission rule or successful execution oracle is added.
Other arguments/statements remain unsupported by this partial adapter. -/
namespace Solidity.Lowering.V08.BoolErrorStatement
open Solidity Source Backend

structure ArgsView {E : Env} {Γ : RCtx} {ts : List STy} (args : RConvArgs E Γ ts) where
 bits : List Bool
 types : ts=BoolErrorLowering.types bits
 same : HEq args (BoolErrorLowering.arguments (E:=E) (Γ:=Γ) bits)

def literalArgs {E : Env} {Γ : RCtx} :
 {ts : List STy} → (args : RConvArgs E Γ ts) → Option (ArgsView args)
 | [], .nil => some ⟨[],rfl,HEq.rfl⟩
 | .bool :: _, .cons expr _ tail =>
   match head : LiteralFailureLowering.boolLiteral expr, literalArgs tail with
   | some bit, some rest => some
     { bits := bit::rest.bits
       types := congrArg (List.cons STy.bool) rest.types
       same := by
        obtain ⟨ht,he⟩ := LiteralFailureLowering.boolLiteral_inv expr bit head
        cases ht
        cases he
        obtain ⟨bits,types,same⟩ := rest
        cases types
        cases same
        rfl }
   | _, _ => none
 | _, _ => none

structure StatementView {E : Env} {Γ Δ : RCtx} (stmt : RStmt E [] false .body Γ Δ) where
 error : Decl
 bits : List Bool
 typed : error.paramTys E=some (BoolErrorLowering.types bits)
 contexts : Δ=Γ
 same : HEq stmt (BoolErrorLowering.statement (Γ:=Γ) error bits typed)

def statementView {E : Env} {Γ Δ : RCtx} :
 (stmt : RStmt E [] false .body Γ Δ) → Option (StatementView stmt)
 | .revertError error typed args =>
   match literalArgs args with
   | none => none
   | some ⟨bits,types,same⟩ => by
     cases types
     cases same
     exact some ⟨error,bits,typed,rfl,HEq.rfl⟩
 | _ => none

/-- The source statement itself selects the emitted bytes. The selected
arguments are syntax literals, not unknown runtime values. -/
def emitStatement {E : Env} {Γ Δ : RCtx} (global : Glob E) (offset : Nat)
 (stmt : RStmt E [] false .body Γ Δ) : Option Backend.Program :=
 (statementView stmt).map (fun view=>BoolErrorLowering.emit global view.error view.bits offset)

theorem selected_witness {E : Env} {Γ Δ : RCtx} (global : Glob E) (offset : Nat)
 (stmt : RStmt E [] false .body Γ Δ) (code : Backend.Program)
 (selected : emitStatement global offset stmt=some code) :
 ∃ view : StatementView stmt, code=BoolErrorLowering.emit global view.error view.bits offset := by
 unfold emitStatement at selected
 cases hv : statementView stmt with
 | none => simp only [hv, Option.map_none] at selected
           cases selected
 | some view =>
   simp only [hv, Option.map_some, Option.some.injEq] at selected
   exact ⟨view,selected.symm⟩

theorem selected_correct {E : Env} {Γ Δ : RCtx} (global : Glob E) (frame : Fr)
 (extra offset : Nat) (stmt : RStmt E [] false .body Γ Δ) (code : Backend.Program)
 (selected : emitStatement global offset stmt=some code)
 (locals : Locals E.layout Γ) (state : St E) :
 ∃ view : StatementView stmt,
  code=BoolErrorLowering.emit global view.error view.bits offset ∧
  (execS global frame (view.bits.length+extra+4) 0 none stmt locals).run (Source.L0 E,state)=
   (.error (.revert (BoolErrorLowering.payload global view.error view.bits)),(Source.L0 E,state)) ∧
  ∀ (suffix : Backend.Program) (machine : Failure.Slice.Machine),
   Failure.Fits offset (BoolErrorLowering.payload global view.error view.bits) →
   machine.stack.length+2≤1024 →
   Failure.Slice.checkedRun (code++suffix) machine=
    some ({machine with memory:=Failure.Slice.putBytes machine.memory offset (BoolErrorLowering.payload global view.error view.bits)},
     some (.revert (BoolErrorLowering.payload global view.error view.bits))) := by
 obtain ⟨view, codeEq⟩ := selected_witness global offset stmt code selected
 have contexts := view.contexts
 cases contexts
 have syntaxEq : stmt = BoolErrorLowering.statement view.error view.bits view.typed :=
  eq_of_heq view.same
 refine ⟨view, codeEq, ?_, ?_⟩
 · exact (congrArg
    (fun s : RStmt E [] false .body Γ Γ =>
     (execS global frame (view.bits.length+extra+4) 0 none s locals).run (Source.L0 E,state))
    syntaxEq).trans
    (BoolErrorLowering.source_run global frame extra view.error view.bits view.typed locals state)
 · intro suffix machine fits stack
   rw [codeEq]
   exact BoolErrorLowering.emitted_run global view.error view.bits offset suffix machine fits stack

end Solidity.Lowering.V08.BoolErrorStatement
