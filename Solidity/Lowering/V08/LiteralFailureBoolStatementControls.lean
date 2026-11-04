import Solidity.Lowering.V08.LiteralFailureBoolStatement
import Solidity.Lowering.V08.BoolErrorControls

namespace Solidity.Lowering.V08.LiteralFailureBoolStatementControls
open Solidity Source Backend LiteralFailureBoolStatement

def error := BoolErrorControls.declaration 3
def emptyError : Decl := ⟨.error,"Empty",some "C",false,.error "Empty" .nil⟩
def environment : Env := ⟨[error,emptyError]⟩
def context : RCtx := [.bool,.bytes .memory]
def caller : Source.Locals environment.layout context := .cons (.bool false) (.cons (.memRef rfl 0) .nil)
def frame := SourceCustomErrorControls.frame
def initial : Source.St environment :=
 ⟨⟨⟨fun _ => Account.empty _⟩,Transient.empty,[]⟩,
  (Source.Heap.empty.alloc ⟨.bytes .memory,.bytes [0,255]⟩).1,[],[],⟨[],.nil⟩, Source.FailureExecution.Cursor.empty⟩
def state : Source.St environment :=
 {initial with ex := initial.ex.run [.account frame.this (fun a => {a with balance := 73,nonce:=4})]}
def program : Source.Program environment :=
 {body:=fun _=>none,consts:=fun _=>none,inits:=fun _=>[],ctor:=fun _=>none,
  ctorLocals:=fun _=>[],baseArgs:=fun _=>[],contracts:=["C"]}
def global (pipeline : Roadmap.Pipeline) : Glob environment :=
 {prog:=program,pipeline:=pipeline,fixed:=Roadmap.Controls.toyFixed,balance0:=fun _=>⟨100,by decide +kernel⟩,
  hasCode:=fun _ _=>false,callee:=fun _=>.answer (.success []),timestamp:=⟨12345,by decide +kernel⟩}
def bits : List Bool := [true,false,true]
def typed : error.paramTys environment = some (BoolErrorLowering.types bits) :=
 BoolErrorControls.declaration_typed environment bits
def statement : RStmt environment [] false .body context context := BoolErrorLowering.statement error bits typed
def emptyStatement : RStmt environment [] false .body context context :=
 .revertError emptyError rfl .nil
def runtimeStatement : RStmt environment [] false .body context context :=
 .revertError error typed (.cons (.local .here) rfl (.cons (.bool false) rfl (.cons (.bool true) rfl .nil)))
def code (pipeline : Roadmap.Pipeline) : Backend.Program := (BoolErrorStatement.emitStatement (global pipeline) 8 statement).getD []

theorem registered : error ∈ environment.decls ∧ emptyError ∈ environment.decls :=
 ⟨List.mem_cons_self,List.mem_cons_of_mem _ List.mem_cons_self⟩
theorem chosen (pipeline : Roadmap.Pipeline) :
 BoolErrorStatement.emitStatement (global pipeline) 8 statement = some (BoolErrorLowering.emit (global pipeline) error bits 8) :=
 BoolErrorCompleteness.emit_complete (global pipeline) 8 error bits typed

theorem code_exact (pipeline : Roadmap.Pipeline) : code pipeline = BoolErrorLowering.emit (global pipeline) error bits 8 := by
 rw [code,chosen]
 rfl

theorem fits (pipeline : Roadmap.Pipeline) : Failure.Fits 8 (BoolErrorLowering.payload (global pipeline) error bits) := by
 have length := BoolErrorLowering.payload_length (global pipeline) error bits
 change _ = 100 at length
 unfold Failure.Fits
 rw [length]
 exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem joint (pipeline : Roadmap.Pipeline) :
 (Source.execS (global pipeline) frame 7 0 none statement caller).run (Source.L0 environment,state) =
  (.error (.revert (BoolErrorLowering.payload (global pipeline) error bits)),(Source.L0 environment,state)) ∧
 Failure.Slice.checkedRun (code pipeline ++ BoolErrorControls.suffix) BoolErrorControls.machine =
  some ({BoolErrorControls.machine with memory := (Failure.Slice.putBytes BoolErrorControls.machine.memory 8 (BoolErrorLowering.payload (global pipeline) error bits))},
   some (.revert (BoolErrorLowering.payload (global pipeline) error bits))) := by
 rw [code_exact]
 have applied := bounded_lowered (global pipeline) frame 0 8 error bits typed caller state
  BoolErrorControls.suffix BoolErrorControls.machine (by decide +kernel) (by decide +kernel)
 rw [BoolErrorCompleteness.emit_complete] at applied
 exact applied

theorem runtime_unhandled (pipeline : Roadmap.Pipeline) : BoolErrorStatement.emitStatement (global pipeline) 8 runtimeStatement = none := by rfl
theorem skip_unhandled (pipeline : Roadmap.Pipeline) :
 BoolErrorStatement.emitStatement (global pipeline) 8 (.skip : RStmt environment [] false .body context context) = none := by rfl

theorem empty_chosen (pipeline : Roadmap.Pipeline) :
 BoolErrorStatement.emitStatement (global pipeline) 8 emptyStatement = some (BoolErrorLowering.emit (global pipeline) emptyError [] 8) := by
 exact BoolErrorCompleteness.emit_complete (global pipeline) 8 emptyError [] rfl

theorem changed_values : BoolErrorLowering.encoded [true,false,true] ≠ BoolErrorLowering.encoded [false,true,true] := by decide +kernel

theorem target_old_byte (pipeline : Roadmap.Pipeline) :
 Failure.Slice.putBytes BoolErrorControls.machine.memory 8 (BoolErrorLowering.payload (global pipeline) error bits) 7 = 231 :=
 Failure.Slice.putBytes_frame _ _ _ _ (Or.inl (by decide +kernel))

theorem old_alias : caller.get (.there .here) = .memRef rfl 0 ∧
 state.heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧ state.heap.next = 1 := ⟨rfl,rfl,rfl⟩

def lastOffset : Nat := Failure.wordLimit - 100

theorem at_end (pipeline : Roadmap.Pipeline) :
 Failure.Slice.checkedRun
  ((BoolErrorStatement.emitStatement (global pipeline) lastOffset statement).getD [] ++ BoolErrorControls.suffix)
  BoolErrorControls.machine =
 some ({BoolErrorControls.machine with memory := (Failure.Slice.putBytes BoolErrorControls.machine.memory lastOffset (BoolErrorLowering.payload (global pipeline) error bits))},
  some (.revert (BoolErrorLowering.payload (global pipeline) error bits))) := by
 have room : 4 + 32 * bits.length ≤ Failure.wordLimit := by decide +kernel
 exact BoolErrorCompleteness.emitted_complete (global pipeline) lastOffset error bits typed
  BoolErrorControls.suffix BoolErrorControls.machine (fits_at_end (global pipeline) error bits room) (by decide +kernel)

theorem one_past (pipeline : Roadmap.Pipeline) :
 ¬ Failure.Fits (lastOffset+1) (BoolErrorLowering.payload (global pipeline) error bits) :=
 not_fits_one_past (global pipeline) error bits (by decide +kernel)

theorem bounded_old_byte (pipeline : Roadmap.Pipeline) :
 Failure.Slice.checkedRun
  ((BoolErrorStatement.emitStatement (global pipeline) 8 statement).getD [] ++ BoolErrorControls.suffix) BoolErrorControls.machine =
 some ({BoolErrorControls.machine with memory := (Failure.Slice.putBytes BoolErrorControls.machine.memory 8 (BoolErrorLowering.payload (global pipeline) error bits))},
  some (.revert (BoolErrorLowering.payload (global pipeline) error bits))) ∧
 Failure.Slice.putBytes BoolErrorControls.machine.memory 8 (BoolErrorLowering.payload (global pipeline) error bits) 7 = 231 :=
 bounded_frame (global pipeline) 8 7 error bits typed BoolErrorControls.suffix BoolErrorControls.machine
  (by decide +kernel) (by decide +kernel) (Or.inl (by decide +kernel))

def render (bytes : Roadmap.Bytes) : String := "[" ++ String.intercalate "," (bytes.map (fun b => toString b.toNat)) ++ "]"
def sourceBytes {α : Type} : Except Source.Halt α → String
 | .error (.revert data) => render data
 | _ => "NO_SOURCE_REVERT"
def targetBytes : Option (Failure.Slice.Machine × Option Roadmap.Outcome) → String
 | some (_,some (.revert data)) => render data
 | _ => "NO_TARGET_REVERT"
#eval String.intercalate "\n"
 [sourceBytes ((Source.execS (global .legacy) frame 7 0 none statement caller).run (Source.L0 environment,state)).1,
  targetBytes (Failure.Slice.checkedRun (code .legacy ++ BoolErrorControls.suffix) BoolErrorControls.machine),
  sourceBytes ((Source.execS (global .legacy) frame 4 0 none emptyStatement caller).run (Source.L0 environment,state)).1,
  targetBytes (Failure.Slice.checkedRun ((BoolErrorStatement.emitStatement (global .legacy) 8 emptyStatement).getD [] ++ BoolErrorControls.suffix) BoolErrorControls.machine),
  targetBytes (Failure.Slice.checkedRun ((BoolErrorStatement.emitStatement (global .legacy) lastOffset statement).getD [] ++ BoolErrorControls.suffix) BoolErrorControls.machine),
  targetBytes (Failure.Slice.checkedRun ((BoolErrorStatement.emitStatement (global .legacy) (Failure.wordLimit-4) emptyStatement).getD [] ++ BoolErrorControls.suffix) BoolErrorControls.machine)]
#eval [(BoolErrorStatement.emitStatement (global .legacy) 8 runtimeStatement).isNone,
 (BoolErrorStatement.emitStatement (global .legacy) 8 (.skip : RStmt environment [] false .body context context)).isNone,
 (BoolErrorStatement.emitStatement (global .legacy) 8 emptyStatement).isSome]
#eval (code .legacy).length
#print axioms LiteralFailureBoolStatement.fits_iff_span
#print axioms LiteralFailureBoolStatement.fits_at_end
#print axioms LiteralFailureBoolStatement.not_fits_one_past
#print axioms LiteralFailureBoolStatement.bounded_lowered
#print axioms LiteralFailureBoolStatement.bounded_frame
#print axioms registered
#print axioms chosen
#print axioms code_exact
#print axioms fits
#print axioms joint
#print axioms runtime_unhandled
#print axioms skip_unhandled
#print axioms empty_chosen
#print axioms changed_values
#print axioms target_old_byte
#print axioms old_alias
#print axioms at_end
#print axioms one_past
#print axioms bounded_old_byte
end Solidity.Lowering.V08.LiteralFailureBoolStatementControls
