import Solidity.Lowering.V08.BoolErrorCompleteness
import Solidity.Semantics.AbiEntry

/-! Agreement of actual closed Source boolean custom-error payloads with the
independent indexed ABI codec. No runtime encoder or decoder is introduced. -/
namespace Solidity.Lowering.V08.BoolErrorAbi
open Solidity Source Backend

def shapes : List Bool → List AbiEntry.Shape
 | [] => []
 | _ :: bs => .word .bool :: shapes bs

def word (b : Bool) : AbiEntry.Word .bool :=
 ⟨if b then 1 else 0,by cases b <;> decide +kernel,by cases b <;> rfl⟩

def values : (bs : List Bool) → AbiEntry.Vals (shapes bs)
 | [] => .nil
 | b :: bs => .cons (.word (word b)) (values bs)

theorem word_bytes (b : Bool) :
 Source.wordBytes (Source.toWord (if b then 1 else 0)) = AbiEntry.wordBytes (word b).val := by
 cases b <;> rfl

theorem static_go (bs : List Bool) (offset : Nat) :
 AbiEntry.assemble.go (AbiEntry.Vals.parts (values bs)) offset =
 (bs.flatMap (fun b => AbiEntry.wordBytes (word b).val),[]) := by
 induction bs with
 | nil => rfl
 | cons b bs ih =>
   simp only [values, AbiEntry.Vals.parts, AbiEntry.Shape.dynamic,
    AbiEntry.Val.enc, AbiEntry.assemble.go, Bool.false_eq_true, ↓reduceIte,
    List.flatMap_cons, ih]

theorem encoding_agreement (bs : List Bool) :
 BoolErrorLowering.encoded bs = AbiEntry.encodeArgs (values bs) := by
 rw [BoolErrorLowering.encoded_values]
 simp only [AbiEntry.encodeArgs, AbiEntry.assemble, static_go, List.append_nil]
 have point : (fun b => Source.wordBytes (Source.toWord (if b then 1 else 0))) =
   (fun b => AbiEntry.wordBytes (word b).val) := funext word_bytes
 rw [point]

theorem payload_agreement {E : Env} (global : Glob E) (error : Decl) (bs : List Bool) :
 BoolErrorLowering.payload global error bs =
 global.selector (Source.sigOf E.layout error.name (BoolErrorLowering.types bs)) ++
 AbiEntry.encodeArgs (values bs) := by
 simp only [BoolErrorLowering.payload, encoding_agreement]

theorem source_typed {E : Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
 (extra : Nat) (error : Decl) (bs : List Bool)
 (typed : error.paramTys E = some (BoolErrorLowering.types bs))
 (locals : Locals E.layout Γ) (state : St E) :
 (execS global frame (bs.length+extra+4) 0 none
  (BoolErrorLowering.statement error bs typed) locals).run (Source.L0 E,state) =
 (.error (.revert (global.selector (Source.sigOf E.layout error.name (BoolErrorLowering.types bs)) ++
  AbiEntry.encodeArgs (values bs))),(Source.L0 E,state)) := by
 simpa only [payload_agreement] using
  BoolErrorLowering.source_run global frame extra error bs typed locals state

theorem packet_readback {E : Env} {Γ : RCtx} (global : Glob E) (offset : Nat)
 (error : Decl) (bs : List Bool)
 (typed : error.paramTys E = some (BoolErrorLowering.types bs))
 (suffix : Backend.Program) (machine : Failure.Slice.Machine)
 (fits : Failure.Fits offset (BoolErrorLowering.payload global error bs))
 (stack : machine.stack.length+2 ≤ 1024) :
 Failure.Slice.checkedRun
  ((BoolErrorStatement.emitStatement global offset
   (BoolErrorLowering.statement (Γ:=Γ) error bs typed)).getD [] ++ suffix) machine =
 some ({machine with memory := Failure.Slice.putBytes machine.memory offset (BoolErrorLowering.payload global error bs)},
  some (.revert (global.selector (Source.sigOf E.layout error.name (BoolErrorLowering.types bs)) ++
   AbiEntry.encodeArgs (values bs)))) ∧
 Failure.Slice.getBytes
  (Failure.Slice.putBytes machine.memory offset (BoolErrorLowering.payload global error bs))
  offset (BoolErrorLowering.payload global error bs).length =
 global.selector (Source.sigOf E.layout error.name (BoolErrorLowering.types bs)) ++
 AbiEntry.encodeArgs (values bs) := by
 constructor
 · have emitted := BoolErrorCompleteness.emitted_complete (Γ:=Γ) global offset error bs typed suffix machine fits stack
   rw [payload_agreement] at emitted ⊢
   exact emitted
 · rw [Failure.Slice.getBytes_putBytes, payload_agreement]

end Solidity.Lowering.V08.BoolErrorAbi
