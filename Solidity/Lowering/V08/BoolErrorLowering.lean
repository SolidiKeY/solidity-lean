import Solidity.Lowering.V08.SourceCustomErrors
import Solidity.Backend.Failure.Correct

/-! Closed boolean-list custom-error lowering over existing intrinsic syntax.
No runtime-value encoder, new decoder or source/world simulation is introduced. -/
namespace Solidity.Lowering.V08.BoolErrorLowering
open Solidity Source Backend

def types : List Bool → List STy
  | [] => []
  | _ :: bs => .bool :: types bs

def arguments {E : Source.Env} {Γ : RCtx} : (bs : List Bool) → RConvArgs E Γ (types bs)
  | [] => .nil
  | b :: bs => .cons (.bool b) rfl (arguments bs)

def values {E : Source.Env} : (bs : List Bool) → Source.Vals E.layout (types bs)
  | [] => .nil
  | b :: bs => .cons (.bool b) (values bs)

/-- These are the existing codec's leaf parts, not a replacement encoder. -/
def parts (bs : List Bool) : List (Bool × Roadmap.Bytes) :=
  bs.map fun b => (false, Source.wordBytes (Source.toWord (if b then 1 else 0)))

def encoded (bs : List Bool) : Roadmap.Bytes := Source.abiLayout (parts bs)

theorem arguments_run {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (extra : Nat) (bs : List Bool) (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.evalConvArgs global frame (bs.length + extra + 3) (arguments bs)).run (locals,state) =
      (.ok (values bs),(locals,state)) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons, arguments, values]
    rw [Source.evalConvArgs]
    simp only [Source.evalE, Source.convRV, Source.getV, Source.RVal.get, Source.EM.lift,
      bind, pure, Except.pure, ExceptT.bind, ExceptT.pure,
      ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind, StateT.pure]
    have fuel : bs.length + 1 + extra + 2 = bs.length + extra + 3 := by omega
    simp only [fuel, ↓reduceDIte]
    simp only [bind, pure, ExceptT.bindCont,
      StateT.bind, StateT.pure]
    have tail := ih
    simp only [ExceptT.run] at tail
    rw [tail]
    rfl

theorem parts_run {E : Source.Env} {Γ : RCtx} (frame : Fr) (horizon : Nat)
    (bs : List Bool) (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.encodeParts frame horizon false (values (E:=E) bs).toR : Source.EM E Γ _).run (locals,state) =
      (.ok (parts bs),(locals,state)) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [values, Source.Vals.toR, Source.encodeParts]
    cases b <;>
      simp only [Source.encodeOne, Source.Val.word, bind, pure, ExceptT.bind,
        ExceptT.pure, ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind]
    all_goals
      simp only [Bool.false_eq_true, ↓reduceIte]
      simp only [bind, pure, ExceptT.bindCont,
        StateT.bind, StateT.pure]
      have tail := ih
      simp only [ExceptT.run] at tail
      rw [tail]
      rfl

theorem encoding_run {E : Source.Env} {Γ : RCtx} (frame : Fr) (horizon : Nat)
    (bs : List Bool) (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.encodeVals frame horizon false (values (E:=E) bs).toR : Source.EM E Γ _).run (locals,state) =
      (.ok (encoded bs),(locals,state)) := by
  have actual := parts_run frame horizon bs locals state
  simp only [ExceptT.run] at actual
  simp only [Source.encodeVals, bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.bindCont,
    ExceptT.run, ExceptT.mk, StateT.bind, StateT.pure, actual, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem static_go (bs : List Bool) (offset : Nat) :
    Source.abiLayout.go (parts bs) offset =
      (bs.flatMap (fun b => Source.wordBytes (Source.toWord (if b then 1 else 0))),[]) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [parts, List.map_cons, Source.abiLayout.go, List.flatMap_cons]
    rw [← parts, ih]

theorem encoded_values (bs : List Bool) :
    encoded bs = bs.flatMap (fun b => Source.wordBytes (Source.toWord (if b then 1 else 0))) := by
  simp only [encoded, Source.abiLayout, static_go, List.append_nil]

theorem encoded_length (bs : List Bool) : (encoded bs).length = 32 * bs.length := by
  rw [encoded_values]
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.flatMap_cons, List.length_append, Source.wordBytes_length, ih, List.length_cons]
    omega

def payload {E : Source.Env} (global : Glob E) (error : Decl) (bs : List Bool) : Roadmap.Bytes :=
  global.selector (Source.sigOf E.layout error.name (types bs)) ++ encoded bs

def statement {E : Source.Env} {Γ : RCtx} (error : Decl) (bs : List Bool)
    (typed : error.paramTys E = some (types bs)) : RStmt E [] false .body Γ Γ :=
  .revertError error typed (arguments bs)

/-- Constant-payload emitter for this closed typed family: it takes the boolean
list as a meta-level input, not the statement. No runtime memory
read or general source admission is implied. -/
def emit {E : Source.Env} (global : Glob E) (error : Decl) (bs : List Bool) (offset : Nat) : Backend.Program :=
  Failure.emit offset (.custom (payload global error bs))

theorem source_run {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (extra : Nat) (error : Decl) (bs : List Bool)
    (typed : error.paramTys E = some (types bs))
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.execS global frame (bs.length + extra + 4) 0 none (statement error bs typed) locals).run
      (Source.L0 E,state) =
      (.error (.revert (payload global error bs)),(Source.L0 E,state)) :=
  SourceCustomErrors.execute global frame (bs.length+extra+3) error typed (arguments bs)
    locals locals state state state (values bs) (encoded bs)
    (arguments_run global frame extra bs locals state)
    (encoding_run frame (bs.length+extra+3) bs (Source.L0 E) state)

theorem payload_length {E : Source.Env} (global : Glob E) (error : Decl) (bs : List Bool) :
    (payload global error bs).length = 4 + 32 * bs.length := by
  simp only [payload, List.length_append, SourceCustomErrors.selector_length, encoded_length]

theorem payload_drop {E : Source.Env} (global : Glob E) (error : Decl) (bs : List Bool) :
    (payload global error bs).drop 4 = encoded bs := by
  unfold payload
  have length := SourceCustomErrors.selector_length global (Source.sigOf E.layout error.name (types bs))
  rw [← length, List.drop_left]

theorem payload_take {E : Source.Env} (global : Glob E) (error : Decl) (bs : List Bool) :
    (payload global error bs).take 4 = global.selector (Source.sigOf E.layout error.name (types bs)) := by
  unfold payload
  have length := SourceCustomErrors.selector_length global (Source.sigOf E.layout error.name (types bs))
  rw [← length, List.take_left]

theorem arguments_zero {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (bs : List Bool) (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.evalConvArgs global frame 0 (arguments bs)).run (locals,state) =
      (.error .timeout,(locals,state)) := rfl

theorem statement_argument_timeout {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (error : Decl) (bs : List Bool) (typed : error.paramTys E = some (types bs))
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.execS global frame 1 0 none (statement error bs typed) locals).run
      (Source.L0 E,state) = (.error .timeout,(Source.L0 E,state)) := rfl

theorem emitted_run {E : Source.Env} (global : Glob E) (error : Decl) (bs : List Bool)
    (offset : Nat) (suffix : Backend.Program) (machine : Failure.Slice.Machine)
    (fits : Failure.Fits offset (payload global error bs)) (stack : machine.stack.length + 2 ≤ 1024) :
    Failure.Slice.checkedRun (emit global error bs offset ++ suffix) machine =
      some ({machine with memory := Failure.Slice.putBytes machine.memory offset (payload global error bs)},
        some (.revert (payload global error bs))) :=
  Failure.checkedRun_emit_suffix offset (.custom (payload global error bs)) suffix machine fits stack

/-- Source execution and the actual emitted terminal slice agree for arbitrary
list length. Only the published architecture gates remain; neither run is assumed. -/
theorem lowered {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (extra : Nat) (error : Decl) (bs : List Bool) (typed : error.paramTys E = some (types bs))
    (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (offset : Nat) (suffix : Backend.Program) (machine : Failure.Slice.Machine)
    (fits : Failure.Fits offset (payload global error bs)) (stack : machine.stack.length+2 ≤ 1024) :
    (Source.execS global frame (bs.length+extra+4) 0 none (statement error bs typed) locals).run
      (Source.L0 E,state) = (.error (.revert (payload global error bs)),(Source.L0 E,state)) ∧
    Failure.Slice.checkedRun (emit global error bs offset ++ suffix) machine =
      some ({machine with memory := Failure.Slice.putBytes machine.memory offset (payload global error bs)},
        some (.revert (payload global error bs))) :=
  ⟨source_run global frame extra error bs typed locals state,
    emitted_run global error bs offset suffix machine fits stack⟩

end Solidity.Lowering.V08.BoolErrorLowering
