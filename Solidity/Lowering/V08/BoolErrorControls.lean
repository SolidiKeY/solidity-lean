import Solidity.Lowering.V08.BoolErrorLowering
import Solidity.Lowering.V08.SourceExternalPhaseControls

namespace Solidity.Lowering.V08.BoolErrorControls
open Solidity Source Backend BoolErrorLowering SourceCustomErrorControls

def parameters : Nat → Source.Syn (.list .errorParam)
  | 0 => .nil
  | n+1 => .cons (.errorParam (.elem .bool) none) (parameters n)

def declaration (n : Nat) : Decl :=
  ⟨.error,"Flags",some "C",false,.error "Flags" (parameters n)⟩

theorem parameters_types (environment : Source.Env) (n : Nat) :
    (parameters n).tys environment (some "C") .memory = some (List.replicate n STy.bool) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [parameters, Source.Syn.tys, Source.Elem.ty, ih, List.replicate_succ]
    rfl

theorem types_replicate (bs : List Bool) : types bs = List.replicate bs.length STy.bool := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [types, List.length_cons, List.replicate_succ, ih]

theorem declaration_typed (environment : Source.Env) (bs : List Bool) :
    (declaration bs.length).paramTys environment = some (types bs) := by
  change (parameters bs.length).tys environment (some "C") .memory = some (types bs)
  rw [parameters_types, types_replicate]

def bits : List Bool := [true,false,true]
def caller := SourceExternalPhaseControls.caller

theorem typed_three : (declaration 3).paramTys E = some (types bits) := rfl
theorem typed_empty : (declaration 0).paramTys E = some (types []) := rfl
theorem kind_three : (declaration 3).kind = .error := rfl

def machine : Failure.Slice.Machine :=
  ⟨[⟨77,by decide +kernel⟩,⟨88,by decide +kernel⟩],fun x => if x=7 then 231 else 17⟩
def suffix : Backend.Program := [.op .ADD]

theorem uniform_client (pipeline : Roadmap.Pipeline) (extra : Nat) (bs : List Bool) :
    (Source.execS (global pipeline) frame (bs.length+extra+4) 0 none
      (BoolErrorLowering.statement (declaration bs.length) bs (declaration_typed E bs)) caller).run
      (Source.L0 E,populated) =
      (.error (.revert (BoolErrorLowering.payload (global pipeline) (declaration bs.length) bs)),
        (Source.L0 E,populated)) :=
  source_run (global pipeline) frame extra (declaration bs.length) bs (declaration_typed E bs) caller populated

theorem client (pipeline : Roadmap.Pipeline) (extra : Nat) :
    (Source.execS (global pipeline) frame (bits.length+extra+4) 0 none
      (BoolErrorLowering.statement (declaration 3) bits typed_three) caller).run (Source.L0 E,populated) =
      (.error (.revert (BoolErrorLowering.payload (global pipeline) (declaration 3) bits)),(Source.L0 E,populated)) :=
  source_run (global pipeline) frame extra (declaration 3) bits typed_three caller populated

theorem empty_client (pipeline : Roadmap.Pipeline) :
    (Source.execS (global pipeline) frame 4 0 none
      (BoolErrorLowering.statement (declaration 0) [] typed_empty) caller).run (Source.L0 E,populated) =
      (.error (.revert (BoolErrorLowering.payload (global pipeline) (declaration 0) [])),(Source.L0 E,populated)) :=
  source_run (global pipeline) frame 0 (declaration 0) [] typed_empty caller populated

theorem fits (pipeline : Roadmap.Pipeline) : Failure.Fits 8 (BoolErrorLowering.payload (global pipeline) (declaration 3) bits) := by
  have length := payload_length (global pipeline) (declaration 3) bits
  change _ = 100 at length
  unfold Failure.Fits
  rw [length]
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem combined (pipeline : Roadmap.Pipeline) :
    (Source.execS (global pipeline) frame 7 0 none
      (BoolErrorLowering.statement (declaration 3) bits typed_three) caller).run (Source.L0 E,populated) =
      (.error (.revert (BoolErrorLowering.payload (global pipeline) (declaration 3) bits)),(Source.L0 E,populated)) ∧
    Failure.Slice.checkedRun (BoolErrorLowering.emit (global pipeline) (declaration 3) bits 8 ++ suffix) machine =
      some ({machine with memory := Failure.Slice.putBytes machine.memory 8 (BoolErrorLowering.payload (global pipeline) (declaration 3) bits)},
        some (.revert (BoolErrorLowering.payload (global pipeline) (declaration 3) bits))) :=
  lowered (global pipeline) frame 0 (declaration 3) bits typed_three caller populated 8 suffix machine
    (fits pipeline) (by decide +kernel)

theorem old_alias : caller.get (.there (.there .here)) = .memRef rfl 0 ∧
    populated.heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ := ⟨rfl,rfl⟩

theorem memory_frame (pipeline : Roadmap.Pipeline) :
    Failure.Slice.putBytes machine.memory 8 (BoolErrorLowering.payload (global pipeline) (declaration 3) bits) 7 = 231 :=
  Failure.Slice.putBytes_frame machine.memory 8 7 _ (Or.inl (by decide +kernel))

theorem low_horizon (pipeline : Roadmap.Pipeline) :
    (Source.execS (global pipeline) frame 1 0 none
      (BoolErrorLowering.statement (declaration 3) bits typed_three) caller).run (Source.L0 E,populated) =
      (.error .timeout,(Source.L0 E,populated)) :=
  statement_argument_timeout (global pipeline) frame (declaration 3) bits typed_three caller populated

theorem wrong_order_encoded : encoded bits ≠ encoded [false,true,true] := by decide +kernel

theorem wrong_order_payload (pipeline : Roadmap.Pipeline) :
    BoolErrorLowering.payload (global pipeline) (declaration 3) bits ≠
      BoolErrorLowering.payload (global pipeline) (declaration 3) [false,true,true] := by
  intro eq
  have tails := congrArg (fun bytes : Roadmap.Bytes => bytes.drop 4) eq
  simp only [payload_drop] at tails
  exact wrong_order_encoded tails

theorem wrong_length (pipeline : Roadmap.Pipeline) :
    (BoolErrorLowering.payload (global pipeline) (declaration 3) bits).length ≠ 68 := by
  rw [payload_length]
  decide +kernel

end Solidity.Lowering.V08.BoolErrorControls
