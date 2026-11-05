import Solidity.Lowering.V08.LiteralFailureCopiedReason
import Solidity.Lowering.V08.LiteralFailureCopySelectorControls
namespace Solidity.Lowering.V08.LiteralFailureCopiedReasonControls
open Solidity Source
open LiteralFailureCopiedReason
abbrev E := LiteralFailureCopySelectorControls.E
abbrev state := LiteralFailureCopySelectorControls.state
abbrev Older := LiteralFailureCopySelectorControls.context
abbrev global := LiteralFailureCopySelectorControls.global
def frame (data : Roadmap.Bytes) (static : Bool) : Fr := {LiteralFailureCopySelectorControls.frame data with static:=static}
def older (w : Roadmap.Word) := LiteralFailureCopySelectorControls.locals [0,255,128,1] rfl 0 0 w true

theorem applied_success (p : Roadmap.Pipeline) (data first second third : Roadmap.Bytes)
 (off len : Nat) (w : Roadmap.Word) (static : Bool) :
 (evalE (global p) (frame data static) 8 expression).run (caller true off len (older w),state first second third)=
 (.ok RVal.unit,(caller true off len (older w),LiteralFailureStringConversion.afterString (state first second third) ((data.drop off).take len))) :=
 success (global p) (frame data static) 0 off len (older w) (state first second third)

theorem applied_failure (p : Roadmap.Pipeline) (data first second third : Roadmap.Bytes)
 (off len : Nat) (w : Roadmap.Word) (static : Bool) :
 (execS (global p) (frame data static) 9 0 none (.expr expression : RStmt E [] false .body (context Older) (context Older))
 (caller false off len (older w))).run (L0 E,state first second third)=
 (.error (.revert (errorData ((data.drop off).take len))),
 (L0 E,LiteralFailureStringConversion.afterString (state first second third) ((data.drop off).take len))) :=
 statement_failure (global p) (frame data static) 0 off len (older w) (state first second third)

theorem readback (p : Roadmap.Pipeline) (first second third : Roadmap.Bytes) (w : Roadmap.Word) (static : Bool) :
 (evalE (global p) (frame [99,0,255,128,7] static) 8 expression).run (caller false 1 3 (older w),state first second third)=
 (.error (.revert (errorData [0,255,128])),
 (caller false 1 3 (older w),LiteralFailureStringConversion.afterString (state first second third) [0,255,128])) ∧
 Semantics.decodeError (errorData [0,255,128])=some [0,255,128] :=
 failure_readback (global p) (frame [99,0,255,128,7] static) 0 1 3 (older w) (state first second third) (by change (3 : Nat)<256^32; decide +kernel)

theorem old_alias (data first second third : Roadmap.Bytes) (off len : Nat) :
 (LiteralFailureStringConversion.afterString (state first second third) ((data.drop off).take len)).heap.get 1=
 some ⟨.string .memory,.string first⟩ := LiteralFailureStringConversion.old_lookup _ _ _ _ rfl

theorem copied_object (data first second third : Roadmap.Bytes) (off len : Nat) :
 (LiteralFailureStringConversion.afterString (state first second third) ((data.drop off).take len)).heap.get 4=
 some ⟨.string .memory,.string ((data.drop off).take len)⟩ := LiteralFailureStringConversion.allocated _ _

theorem timeout_before_copy (p : Roadmap.Pipeline) (data first second third : Roadmap.Bytes) (condition static : Bool) :
 (evalE (global p) (frame data static) 5 expression).run (caller condition 0 1 (older ⟨300,by decide +kernel⟩),state first second third)=
 (.error .timeout,(caller condition 0 1 (older ⟨300,by decide +kernel⟩),state first second third)) := by cases condition <;> rfl

theorem completed_at_six (p : Roadmap.Pipeline) (data first second third : Roadmap.Bytes) (static : Bool) :
 (evalE (global p) (frame data static) 6 expression).run (caller false 0 1 (older ⟨300,by decide +kernel⟩),state first second third)=
 (.error (.revert (errorData (data.take 1))),
 (caller false 0 1 (older ⟨300,by decide +kernel⟩),LiteralFailureStringConversion.afterString (state first second third) (data.take 1))) := rfl

theorem wrong_catch_kind : Semantics.decodePanic (errorData [0,255,128])=none := by decide +kernel

theorem wrong_reason : errorData [0,255,128]≠errorData [0,128,255] := by decide +kernel

def render := LiteralFailureTypedFieldsControls.render
def observe (p : Roadmap.Pipeline) (data : Roadmap.Bytes) (off len : Nat) (w : Roadmap.Word) (condition static : Bool) : String :=
 let (out,(ls,after)) := (evalE (global p) (frame data static) 8 expression).run
  (caller condition off len (older w),state [195,169] [128] [171,0])
 let outcome := match out with | .ok _ => some ("ok",[]) | .error (.revert bs) => some ("revert",bs) | _ => none
 match outcome,after.heap.get 4,after.heap.get 1,ls.getAt 4 (.int IntTy.u256) with
 | some (kind,bs),some ⟨.string .memory,.string copied⟩,some ⟨.string .memory,.string oldBytes⟩,.ok marker =>
  match marker.word with
  | some word => "{\"outcome\":\""++kind++"\",\"cursor\":"++toString after.heap.next++",\"copy\":"++render copied++",\"old\":"++render oldBytes++",\"marker\":"++toString word.val++",\"bytes\":"++render bs++"}"
  | none => "null"
 | _,_,_,_ => "null"
def suite (p : Roadmap.Pipeline) := "["++String.intercalate "," [
 observe p [] 0 0 ⟨0,by decide +kernel⟩ true false,
 observe p [] 0 0 ⟨0,by decide +kernel⟩ false false,
 observe p [99,0,255,128,7] 1 3 ⟨300,by decide +kernel⟩ true true,
 observe p [99,0,255,128,7] 1 3 ⟨300,by decide +kernel⟩ false true,
 observe p (List.replicate 31 255++[0]++List.replicate 33 128) 32 33 ⟨2^256-1,by decide +kernel⟩ true true,
 observe p (List.replicate 31 255++[0]++List.replicate 33 128) 32 33 ⟨2^256-1,by decide +kernel⟩ false true,
 observe p [0,255,128] 99 33 ⟨2^255,by decide +kernel⟩ true false,
 observe p [0,255,128] 99 33 ⟨2^255,by decide +kernel⟩ false false,
 observe p ([0]++List.replicate 33 128++[255]) 1 32 ⟨42,by decide +kernel⟩ true true,
 observe p ([0]++List.replicate 33 128++[255]) 1 32 ⟨42,by decide +kernel⟩ false true]++"]"
#eval "COPIED_REASON_LEGACY="++suite .legacy
#eval "COPIED_REASON_VIAIR="++suite .viaIR
#print axioms LiteralFailureCopiedReason.success
#print axioms LiteralFailureCopiedReason.failure
#print axioms LiteralFailureCopiedReason.statement_success
#print axioms LiteralFailureCopiedReason.statement_failure
#print axioms LiteralFailureCopiedReason.failure_readback
#print axioms applied_success
#print axioms applied_failure
#print axioms readback
#print axioms old_alias
#print axioms copied_object
#print axioms timeout_before_copy
#print axioms completed_at_six
#print axioms wrong_catch_kind
#print axioms wrong_reason
end Solidity.Lowering.V08.LiteralFailureCopiedReasonControls
