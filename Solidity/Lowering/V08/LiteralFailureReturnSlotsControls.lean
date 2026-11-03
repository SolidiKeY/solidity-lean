import Solidity.Lowering.V08.LiteralFailureReturnSlots
import Solidity.Lowering.V08.LiteralFailureDynamicReturnControls
namespace Solidity.Lowering.V08.LiteralFailureReturnSlotsControls
open Solidity Source Backend
open LiteralFailureReturnSlots
open SourceCustomErrorControls (E frame global populated)
open LiteralFailureDynamicReturnControls (state saved live)

def types : RCtx := [.bytes .memory,.int IntTy.u256]
def parameterTypes : RCtx := [.bytes .memory,.int IntTy.u256,.bytes .memory,.bool]
def parameters (marker : Roadmap.Word) : Locals E.layout parameterTypes :=
 .cons (.memRef rfl 1) (.cons (SourceEnvironment.sourceWord marker)
  (.cons (.memRef rfl 0) (.cons (.bool true) .nil)))
def old : Source.Vals E.layout types := LiteralFailureDynamicError.values 0 ⟨7,by decide +kernel⟩
def values (marker : Roadmap.Word) : Source.Vals E.layout types := LiteralFailureDynamicError.values 1 marker

def arguments : RConvArgs E (types.reverseAux parameterTypes) types :=
 .cons (.local (.there (.there .here))) rfl
  (.cons (.local (.there (.there (.there .here)))) rfl .nil)
def statement : RStmt E types false .body (types.reverseAux parameterTypes) (types.reverseAux parameterTypes) :=
 .retTuple arguments

theorem arguments_run (p : Roadmap.Pipeline) (static : Bool) (marker : Roadmap.Word)
 (bytes : Roadmap.Bytes) :
 (evalConvArgs (global p) {frame with static:=static} 5 arguments).run
 (old.onto (parameters marker),state bytes [])=
 (.ok (values marker),(old.onto (parameters marker),state bytes [])) := by rfl

theorem body_return (p : Roadmap.Pipeline) (static : Bool) (marker : Roadmap.Word)
 (bytes : Roadmap.Bytes) :
 (execS (global p) {frame with static:=static} 6 4 none statement
 (old.onto (parameters marker))).run (L0 E,state bytes [])=
 (.ok (.ret ((values marker).onto (parameters marker))),(L0 E,state bytes [])) :=
 tuple_statement (global p) {frame with static:=static} 5 old (values marker)
 (parameters marker) (old.onto (parameters marker)) arguments (state bytes []) (state bytes []) (arguments_run p static marker bytes)

def seven : Roadmap.Word := ⟨7,by decide +kernel⟩
def effectArguments : RConvArgs E (types.reverseAux parameterTypes) types :=
 .cons (.local (.there (.there .here))) rfl
  (.cons (.assign (.local (.there (.there (.there .here)))) (.local .here)) rfl .nil)

def effectStatement : RStmt E types false .body (types.reverseAux parameterTypes) (types.reverseAux parameterTypes) :=
 .retTuple effectArguments

theorem effect_arguments_run (p : Roadmap.Pipeline) (static : Bool) (marker : Roadmap.Word)
 (bytes : Roadmap.Bytes) :
 (evalConvArgs (global p) {frame with static:=static} 7 effectArguments).run
 (old.onto (parameters marker),state bytes [])=
 (.ok (values seven),(old.onto (parameters seven),state bytes [])) := by rfl

theorem effect_body_return (p : Roadmap.Pipeline) (static : Bool) (marker : Roadmap.Word)
 (bytes : Roadmap.Bytes) :
 (execS (global p) {frame with static:=static} 8 4 none effectStatement
 (old.onto (parameters marker))).run (L0 E,state bytes [])=
 (.ok (.ret ((values seven).onto (parameters seven))),(L0 E,state bytes [])) :=
 tuple_statement (global p) {frame with static:=static} 7 old (values seven)
 (parameters seven) (old.onto (parameters marker)) effectArguments (state bytes []) (state bytes [])
 (effect_arguments_run p static marker bytes)

theorem returned_values (marker : Roadmap.Word) :
 retVals ((values marker).onto (parameters marker)) 0 types=.ok (values marker).toR :=
 extraction (values marker) (parameters marker)

theorem encoding (F : Fr) (fuel : Nat) (marker : Roadmap.Word) (bytes : Roadmap.Bytes) :
 FailurePaths.Premises.EncodingAt F fuel (values marker).toR (state bytes []) (state bytes [])
 (AbiEntry.encodeArgs (LiteralFailureDynamicError.abiValues bytes marker)) := by
 simpa only [values,LiteralFailureDynamicError.abi_agreement] using
  LiteralFailureDynamicError.encoding_run F fuel 1 marker bytes (L0 E) (state bytes []) (.inl rfl)

theorem wrong_order (marker : Roadmap.Word) :
 retVals ((values marker).onto (parameters marker)) 0 [.int IntTy.u256,.bytes .memory]=
 .error (.stuck "local type") := by rfl

theorem older_alias (marker : Roadmap.Word) :
 ((values marker).onto (parameters marker)).getAt 4 (.bytes .memory)=.ok (.memRef rfl 0) := by
 have read := get_older (values marker) (parameters marker) 2 (.bytes .memory)
 exact read

theorem empty_slots (marker : Roadmap.Word) :
 setRets (parameters marker) 0 (.nil : Source.Vals E.layout [])=.ok (parameters marker) ∧
 retVals (parameters marker) 0 []=.ok .nil := ⟨rfl,rfl⟩

def packet (bytes : Roadmap.Bytes) (marker : Roadmap.Word) : Roadmap.Bytes :=
 AbiEntry.encodeArgs (LiteralFailureDynamicError.abiValues bytes marker)

theorem transport (marker : Roadmap.Word) (bytes : Roadmap.Bytes)
 (fits : Failure.Fits 8 (packet bytes marker)) :
 Failure.Local.execute (Failure.Local.save (MemoryOps.Physical.worldJournal populated.ex saved))
 8 (.returned (packet bytes marker)) (MemoryOps.Physical.worldJournal (state bytes []).ex live)=
 some (MemoryOps.Physical.worldJournal (state bytes []).ex
  {live with memory:=Failure.Slice.putBytes live.memory 8 (packet bytes marker)},.success (packet bytes marker)) :=
 (FailurePaths.encoded_return frame 0 8 (values marker).toR (state bytes []) (state bytes [])
  populated (packet bytes marker) (encoding frame 0 marker bytes) saved live fits (by decide)).2.2

theorem finite_fits : Failure.Fits 8 (packet [0,255] ⟨42,by decide +kernel⟩) := by
 have length : (packet [0,255] ⟨42,by decide +kernel⟩).length=128 := by decide +kernel
 simp only [Failure.Fits,length]
 decide +kernel

theorem finite_transport :
 Failure.Local.execute (Failure.Local.save (MemoryOps.Physical.worldJournal populated.ex saved))
 8 (.returned (packet [0,255] ⟨42,by decide +kernel⟩))
 (MemoryOps.Physical.worldJournal (state [0,255] []).ex live)=
 some (MemoryOps.Physical.worldJournal (state [0,255] []).ex
  {live with memory:=Failure.Slice.putBytes live.memory 8 (packet [0,255] ⟨42,by decide +kernel⟩)},
  .success (packet [0,255] ⟨42,by decide +kernel⟩)) := transport _ _ finite_fits

theorem overwritten (marker : Roadmap.Word) :
 old.onto (parameters marker)≠(values marker).onto (parameters marker) := by
 intro equal
 have bad := congrArg (fun locals=>locals.get (.there .here)) equal
 cases bad

def packets : List Roadmap.Bytes :=
 [packet [0,255] ⟨42,by decide +kernel⟩,packet [] ⟨300,by decide +kernel⟩,
  packet (List.replicate 31 255) ⟨2^256-1,by omega⟩,
  packet (List.replicate 32 0) ⟨0,by decide +kernel⟩,
  packet (List.replicate 33 128) ⟨2^255,by decide +kernel⟩]
def jsonBytes (bs : List UInt8) : String :=
 "[" ++ String.intercalate "," (bs.map (fun b=>toString b.toNat)) ++ "]"
#eval IO.println ("RETURN_SLOTS_PACKETS=[" ++ String.intercalate "," (packets.map jsonBytes) ++ "]")
#print axioms get_older
#print axioms extraction
#print axioms set_older
#print axioms overwrite
#print axioms tuple_statement
#print axioms arguments_run
#print axioms body_return
#print axioms effect_arguments_run
#print axioms effect_body_return
#print axioms returned_values
#print axioms encoding
#print axioms wrong_order
#print axioms older_alias
#print axioms empty_slots
#print axioms transport
#print axioms finite_transport
#print axioms overwritten
end Solidity.Lowering.V08.LiteralFailureReturnSlotsControls
