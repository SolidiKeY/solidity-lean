import Solidity.Lowering.V08.LiteralFailureReferenceReturn
import Solidity.Lowering.V08.LiteralFailureDynamicReturnControls
namespace Solidity.Lowering.V08.LiteralFailureReferenceReturnControls
open Solidity Source Backend
open SourceCustomErrorControls (E frame global populated)
open LiteralFailureDynamicReturnControls (state saved live)
open LiteralFailureReferenceReturn

def parameters : Locals E.layout [.bytes .memory,.bytes .memory,.bool] :=
 .cons (.memRef rfl 1) (.cons (.memRef rfl 0) (.cons (.bool true) .nil))
def old : Source.Val E.layout (.bytes .memory) := .memRef rfl 0
def returnedBytes (bytes : Roadmap.Bytes) := LiteralFailureDynamicReturn.payload [bytes]

theorem memory (bytes : Roadmap.Bytes) :
 LiteralFailureDynamicListError.represented parameters (state bytes []) .here bytes :=
 ⟨1,rfl,.inl rfl⟩

theorem actual_body (p : Roadmap.Pipeline) (static : Bool) (bytes : Roadmap.Bytes) :
 (execS (global p) {frame with static:=static} 6 3 none (statement .here)
 (before old parameters)).run (L0 E,state bytes [])=
 (.ok (.ret (finished parameters .here)),(L0 E,state bytes [])) :=
 source_run (global p) {frame with static:=static} 0 old parameters .here (state bytes [])

theorem actual_encoding (bytes : Roadmap.Bytes) :
 FailurePaths.Premises.EncodingAt frame 0 (extracted parameters .here)
 (state bytes []) (state bytes []) (returnedBytes bytes) :=
 LiteralFailureDynamicReturn.encodingAt frame 0 [.here] [bytes] parameters (state bytes [])
  ⟨memory bytes,trivial⟩

def output (bytes : Roadmap.Bytes) :=
 MemoryOps.Physical.worldJournal (state bytes []).ex
 {live with memory:=Failure.Slice.putBytes live.memory 8 (returnedBytes bytes)}

theorem actual_target (p : Roadmap.Pipeline) (static : Bool) (bytes : Roadmap.Bytes)
 (fits : Failure.Fits 8 (returnedBytes bytes)) :
 Failure.Local.execute (Failure.Local.save (MemoryOps.Physical.worldJournal populated.ex saved))
 8 (.returned (returnedBytes bytes)) (MemoryOps.Physical.worldJournal (state bytes []).ex live)=
 some (output bytes,.success (returnedBytes bytes)) :=
 (chain (global p) {frame with static:=static} 0 0 8 old parameters .here bytes
  (state bytes []) populated (memory bytes) saved live fits (by decide)).2.2.2.2

theorem empty_fits : Failure.Fits 8 (returnedBytes []) := by
 have length : (returnedBytes []).length=64 := by decide +kernel
 simp only [Failure.Fits,length]
 decide +kernel

theorem finite_fits : Failure.Fits 8 (returnedBytes [128,0,255]) := by
 have length : (returnedBytes [128,0,255]).length=96 := by decide +kernel
 simp only [Failure.Fits,length]
 decide +kernel

theorem empty_target :
 Failure.Local.execute (Failure.Local.save (MemoryOps.Physical.worldJournal populated.ex saved))
 8 (.returned (returnedBytes [])) (MemoryOps.Physical.worldJournal (state [] []).ex live)=
 some (output [],.success (returnedBytes [])) := actual_target .legacy false [] empty_fits

theorem finite_target :
 Failure.Local.execute (Failure.Local.save (MemoryOps.Physical.worldJournal populated.ex saved))
 8 (.returned (returnedBytes [128,0,255])) (MemoryOps.Physical.worldJournal (state [128,0,255] []).ex live)=
 some (output [128,0,255],.success (returnedBytes [128,0,255])) :=
 actual_target .viaIR true [128,0,255] finite_fits

theorem overwritten : before old parameters≠finished parameters .here := by
 intro equal
 have bad := congrArg (fun locals=>locals.get .here) equal
 cases bad

/-- Positive stale-slot baseline: it encodes the old object, not the returned one. -/
theorem before_encoding (bytes : Roadmap.Bytes) :
 FailurePaths.Premises.EncodingAt frame 0 (.cons (.val old) .nil)
 (state bytes []) (state bytes []) (LiteralFailureDynamicReturn.payload [[0,255]]) :=
 LiteralFailureDynamicReturn.encodingAt frame 0 [.here] [[0,255]] (before old parameters)
  (state bytes []) ⟨⟨0,rfl,.inl rfl⟩,trivial⟩

theorem wrong_old_packet : returnedBytes [128,0,255]≠LiteralFailureDynamicReturn.payload [[0,255]] := by
 decide +kernel

theorem old_alias_and_cursor (bytes : Roadmap.Bytes) :
 (state bytes []).heap.get 0=some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
 (state bytes []).heap.next=3 ∧
 (finished parameters .here).get (.there (.there .here))=.memRef rfl 0 := ⟨rfl,rfl,rfl⟩

def packets : List Roadmap.Bytes :=
 [returnedBytes [],returnedBytes [128,0,255],returnedBytes (List.replicate 31 255),
 returnedBytes (List.replicate 32 0),returnedBytes (List.replicate 33 128)]
def jsonBytes (bs : List UInt8) : String :=
 "[" ++ String.intercalate "," (bs.map (fun b=>toString b.toNat)) ++ "]"
#eval IO.println ("REFERENCE_RETURN_PACKETS=[" ++ String.intercalate "," (packets.map jsonBytes) ++ "]")
#print axioms source_run
#print axioms extraction
#print axioms chain
#print axioms actual_body
#print axioms actual_encoding
#print axioms actual_target
#print axioms empty_target
#print axioms finite_target
#print axioms overwritten
#print axioms before_encoding
#print axioms wrong_old_packet
#print axioms old_alias_and_cursor
end Solidity.Lowering.V08.LiteralFailureReferenceReturnControls
