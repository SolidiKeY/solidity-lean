import Solidity.Lowering.V08.LiteralFailureDynamicReturn
import Solidity.Lowering.V08.SourceCustomErrorControls
namespace Solidity.Lowering.V08.LiteralFailureDynamicReturnControls
open Solidity Source Backend
open SourceCustomErrorControls (E frame populated)
open LiteralFailureDynamicReturn

def context : RCtx := [.bytes .memory,.bytes .memory,.bytes .memory,.bool]
def locals : Locals E.layout context :=
 .cons (.memRef rfl 1) (.cons (.memRef rfl 2) (.cons (.memRef rfl 0) (.cons (.bool true) .nil)))
def refs : List (Source.Idx context (.bytes .memory)) := [.here,.there .here,.here]
def state (first second : Roadmap.Bytes) : St E :=
 {populated with
  heap := ((populated.heap.alloc ⟨.bytes .memory,.bytes first⟩).1.alloc ⟨.bytes .memory,.bytes second⟩).1
  ex := populated.ex.run [.account frame.this (fun account=>{account with nonce:=4})]}

theorem memory (first second : Roadmap.Bytes) :
 LiteralFailureDynamicListError.all_represented locals (state first second) refs [first,second,first] :=
 ⟨⟨1,rfl,.inl rfl⟩,⟨⟨2,rfl,.inl rfl⟩,⟨⟨1,rfl,.inl rfl⟩,trivial⟩⟩⟩

def saved : Failure.Slice.Machine := ⟨[99],fun _=>170⟩
def live : Failure.Slice.Machine := ⟨[7,9],fun _=>85⟩
def checkpoint := Failure.Local.save (MemoryOps.Physical.worldJournal populated.ex saved)
def returned (first second : Roadmap.Bytes) :=
 MemoryOps.Physical.worldJournal (state first second).ex
 {live with memory:=Failure.Slice.putBytes live.memory 8 (LiteralFailureDynamicReturn.payload [first,second,first])}

theorem actual_return (F : Fr) (fuel : Nat) (first second : Roadmap.Bytes)
 (fits : Failure.Fits 8 (LiteralFailureDynamicReturn.payload [first,second,first])) :
 Failure.Local.execute checkpoint 8 (.returned (LiteralFailureDynamicReturn.payload [first,second,first]))
 (MemoryOps.Physical.worldJournal (state first second).ex live)=
 some (returned first second,.success (LiteralFailureDynamicReturn.payload [first,second,first])) :=
 (return_transport F fuel 8 refs [first,second,first] locals (state first second) populated
  (memory first second) saved live fits (by decide)).2.2

theorem empty_return (F : Fr) (fuel : Nat) :
 Failure.Local.execute checkpoint 8 (.returned (LiteralFailureDynamicReturn.payload []))
 (MemoryOps.Physical.worldJournal (state [] []).ex live)=
 some (MemoryOps.Physical.worldJournal (state [] []).ex
  {live with memory:=Failure.Slice.putBytes live.memory 8 (LiteralFailureDynamicReturn.payload [])},
  .success (LiteralFailureDynamicReturn.payload [])) :=
 (return_transport F fuel 8 [] [] locals (state [] []) populated trivial saved live
  (by simp only [Failure.Fits,LiteralFailureDynamicReturn.payload,
    LiteralFailureDynamicListError.abiValues,AbiEntry.encodeArgs,AbiEntry.assemble,
    AbiEntry.Vals.parts,AbiEntry.assemble.go,List.foldl_nil,List.append_nil,List.length_nil]; decide +kernel)
  (by decide)).2.2

theorem fits : Failure.Fits 8 (LiteralFailureDynamicReturn.payload [[0,255],[128],[0,255]]) := by
 have length : (LiteralFailureDynamicReturn.payload [[0,255],[128],[0,255]]).length=288 := by decide +kernel
 simp only [Failure.Fits,length]
 decide +kernel

theorem finite_return :
 Failure.Local.execute checkpoint 8 (.returned (LiteralFailureDynamicReturn.payload [[0,255],[128],[0,255]]))
 (MemoryOps.Physical.worldJournal (state [0,255] [128]).ex live)=
 some (returned [0,255] [128],.success (LiteralFailureDynamicReturn.payload [[0,255],[128],[0,255]])) :=
 actual_return frame 0 [0,255] [128] fits

theorem actual_revert_same_bytes :
 Failure.Local.execute checkpoint 8 (.custom (LiteralFailureDynamicReturn.payload [[0,255],[128],[0,255]]))
 (MemoryOps.Physical.worldJournal (state [0,255] [128]).ex live)=
 some (Failure.Local.restore checkpoint,.revert (LiteralFailureDynamicReturn.payload [[0,255],[128],[0,255]])) :=
 Failure.Local.execute_failure checkpoint 8 _ _ fits (by decide)

theorem world_prefix :
 ((state [0,255] [128]).ex.world.accounts frame.this).nonce=4 ∧
 (populated.ex.world.accounts frame.this).nonce=1 ∧
 (state [0,255] [128]).heap.get 0=some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
 (state [0,255] [128]).heap.next=3 := ⟨rfl,rfl,rfl,rfl⟩

theorem return_does_not_restore :
 Failure.Local.execute checkpoint 8 (.returned (LiteralFailureDynamicReturn.payload [[0,255],[128],[0,255]]))
 (MemoryOps.Physical.worldJournal (state [0,255] [128]).ex live) ≠
 some (Failure.Local.restore checkpoint,.success (LiteralFailureDynamicReturn.payload [[0,255],[128],[0,255]])) := by
 rw [finite_return]
 intro equal
 have bad := congrArg (fun result=>result.map (fun pair=>(pair.1.persistent.accounts frame.this).nonce)) equal
 change some 4=some 1 at bad
 cases bad

def packets : List Roadmap.Bytes :=
 [LiteralFailureDynamicReturn.payload [],LiteralFailureDynamicReturn.payload [[0,255],[128],[0,255]],LiteralFailureDynamicReturn.payload [[],[],[]],
  LiteralFailureDynamicReturn.payload [List.replicate 31 255,List.replicate 32 0,List.replicate 31 255],
  LiteralFailureDynamicReturn.payload [List.replicate 33 128,[0,255,0],List.replicate 33 128]]
def jsonBytes (bs : List UInt8) : String :=
 "[" ++ String.intercalate "," (bs.map (fun b=>toString b.toNat)) ++ "]"
#eval IO.println ("DYNAMIC_RETURN_PACKETS=[" ++ String.intercalate "," (packets.map jsonBytes) ++ "]")
#print axioms encodingAt
#print axioms return_transport
#print axioms memory
#print axioms actual_return
#print axioms empty_return
#print axioms fits
#print axioms finite_return
#print axioms actual_revert_same_bytes
#print axioms world_prefix
#print axioms return_does_not_restore
end Solidity.Lowering.V08.LiteralFailureDynamicReturnControls
