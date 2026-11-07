import Solidity.Backend.AbiWorld.MutatingWritePhysical
import Solidity.Backend.MemoryOps.PhysicalByteWorldInterface

/-! Consumer of the PUBLISHED pending ByteWorld producer. The intrinsic statement/word
write and reached physical bytes are proved first. Store-plus-load execution
then uses exactly the imported producer field; no concrete loadCode/Producer
is invented and no unknown-memory encoder or physical compiler is claimed. -/
namespace Solidity.Backend.AbiWorld.MutatingByteLoad
open Solidity Evm Evm.Memory
open Solidity.Backend.InternalFlow.RuntimeFrame
open RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes
open Solidity.Backend.MemoryOps.Physical
abbrev A := MutatingActivation.A

theorem write_then_load {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
 (σ : State C (Parameters A)) (n : Nat) (fit : n+1<W) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) fit)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (within : n<σ.heap.len ref .dyn)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F σ base before)
 (bytes : Environment.Memory) (live : Nat → Prop) (physical : WordFrame before bytes live)
 (span : 32*((base ref.id).val+1+n)+32≤W)
 (loadCode : Nat → Backend.Program) (producer : ByteWorld.Producer loadCode)
 (byteFrame : Environment.Frame) (tail : List Environment.Word) (room : tail.length+1≤1024) :
 let cell := (base ref.id).val+1+n
 let word : Fin W := ⟨n+1,fit⟩
 let after := writeMachine before cell (.val word)
 let image := Environment.writeBytes bytes (32*cell) (Semantics.wordBytes (n+1))
 Memory.compileStmt b F (MutatingActivation.write (C:=C))=some (MutatingActivation.selected b F) ∧
 (MutatingActivation.write (C:=C)).run σ=.ok ⟨MutatingActivation.changed σ ref n,List.prefix_refl _⟩ ∧
 run (MutatingActivation.selected (C:=C) b F).code before=.ok after 0 ∧
 StateRepr L b frame F (MutatingActivation.changed σ ref n) base after ∧
 GrowsAllocator b frame 0 σ base before (MutatingActivation.changed σ ref n) base after ∧
 Footprint.Words 0 frame before after ∧
 WordFrame after image (fun c => live c ∨ c=cell) ∧
 Environment.readMemory image (32*cell) 32=AbiEntry.wordBytes (n+1) ∧
 (∀ k,k<32*cell ∨ 32*cell+32≤k → image k=bytes k) ∧
 run [.mloadAt] (after.push (.val ⟨cell,by omega⟩))=.ok (after.push (.val word)) 0 ∧
 Environment.runSlice byteFrame (loadCode cell) ⟨tail,image⟩=
 some ⟨lenU (n+1) fit::tail,image⟩ ∧
 Environment.runSlice byteFrame (.op .MSTORE::loadCode cell)
  ⟨lenU (32*cell) (by change 32*cell<W;omega)::lenU (n+1) fit::tail,bytes⟩=
 some ⟨lenU (n+1) fit::tail,image⟩ := by
 first | (solve | rfl) | (solve | decide) | (solve | omega) | skip
 obtain ⟨source,actual,reached,growth,footprint,representation,stored,read,exterior⟩ :=
  MutatingWritePhysical.write_prefix σ n fit ref counter alias within base before repr bytes live physical span tail
 have imageRead : Environment.readMemory
   (Environment.writeBytes bytes (32*((base ref.id).val+1+n)) (Semantics.wordBytes (n+1)))
   (32*((base ref.id).val+1+n)) 32=Semantics.wordBytes (n+1) := by
  exact read.trans (LibraryResultPacket.word_bytes (n+1))
 have loaded := producer.load byteFrame _ ⟨(base ref.id).val+1+n,by omega⟩ ⟨n+1,fit⟩ tail span room imageRead
 refine ⟨MutatingActivation.public_selection b F,source,actual,reached,growth,footprint,
  representation,read,exterior,?_,loaded,?_⟩
 · change Evm.Out.ok ((writeMachine before _ (.val ⟨n+1,fit⟩)).push
    ((writeMachine before _ (.val ⟨n+1,fit⟩)).mem _)) 0=_
   simp only [writeMachine,upd_same]
 · rw [Environment.runSlice]
   change (Environment.cryptoStep (.op .MSTORE)
    ⟨lenU (32*((base ref.id).val+1+n)) (by change 32*((base ref.id).val+1+n)<W;omega)::
     lenU (n+1) fit::tail,bytes⟩).bind
      (Environment.runSlice byteFrame (loadCode ((base ref.id).val+1+n)))=_
   rw [stored]
   exact loaded

/-- Concrete negative for the literal instruction currently absent from the
published slice. This does not show every possible load program impossible. -/
theorem literal_mload_refused (frame : Environment.Frame) :
 ¬ ByteWorld.Producer (fun _ => [.op .MLOAD]) := by
 first | (solve | rfl) | (solve | decide) | (solve | omega) | skip
 intro producer
 have image : Environment.readMemory (fun _ => 0) 0 32=Semantics.wordBytes 0 := by decide +kernel
 have required := producer.load frame (fun _ => 0) ⟨0,by decide⟩ ⟨0,by decide⟩ [] (by decide) (by decide) image
 change (none : Option Environment.Slice)=some _ at required
 cases required
end Solidity.Backend.AbiWorld.MutatingByteLoad
