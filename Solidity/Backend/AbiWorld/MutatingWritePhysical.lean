import Solidity.Backend.AbiWorld.MutatingEntryWords
import Solidity.Backend.MemoryOps.PhysicalWordFrame

/-! Physical consumption of the actual selected mutating WRITE PREFIX.
The initial P6 WordFrame and its stronger byte-span bound remain explicit.
Scaled byte MSTORE is a separate existing operation, not identical emitted code
or a proof of the subsequent allocating/call-frame physical execution. -/
namespace Solidity.Backend.AbiWorld.MutatingWritePhysical
open Solidity Evm Evm.Memory
open Solidity.Backend.InternalFlow.RuntimeFrame
open RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes
open Solidity.Backend.MemoryOps.Physical
abbrev A := MutatingActivation.A

theorem write_prefix {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
 (σ : State C (Parameters A)) (n : Nat) (fit : n+1<W) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) fit)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (within : n<σ.heap.len ref .dyn)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F σ base before)
 (bytes : Environment.Memory) (live : Nat → Prop) (physical : WordFrame before bytes live)
 (span : 32*((base ref.id).val+1+n)+32≤W) (tail : List Environment.Word) :
 let cell := (base ref.id).val+1+n
 let word : Fin W := ⟨n+1,fit⟩
 let after := writeMachine before cell (.val word)
 let image := Environment.writeBytes bytes (32*cell) (Semantics.wordBytes (n+1))
 (MutatingActivation.write (C:=C)).run σ=.ok ⟨MutatingActivation.changed σ ref n,List.prefix_refl _⟩ ∧
 run (MutatingActivation.selected (C:=C) b F).code before=.ok after 0 ∧
 StateRepr L b frame F (MutatingActivation.changed σ ref n) base after ∧
 GrowsAllocator b frame 0 σ base before (MutatingActivation.changed σ ref n) base after ∧
 Footprint.Words 0 frame before after ∧
 WordFrame after image (fun c => live c ∨ c=cell) ∧
 Environment.cryptoStep (.op .MSTORE)
  ⟨lenU (32*cell) (by change 32*cell<W;omega)::lenU (n+1) fit::tail,bytes⟩=
  some ⟨tail,image⟩ ∧
 Environment.readMemory image (32*cell) 32=AbiEntry.wordBytes (n+1) ∧
 (∀ k,k<32*cell ∨ 32*cell+32≤k → image k=bytes k) := by
 obtain ⟨word,represented,actual,reached,growth,footprint⟩ :=
  MutatingActivation.written σ n fit ref counter alias within base before repr
 change σ.env.1=countValue (n+1) fit at counter
 have exactWord : word=.val (⟨n+1,fit⟩ : Fin W) :=
  Restore.uint_unique represented (by rw [counter];exact ReprV.uint_of rfl)
 subst word
 refine ⟨MutatingActivation.source_write σ n fit ref counter alias within,
  actual,reached,growth,footprint,physical.write _ _ span,?_,?_,?_⟩
 · simpa only [] using byte_mstore bytes tail
    (⟨(base ref.id).val+1+n,by omega⟩ : Fin W) (⟨n+1,fit⟩ : Fin W) span
 · rw [LibraryResultPacket.word_bytes]
   exact Environment.read_written _ _ _
 · intro k outside
   apply Environment.writeBytes_frame
   rw [Environment.wordBytes_length]
   exact outside
end Solidity.Backend.AbiWorld.MutatingWritePhysical
