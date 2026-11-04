import Solidity.Backend.AbiWorld.MutatingWritePhysical

/-! Initial nonempty two-cell physical frame for the real selected write.
The original heap alias cell changes 9 to 2; distinct old-object cell 21 stays 4.
The byte addresses are 576 and 672, NOT word addresses 18 and 21. -/
namespace Solidity.Backend.AbiWorld.MutatingWritePhysicalControls
open Solidity Evm Evm.Memory
open Solidity.Backend.InternalFlow.RuntimeFrame
open RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes
open CountdownWitness
open Solidity.Backend.MemoryOps.Physical
abbrev before := MutatingActivation.Checks.before
def bytes : Environment.Memory := Environment.writeBytes
 (Environment.writeBytes (fun _ => 0) 576 (Semantics.wordBytes 9)) 672 (Semantics.wordBytes 4)
def image : Environment.Memory := Environment.writeBytes bytes 576 (Semantics.wordBytes 2)
def live (c : Nat) : Prop := c=18 ∨ c=21

theorem initial : WordFrame before bytes live := by
 constructor
 · intro c hc
   rcases hc with rfl | rfl <;> decide +kernel
 · intro c hc
   rcases hc with rfl | rfl
   · refine ⟨⟨9,by decide +kernel⟩,by decide +kernel,?_⟩
     change Environment.readMemory (Environment.writeBytes _ 672 (Semantics.wordBytes 4)) 576 32=_
     rw [readMemory_write_frame _ 576 32 672 _ (Or.inl (by decide))]
     exact Environment.read_written _ _ _
   · exact ⟨⟨4,by decide +kernel⟩,by decide +kernel,Environment.read_written _ _ _⟩

theorem applied :
 let after := writeMachine before 18 w[2]
 (MutatingActivation.write (C:=P.C)).run callee=
 .ok ⟨MutatingActivation.changed callee P.r0 1,List.prefix_refl _⟩ ∧
 run (MutatingActivation.selected (C:=P.C) 2 F).code before=.ok after 0 ∧
 StateRepr 1 2 16 F (MutatingActivation.changed callee P.r0 1) P.base after ∧
 WordFrame after image (fun c => live c ∨ c=18) ∧
 Environment.cryptoStep (.op .MSTORE) ⟨lenU 576 (by decide)::lenU 2 (by decide)::[lenU 77 (by decide)],bytes⟩=
 some ⟨[lenU 77 (by decide)],image⟩ ∧
 Environment.readMemory image 576 32=AbiEntry.wordBytes 2 ∧
 Environment.readMemory image 672 32=AbiEntry.wordBytes 4 := by
 obtain ⟨source,actual,represented,growth,footprint,physical,stored,read,exterior⟩ :=
  MutatingWritePhysical.write_prefix callee 1 (by decide) P.r0 rfl rfl
   (by rw [HeapDomain.Checks.length_zero];decide) P.base before ParentPrefixes.Checks.initial
   bytes live initial (by decide) [lenU 77 (by decide)]
 refine ⟨source,actual,represented,physical,stored,read,?_⟩
 change Environment.readMemory (Environment.writeBytes bytes 576 (Semantics.wordBytes 2)) 672 32=_
 rw [readMemory_write_frame _ 672 32 576 _ (Or.inr (by decide))]
 rw [LibraryResultPacket.word_bytes]
 exact Environment.read_written _ _ _

theorem wrong_scale : Environment.readMemory image 18 32≠AbiEntry.wordBytes 2 := by decide +kernel

theorem stale_bytes : Environment.readMemory image 576 32≠AbiEntry.wordBytes 9 := by decide +kernel

theorem word_fit_is_not_byte_fit : W-1<W ∧ ¬ (32*(W-1)+32≤W) := by decide +kernel

def render (bs : List UInt8) := "["++String.intercalate "," (bs.map (fun b=>toString b.toNat))++"]"
#eval "PHYSICAL_WRITE_OLD="++render (Environment.readMemory bytes 576 32)
#eval "PHYSICAL_WRITE_NEW="++render (Environment.readMemory image 576 32)
#eval "PHYSICAL_WRITE_NEIGHBOR="++render (Environment.readMemory image 672 32)
/-- info: 'Solidity.Backend.AbiWorld.MutatingWritePhysical.write_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MutatingWritePhysical.write_prefix
/-- info: 'Solidity.Backend.AbiWorld.MutatingWritePhysicalControls.initial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms initial
/-- info: 'Solidity.Backend.AbiWorld.MutatingWritePhysicalControls.applied' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms applied
/-- info: 'Solidity.Backend.AbiWorld.MutatingWritePhysicalControls.wrong_scale' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms wrong_scale
/-- info: 'Solidity.Backend.AbiWorld.MutatingWritePhysicalControls.stale_bytes' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms stale_bytes
/-- info: 'Solidity.Backend.AbiWorld.MutatingWritePhysicalControls.word_fit_is_not_byte_fit' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms word_fit_is_not_byte_fit
end Solidity.Backend.AbiWorld.MutatingWritePhysicalControls
