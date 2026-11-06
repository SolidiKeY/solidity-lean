import Solidity.Backend.StorageOps.TargetArrayCopyTail

/-! Repetition of the ACTUAL two-loop storage-copy instructions. Access sets
are existing target slots; they add no IR/value/state layer or hash premise.
Structured target execution remains separate from Source/bytecode/world. -/
namespace Solidity.Backend.StorageOps.TargetArrayRepeat
open TargetArrayCopyTail

def reads (machine : Evm.Machine) (src : Evm.Slot) : List Evm.Slot :=
 src :: (List.range (machine.store src)).map (Evm.Slot.data src)
def writes (machine : Evm.Machine) (src dst : Evm.Slot) : List Evm.Slot :=
 dst :: (List.range (max (machine.store src) (machine.store dst))).map (Evm.Slot.data dst)
def code (src dst : Evm.Slot) : List Evm.Instr :=
 [.push (.slot dst),.push (.slot src)] ++ TargetArrayCopy.code

/-- Two actual runtime-length copy/clear programs (including actual address
pushes) return the first copy's entire Machine. Generated address separation
or exact self-copy derives CURRENT source stability; no postresult assumed. -/
theorem complete (machine : Evm.Machine) (src dst : Evm.Slot)
 (safe : src=dst ∨ ∀ w∈writes machine src dst,∀ r∈reads machine src,w≠r) :
 Evm.run (code src dst ++ code src dst) machine=
  .ok (afterCopy machine machine.stack src dst) 0 ∧
 afterCopy (afterCopy machine machine.stack src dst) machine.stack src dst=
  afterCopy machine machine.stack src dst := by
 let first := afterCopy machine machine.stack src dst
 have stable : first.store src=machine.store src ∧
   ∀ i<machine.store src,first.store (.data src i)=machine.store (.data src i) := by
  rcases safe with same | separate
  · subst dst
    refine ⟨after_header _ _ _ _,?_⟩
    intro i inside
    change (afterCopy machine machine.stack src src).store (.data src i)=_
    rw [after_data,if_pos inside]
  · have frame : ∀ r∈reads machine src,first.store r=machine.store r := by
     intro r member
     apply after_outside
     · intro equal
       exact separate dst List.mem_cons_self r member equal.symm
     · intro j inside equal
       have visited : Evm.Slot.data dst j∈writes machine src dst :=
        List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j,List.mem_range.mpr inside,rfl⟩)
       exact separate _ visited r member equal.symm
    refine ⟨frame src List.mem_cons_self,?_⟩
    intro i inside
    exact frame _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,List.mem_range.mpr inside,rfl⟩))
 have newDst : first.store dst=machine.store src := after_header _ _ _ _
 have words : ∀ observer,(afterCopy first machine.stack src dst).store observer=first.store observer := by
  intro observer
  by_cases header : observer=dst
  · subst observer
    rw [after_header,stable.1,newDst]
  · by_cases payload : ∃ i,observer=Evm.Slot.data dst i
    · obtain ⟨i,rfl⟩:=payload
      rw [after_data,stable.1,newDst]
      by_cases live : i<machine.store src
      · rw [if_pos live,stable.2 i live]
        change _=(afterCopy machine machine.stack src dst).store (.data dst i)
        rw [after_data,if_pos live]
      · rw [if_neg live,if_neg live]
    · apply after_outside
      · exact header
      · intro i _ equal
        exact payload ⟨i,equal⟩
 have stores := Evm.WordStore.ext words
 have repeated : afterCopy first machine.stack src dst=first :=
  congrArg (fun store : Evm.WordStore => {machine with store:=store}) stores
 have runOnce : ∀ current : Evm.Machine,Evm.run (code src dst) current=
   .ok (afterCopy current current.stack src dst) 0 := by
  intro current
  have pushes : Evm.run [.push (.slot dst),.push (.slot src)] current=
   .ok {current with stack:=.slot src :: .slot dst :: current.stack} 0 := by rfl
  unfold code
  rw [Evm.run_append_ok pushes]
  exact run_current current current.stack src dst
 refine ⟨?_,repeated⟩
 rw [Evm.run_append_ok (runOnce machine),runOnce]
 change Evm.Out.ok (afterCopy first machine.stack src dst) 0=Evm.Out.ok first 0
 rw [repeated]

/-- info: 'Solidity.Backend.StorageOps.TargetArrayRepeat.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete
end Solidity.Backend.StorageOps.TargetArrayRepeat
