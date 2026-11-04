import Solidity.Backend.MemoryOps.PhysicalPointerMaterialize
import Solidity.Backend.MemoryOps.PhysicalWorldUnwind

/-! A saved mixed frame is DERIVED from actual byte materialization. Existing
Source journal operations and actual ABI emission then restore that reached
checkpoint. No world/heap codec or transaction/catch compiler is defined. -/
namespace Solidity.Backend.MemoryOps.Physical

theorem materialize_checked_complete (b : UInt8) (bs : List UInt8) (a : Nat)
    (tail : List Roadmap.Word) (bytes : Environment.Memory)
    (fits : a+(b::bs).length≤2^256) (room : tail.length+2≤1024) :
    Failure.Slice.checkedRun (Environment.materialize a (b::bs)) ⟨tail,bytes⟩=
      some (⟨tail,Environment.writeBytes bytes a (b::bs)⟩,none) := by
  first
  | solve | simp only [] | omega
  | have run := materialize_checked_suffix_exact b bs a tail bytes [] fits
    rw [if_pos room] at run
    have safe : Failure.Slice.stackSafe [] ⟨tail,Environment.writeBytes bytes a (b::bs)⟩=true := by
      change decide (tail.length≤1024)=true
      exact decide_eq_true (by omega)
    have finish : Failure.Slice.checkedRun [] ⟨tail,Environment.writeBytes bytes a (b::bs)⟩=
        some (⟨tail,Environment.writeBytes bytes a (b::bs)⟩,none) := by
      rw [Failure.Slice.checkedRun,if_pos safe]
      rfl
    rw [finish] at run
    simpa only [List.append_nil] using run

/-- The actual successful prefix supplies checkpoint bytes and frames. Dirty
Source stores are actual run outputs, and ABI reason bytes are obtained before
restoration. Only the explicit published component checkpoint is restored. -/
theorem ReferenceArrayAt.materialize_world_unwind {H : HTy} {R : RefTy} {hp : Heap H}
    {root : HRef H (.array (.ref R))} {base : Nat → Fin Evm.W} {m : Evm.Machine} {bytes : Environment.Memory}
    (h : ReferenceArrayAt hp root base m bytes) (numeric : Nat → Prop) (words : WordFrame m bytes numeric)
    {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    (state : Source.ExecState D L T) (prefixOps dirtyOps : List (Source.Op D L T))
    (this caller : Roadmap.Address) (value : Roadmap.Word) (input : Roadmap.Bytes) (static : Bool)
    (b : UInt8) (bs : List UInt8) (offset : Nat) (tail : List Roadmap.Word)
    (fits : offset+(b::bs).length≤2^256) (room : tail.length+2≤1024)
    (header : offset+(b::bs).length≤32*(base root.id).val ∨ 32*(base root.id).val+32≤offset)
    (pointers : ∀ c,ReferenceSlots hp root base c → offset+(b::bs).length≤32*c ∨ 32*c+32≤offset)
    (numbers : ∀ c,numeric c → offset+(b::bs).length≤32*c ∨ 32*c+32≤offset)
    (a : Nat) (reason : Roadmap.Bytes) (suffix : Backend.Program)
    (reasonFits : Failure.Fits a (Semantics.encodeError reason)) :
    let savedBytes := Environment.writeBytes bytes offset (b::bs)
    let saved : Failure.Slice.Machine := ⟨tail,savedBytes⟩
    let before := state.run prefixOps
    let dirty := before.run dirtyOps
    Failure.Slice.checkedRun (Environment.materialize offset (b::bs)) ⟨tail,bytes⟩=some (saved,none) ∧
    (before.enter this caller value input static).rollback dirty=before ∧
    Failure.Slice.checkedRun (Failure.emit a (.reason reason)++suffix) saved=
      some ({saved with memory := Failure.Slice.putBytes savedBytes a (Source.errorData reason)},
        some (.revert (Source.errorData reason))) ∧
    ∃ output,Failure.Local.execute (Failure.Local.save (worldJournal before saved)) a (.reason reason)
        (worldJournal dirty saved)=some (output,.revert (Source.errorData reason)) ∧
      ReferenceArrayAt hp root base m output.machine.memory ∧ WordFrame m output.machine.memory numeric ∧
      output.machine=saved ∧ output.persistent=before.world ∧ output.transient=before.transient := by
  first
  | solve | simp only [] | omega
  | dsimp only
    have firstRun := materialize_checked_complete b bs offset tail bytes fits room
    have world := world_reason_unwind (state.run prefixOps) dirtyOps this caller value input static
      ⟨tail,Environment.writeBytes bytes offset (b::bs)⟩ ⟨tail,Environment.writeBytes bytes offset (b::bs)⟩ a reason reasonFits room
    have emitted := reason_live_bytes a reason ⟨tail,Environment.writeBytes bytes offset (b::bs)⟩ suffix reasonFits room
    refine ⟨firstRun,world.1,emitted,worldJournal (state.run prefixOps) _,world.2,?_,?_,rfl,rfl,rfl⟩
    · exact h.materialize_outside offset (b::bs) header pointers
    · exact words.materialize_outside offset (b::bs) numbers

/-- info: 'Solidity.Backend.MemoryOps.Physical.materialize_checked_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms materialize_checked_complete
/-- info: 'Solidity.Backend.MemoryOps.Physical.ReferenceArrayAt.materialize_world_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ReferenceArrayAt.materialize_world_unwind
end Solidity.Backend.MemoryOps.Physical
