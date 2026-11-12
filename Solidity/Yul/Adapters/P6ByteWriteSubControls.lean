import Solidity.Yul.Adapters.P6ByteWriteSub
import Solidity.Yul.Adapters.P6ByteReferenceWriteControls
import Solidity.Yul.Views.HeapByteResizeControls

/-! Empty child locals do not erase two suspended caller aliases. Both success
and a late explicit Source revert retain the byte write; immediate bounds
failure retains the old store. Substitution is not a call/frame rollback. -/
namespace Solidity.Yul.Adapters.P6ByteWriteSub.Controls
open Solidity.Yul.Views Solidity.Yul.Views.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open P6ByteFamilyCopy.Controls (placement entries residual carrier fits)
open P6ByteReferenceWrite.Controls (image reached)

def output := withSourceHeap stringAliasState (byteHeap.write 1
  (Source.Data.string (l:=.memory) (stringOld.set 32 0xff)) (by rfl))

/-- The same realized Source state describes child success, late error and
whole physical reconstruction despite the child having no reference locals. -/
theorem empty_child : ∃ r : InventoryRealization placement,
    withSourceHeap stringAliasState r.heap=output ∧
    (Source.EM.sub (Source.Locals.nil (D:=heapByteEnv.layout))
      (Source.writeLoc byteReadFrame 0 (.memByte 1 32)
        (Source.Val.fixedBytes (n:=1) (h:=by decide) [0xff] rfl))).run stringAliasState=
        (.ok ((),.nil),output) ∧
    (Source.EM.sub (Source.Locals.nil (D:=heapByteEnv.layout))
      ((Source.writeLoc byteReadFrame 0 (.memByte 1 32)
        (Source.Val.fixedBytes (n:=1) (h:=by decide) [0xff] rfl)) >>= fun _ =>
          (Source.EM.halt (.revert [0xde,0xad]) : Source.EM heapByteEnv [] Unit))).run stringAliasState=
        (.error (.revert [0xde,0xad]),output) ∧
    encodeMixedHeap r.placement r.entries (frameBytes reached)=frameBytes reached ∧
    CoversMixedHeap r.entries ∧ r.entries.map MixedHeapEntry.id=[0,1,2] ∧
    (∀ H,Source.MemOK heapByteEnv H stringAliasState → Source.MemOK heapByteEnv H output) := by
  have initial : frameBytes image=encodeMixedHeap placement entries residual := FrameHeap.frameOf_bytes _ _ _ _ _ _
  obtain ⟨r,run,halt,encoded,covered,ids,cell,safe,other⟩ := inventory byteReadFrame 0 stringAliasState .nil
    placement placement .initial entries P6ByteFamilyCopy.Controls.coverage (by decide) image residual initial
    1 true stringOld rfl 32 (by decide) 0xff (by decide)
  have known := success byteReadFrame 0 stringAliasState (Source.Locals.nil (D:=heapByteEnv.layout))
    1 true stringOld rfl 32 (by decide) 0xff
  have same := congrArg Prod.snd (run.symm.trans known)
  change withSourceHeap stringAliasState r.heap=output at same
  refine ⟨r,same,?_,?_,encoded,covered,?_,?_⟩
  · rw [←same];exact run
  · rw [←same];exact halt (.revert [0xde,0xad])
  · rw [ids];rfl
  · rw [←same];exact safe

/-- Both actual caller aliases read the changed heap after child completion or
late halt; the bytes/string memory compatibility does not relabel Source.Data. -/
theorem caller_reads (n : Nat) : output.1=stringAliasState.1 ∧
    (Source.bytesOfRV byteReadFrame n (.val (output.1.get .here))).run output=
      (.ok (stringOld.set 32 0xff),output) ∧
    (Source.bytesOfRV byteReadFrame n (.val (output.1.get (.there .here)))).run output=
      (.ok (stringOld.set 32 0xff),output) := ⟨rfl,rfl,rfl⟩

/-- Actual initial owner MemOK is inhabited for the suspended aliased caller. -/
theorem initial_safe : Source.MemOK heapByteEnv byteHeap.ty stringAliasState := string_alias_initial_MemOK

/-- Immediate child bounds failure restores the entire prior Source state. -/
theorem outside_child :
    (Source.EM.sub (Source.Locals.nil (D:=heapByteEnv.layout))
      (Source.writeLoc byteReadFrame 0 (.memByte 1 40)
        (Source.Val.fixedBytes (n:=1) (h:=by decide) [0xff] rfl))).run stringAliasState=
        (.error (.revert (Source.panicData .index)),stringAliasState) :=
  outside byteReadFrame 0 stringAliasState .nil 1 true stringOld rfl 40 (by decide) 0xff

/-- Treating late halt as rollback would lose a real changed Source byte. -/
theorem late_halt_not_rollback : output≠stringAliasState := by
  intro same
  have byte := congrArg (fun s => (Source.readLoc byteReadFrame (.memByte 1 32)).run s |>.1) same
  have changed : ((Source.readLoc byteReadFrame (.memByte 1 32)).run output).1=
      .ok (Source.Val.fixedBytes (n:=1) (h:=by decide) [0xff] rfl) := by rfl
  have old : ((Source.readLoc byteReadFrame (.memByte 1 32)).run stringAliasState).1=
      .ok (Source.Val.fixedBytes (n:=1) (h:=by decide) [0x61] rfl) := by rfl
  dsimp only at byte
  rw [changed,old] at byte
  cases byte
end Solidity.Yul.Adapters.P6ByteWriteSub.Controls
