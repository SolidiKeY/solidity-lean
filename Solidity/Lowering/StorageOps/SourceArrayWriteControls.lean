import Solidity.Lowering.StorageOps.SourceArrayWrite
import Solidity.Lowering.StorageOps.SourceArrayIndexControls
namespace Solidity.Lowering.StorageOps.SourceArrayWriteControls
open Solidity.Backend.StorageOps
open SourceArrayIndexControls

def writable : Source.Fr := {frame with static:=false}
def payload : Source.Val env.layout (env.cellTy (child 1)) := .int 83 (by decide)
def afterState := SourceWordWrite.after writable (child 1) payload state
def sourceRun (budget : Nat) := (SourceArrayWrite.write (E:=env) (Γ:=[]) writable budget path (env.cellTy (child 1)) 1 payload).run initial
def targetInput : Evm.Machine := {target with stack:=.val ⟨1,by decide⟩ :: .slot (.root 0) :: .val ⟨83,by decide⟩ :: target.stack}
def afterTarget : Evm.Machine := {target with store:=Evm.WordStore.write target.store (.data (.root 0) 1) 83}
def targetRun := Evm.run TargetArrayWrite.code targetInput

theorem source_success (budget : Nat) : sourceRun budget=(.ok (),(.nil,afterState)) := by
  exact SourceArrayWrite.source_run env [] writable path 1 .nil state rfl rfl
    (.int 2 (by decide)) 2 (by decide) rfl rfl payload budget rfl rfl (by decide)

theorem target_success : targetRun=.ok afterTarget 0 := by
  unfold targetRun targetInput
  rw [TargetArrayWrite.run_current]
  rfl

def rejected := (SourceArrayWrite.write (E:=env) (Γ:=[]) writable 0 path (env.cellTy (child 2)) 2 (.int 83 (by decide))).run initial

theorem fresh_failure : rejected=(.error (.revert (Source.panicData .index)),initial) := by
  unfold rejected SourceArrayWrite.write
  dsimp only [initial]
  rw [Source.Hoare.run_bind,SourceArrayIndex.locate env [] writable path _ 2 .nil state rfl rfl (.int 2 (by decide)) 2 (by decide) rfl rfl]
  rfl

def retainedAfter := SourceWordWrite.after writable (child 2) (.int 83 (by decide)) state

theorem retained_success :
    (Source.writeLoc (E:=env) (Γ:=[]) writable 0 captured (.int 83 (by decide))).run initial =
      (.ok (),(.nil,retainedAfter)) := by
  change (Source.writeAt (E:=env) (Γ:=[]) (τ:=env.cellTy (child 2)) writable (child 2) (.int 83 (by decide)) : Source.EM env [] Unit).run initial = _
  exact SourceWordWrite.source_write (E:=env) (Γ:=[]) writable (child 2) (.int 83 (by decide)) .nil state rfl rfl

/-- Complete ordered old/new Source and target observations: header, all live
and retained children, unrelated cell, journal and machine/account context. -/
def ordered := (sourceView state,sourceView afterState,targetView target,targetView afterTarget)

theorem observations : ordered =
 (([some 2,some 53,some 59,some 61,some 97],0,19,3,some 0,0,0),
  ([some 2,some 53,some 83,some 61,some 97],1,19,3,some 0,0,0),
  ([2,53,59,61,99],[Evm.Word.val ⟨23,by decide⟩,.slot (.root 9)],.val (Evm.wmod 31),37,41,Evm.wmod 43,Evm.wmod 47,Evm.wmod 0,Evm.wmod 53,false),
  ([2,53,83,61,99],[Evm.Word.val ⟨23,by decide⟩,.slot (.root 9)],.val (Evm.wmod 31),37,41,Evm.wmod 43,Evm.wmod 47,Evm.wmod 0,Evm.wmod 53,false)) := by rfl
/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWriteControls.source_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_success
/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWriteControls.target_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms target_success
/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWriteControls.fresh_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fresh_failure
/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWriteControls.retained_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms retained_success
/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWriteControls.observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms observations
end Solidity.Lowering.StorageOps.SourceArrayWriteControls
