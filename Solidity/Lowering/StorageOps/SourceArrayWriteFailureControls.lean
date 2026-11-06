import Solidity.Lowering.StorageOps.SourceArrayWriteFailure
import Solidity.Lowering.StorageOps.SourceArrayWriteControls
/-! Complete ordered bounds/type/static/fuel controls on populated actual
Source and target states. Malformed adapter inputs are negative controls, not
an extension of admitted Source programs. Raw cell absence and defaulted reads
are observed separately; target revert does not assert world rollback. -/
namespace Solidity.Lowering.StorageOps.SourceArrayWriteFailureControls
open Solidity.Backend.StorageOps SourceArrayIndexControls

def bool_certificate (i : Fin 4) (outside : 2≤i.val) :=
 SourceArrayWriteFailure.bounds_failure env [] frame path .bool i.val .nil state rfl rfl
 (.int 2 (by decide)) 2 (by decide) rfl rfl (.bool true) 0 outside
 target target.stack (.root 0) (Nat.lt_trans i.isLt (by decide : 4<Evm.W)) (Evm.wmod 83) rfl

def aggregate : Source.Val env.layout (.array .storage (.int Source.IntTy.u256) none) := .storRef (by rfl) path

def aggregate_certificate := SourceArrayWriteFailure.bounds_failure env [] frame path
 (.array .storage (.int Source.IntTy.u256) none) 2 .nil state rfl rfl
 (.int 2 (by decide)) 2 (by decide) rfl rfl aggregate 0 (by decide)
 target target.stack (.root 0) (by decide) (Evm.wmod 0) rfl

def wrongLive := (SourceArrayWrite.write (E:=env) (Γ:=[]) frame 0 path .bool 1 (.bool true)).run initial
def staticLive := (SourceArrayWrite.write (E:=env) (Γ:=[]) frame 0 path (.int Source.IntTy.u256) 1 (.int 83 (by decide))).run initial

theorem wrong_live : wrongLive=(.error (.stuck "storage cell type"),initial) := by
 rfl

theorem static_live : staticLive=(.error (.revert []),initial) := by
 rfl

def boolRun (i : Fin 4) := (SourceArrayWrite.write (E:=env) (Γ:=[]) frame 0 path .bool i.val (.bool true)).run initial
def aggregateRun := (SourceArrayWrite.write (E:=env) (Γ:=[]) frame 0 path
 (.array .storage (.int Source.IntTy.u256) none) 2 aggregate).run initial
def targetRun (i : Fin 4) := Evm.run TargetArrayWrite.code
 {target with stack:=.val ⟨i.val,Nat.lt_trans i.isLt (by decide : 4<Evm.W)⟩ :: .slot (.root 0) :: .val (Evm.wmod 83) :: target.stack}

def aggregateLive := (SourceArrayWrite.write (E:=env) (Γ:=[]) frame 0 path
 (.array .storage (.int Source.IntTy.u256) none) 1 aggregate).run initial

theorem aggregate_live : aggregateLive=(.error .timeout,initial) := by
 rfl

def ordered : Prop :=
 (boolRun 2,boolRun 3,aggregateRun,wrongLive,staticLive,aggregateLive,targetRun 2,targetRun 3,
  SourceArrayWriteControls.targetRun,sourceView state,targetView target,
  SourceArrayDeleteTarget.wordAt frame state.ex (child 2),SourceArrayDeleteTarget.wordAt frame state.ex (child 3),
  ((state.ex.world.accounts frame.this).storage.cell (child 3)).isNone) =
 ((.error (.revert (Source.panicData .index)),initial),
  (.error (.revert (Source.panicData .index)),initial),
  (.error (.revert (Source.panicData .index)),initial),
  (.error (.stuck "storage cell type"),initial),(.error (.revert []),initial),(.error .timeout,initial),
  .revert,.revert,.ok SourceArrayWriteControls.afterTarget 0,
  ([some 2,some 53,some 59,some 61,some 97],0,19,3,some 0,0,0),
  ([2,53,59,61,99],[.val (Evm.wmod 23),.slot (.root 9)],.val (Evm.wmod 31),37,41,Evm.wmod 43,Evm.wmod 47,Evm.wmod 0,Evm.wmod 53,false),
  some 61,some 0,true)

theorem observations : ordered := by
  have source2 : boolRun 2=(.error (.revert (Source.panicData .index)),initial) := (bool_certificate 2 (by decide)).1
  have source3 : boolRun 3=(.error (.revert (Source.panicData .index)),initial) := (bool_certificate 3 (by decide)).1
  have aggregate2 : aggregateRun=(.error (.revert (Source.panicData .index)),initial) := aggregate_certificate.1
  have target2 : targetRun 2=.revert := (bool_certificate 2 (by decide)).2
  have target3 : targetRun 3=.revert := (bool_certificate 3 (by decide)).2
  unfold ordered
  rw [source2,source3,aggregate2,wrong_live,static_live,aggregate_live,target2,target3,SourceArrayWriteControls.target_success]
  rfl
end Solidity.Lowering.StorageOps.SourceArrayWriteFailureControls







/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWriteFailureControls.bool_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceArrayWriteFailureControls.bool_certificate

/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWriteFailureControls.aggregate_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceArrayWriteFailureControls.aggregate_certificate

/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWriteFailureControls.wrong_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceArrayWriteFailureControls.wrong_live

/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWriteFailureControls.static_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceArrayWriteFailureControls.static_live

/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWriteFailureControls.aggregate_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceArrayWriteFailureControls.aggregate_live

/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWriteFailureControls.observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceArrayWriteFailureControls.observations
