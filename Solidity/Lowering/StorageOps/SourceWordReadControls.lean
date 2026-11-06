import Solidity.Lowering.StorageOps.SourceWordRead
import Solidity.Lowering.StorageOps.SourceWordWriteControls

/-! Populated independent Source/SLOAD reads, readonly/static context retention,
transient separation, missing/type refusals and wrong-address controls. -/
namespace Solidity.Lowering.StorageOps.SourceWordReadControls
open Solidity.Backend.StorageOps
open SourceWordWriteControls

def source := (Source.readAt (E:=env) (Γ:=[]) frame left (env.cellTy left)).run initial
def readonly := (Source.readAt (E:=env) (Γ:=[]) {frame with static:=true} left (env.cellTy left)).run initial
def scratchRead := (Source.readAt (E:=env) (Γ:=[]) frame scratch (env.cellTy scratch)).run initial
def missingRead := (Source.readAt (E:=env) (Γ:=[]) frame missing (env.cellTy missing)).run initial
def wrongType := (Source.readAt (E:=env) (Γ:=[]) frame left .bool).run initial
def target := Evm.run (TargetOperations.readCode (.root 0)) machine
def wrongAddress := Evm.run (TargetOperations.readCode (.root 1)) machine
def malformed := Evm.run [.sload] machine
def ordered : Prop :=
 (source,readonly,scratchRead,missingRead,wrongType,target,wrongAddress,malformed,
  sourceView source.2.2,sourceView readonly.2.2,
  targetView {machine with stack:=.val (Evm.wmod 11)::machine.stack},
  targetView {machine with stack:=.val (Evm.wmod 17)::machine.stack}) =
 ((.ok (.int 11 (by decide)),initial),(.ok (.int 11 (by decide)),initial),
  (.ok (.int 41 (by decide)),initial),
  (.error (.stuck "storage cell without a value"),initial),
  (.error (.stuck "storage cell type"),initial),
  .ok {machine with stack:=.val (Evm.wmod 11)::machine.stack} 0,
  .ok {machine with stack:=.val (Evm.wmod 17)::machine.stack} 0,.fault,
  ([some 11,some 17,some 41,none],0,19,3,some 0,0,0),
  ([some 11,some 17,some 41,none],0,19,3,some 0,0,0),
  ([11,17,99,0],[.val (Evm.wmod 11),.val (Evm.wmod 23),.slot (.root 9)],
   .val (Evm.wmod 31),37,41,Evm.wmod 43,Evm.wmod 47,Evm.wmod 0,Evm.wmod 53,false),
  ([11,17,99,0],[.val (Evm.wmod 17),.val (Evm.wmod 23),.slot (.root 9)],
   .val (Evm.wmod 31),37,41,Evm.wmod 43,Evm.wmod 47,Evm.wmod 0,Evm.wmod 53,false))

theorem observations : ordered := by rfl

/-- An inhabited client discharges the raw input premises by actual computation. -/
def certificate := SourceWordRead.complete env [] frame left .nil state rfl
  (.int 11 (by decide)) rfl machine (.root 0) rfl

/-- info: 'Solidity.Lowering.StorageOps.SourceWordReadControls.observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms observations
/-- info: 'Solidity.Lowering.StorageOps.SourceWordReadControls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate
end Solidity.Lowering.StorageOps.SourceWordReadControls
