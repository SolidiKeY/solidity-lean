import Solidity.Yul.Views.AggregateStorageSource
import Solidity.Yul.Views.RecursiveDynamicMetadata
import Solidity.Yul.Views.PackedResidualBoundaryControls

namespace Solidity.Yul.Views.Controls

def agName (s : String) : Source.DeclName := ⟨some "AG",s⟩
def agNode : Source.DeclName := ⟨none,"NodeAG"⟩
def agEnv : Source.Env := ⟨[
  ⟨.contract,"AG",none,true,.contract false "AG" .none .nil .nil⟩,
  ⟨.struct,"NodeAG",none,true,.struct "NodeAG" (.structMember (.elem (.int false 16 (by decide))) "stamp")
    (.cons (.structMember (.array (.elem (.int false 16 (by decide))) .none) "xs") .nil)⟩,
  ⟨.stateVar,"nodes",some "AG",false,.stateVar (.array (.userType ⟨"NodeAG",[]⟩) .none) none none none false "nodes" .none⟩]⟩
def agFields : List (String × Source.STy) := [("stamp",.int rcU16),("xs",.array .storage (.int rcU16) none)]
def agChild : RecursiveStorageDeclaration agEnv (.struct .storage agNode) true :=
  .strct agNode agFields rfl (.cons (.leaf (.fixed (.scalar (.int rcU16) rfl)))
    (.cons (.leaf (.packedUnsignedArray rcU16 rfl (by decide))) .nil))
def agElement := AggregateStorageDeclaration.ordinary agChild
def agDeclaration := AggregateStorageDeclaration.array agElement (by rfl)
def agPath : Source.SPath := ⟨agName "nodes",[]⟩
def agInner (i : Nat) : Source.SPath := agPath.go (.index i) |>.go (.field 1)
def agFixed : Roadmap.Evm.Fixed where
  keccak b := if b=layoutPreimageBytes (.data 0) then 100 else if b=layoutPreimageBytes (.data 101) then 1000 else 2000
  keccak_lt _ := by split; decide; split <;> decide
  precompile _ _ := none
  precompileGas _ _ := 0

def agRaw : SlotView := fun q => if q=0 then 2 else if q=101 then 2 else if q=103 then 1 else
  if q=100 then ⟨12+2^240,by decide⟩ else if q=102 then ⟨13+2^240,by decide⟩ else
  if q=1000 then ⟨77+88*65536+2^240,by decide⟩ else if q=2000 then ⟨99+2^240,by decide⟩ else 999

theorem ag_stride : agElement.stride=2 := rfl
theorem ag_header_only : agDeclaration.paths agPath = [agPath] := rfl
theorem ag_nested_array_stride : (AggregateStorageDeclaration.array agDeclaration (by rfl)).stride=1 :=
  aggregate_array_stride _ _
theorem ag_collect_ready : (agDeclaration.collect agFixed agPath account (aggregateRawLengths agRaw) 0).isSome := by decide

def agComputed := (agDeclaration.collect agFixed agPath account (aggregateRawLengths agRaw) 0).get ag_collect_ready
theorem ag_coordinates : agComputed.1.map (fun c => (c.path.steps,c.slot.val,c.field.offset,c.field.width)) =
  [([],0,0,32),([.index 0,.field 0],100,0,2),([.index 0,.field 1],101,0,32),
   ([.index 0,.field 1,.index 0],1000,0,2),([.index 0,.field 1,.index 1],1000,2,2),
   ([.index 1,.field 0],102,0,2),([.index 1,.field 1],103,0,32),([.index 1,.field 1,.index 0],2000,0,2)] := rfl

theorem ag_stop : agComputed.2=32 := rfl
theorem ag_separated : packedSeparationCheck agComputed.1=true := by decide

def agState : Source.EMState agEnv [] :=
  ⟨.nil,⟨⟨⟨fun _ => Source.Account.empty (D := agEnv.layout) (agEnv.lay account)⟩,.empty,[]⟩,.empty,[],[],⟨[],.nil⟩⟩⟩
theorem ag_initial_MemOK : Source.MemOK agEnv agState.2.heap.ty agState :=
  ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
theorem ag_apply_ready : (aggregateApplySnapshot? packedStepFrame agDeclaration agFixed agPath 0 agRaw agState).isSome := by decide
def agApplied := (aggregateApplySnapshot? packedStepFrame agDeclaration agFixed agPath 0 agRaw agState).get ag_apply_ready
theorem ag_success : agApplied.1=.ok () := rfl
theorem ag_step : aggregateApplySnapshot? packedStepFrame agDeclaration agFixed agPath 0 agRaw agState = some (.ok (),agApplied.2) :=
  (Option.get_mem ag_apply_ready).trans (congrArg some (Prod.ext ag_success rfl))
theorem ag_every_H (H : Source.HeapTy) (ok : Source.MemOK agEnv H agState) : Source.MemOK agEnv H agApplied.2 :=
  aggregateApply_MemOK packedStepFrame agDeclaration agFixed agPath 0 agRaw agState agApplied (Option.get_mem ag_apply_ready) H ok

theorem ag_view : finiteView agComputed.1 (agApplied.2.2.ex.world.accounts account).storage agRaw :=
  aggregateApply_view packedStepFrame agDeclaration agFixed agPath 0 agRaw agState agApplied.2 _ _
    (Option.get_mem ag_collect_ready) ag_step rfl

theorem ag_whole_map : finiteEncode agComputed.1 (agApplied.2.2.ex.world.accounts account).storage
    (packedMask agComputed.1 agRaw) = some agRaw :=
  finiteEncode_fromComplement _ _ _ ((packedSeparationCheck_iff _).mp ag_separated) ag_view

theorem ag_unchanged_store : aggregateSnapshotWriteback agDeclaration agFixed agPath account 0 agRaw
    (agApplied.2.2.ex.world.accounts account).storage =
      some ((agApplied.2.2.ex.world.accounts account).storage,packedMask agComputed.1 agRaw) :=
  aggregateSnapshot_unchanged agDeclaration agFixed agPath account 0 agRaw _ _ _
    (Option.get_mem ag_collect_ready) ag_separated ag_view

theorem ag_wrong_root : agDeclaration.collect agFixed ⟨agName "missing",[]⟩ account (aggregateRawLengths agRaw) 0=none := rfl

theorem ag_wrong_type : agElement.collect agFixed agPath account (aggregateRawLengths agRaw) 0=none := rfl

end Solidity.Yul.Views.Controls
