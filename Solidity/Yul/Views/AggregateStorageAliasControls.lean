import Solidity.Yul.Views.AggregateStorageControls

namespace Solidity.Yul.Views.Controls

/-- Two real aliases to the same inner array; no re-formation through the
outer index occurs when the retained reference is subsequently read. -/
def agAliasTy : Source.STy := .array .storage (.int rcU16) none
def agAliases : Source.EMState agEnv [agAliasTy,agAliasTy] :=
  ⟨.cons (.storRef (by rfl) (agInner 0)) (.cons (.storRef (by rfl) (agInner 0)) .nil),agApplied.2.2⟩

def agShrink := (Source.writeLen (E := agEnv) packedStepFrame agPath 0).run agAliases

theorem ag_shrink_source_success : agShrink.1=.ok () := rfl

theorem ag_shrink_outer_zero : (Source.readLen (E := agEnv) packedStepFrame agPath).run agShrink.2 =
    (.ok 0,agShrink.2) := rfl

theorem ag_retained_inner_length : (Source.readLen (E := agEnv) packedStepFrame (agInner 0)).run agShrink.2 =
    (.ok 2,agShrink.2) := rfl

theorem ag_two_aliases_retained : agShrink.2.1.get .here = Source.Val.storRef (by rfl) (agInner 0) ∧
    agShrink.2.1.get (.there .here) = Source.Val.storRef (by rfl) (agInner 0) := ⟨rfl,rfl⟩

/-- Concrete discriminator: a live-only collector drops dormant child headers.
It therefore must NOT be claimed to implement all alias-visible ownership
changes. Current-local scanning also misses aliases held by suspended callers. -/
def agDormantRaw := saveSlot (saveSlot agRaw 0 0) 101 3

theorem ag_dormant_collect_ready : (agDeclaration.collect agFixed agPath account (aggregateRawLengths agDormantRaw) 0).isSome := by decide

def agDormantComputed := (agDeclaration.collect agFixed agPath account (aggregateRawLengths agDormantRaw) 0).get ag_dormant_collect_ready

theorem ag_dormant_paths : agDormantComputed.1.map ScalarPath.path = [agPath] := rfl

theorem ag_dormant_changed_raw_header : agDormantRaw 101=3 := rfl

theorem ag_dormant_alias_disagrees : ((Source.readLen (E := agEnv) packedStepFrame (agInner 0)).run agShrink.2).1 = .ok 2 := rfl

theorem ag_static_exact : ∀ result,
    aggregateApplySnapshot? {packedStepFrame with static:=true} agDeclaration agFixed agPath 0 agRaw agState = some result →
    result=(.error (.revert []),agState) := fun result step =>
  aggregateApply_static _ _ _ _ _ _ _ result step rfl

/-- Nonwrapping is a checked preparation boundary, not a new language rule. -/
theorem ag_overflow_elements : (collectAggregateElements (agElement.collect agFixed) agFixed agPath account
    (aggregateRawLengths agRaw) (2^256-1) agElement.stride 0 1).isNone=true := by decide

theorem ag_zero_stride : collectAggregateElements (agElement.collect agFixed) agFixed agPath account
    (aggregateRawLengths agRaw) 100 0 0 1=none := rfl

/-- The inhabited OLD live inventory is derived from actual readLen calls in
one concrete source state, not manually supplied lengths. General nested
source/raw traversal equality and retained-alias closure remain open. -/
theorem ag_actual_source_inventory : agDeclaration.collect agFixed agPath account
    (aggregateSourceLengths packedStepFrame agApplied.2) 0 = some agComputed := rfl

theorem ag_alias_MemOK : Source.MemOK agEnv agState.2.heap.ty agAliases := by
  have h := ag_every_H _ ag_initial_MemOK
  exact ⟨⟨h.1.1,⟨rfl,rfl,trivial⟩⟩,h.2⟩

end Solidity.Yul.Views.Controls
