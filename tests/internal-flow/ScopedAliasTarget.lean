import tests.«internal-flow».ScopedAliasFacts
namespace Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias
open Evm Evm.Memory
theorem actual_endpoint : ∃ (m₀ : Machine) (base₀ : Nat → Fin W)
    (m₁ : Machine) (base₁ : Nat → Fin W) (m₂ : Machine) (base₂ : Nat → Fin W),
    Evm.run prefixCode machine = .ok m₀ 0 ∧ Evm.run producer.code m₀ = .ok m₁ 0 ∧
    Evm.run cert.code m₁ = .ok m₂ 0 ∧
    StateRepr 3 1 128 prefixProducer.frag caller.st base₀ m₀ ∧
    StateRepr 3 1 128 producer.frag final.st base₁ m₁ ∧
    StateRepr 3 1 128 stmt.frag reached.st base₂ m₂ ∧ m₂.stack = machine.stack ∧
    BaseExtends final.st.H base₁ base₂ ∧
    GrowsAllocator 1 128 2 final.st base₁ m₁ reached.st base₂ m₂ ∧
    AllocationInput 1 128 2 final.st base₁ m₁ ∧
    checked.Input 3 128 base₁ final.st m₁ ∧ checked.Agrees 3 128 base₁ final.st m₁ ∧
    (∀ (R : RefTy) (i : Idx ProtectedCtx (.mem R)) (r : HRef final.st.H R),
      TEnv.get (i.wk protection) final.st.env = some r →
        m₂.mem (cellOf 1 (i.wk protection)) = .val (base₁ r.id)) ∧
    (∀ (p : PrimTy) (i : Idx ProtectedCtx (.val p)),
      ReprV p (TEnv.get (i.wk protection) final.st.env) (m₂.mem (cellOf 1 (i.wk protection)))) := by
  obtain ⟨m₀,base₀,hprefix,repr₀,stack₀,space⟩ :=
    prefix_endpoint (producer.cost caller.st + stmt.cost final.st) total_room
  have beforeRoom : 1 + producer.need ≤ 128 := by rw [old_need]; decide +kernel
  have afterRoom : 1 + stmt.need ≤ 128 := by change 1 + cert.need ≤ 128; rw [need]; decide +kernel
  have cap5 : AllocationInput 1 128 5 caller.st base₀ m₀ := by
    simpa only [old_cost,stmt_cost] using space
  have beforeCapacity : AllocationInput 1 128 (producer.cost caller.st) caller.st base₀ m₀ := by
    apply cap5.of_le
    rw [old_cost]
    decide +kernel
  obtain ⟨m₁,base₁,hbefore,repr₁,stack₁,extend₁,grow₁⟩ := PublishedDirectCalls.program_endpoint
    (C := C) (b := 1) (L := 3) (frame := 128) (σ := caller.st) (base := base₀) (m := m₀)
    producer repr₀ beforeRoom beforeCapacity previous previous_run
  have growth3 : GrowsAllocator 1 128 3 caller.st base₀ m₀ final.st base₁ m₁ := by
    simpa only [old_cost] using grow₁
  have capacity2 : AllocationInput 1 128 2 final.st base₁ m₁ :=
    growth3.nextInput (tail := 2) cap5
  have input₂ : AllocationInput 1 128 (stmt.cost final.st) final.st base₁ m₁ := by
    rw [stmt_cost]
    exact capacity2
  obtain ⟨m₂,base₂,hafter,repr₂,stack₂,extend₂,grow₂⟩ := PublishedDirectCalls.statement_endpoint
    (C := C) (b := 1) (L := 3) (frame := 128) (σ := final.st) (base := base₁) (m := m₁)
    stmt repr₁ afterRoom input₂ reached stmt_run
  have input : checked.Input 3 128 base₁ final.st m₁ := by
    apply (checked.memoryCalls_input (by unfold checked; rfl) 3 128 base₁ final.st m₁).mpr
    refine ⟨repr₁,?_,?_⟩
    · rw [checked_need]; exact afterRoom
    · rw [checked_cost]; exact input₂
  have growth : GrowsAllocator 1 128 2 final.st base₁ m₁ reached.st base₂ m₂ := by
    simpa only [stmt_cost] using grow₂
  have capacity : AllocationInput 1 128 2 final.st base₁ m₁ := by
    simpa only [stmt_cost] using input₂
  refine ⟨m₀,base₀,m₁,base₁,m₂,base₂,hprefix,hbefore,hafter,repr₀,repr₁,repr₂,
    stack₂.trans (stack₁.trans stack₀),extend₂,growth,capacity,input,checked.correct input,?_,?_⟩
  · exact CallerView.represented (σ := final.st) reached protection captured_locals repr₂ extend₂
  · intro p i
    exact CallerView.represented_value_drop (σ := final.st) reached Ext.refl protection captured_locals repr₂ i
/-- Protecting the actually assigned same-typed scalar is rejected by the exact leaf guard. -/
theorem written_scalar_guard :
    ¬ ((LTy.val .uint,5) ∉ [(LTy.val .uint,5)]) := by decide +kernel

theorem wrong_old_contents : contents reached.st ≠
    some [[2,7,84],[1,23],[2,99,101],[1,55]] := by
  rw [complete_source.2.1]
  decide +kernel

theorem wrong_new_alias : aliases reached.st ≠ [some 3,some 0,some 0] := by
  rw [complete_source.2.2.2.1]
  decide +kernel

theorem private_marker_nonescape : scalars reached.st ≠ [77,1] := by
  rw [complete_source.2.2.1]
  decide +kernel

theorem wrong_persistent_value : storageValues reached.st ≠
    some [11,13,21,23,2,11,13,84,23,9] := by
  rw [complete_source.1]
  decide +kernel

/-- A genuinely skipped allocating body takes the original bare-revert default. -/
def skipped : Stmt C Final Final :=
  .ite (.simple (.bool false)) body (.cons .revert .nil)
theorem skipped_reverts : skipped.run final.st = .error .revert := by rfl

end Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias

#print axioms Solidity.Backend.InternalFlow.LocalStoreFlow.StmtPlan.sound
#print axioms Solidity.Backend.InternalFlow.LocalStoreFlow.ProgPlan.sound
#print axioms Solidity.Backend.InternalFlow.LocalStoreFlow.ProgPlan.plain_slot
#print axioms Solidity.Backend.InternalFlow.LocalStoreFlow.ProgPlan.fragile_slot
#print axioms Solidity.Backend.InternalFlow.LocalStoreFlow.program_statement_frames
#print axioms Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.source_run
#print axioms Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.alias_frame
#print axioms Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.selected_guard
#print axioms Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.complete_source
#print axioms Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.protected_unwritten
#print axioms Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.captured_locals
#print axioms Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.original_guard_rejects
#print axioms Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.actual_endpoint
#print axioms Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.written_scalar_guard
#print axioms Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.wrong_old_contents
#print axioms Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.wrong_new_alias
#print axioms Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.private_marker_nonescape
#print axioms Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.wrong_persistent_value
#print axioms Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.skipped_reverts
