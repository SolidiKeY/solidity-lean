import tests.«internal-flow».LoopTargetMachineFacts
namespace Solidity.Backend.InternalFlow.LoopTargetChecks
open Evm Evm.Memory LocalStoreFlow

theorem actual_endpoint : ∃ m0 base0 m1 base1,
    run (storageCode ++ before.code) machine = .ok m0 0 ∧
    run selected.code m0 = .ok m1 0 ∧
    run ((storageCode ++ before.code) ++ selected.code) machine = .ok m1 0 ∧
    StateRepr 3 1 128 before.frag caller.st base0 m0 ∧
    StateRepr 3 1 128 before.frag finalOut.st base1 m1 ∧
    LoopPrefix LoopLocalChecks.condition LoopLocalChecks.body caller.st finalOut 4 ∧
    BaseExtends caller.st.H base0 base1 ∧
    GrowsAllocator 1 128 4 caller.st base0 m0 finalOut.st base1 m1 ∧
    m1.stack = machine.stack ∧
    TEnv.thin LoopLocalChecks.protection finalOut.st.env =
      TEnv.wk finalOut.ext LoopLocalChecks.ProtectedCtx (TEnv.thin LoopLocalChecks.protection caller.st.env) ∧
    (∀ (R : RefTy) (i : Idx LoopLocalChecks.ProtectedCtx (.mem R)) (r : HRef caller.st.H R),
      TEnv.get (i.wk LoopLocalChecks.protection) caller.st.env = some r →
        m1.mem (cellOf 1 (i.wk LoopLocalChecks.protection)) = .val (base0 r.id)) ∧
    (∀ (p : PrimTy) (i : Idx LoopLocalChecks.ProtectedCtx (.val p)),
      ReprV p (TEnv.get (i.wk LoopLocalChecks.protection) caller.st.env)
        (m1.mem (cellOf 1 (i.wk LoopLocalChecks.protection)))) := by
  obtain ⟨m0,base0,hp,repr,stack,input⟩ := prefix_capacity 4 (by decide +kernel)
  have plans : ∀ {t : LTy} (i : Idx LoopLocalChecks.ProtectedCtx t),
      ProgPlan t LoopLocalChecks.body (i.wk LoopLocalChecks.protection) :=
    fun i => LoopLocalChecks.bodyPlan _ (LoopLocalChecks.protected_unwritten i)
  obtain ⟨m1,base1,amount,ht,hcost,hr,hstack,he,hg,env,pointers,values⟩ :=
    LoopLocalTarget.endpoint (C := C) (b := 1) (L := 3) (frame := 128)
      (σ := caller.st) (base := base0) (m := m0)
      cert LoopLocalChecks.protection plans .auto repr body_frame (reached_room input) finalOut source_run
  have cost := exact_loop_cost hcost
  subst amount
  have target : run selected.code m0 = .ok m1 0 := by rw [selector_code]; exact ht
  refine ⟨m0,base0,m1,base1,hp,target,?_,repr,hr,hcost,he,hg,hstack.trans stack,env,pointers,values⟩
  rw [run_append_ok hp]
  exact target

theorem represented_endpoint : ∃ base0 base1,
    run ((storageCode ++ before.code) ++ selected.code) machine = .ok finalMachine 0 ∧
    StateRepr 3 1 128 before.frag caller.st base0 prefixMachine ∧
    StateRepr 3 1 128 before.frag finalOut.st base1 finalMachine ∧
    LoopPrefix LoopLocalChecks.condition LoopLocalChecks.body caller.st finalOut 4 ∧
    BaseExtends caller.st.H base0 base1 ∧
    GrowsAllocator 1 128 4 caller.st base0 prefixMachine finalOut.st base1 finalMachine ∧
    finalMachine.stack = machine.stack ∧ finalMachine.mem 0 = w[263] ∧
    TEnv.thin LoopLocalChecks.protection finalOut.st.env =
      TEnv.wk finalOut.ext LoopLocalChecks.ProtectedCtx (TEnv.thin LoopLocalChecks.protection caller.st.env) ∧
    (∀ (R : RefTy) (i : Idx LoopLocalChecks.ProtectedCtx (.mem R)) (r : HRef caller.st.H R),
      TEnv.get (i.wk LoopLocalChecks.protection) caller.st.env = some r →
        finalMachine.mem (cellOf 1 (i.wk LoopLocalChecks.protection)) = .val (base0 r.id)) ∧
    (∀ (p : PrimTy) (i : Idx LoopLocalChecks.ProtectedCtx (.val p)),
      ReprV p (TEnv.get (i.wk LoopLocalChecks.protection) caller.st.env)
        (finalMachine.mem (cellOf 1 (i.wk LoopLocalChecks.protection)))) := by
  obtain ⟨m0,base0,m1,base1,hp,ht,whole,hr0,hr1,hcost,he,hg,hstack,env,ptrs,vals⟩ := actual_endpoint
  have same0 : m0 = prefixMachine := (Evm.Out.ok.inj (hp.symm.trans prefix_actual)).1
  subst m0
  have same1 : m1 = finalMachine := (Evm.Out.ok.inj (ht.symm.trans loop_target_actual)).1
  subst m1
  exact ⟨base0,base1,whole,hr0,hr1,hcost,he,hg,hstack,final_cursor,env,ptrs,vals⟩

theorem whole_target_actual : run ((storageCode ++ before.code) ++ selected.code) machine = .ok finalMachine 0 := by
  rw [run_append_ok prefix_actual]
  exact loop_target_actual

theorem wrong_loop_cost : ¬ LoopPrefix LoopLocalChecks.condition LoopLocalChecks.body caller.st finalOut 2 := by
  intro wrong
  have bad := exact_loop_cost wrong
  cases bad

/-- A single composed proof keeps the SAME actual bases for prefix growth3
and loop growth4; no representation/base-map midpoint is supplied. -/
theorem complete_endpoint : ∃ base0 base1,
    run ((storageCode ++ before.code) ++ selected.code) machine = .ok finalMachine 0 ∧
    StateRepr 3 1 128 before.frag caller.st base0 prefixMachine ∧
    StateRepr 3 1 128 before.frag finalOut.st base1 finalMachine ∧
    AllocationInput 1 128 4 caller.st base0 prefixMachine ∧
    LoopRoom 1 128 LoopLocalChecks.condition LoopLocalChecks.body caller.st base0 prefixMachine ∧
    LoopPrefix LoopLocalChecks.condition LoopLocalChecks.body caller.st finalOut 4 ∧
    BaseExtends caller.st.H base0 base1 ∧
    GrowsAllocator 1 128 4 caller.st base0 prefixMachine finalOut.st base1 finalMachine ∧
    GrowsAllocator 1 128 7 initial bases machine finalOut.st base1 finalMachine ∧
    finalMachine.stack = machine.stack ∧ finalMachine.mem 0 = w[263] ∧
    TEnv.thin LoopLocalChecks.protection finalOut.st.env =
      TEnv.wk finalOut.ext LoopLocalChecks.ProtectedCtx (TEnv.thin LoopLocalChecks.protection caller.st.env) := by
  obtain ⟨m0,hs,repr0,alloc0,stack0⟩ := storage_reached
  have capacity : AllocationInput 1 128 (before.cost stored.st + 4) stored.st bases m0 :=
    .inr ⟨by decide,wmod 256,alloc0,by rw [before_cost]; decide +kernel⟩
  obtain ⟨m1,base0,hp,repr1,stack1,he0,hg0⟩ := PublishedDirectCalls.program_endpoint
    (C := C) (b := 1) (L := 3) (frame := 128) (σ := stored.st) (base := bases) (m := m0)
    before repr0 before_frame (capacity.of_le (Nat.le_add_right _ _)) caller actual_memory
  have combined : run (storageCode ++ before.code) machine = .ok m1 0 := by
    rw [run_append_ok hs]
    exact hp
  have same1 : m1 = prefixMachine := (Evm.Out.ok.inj (combined.symm.trans prefix_actual)).1
  subst m1
  have input : AllocationInput 1 128 4 caller.st base0 prefixMachine := hg0.nextInput capacity
  have room := reached_room input
  have plans : ∀ {t : LTy} (i : Idx LoopLocalChecks.ProtectedCtx t),
      ProgPlan t LoopLocalChecks.body (i.wk LoopLocalChecks.protection) :=
    fun i => LoopLocalChecks.bodyPlan _ (LoopLocalChecks.protected_unwritten i)
  obtain ⟨m2,base1,amount,ht,hcost,repr2,stack2,he1,hg1,env,ptrs,vals⟩ :=
    LoopLocalTarget.endpoint (C := C) (b := 1) (L := 3) (frame := 128)
      (σ := caller.st) (base := base0) (m := prefixMachine)
      cert LoopLocalChecks.protection plans .auto repr1 body_frame room finalOut source_run
  have exactCost := exact_loop_cost hcost
  subst amount
  have target : run selected.code prefixMachine = .ok m2 0 := by rw [selector_code]; exact ht
  have same2 : m2 = finalMachine := (Evm.Out.ok.inj (target.symm.trans loop_target_actual)).1
  subst m2
  have zero : GrowsAllocator 1 128 0 initial bases machine stored.st bases m0 :=
    LoopLocalTarget.storage_grows (P := storagePrefix) (by decide +kernel) (by decide +kernel) actual_storage hs
  have firstGrowth : GrowsAllocator 1 128 3 initial bases machine caller.st base0 prefixMachine := by
    have growth := zero.comp hg0
    simpa only [before_cost,Nat.zero_add] using growth
  have total : GrowsAllocator 1 128 7 initial bases machine finalOut.st base1 finalMachine := firstGrowth.comp hg1
  exact ⟨base0,base1,whole_target_actual,repr1,repr2,input,room,hcost,he1,hg1,total,
    stack2.trans (stack1.trans stack0),final_cursor,env⟩

theorem compiler_input_agrees : ∃ base,
    checked.Input 3 128 base caller.st prefixMachine ∧ checked.Agrees 3 128 base caller.st prefixMachine := by
  obtain ⟨base0,base1,whole,repr0,repr1,input,room,rest⟩ := complete_endpoint
  have actualInput : checked.Input 3 128 base0 caller.st prefixMachine := by
    apply (checked.memoryLoops_input (by unfold checked; rfl) 3 128 base0 caller.st prefixMachine).mpr
    refine ⟨repr0,?_,?_⟩
    · rw [checked_result,program_need]; decide +kernel
    · rw [checked_result]; exact program_room room
  exact ⟨base0,actualInput,checked.correct actualInput⟩
end Solidity.Backend.InternalFlow.LoopTargetChecks

#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.actual_endpoint
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.represented_endpoint
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.whole_target_actual
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.wrong_loop_cost
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.complete_endpoint
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.compiler_input_agrees
