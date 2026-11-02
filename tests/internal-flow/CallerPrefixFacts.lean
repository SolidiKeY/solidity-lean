import tests.«internal-flow».LoopTargetControls
import Solidity.Backend.InternalFlow.LoopCallerPrefix
namespace Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes
open Evm Evm.Memory LocalStoreFlow

theorem first_scoped : scopedLoopBody LoopLocalChecks.body start = .ok first := by
  unfold scopedLoopBody
  change (LoopLocalChecks.body.runR caller.st).map _ = _
  rw [first_run]
  rfl

theorem second_scoped : scopedLoopBody LoopLocalChecks.body first = .ok finalOut := by
  unfold scopedLoopBody
  rw [second_run]
  rfl

theorem source_one : TLoop.iterN (scopedLoopBody LoopLocalChecks.body)
    (fun o => LoopLocalChecks.condition.evalT o.st) 1 start = .inl first := by
  simp only [TLoop.iterN,TLoop.step,conditions.1,first_scoped]

theorem source_two : TLoop.iterN (scopedLoopBody LoopLocalChecks.body)
    (fun o => LoopLocalChecks.condition.evalT o.st) 2 start = .inl finalOut := by
  simp only [TLoop.iterN,TLoop.step,conditions.1,first_scoped,conditions.2.1,second_scoped]

theorem source_stopped (n : Nat) (hn : 3 ≤ n) :
    TLoop.iterN (scopedLoopBody LoopLocalChecks.body)
      (fun o => LoopLocalChecks.condition.evalT o.st) n start = .inr (.ok finalOut) :=
  TLoop.iterN_done_le hn source_horizon

theorem source_captured (n : Nat) (out : Solidity.Out C caller.st.H Caller)
    (actual : TLoop.iterN (scopedLoopBody LoopLocalChecks.body)
      (fun o => LoopLocalChecks.condition.evalT o.st) n start = .inl out ∨
      TLoop.iterN (scopedLoopBody LoopLocalChecks.body)
      (fun o => LoopLocalChecks.condition.evalT o.st) n start = .inr (.ok out)) :
    TEnv.thin LoopLocalChecks.protection out.st.env =
      TEnv.wk out.ext LoopLocalChecks.ProtectedCtx (TEnv.thin LoopLocalChecks.protection caller.st.env) :=
  LoopCallerPrefix.captured LoopLocalChecks.protection
    (fun i => LoopLocalChecks.bodyPlan _ (LoopLocalChecks.protected_unwritten i))
    LoopLocalChecks.condition caller.st n out actual

/-- Actual public body compilation, without a loop-prefix simulation premise. -/
def bodyProgram : Calls.Program 1 before.frag LoopLocalChecks.body := Calls.plain bodyCompiled

theorem body_cost (s : State C Caller) : bodyProgram.cost s = allocationCostProg LoopLocalChecks.body s := rfl
theorem body_code : bodyProgram.code = bodyCompiled.code := rfl
theorem body_need : bodyProgram.need = frameNeedProg LoopLocalChecks.body := rfl
theorem body_frag : bodyProgram.frag = bodyCompiled.frag := rfl

/-- The first reached representation is obtained by executing the actual body,
then matched to C39's checked target horizon. No midpoint is supplied. -/
theorem first_reached : ∃ base0 base1,
    StateRepr 3 1 128 before.frag caller.st base0 prefixMachine ∧
    AllocationInput 1 128 4 caller.st base0 prefixMachine ∧
    StateRepr 3 1 128 before.frag first.st base1 firstMachine ∧
    BaseExtends caller.st.H base0 base1 ∧
    GrowsAllocator 1 128 2 caller.st base0 prefixMachine first.st base1 firstMachine ∧
    firstMachine.stack = prefixMachine.stack := by
  obtain ⟨base0,baseF,whole,repr0,reprF,input,rest⟩ := complete_endpoint
  have cap : AllocationInput 1 128 (bodyProgram.cost caller.st) caller.st base0 prefixMachine := by
    rw [body_cost,show allocationCostProg LoopLocalChecks.body caller.st = 2 from congrArg Prod.fst allocation_costs]
    exact input.of_le (by decide)
  obtain ⟨m1,base1,ht,hr,hstack,he,hg⟩ := PublishedDirectCalls.program_endpoint
    bodyProgram repr0 (by rw [body_need]; exact body_frame) cap firstBody first_run
  have hc := LoopCallerPrefix.condition_run conditionCompiled.cert repr0 true conditions.1
  have turn : loopTurn (fun m => exec conditionCompiled.code 0 m)
      (fun m => exec bodyCompiled.code 0 m) prefixMachine = .inl m1 := by
    change exec conditionCompiled.code 0 prefixMachine = _ at hc
    rw [body_code] at ht
    change exec bodyCompiled.code 0 prefixMachine = _ at ht
    simp only [loopTurn,hc,Machine.push,bword]
    rw [ht]
    rfl
  have same : m1 = firstMachine := by
    have checked := first_target_horizon
    simp only [loopIterN,turn] at checked
    exact Sum.inl.inj checked
  subst m1
  have dropped := hr.drop LoopLocalChecks.body.ext
  rw [body_frag,body_stable] at dropped
  refine ⟨base0,base1,repr0,input,dropped,he,?_,hstack⟩
  simpa only [body_cost,show allocationCostProg LoopLocalChecks.body caller.st = 2 from congrArg Prod.fst allocation_costs] using hg

/-- Second-turn capacity is transferred by actual first-turn allocator growth. -/
theorem second_reached : ∃ base0 base1 base2,
    StateRepr 3 1 128 before.frag caller.st base0 prefixMachine ∧
    StateRepr 3 1 128 before.frag first.st base1 firstMachine ∧
    StateRepr 3 1 128 before.frag finalOut.st base2 finalMachine ∧
    AllocationInput 1 128 2 first.st base1 firstMachine ∧
    BaseExtends caller.st.H base0 base1 ∧ BaseExtends caller.st.H base0 base2 ∧
    GrowsAllocator 1 128 2 caller.st base0 prefixMachine first.st base1 firstMachine ∧
    GrowsAllocator 1 128 4 caller.st base0 prefixMachine finalOut.st base2 finalMachine ∧
    firstMachine.stack = prefixMachine.stack ∧ finalMachine.stack = prefixMachine.stack ∧
    loopIterN (fun m => exec conditionCompiled.code 0 m)
      (fun m => exec bodyCompiled.code 0 m) 2 prefixMachine = .inl finalMachine := by
  obtain ⟨base0,base1,repr0,input,repr1,he1,hg1,stack1⟩ := first_reached
  have next : AllocationInput 1 128 2 first.st base1 firstMachine := hg1.nextInput input
  have cap : AllocationInput 1 128 (bodyProgram.cost first.st) first.st base1 firstMachine := by
    rw [body_cost,show allocationCostProg LoopLocalChecks.body first.st = 2 from congrArg Prod.snd allocation_costs]
    exact next
  obtain ⟨m2,base2,ht,hr,stack2,he2,hg2⟩ := PublishedDirectCalls.program_endpoint
    bodyProgram repr1 (by rw [body_need]; exact body_frame) cap secondBody second_run
  have repr2 : StateRepr 3 1 128 before.frag finalOut.st base2 m2 := by
    have dropped := hr.drop LoopLocalChecks.body.ext
    rw [body_frag,body_stable] at dropped
    exact dropped
  have hc1 := LoopCallerPrefix.condition_run conditionCompiled.cert repr1 true conditions.2.1
  have turn1 : loopTurn (fun m => exec conditionCompiled.code 0 m)
      (fun m => exec bodyCompiled.code 0 m) firstMachine = .inl m2 := by
    change exec conditionCompiled.code 0 firstMachine = _ at hc1
    rw [body_code] at ht
    change exec bodyCompiled.code 0 firstMachine = _ at ht
    simp only [loopTurn,hc1,Machine.push,bword]
    rw [ht]
    rfl
  have turn0 : loopTurn (fun m => exec conditionCompiled.code 0 m)
      (fun m => exec bodyCompiled.code 0 m) prefixMachine = .inl firstMachine := by
    have h := first_target_horizon
    cases hturn : loopTurn (fun m => exec conditionCompiled.code 0 m)
      (fun m => exec bodyCompiled.code 0 m) prefixMachine with
    | inl m =>
      simp only [loopIterN,hturn] at h
      exact congrArg Sum.inl (Sum.inl.inj h)
    | inr r => simp only [loopIterN,hturn] at h; contradiction
  have two : loopIterN (fun m => exec conditionCompiled.code 0 m)
      (fun m => exec bodyCompiled.code 0 m) 2 prefixMachine = .inl m2 := by
    simp only [loopIterN,turn0,turn1]
  have hc2 := LoopCallerPrefix.condition_run conditionCompiled.cert repr2 false conditions.2.2
  have stop : loopTurn (fun m => exec conditionCompiled.code 0 m)
      (fun m => exec bodyCompiled.code 0 m) m2 = .inr (.ok m2 0) := by
    change exec conditionCompiled.code 0 m2 = _ at hc2
    simp only [loopTurn,hc2,Machine.push,bword]
    rfl
  have three : loopIterN (fun m => exec conditionCompiled.code 0 m)
      (fun m => exec bodyCompiled.code 0 m) 3 prefixMachine = .inr (.ok m2 0) := by
    simp only [loopIterN,turn0,turn1,stop]
  have same : m2 = finalMachine := (Evm.Out.ok.inj (Sum.inr.inj (three.symm.trans final_target_horizon))).1
  subst m2
  have grow2 : GrowsAllocator 1 128 2 first.st base1 firstMachine finalOut.st base2 finalMachine := by
    simpa only [body_cost,show allocationCostProg LoopLocalChecks.body first.st = 2 from congrArg Prod.snd allocation_costs] using hg2
  exact ⟨base0,base1,base2,repr0,repr1,repr2,next,he1,he1.trans first.ext he2,hg1,
    hg1.comp grow2,stack1,stack2.trans stack1,two⟩

/-- Every horizon uses the SAME concrete mixed body and checked target codes.
Two turns have run at horizon2, but the false condition completes at horizon3.
All later horizons are genuinely stopped, not a depth admission cutoff. -/
theorem reached_all : ∃ base0, ∀ n : Nat, ∃ (out : Solidity.Out C caller.st.H Caller)
    (m : Evm.Machine) (base' : Nat → Fin W) (amount : Nat),
    TLoop.iterN (scopedLoopBody LoopLocalChecks.body)
      (fun o => LoopLocalChecks.condition.evalT o.st) n start =
      (if n < 3 then .inl out else .inr (.ok out)) ∧
    loopIterN (fun m => exec conditionCompiled.code 0 m)
      (fun m => exec bodyCompiled.code 0 m) n prefixMachine =
      (if n < 3 then .inl m else .inr (.ok m 0)) ∧
    LoopPrefix LoopLocalChecks.condition LoopLocalChecks.body caller.st out amount ∧
    StateRepr 3 1 128 before.frag out.st base' m ∧
    BaseExtends caller.st.H base0 base' ∧
    GrowsAllocator 1 128 amount caller.st base0 prefixMachine out.st base' m ∧
    m.stack = prefixMachine.stack ∧ amount = (if n = 0 then 0 else if n = 1 then 2 else 4) := by
  obtain ⟨base0,base1,base2,repr0,repr1,repr2,input,he1,he2,hg1,hg2,st1,st2,two⟩ := second_reached
  have pref1 : LoopPrefix LoopLocalChecks.condition LoopLocalChecks.body caller.st first 2 := by
    have hp := LoopPrefix.next (LoopPrefix.start (c := LoopLocalChecks.condition)
      (body := LoopLocalChecks.body) (σ := caller.st)) conditions.1 first_run
    simpa only [show allocationCostProg LoopLocalChecks.body caller.st = 2 from congrArg Prod.fst allocation_costs,
      Nat.zero_add] using hp
  have pref2 : LoopPrefix LoopLocalChecks.condition LoopLocalChecks.body caller.st finalOut 4 := by
    have hp := LoopPrefix.next pref1 conditions.2.1 second_run
    simpa only [show allocationCostProg LoopLocalChecks.body first.st = 2 from congrArg Prod.snd allocation_costs] using hp
  have zero : GrowsAllocator 1 128 0 caller.st base0 prefixMachine start.st base0 prefixMachine := by
    intro cursor hb ha hs
    exact ha
  refine ⟨base0,fun n => ?_⟩
  cases n with
  | zero => exact ⟨start,prefixMachine,base0,0,rfl,rfl,.start,repr0,BaseExtends.refl base0,zero,rfl,rfl⟩
  | succ n =>
    cases n with
    | zero => exact ⟨first,firstMachine,base1,2,source_one,first_target_horizon,pref1,repr1,he1,hg1,st1,rfl⟩
    | succ n =>
      cases n with
      | zero => exact ⟨finalOut,finalMachine,base2,4,source_two,two,pref2,repr2,he2,hg2,st2,rfl⟩
      | succ n =>
        refine ⟨finalOut,finalMachine,base2,4,?_,?_,pref2,repr2,he2,hg2,st2,?_⟩
        · rw [if_neg (by omega)]
          exact source_stopped _ (by omega)
        · rw [if_neg (by omega)]
          exact loopIterN_done_le (by omega) final_target_horizon
        · rw [if_neg (by omega),if_neg (by omega)]

/-- Caller-local identity/value observations from the SAME actual reached
source and target states, even while the old array contents are mutating. -/
theorem protected_all : ∃ (base0 : Nat → Fin W), ∀ n : Nat, ∃ (out : Solidity.Out C caller.st.H Caller)
    (m : Evm.Machine) (base' : Nat → Fin W),
    TLoop.iterN (scopedLoopBody LoopLocalChecks.body)
      (fun o => LoopLocalChecks.condition.evalT o.st) n start =
      (if n < 3 then .inl out else .inr (.ok out)) ∧
    loopIterN (fun m => exec conditionCompiled.code 0 m)
      (fun m => exec bodyCompiled.code 0 m) n prefixMachine =
      (if n < 3 then .inl m else .inr (.ok m 0)) ∧
    StateRepr 3 1 128 before.frag out.st base' m ∧
    TEnv.thin LoopLocalChecks.protection out.st.env =
      TEnv.wk out.ext LoopLocalChecks.ProtectedCtx (TEnv.thin LoopLocalChecks.protection caller.st.env) ∧
    (∀ (R : RefTy) (i : Idx LoopLocalChecks.ProtectedCtx (.mem R)) (r : HRef caller.st.H R),
      TEnv.get (i.wk LoopLocalChecks.protection) caller.st.env = some r →
      m.mem (cellOf 1 (i.wk LoopLocalChecks.protection)) = .val (base0 r.id)) ∧
    (∀ (p : PrimTy) (i : Idx LoopLocalChecks.ProtectedCtx (.val p)),
      ReprV p (TEnv.get (i.wk LoopLocalChecks.protection) caller.st.env)
        (m.mem (cellOf 1 (i.wk LoopLocalChecks.protection)))) := by
  obtain ⟨base0,all⟩ := reached_all
  refine ⟨base0,fun n => ?_⟩
  obtain ⟨out,m,base',amount,hs,ht,pref,repr,he,growth,stack,cost⟩ := all n
  have healthy : TLoop.iterN (scopedLoopBody LoopLocalChecks.body)
      (fun o => LoopLocalChecks.condition.evalT o.st) n start = .inl out ∨
      TLoop.iterN (scopedLoopBody LoopLocalChecks.body)
      (fun o => LoopLocalChecks.condition.evalT o.st) n start = .inr (.ok out) := by
    split at hs
    · exact .inl hs
    · exact .inr hs
  have view := LoopCallerPrefix.represented LoopLocalChecks.protection
    (fun i => LoopLocalChecks.bodyPlan _ (LoopLocalChecks.protected_unwritten i))
    LoopLocalChecks.condition caller.st n out healthy repr he
  exact ⟨out,m,base',hs,ht,repr,view⟩
end Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes

#print axioms Solidity.Backend.InternalFlow.LoopCallerPrefix.condition_run
#print axioms Solidity.Backend.InternalFlow.LoopCallerPrefix.captured
#print axioms Solidity.Backend.InternalFlow.LoopCallerPrefix.represented
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.first_scoped
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.second_scoped
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.source_one
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.source_two
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.source_stopped
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.source_captured
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.body_cost
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.body_code
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.body_need
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.body_frag
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.first_reached
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.second_reached
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.reached_all
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.protected_all

#print axioms Solidity.Backend.InternalFlow.LoopCallerPrefix.condition_revert
#print axioms Solidity.Backend.InternalFlow.LoopCallerPrefix.program_revert
