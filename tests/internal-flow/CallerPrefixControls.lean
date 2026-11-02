import tests.«internal-flow».CallerPrefixFacts
namespace Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes
open Evm Evm.Memory LocalStoreFlow

/-- A genuinely always-running loop over the populated actual caller. -/
theorem spin_turn (m : Evm.Machine) : loopTurn (fun m => exec trueCondition.code 0 m)
    (fun m => exec spinCompiled.code 0 m) m = .inl m := by
  unfold trueCondition spinCompiled
  rfl

theorem spin_target_all (n : Nat) : loopIterN (fun m => exec trueCondition.code 0 m)
    (fun m => exec spinCompiled.code 0 m) n prefixMachine = .inl prefixMachine := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [loopIterN,spin_turn] using ih

theorem spin_represented_all : ∃ base, ∀ n : Nat,
    TLoop.iterN (scopedLoopBody spin) (fun _ => (.ok true : TRes Bool)) n start = .inl start ∧
    loopIterN (fun m => exec trueCondition.code 0 m)
      (fun m => exec spinCompiled.code 0 m) n prefixMachine = .inl prefixMachine ∧
    StateRepr 3 1 128 before.frag start.st base prefixMachine ∧
    TEnv.thin LoopLocalChecks.protection start.st.env =
      TEnv.wk start.ext LoopLocalChecks.ProtectedCtx (TEnv.thin LoopLocalChecks.protection caller.st.env) := by
  obtain ⟨base0,base1,whole,repr0,rest⟩ := complete_endpoint
  exact ⟨base0,fun n => ⟨spin_horizon n,spin_target_all n,repr0,source_captured 0 start (.inl rfl)⟩⟩

/-- Condition failure has no reached successful State, at ANY positive horizon. -/
theorem condition_failure_all (n : Nat) (positive : 0 < n) :
    TLoop.iterN (scopedLoopBody LoopLocalChecks.body)
      (fun o => LoopLocalChecks.badCondition.evalT o.st) n start = .inr (.error .revert) ∧
    loopIterN (fun m => exec badCondition.code 0 m)
      (fun m => exec bodyCompiled.code 0 m) n prefixMachine = .inr .revert := by
  have hs : TLoop.iterN (scopedLoopBody LoopLocalChecks.body)
      (fun o => LoopLocalChecks.badCondition.evalT o.st) 1 start = .inr (.error .revert) := by
    have bad : LoopLocalChecks.badCondition.evalT start.st = .error .revert := bad_condition_source
    simp only [TLoop.iterN,TLoop.step,bad]
  obtain ⟨base0,base1,whole,repr0,rest⟩ := complete_endpoint
  have ht : run badCondition.code prefixMachine = .revert :=
    LoopCallerPrefix.condition_revert (C := C) (b := 1) (L := 3) (frame := 128)
      (σ := caller.st) (base := base0) (m := prefixMachine) badCondition.cert repr0 bad_condition_source
  have target : loopIterN (fun m => exec badCondition.code 0 m)
      (fun m => exec bodyCompiled.code 0 m) 1 prefixMachine = .inr .revert := by
    change exec badCondition.code 0 prefixMachine = _ at ht
    simp only [loopIterN,loopTurn,ht]
  exact ⟨TLoop.iterN_done_le (by omega) hs,loopIterN_done_le (by omega) target⟩

/-- Allocation and mutations are reached BEFORE an actual body bare revert.
This exposes no fictitious failed State and makes no rollback claim. -/
def failingBody : Prog C Caller Turn := LoopLocalChecks.bodyWith (.cons .revert .nil)
def failingCompiled : Memory.CompiledProg 1 before.frag failingBody :=
  (Memory.compileProg 1 before.frag failingBody).get (by decide +kernel)
attribute [irreducible] failingCompiled
def failingProgram : Calls.Program 1 before.frag failingBody := Calls.plain failingCompiled

theorem failure_code : failingProgram.code = failingCompiled.code := rfl

private theorem reflect_failure {α : Type} (r : TRes α) (h : r.halt? = some THalt.revert) :
    r = .error .revert := by
  cases r with
  | ok v => cases h
  | error e => exact congrArg Except.error (Option.some.inj h)

theorem body_failed : failingBody.runR caller.st = .error .revert := reflect_failure _ (by decide +kernel)
theorem failure_cost : failingProgram.cost caller.st = 2 := by
  change allocationCostProg failingBody caller.st = 2
  decide +kernel
theorem failure_need : 1 + failingProgram.need ≤ 128 := by
  change 1 + frameNeedProg failingBody ≤ 128
  decide +kernel

attribute [irreducible] failingProgram

theorem body_failure_all (n : Nat) (positive : 0 < n) :
    TLoop.iterN (scopedLoopBody failingBody)
      (fun o => LoopLocalChecks.condition.evalT o.st) n start = .inr (.error .revert) ∧
    loopIterN (fun m => exec conditionCompiled.code 0 m)
      (fun m => exec failingCompiled.code 0 m) n prefixMachine = .inr .revert := by
  have hs : TLoop.iterN (scopedLoopBody failingBody)
      (fun o => LoopLocalChecks.condition.evalT o.st) 1 start = .inr (.error .revert) := by
    have failed : failingBody.runR start.st = .error .revert := body_failed
    simp only [TLoop.iterN,TLoop.step,conditions.1,scopedLoopBody,failed,Except.map]
  obtain ⟨base0,base1,whole,repr0,repr1,input,rest⟩ := complete_endpoint
  have cap : AllocationInput 1 128 (failingProgram.cost caller.st) caller.st base0 prefixMachine := by
    rw [failure_cost]; exact input.of_le (by decide)
  have ht : run failingProgram.code prefixMachine = .revert :=
    LoopCallerPrefix.program_revert (C := C) (b := 1) (L := 3) (frame := 128)
      (σ := caller.st) (base := base0) (m := prefixMachine) failingProgram repr0 failure_need cap body_failed
  have hc := LoopCallerPrefix.condition_run conditionCompiled.cert repr0 true conditions.1
  have target : loopIterN (fun m => exec conditionCompiled.code 0 m)
      (fun m => exec failingCompiled.code 0 m) 1 prefixMachine = .inr .revert := by
    change exec conditionCompiled.code 0 prefixMachine = _ at hc
    rw [failure_code] at ht
    change exec failingCompiled.code 0 prefixMachine = _ at ht
    simp only [loopIterN,loopTurn,hc,Machine.push,bword]
    rw [ht]
    rfl
  exact ⟨TLoop.iterN_done_le (by omega) hs,loopIterN_done_le (by omega) target⟩

theorem not_complete_at_two : TLoop.iterN (scopedLoopBody LoopLocalChecks.body)
    (fun o => LoopLocalChecks.condition.evalT o.st) 2 start ≠ .inr (.ok finalOut) := by
  rw [source_two]; intro h; cases h

theorem wrong_one_source : TLoop.iterN (scopedLoopBody LoopLocalChecks.body)
    (fun o => LoopLocalChecks.condition.evalT o.st) 1 start ≠ .inl finalOut := by
  rw [source_one]
  intro h
  exact final_different_first (Sum.inl.inj h).symm

theorem first_snapshot : firstMachine.stack = [w[77]] ∧ addresses.map firstMachine.mem =
    [w[261],w[99],w[17],w[10],w[256],w[256],w[259],w[77],w[2],w[9],w[11],w[1],w[10],w[0],w[0]] := by
  have raw := congrArg (fun triple => triple.2.1) ordered_target_words
  change firstMachine.stack ++ addresses.map firstMachine.mem = [w[77]] ++ _ at raw
  have size : firstMachine.stack.length = ([w[77]] : List Evm.Word).length := by
    have sizes := congrArg List.length raw
    simp only [List.length_append,List.length_map] at sizes ⊢
    change firstMachine.stack.length + 15 = 1 + 15 at sizes
    change firstMachine.stack.length = 1
    omega
  exact List.append_inj raw size

theorem wrong_one_cursor : firstMachine.mem 0 ≠ w[263] := by
  have hc : firstMachine.mem 0 = w[261] :=
    congrArg (fun xs : List Evm.Word => xs[0]!) first_snapshot.2
  rw [hc]; decide +kernel

theorem wrong_final_old_alias : finalMachine.mem 3 ≠ w[261] := wrong_alias_identity

theorem failure_not_fault (n : Nat) (positive : 0 < n) :
    loopIterN (fun m => exec conditionCompiled.code 0 m)
      (fun m => exec failingCompiled.code 0 m) n prefixMachine ≠ .inr .fault := by
  rw [(body_failure_all n positive).2]; intro h; cases h

theorem protected_scalar_not_private : finalMachine.mem 1 ≠ w[77] := by
  have hc : finalMachine.mem 1 = w[17] :=
    congrArg (fun xs : List Evm.Word => xs[2]!) final_cells.2
  rw [hc]; decide +kernel

/-- Old contents REALLY change; protecting bindings is not Heap.Keeps. -/
theorem old_contents_change : (observe start).oldA ≠ (observe finalOut).oldA := by
  have h := congrArg (fun t => (t.1.oldA,t.2.2.oldA)) source_vectors
  intro bad
  have first := congrArg Prod.fst h
  have last := congrArg Prod.snd h
  have impossible := first.symm.trans (bad.trans last)
  cases impossible
end Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes

#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.spin_turn
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.spin_target_all
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.spin_represented_all
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.condition_failure_all
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.body_failed
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.failure_cost
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.failure_need
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.body_failure_all
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.not_complete_at_two
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.wrong_one_source
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.first_snapshot
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.wrong_one_cursor
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.wrong_final_old_alias
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.failure_not_fault
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.protected_scalar_not_private
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.old_contents_change

#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.CallerPrefixes.failure_code
