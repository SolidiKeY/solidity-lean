import Solidity.Backend.InternalFlow.RuntimeFrameV3CallerPrefixes
import Solidity.Theory.Typed.Mem

/-! Derive the guarded countdown's source read domain from the actual typed heap
length. This is local evaluation evidence, not approved-profile provenance. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.HeapDomain
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes

theorem index_nat (n : Nat) (fit : n<W) : (countValue n fit).1.toNat=n := by rfl

/-- Actual expression evaluation resolves the represented alias and checked
counter decrement before reading the existing typed heap address. -/
theorem probe_eval {C : Contract} (σ : State C (Parameters A)) (n : Nat) (fit : n+1<W)
 (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) fit)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref) :
 ArrayProbe.value.evalT σ=TRes.ofOpt (σ.heap.readAddr (.index ref .dyn (countValue n (by omega)))) := by
 have decremented := decrement_eval rfl σ n fit ref counter alias
 simp only [ArrayProbe.value,Val.evalT,MLoc.addrT,MPath.mvalT,alias,decremented,ok_bind]
 rfl

/-- The published readAddr index theorem gives exact successful evaluation,
not an assumed read result or recursive simulation. -/
theorem success_iff {C : Contract} (σ : State C (Parameters A)) (n : Nat) (fit : n+1<W)
 (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) fit)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref) :
 (∃ v, ArrayProbe.value.evalT σ=.ok v) ↔ n<σ.heap.len ref .dyn := by
 have live := Heap.readAddr_index_isSome σ.heap ref .dyn (countValue n (by omega))
 rw [index_nat] at live
 rw [probe_eval σ n fit ref counter alias]
 cases read : σ.heap.readAddr (.index ref .dyn (countValue n (by omega))) with
 | none =>
   rw [read] at live
   have outside : ¬n<σ.heap.len ref .dyn := by
     intro within
     rw [decide_eq_true within] at live
     cases live
   constructor
   · rintro ⟨v,bad⟩
     cases bad
   · intro within
     exact (outside within).elim
 | some v =>
   rw [read] at live
   have within : n<σ.heap.len ref .dyn := of_decide_eq_true live.symm
   simp only [TRes.ofOpt]
   exact ⟨fun _ => within,fun _ => ⟨v,rfl⟩⟩

/-- Out of bounds means exactly this source read's bare revert. Exhaustion,
panic and divergence are not inferred from an empty payload projection. -/
theorem failure_iff {C : Contract} (σ : State C (Parameters A)) (n : Nat) (fit : n+1<W)
 (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) fit)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref) :
 ArrayProbe.value.evalT σ=.error .revert ↔ σ.heap.len ref .dyn≤n := by
 have live := Heap.readAddr_index_isSome σ.heap ref .dyn (countValue n (by omega))
 rw [index_nat] at live
 rw [probe_eval σ n fit ref counter alias]
 cases read : σ.heap.readAddr (.index ref .dyn (countValue n (by omega))) with
 | none =>
   rw [read] at live
   have notWithin : ¬n<σ.heap.len ref .dyn := by
     intro within
     rw [decide_eq_true within] at live
     cases live
   have outside : σ.heap.len ref .dyn≤n := by omega
   simp only [TRes.ofOpt]
   exact ⟨fun _ => outside,fun _ => True.intro⟩
 | some v =>
   rw [read] at live
   have within : n<σ.heap.len ref .dyn := of_decide_eq_true live.symm
   simp only [TRes.ofOpt,reduceCtorEq,false_iff]
   omega

/-- Every positive lower-counter read follows from one actual object-length
bound. This does not declare that bound an approved source/resource profile. -/
theorem domain_of_length {C : Contract} (σ : State C (Parameters A)) (ref : HRef σ.H A)
 (count : Nat) (enough : count≤σ.heap.len ref .dyn) : ReadDomain σ ref count := by
 intro k positive lower fit
 cases k with
 | zero => omega
 | succ n =>
   apply (success_iff (σ.withEnv (Δ:=Parameters A) (countValue (n+1) fit,(some ref,()))) n fit ref rfl rfl).2
   change n<σ.heap.len ref .dyn
   omega

/-- Exact local success-domain characterization for a genuine uint counter.
The word bound matters: it prevents quantification over impossible indices. -/
theorem domain_iff {C : Contract} (σ : State C (Parameters A)) (ref : HRef σ.H A)
 (count : Nat) (fit : count<W) : ReadDomain σ ref count ↔ count≤σ.heap.len ref .dyn := by
 constructor
 · intro domain
   cases count with
   | zero => omega
   | succ n =>
     have last := domain (n+1) (by omega) (by omega) fit
     have within := (success_iff (σ.withEnv (Δ:=Parameters A) (countValue (n+1) fit,(some ref,()))) n fit ref rfl rfl).1 last
     change n<σ.heap.len ref .dyn at within
     omega
 · exact domain_of_length σ ref count

/-- Source native-call horizons now consume the actual object's length bound,
not a supplied family of successful reads or a source simulation theorem. -/
theorem native_horizons {C : Contract} {Γ : Ctx} (name : Name)
 (args : Args C Γ (Parameters A)) (depth : Nat) (caller : State C Γ)
 (count : Nat) (fit : count<W) (ref : HRef caller.H A)
 (evaluated : args.evalT caller=.ok (countValue count fit,(some ref,())))
 (enough : count≤caller.heap.len ref .dyn) :
 (InterfaceV1.recursiveSource name args .none GuardedRecursion.step depth).run caller=
 if count<depth then .ok ⟨caller,List.prefix_refl _⟩ else .error .exhausted :=
 GuardedCaller.call_all_horizons name args depth caller count fit ref evaluated
 (domain_of_length (caller.withEnv (Δ:=Parameters A) (countValue count fit,(some ref,()))) ref count enough)

namespace Checks
open CountdownWitness

theorem length_zero : callee.heap.len P.r0 .dyn=2 := by with_unfolding_all rfl
theorem length_one : callee.heap.len Evm.Memory.CompileExamples.r1 .dyn=1 := by with_unfolding_all rfl

theorem domain_from_heap : ReadDomain callee P.r0 2 :=
 domain_of_length callee P.r0 2 (Nat.le_of_eq length_zero.symm)

theorem wrong_reference : ¬ReadDomain callee Evm.Memory.CompileExamples.r1 2 := by
 rw [domain_iff callee Evm.Memory.CompileExamples.r1 2 (by decide),length_one]
 decide

theorem wrong_count : ¬ReadDomain callee P.r0 3 := by
 rw [domain_iff callee P.r0 3 (by decide),length_zero]
 decide

theorem source_horizons (depth : Nat) : (GuardedCaller.Checks.call depth).run caller=
 if 2<depth then .ok ⟨caller,List.prefix_refl _⟩ else .error .exhausted :=
 native_horizons "guardedCountdown" CountdownWitness.args depth caller 2 (by decide) P.r0
 CountdownWitness.arguments (Nat.le_of_eq length_zero.symm)

/-- All real caller/heap/capacity premises are discharged. Only the derivation
of read validity changed; no target code or source fixture was substituted. -/
noncomputable def boundedPrefix (steps : Nat) (small : steps≤2) : Machine :=
 (CallerPrefixes.endpoint (tail:=[.mem CountdownWitness.A,.mem CountdownWitness.A]) steps 2 small caller (by decide) P.r0 rfl rfl
   domain_from_heap P.base GuardedCaller.Checks.input GuardedCaller.Checks.input_repr 8 8 10
   (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl).choose

theorem prefix_run (steps : Nat) (small : steps≤2) :
 loopIterN (run (guardCompiled (C:=P.C) 2 CountdownWitness.F).code)
 (run (turnCode (C:=P.C) 2 CountdownWitness.F 8)) steps GuardedCaller.Checks.input=.inl (boundedPrefix steps small) :=
 (CallerPrefixes.endpoint (tail:=[.mem CountdownWitness.A,.mem CountdownWitness.A]) steps 2 small caller (by decide) P.r0 rfl rfl
   domain_from_heap P.base GuardedCaller.Checks.input GuardedCaller.Checks.input_repr 8 8 10
   (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl).choose_spec.1

/-- Machine equality is determined by the TWO actual executions of the same
instruction prefix, not by equating two chosen certificate implementations. -/
theorem prefix_identity (steps : Nat) (small : steps≤2) :
 boundedPrefix steps small=CallerPrefixes.Checks.atPrefix steps small := by
 have actual := prefix_run steps small
 have previous := (CallerPrefixes.Checks.specification steps small).1
 exact Sum.inl.inj (actual.symm.trans previous)

theorem zero_observation : (CountdownWitness.observed (boundedPrefix 0 (by decide)),(boundedPrefix 0 (by decide)).mem 7)=
 (([w[77]],[w[20],w[16],w[16],w[2],w[10],w[99],w[0],w[0],w[0],w[0],w[2],w[7],w[9],w[1],w[4]]),w[10]) := by
 rw [prefix_identity]
 exact CallerPrefixes.Checks.zero_observation

theorem one_observation : (CountdownWitness.observed (boundedPrefix 1 (by decide)),(boundedPrefix 1 (by decide)).mem 7)=
 (([w[77]],[w[20],w[16],w[16],w[1],w[12],w[99],w[16],w[2],w[0],w[0],w[2],w[7],w[9],w[1],w[4]]),w[10]) := by
 rw [prefix_identity]
 exact CallerPrefixes.Checks.one_observation

theorem two_observation : (CountdownWitness.observed (boundedPrefix 2 (by decide)),(boundedPrefix 2 (by decide)).mem 7)=
 (([w[77]],[w[20],w[16],w[16],w[0],w[14],w[99],w[16],w[2],w[16],w[1],w[2],w[7],w[9],w[1],w[4]]),w[10]) := by
 rw [prefix_identity]
 exact CallerPrefixes.Checks.two_observation

/-- The count-three entered read is derived out of bounds from the heap,
without using the earlier independently calculated read outcome. -/
theorem bad_read_from_heap :
 ArrayProbe.value.evalT (GuardedCaller.Checks.badCaller.withEnv (Δ:=Parameters GuardedRecursion.A)
   (countValue 3 (by decide),(some P.r0,())))=.error .revert := by
 apply (failure_iff _ 2 (by decide) P.r0 rfl rfl).2
 change callee.heap.len P.r0 .dyn≤2
 simpa only [length_zero] using (Nat.le_refl 2)

theorem bad_native (depth : Nat) :
 (GuardedCaller.Checks.call (depth+1)).run GuardedCaller.Checks.badCaller=.error .revert :=
 GuardedCaller.call_read_failure "guardedCountdown" CountdownWitness.args depth GuardedCaller.Checks.badCaller 2 (by decide) P.r0 rfl bad_read_from_heap

theorem bad_target : run (image (C:=P.C) 2 CountdownWitness.F 8 7) GuardedCaller.Checks.badMachine=.revert := by
 have projected := parameter_projection (tail:=[.mem CountdownWitness.A,.mem CountdownWitness.A]) GuardedCaller.Checks.bad_repr
 exact target_failure _ 2 (by decide) rfl P.base GuardedCaller.Checks.badMachine projected 8 7 bad_read_from_heap

theorem bad_read_not_exhausted :
 ArrayProbe.value.evalT (GuardedCaller.Checks.badCaller.withEnv (Δ:=Parameters GuardedRecursion.A)
   (countValue 3 (by decide),(some P.r0,())))≠.error .exhausted := by
 rw [bad_read_from_heap]
 intro mismatch
 cases mismatch

end Checks

end Solidity.Backend.InternalFlow.RuntimeFrame.HeapDomain

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.HeapDomain.domain_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.HeapDomain.domain_iff
