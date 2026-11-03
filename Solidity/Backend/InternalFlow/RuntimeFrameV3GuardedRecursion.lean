import Solidity.Backend.InternalFlow.RuntimeFrameV3ArrayProbe

/-! Actual scoped probe in an intrinsic recursive family, plus its checked
runtime failure branch. This is not yet a complete recursive producer. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.GuardedRecursion
open Evm Evm.Memory RecursiveSource RecursiveActivation
abbrev A := ArrayProbe.A

def probe {C : Contract} : Stmt C (Parameters A) (Parameters A) :=
 .block (.cons (.declLocal .uint (.user "probe") (some ArrayProbe.value)) .nil)

theorem probe_success {C : Contract} (σ : State C (Parameters A)) (v : PrimTy.uint.Denote)
 (evaluated : ArrayProbe.value.evalT σ=.ok v) :
 (probe (C:=C)).run σ=.ok ⟨σ,List.prefix_refl _⟩ := by
 change TRun.block (.push .refl) (TRun.seq (TRun.declLocal .uint (some ArrayProbe.value)) TRun.nil) σ=_
 simp only [TRun.block,TRun.seq,TRun.declLocal,evaluated,ok_bind,TRun.nil,Except.map]
 rfl

theorem probe_failure {C : Contract} (σ : State C (Parameters A))
 (evaluated : ArrayProbe.value.evalT σ=.error .revert) :
 (probe (C:=C)).run σ=.error .revert := by
 change TRun.block (.push .refl) (TRun.seq (TRun.declLocal .uint (some ArrayProbe.value)) TRun.nil) σ=_
 simp only [TRun.block,TRun.seq,TRun.declLocal,evaluated,error_bind,Except.map]

def step {C : Contract} (depth : Nat) (back : Unit → Prog C (Parameters A) (Parameters A)) :
 Prog C (Parameters A) (Parameters A) :=
 .cons (.ite nonzero (.cons probe (.cons (.callRec "guardedCountdown" depth (nextArgs A rfl) .none back) .nil)) .nil) .nil

def body {C : Contract} (depth : Nat) : Prog C (Parameters A) (Parameters A) :=
 recUnroll Prog.recBase step depth

theorem base_exhausts {C : Contract} (σ : State C (Parameters A)) :
 (body 0).run σ=.error .exhausted := by rfl

/-- Failure of the actual scoped read takes precedence over the child result, at EVERY
positive source horizon. The exhausted depth-zero case remains separate. -/
theorem source_failure {C : Contract} (σ : State C (Parameters A)) (depth : Nat)
 (guard : nonzero.evalT σ=.ok true) (evaluated : ArrayProbe.value.evalT σ=.error .revert) :
 (body (depth+1)).run σ=.error .revert := by
 have failed := probe_failure σ evaluated
 change TRun.seq (TRun.ite nonzero .refl
   (TRun.seq (probe (C:=C)).runR
     (TRun.seq (TRun.call (nextArgs A rfl) .none .refl (body depth).runR) TRun.nil))
   .refl TRun.nil) TRun.nil σ=_
 change (probe (C:=C)).runR σ=.error .revert at failed
 simp only [TRun.seq,TRun.ite,guard,boolT,if_true,failed,ok_bind,Except.map]

/-- Successful scoped evaluation selects the ACTUAL native child call. -/
theorem source_positive {C : Contract} (σ : State C (Parameters A)) (depth : Nat)
 (v : PrimTy.uint.Denote) (guard : nonzero.evalT σ=.ok true)
 (evaluated : ArrayProbe.value.evalT σ=.ok v) :
 (body (depth+1)).run σ=
 (.call "guardedCountdown" (nextArgs A rfl) .none (body depth) : Stmt C (Parameters A) (Parameters A)).run σ := by
 have passed := probe_success σ v evaluated
 let call : TStep C (Parameters A) (Parameters A) := TRun.call (nextArgs A rfl) .none .refl (body depth).runR
 change TRun.seq (TRun.ite nonzero .refl (TRun.seq (probe (C:=C)).runR (TRun.seq call TRun.nil))
   .refl TRun.nil) TRun.nil σ=call σ
 change (probe (C:=C)).runR σ=.ok ⟨σ,List.prefix_refl _⟩ at passed
 simp only [TRun.seq,TRun.ite,guard,boolT,if_true,passed,ok_bind,Except.map]
 cases actual : call σ with
 | error halt => simp only [actual,Except.map]
 | ok out => simp only [actual,TRun.nil,Except.map];cases out;rfl

/-- The native child result here is actual execution evidence, discharged
by the following nested client, not a target preservation assumption. -/
theorem child_returns {C : Contract} (σ : State C (Parameters A)) (n : Nat) (bound : n+1<W)
 (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) bound)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (depth : Nat)
 (child : (body depth).run (σ.withEnv (Δ:=Parameters A) (countValue n (by omega),(some ref,())))=
   .ok ⟨σ.withEnv (Δ:=Parameters A) (countValue n (by omega),(some ref,())),List.prefix_refl _⟩) :
 (.call "guardedCountdown" (nextArgs A rfl) .none (body depth) : Stmt C (Parameters A) (Parameters A)).run σ=
 .ok ⟨σ,List.prefix_refl _⟩ := by
 have args := next_eval rfl σ n bound ref counter alias
 change TRun.call (nextArgs A rfl) .none .refl (body depth).runR σ=_
 unfold TRun.call
 simp only [args,ok_bind,CallRet.enterT]
 change (do
   let out ← (body depth).run (σ.withEnv (Δ:=Parameters A) (countValue n (by omega),(some ref,())))
   pure (⟨out.st.withEnv (TEnv.wk ((List.prefix_refl σ.H).trans out.ext) (Parameters A) σ.env),
     (List.prefix_refl σ.H).trans out.ext⟩ : Solidity.Out C σ.H (Parameters A)))=_
 rw [child]
 simp only [ok_bind,TEnv.wk_self]
 rfl

theorem source_zero {C : Contract} (σ : State C (Parameters A)) (depth : Nat)
 (guard : nonzero.evalT σ=.ok false) : (body (depth+1)).run σ=.ok ⟨σ,List.prefix_refl _⟩ := by
 change TRun.seq (TRun.ite nonzero .refl
   (TRun.seq (probe (C:=C)).runR
     (TRun.seq (TRun.call (nextArgs A rfl) .none .refl (body depth).runR) TRun.nil))
   .refl TRun.nil) TRun.nil σ=_
 simp only [TRun.seq,TRun.ite,guard,boolT,if_false,TRun.nil,ok_bind,Except.map]
 rfl

theorem child_failure {C : Contract} (σ : State C (Parameters A)) (n : Nat) (bound : n+1<W)
 (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) bound)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (depth : Nat) (halt : THalt)
 (child : (body depth).run (σ.withEnv (Δ:=Parameters A) (countValue n (by omega),(some ref,())))=.error halt) :
 (.call "guardedCountdown" (nextArgs A rfl) .none (body depth) : Stmt C (Parameters A) (Parameters A)).run σ=.error halt := by
 have args := next_eval rfl σ n bound ref counter alias
 change TRun.call (nextArgs A rfl) .none .refl (body depth).runR σ=_
 unfold TRun.call
 simp only [args,ok_bind,CallRet.enterT]
 change (do
   let out ← (body depth).run (σ.withEnv (Δ:=Parameters A) (countValue n (by omega),(some ref,())))
   pure (⟨out.st.withEnv (TEnv.wk ((List.prefix_refl σ.H).trans out.ext) (Parameters A) σ.env),
     (List.prefix_refl σ.H).trans out.ext⟩ : Solidity.Out C σ.H (Parameters A)))=_
 rw [child]
 rfl

def turnCode {C : Contract} (b : Nat) (F : Frag (Parameters A)) (pointer : Nat) : List Instr :=
 ArrayProbe.code (C:=C) b F ++ activationCode (C:=C) b F pointer

def image {C : Contract} (b : Nat) (F : Frag (Parameters A)) (pointer bottom : Nat) : List Instr :=
 [.loop (guardCompiled (C:=C) b F).code (turnCode (C:=C) b F pointer)] ++ PairedUnwind.code b pointer bottom A

/-- Small execution boundary keeps the actual checked code opaque. -/
theorem failing_turn (rc rb : Machine → Evm.Out) (machine : Machine)
 (guard : rc machine=.ok (machine.push w[1]) 0) (failed : rb machine=.revert) :
 loopIterN rc rb 1 machine=.inr .revert := by
 simp only [loopIterN,loopTurn,guard,Machine.push,if_false,Nat.one_ne_zero,failed]

theorem successful_turn (rc rb : Machine → Evm.Out) (machine next : Machine)
 (guard : rc machine=.ok (machine.push w[1]) 0) (executed : rb machine=.ok next 0) :
 loopTurn rc rb machine=.inl next := by
 simp only [loopTurn,guard,Machine.push,if_false,Nat.one_ne_zero,executed]

theorem empty_turn (rc rb : Machine → Evm.Out) (machine : Machine)
 (guard : rc machine=.ok (machine.push w[0]) 0) : loopTurn rc rb machine=.inr (.ok machine 0) := by
 simp only [loopTurn,guard,Machine.push,if_true]

theorem successful_loop (condition body : List Instr) (machine last : Machine) (n : Nat)
 (observed : loopIterN (run condition) (run body) n machine=.inr (.ok last 0)) :
 run [.loop condition body] machine=.ok last 0 := by
 have stopped := loopRun_of_iterN observed
 change loopRun (fun m => exec condition 0 m) (fun m => exec body 0 m) machine=.ok last 0 at stopped
 simp only [run,exec_cons_zero,Instr.step,stopped,Out.ok_bind,exec_nil]

theorem failing_loop (condition body suffix : List Instr) (machine : Machine)
 (observed : loopIterN (run condition) (run body) 1 machine=.inr .revert) :
 run (.loop condition body :: suffix) machine=.revert := by
 have stopped := loopRun_of_iterN observed
 change loopRun (fun m => exec condition 0 m) (fun m => exec body 0 m) machine=.revert at stopped
 simp only [run,exec_cons_zero,Instr.step,stopped,Out.revert_bind]

/-- Actual positive guard and checked failing read end the real target loop,
absorbing both activation and unwind. No final failed State is reconstructed. -/
theorem target_failure {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
 (σ : State C (Parameters A)) (n : Nat) (bound : n+1<W)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) bound)
 (base : Nat → Fin W) (machine : Machine) (repr : StateRepr L b frame F σ base machine)
 (pointer bottom : Nat) (evaluated : ArrayProbe.value.evalT σ=.error .revert) :
 run (image (C:=C) b F pointer bottom) machine=.revert := by
 have guard := guard_run σ (n+1) bound counter base machine repr
 have failed := ArrayProbe.failure_suffix repr evaluated (activationCode (C:=C) b F pointer)
 have positive : decide (0<n+1)=true := decide_eq_true (by omega)
 have checkedGuard : run (guardCompiled (C:=C) b F).code machine=.ok (machine.push w[1]) 0 := by
   simpa only [positive,bword] using guard
 have observed := failing_turn (run (guardCompiled (C:=C) b F).code)
   (run (turnCode (C:=C) b F pointer)) machine checkedGuard failed
 exact failing_loop _ _ _ machine observed

/-- Successful probe insertion is justified by actual checked evaluation;
the fixed activation execution remains the existing producer fact. -/
theorem probed_turn {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
 (σ : State C (Parameters A)) (n : Nat) (bound : n+1<W)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) bound)
 (base : Nat → Fin W) (machine next : Machine) (repr : StateRepr L b frame F σ base machine)
 (pointer : Nat) (v : PrimTy.uint.Denote) (evaluated : ArrayProbe.value.evalT σ=.ok v)
 (activation : run (activationCode (C:=C) b F pointer) machine=.ok next 0) :
 loopTurn (run (guardCompiled (C:=C) b F).code) (run (turnCode (C:=C) b F pointer)) machine=.inl next := by
 have guard := guard_run σ (n+1) bound counter base machine repr
 have positive : decide (0<n+1)=true := decide_eq_true (by omega)
 have checkedGuard : run (guardCompiled (C:=C) b F).code machine=.ok (machine.push w[1]) 0 := by
   simpa only [positive,bword] using guard
 have checkedBody : run (turnCode (C:=C) b F pointer) machine=.ok next 0 :=
   (run_append_ok (ArrayProbe.success repr v evaluated)).trans activation
 exact successful_turn _ _ _ _ checkedGuard checkedBody

def entry {C : Contract} (b : Nat) (F : Frag (Parameters A)) (pointer bottom : Nat) : List Instr :=
 RecursiveReturn.initializeCode pointer bottom ++ image (C:=C) b F pointer bottom

/-- Generic initialized failure branch: all matching premises are actual
input representation/counter/read facts, not a source-target simulation. -/
theorem failure_pair {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
 (σ : State C (Parameters A)) (n depth : Nat) (bound : n+1<W)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) bound)
 (base : Nat → Fin W) (machine : Machine) (repr : StateRepr L b frame F σ base machine)
 (pointer bottom : Nat) (bottomAbove : b+2≤bottom) (bottomBelow : bottom<frame)
 (evaluated : ArrayProbe.value.evalT σ=.error .revert) :
 GrowingResult L b frame 0 F σ base machine ((body (C:=C) (depth+1)).run σ)
   (run (entry (C:=C) b F pointer bottom) machine) := by
 have guard : nonzero.evalT σ=.ok true := by
   have actual := guard_eval σ (n+1) (congrArg (fun v : PrimTy.uint.Denote => v.val) counter)
   simpa only [show decide (0<n+1)=true from decide_eq_true (by omega)] using actual
 have source := source_failure σ depth guard evaluated
 have initialized := RecursiveReturn.initialize_repr repr pointer bottom bottomAbove bottomBelow
 have failed := target_failure σ n bound counter base _ initialized pointer bottom evaluated
 exact .inr ⟨source,(run_append_ok (RecursiveReturn.initialize_run machine pointer bottom)).trans failed⟩

namespace Checks
open CountdownWitness
abbrev F := CountdownWitness.F

theorem bad_source (depth : Nat) : (body (C:=P.C) (depth+1)).run ArrayProbe.Checks.bad=.error .revert := by
 apply source_failure _ depth _ ArrayProbe.Checks.bad_evaluated
 simpa only [show decide (0<3)=true from rfl] using guard_eval ArrayProbe.Checks.bad 3 rfl

theorem bad_target : run (image (C:=P.C) 2 F 8 7) ArrayProbe.Checks.badMachine=.revert :=
 target_failure _ 2 (by decide) rfl P.base _ ArrayProbe.Checks.bad_repr 8 7 ArrayProbe.Checks.bad_evaluated

def one := callee.withEnv (Δ:=Parameters A) (countValue 1 (by decide),(some P.r0,()))
def zero := one.withEnv (Δ:=Parameters A) (countValue 0 W_pos,(some P.r0,()))

theorem zero_source : (body (C:=P.C) 1).run zero=.ok ⟨zero,List.prefix_refl _⟩ := by
 apply source_zero zero 0
 simpa only [show decide (0<0)=false from rfl] using guard_eval zero 0 rfl

theorem one_probe : ArrayProbe.value.evalT one=.ok (P.uint 7 (by decide)) := by
 with_unfolding_all rfl

theorem one_source : (body (C:=P.C) 2).run one=.ok ⟨one,List.prefix_refl _⟩ := by
 have guard : nonzero.evalT one=.ok true := by
   simpa only [show decide (0<1)=true from rfl] using guard_eval one 1 rfl
 rw [source_positive one 1 _ guard one_probe]
 exact child_returns one 0 (by decide) P.r0 rfl rfl 1 zero_source

theorem nested_source : (body (C:=P.C) 3).run callee=.ok ⟨callee,List.prefix_refl _⟩ := by
 have guard : nonzero.evalT callee=.ok true := by
   simpa only [show decide (0<2)=true from rfl] using guard_eval callee 2 rfl
 rw [source_positive callee 2 _ guard ArrayProbe.Checks.good_evaluated]
 exact child_returns callee 1 (by decide) P.r0 rfl rfl 2 one_source

/-- The successful image uses actual probe/activation runs twice. Its
return is shared with the old image only after proving the SAME reached state. -/
theorem good_target : ∃ last,
 run (entry (C:=P.C) 2 F 8 7) AllocatorReturn.Checks.input=.ok last 0 ∧
 StateRepr 1 2 16 F callee P.base last ∧ last.stack=[w[77]] ∧ last.mem 8=w[10] ∧
 StructAllocatorRepr callee.heap P.base 16 ⟨22,by decide⟩ last ∧
 [last.mem 0,last.mem 1,last.mem 2,last.mem 3,last.mem 7,last.mem 8,last.mem 9,
  last.mem 10,last.mem 11,last.mem 12,last.mem 13,last.mem 16,last.mem 17,last.mem 18,last.mem 20,last.mem 21]=
 [w[22],w[16],w[16],w[2],w[10],w[10],w[99],w[16],w[2],w[16],w[1],w[2],w[7],w[9],w[1],w[4]] ∧
 GrowsAllocator 2 16 0 callee P.base AllocatorReturn.Checks.input callee P.base last := by
 let input := ParentPrefixes.Checks.input
 obtain ⟨saved1,next1,addr1,args1,entered1,captured1,updated1,run1,repr1,stack1,ext1,grow1,cur1,payload1⟩ :=
   activation rfl callee 1 (by decide) P.r0 rfl rfl P.base input ParentPrefixes.Checks.initial
     8 8 10 (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)) (by decide) rfl
 obtain ⟨saved2,next2,addr2,args2,entered2,captured2,updated2,run2,repr2,stack2,ext2,grow2,cur2,payload2⟩ :=
   activation rfl one 0 (by decide) P.r0 rfl rfl addr1 next1 repr1
     8 8 12 (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)) (by decide) cur1
 have turn1 := probed_turn callee 1 (by decide) rfl P.base input next1 ParentPrefixes.Checks.initial
   8 _ ArrayProbe.Checks.good_evaluated run1
 have turn2 := probed_turn one 0 (by decide) rfl addr1 next1 next2 repr1 8 _ one_probe run2
 have old1 := RecursiveActivation.positive_turn callee 1 (by decide) rfl P.base input next1 ParentPrefixes.Checks.initial 8 run1
 have old2 := RecursiveActivation.positive_turn one 0 (by decide) rfl addr1 next1 next2 repr1 8 run2
 have guard := guard_run zero 0 W_pos rfl addr2 next2 repr2
 have newDone : loopTurn (run (guardCompiled (C:=P.C) 2 F).code)
     (run (turnCode (C:=P.C) 2 F 8)) next2=.inr (.ok next2 0) :=
   empty_turn _ _ next2 guard
 have oldDone := RecursiveActivation.zero_turn zero rfl addr2 next2 repr2 8
 have newStopped : loopIterN (run (guardCompiled (C:=P.C) 2 F).code)
     (run (turnCode (C:=P.C) 2 F 8)) 3 input=.inr (.ok next2 0) := by
   simp only [loopIterN,turn1,turn2,newDone]
 have oldStopped : loopIterN (run (guardCompiled (C:=P.C) 2 F).code)
     (run (activationCode (C:=P.C) 2 F 8)) 3 input=.inr (.ok next2 0) := by
   simp only [loopIterN,old1,old2,oldDone]
 have newRun := successful_loop _ _ input next2 3 newStopped
 have oldRun := RecursiveDescent.run_of_stopped oldStopped
 obtain ⟨last,source,oldReturned,represented,stack,cursor,low,high,history⟩ :=
   RecursiveReturn.endpoint rfl 2 (by decide) callee P.r0 rfl rfl P.base input ParentPrefixes.Checks.initial
     8 8 7 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
     (by decide) (by decide) (by decide) (by decide) rfl rfl
 have returned : run (PairedUnwind.code 2 8 7 A) next2=.ok last 0 :=
   (run_append_ok oldRun).symm.trans oldReturned
 have joined : run (image (C:=P.C) 2 F 8 7) input=.ok last 0 := (run_append_ok newRun).trans returned
 have initialized : run (RecursiveReturn.initializeCode 8 7) AllocatorReturn.Checks.input=.ok input 0 := by rfl
 have completed : run (entry (C:=P.C) 2 F 8 7) AllocatorReturn.Checks.input=.ok last 0 :=
   (run_append_ok initialized).trans joined
 have growth := AllocatorReturn.growth represented (low 0 (by decide)) high
 have owned := growth ⟨22,by decide⟩ (by decide) ParentPrefixes.Checks.ownership (by decide)
 have initializedGrowth : GrowsAllocator 2 16 0 callee P.base AllocatorReturn.Checks.input callee P.base input := by
   intro c positive ownership space
   simpa only [Nat.add_zero] using ownership.localWrite 7 (by decide) (by decide) w[10]
 have totalGrowth := initializedGrowth.comp growth
 refine ⟨last,completed,represented,stack,cursor,owned,?_,by simpa only [Nat.add_zero] using totalGrowth⟩
 have h0 := history 0 (by decide)
 have h1 := history 1 (by decide)
 rw [low 0 (by decide),low 1 (by decide),low 2 (by decide),low 3 (by decide),low 7 (by decide),
   low 8 (by decide),low 9 (by decide),h0.1,h0.2,h1.1,h1.2,
   high 16 (by decide),high 17 (by decide),high 18 (by decide),high 20 (by decide),high 21 (by decide)]
 rfl

theorem bad_entry : run (entry (C:=P.C) 2 F 8 7) ArrayProbe.Checks.badMachine=.revert := by
 have repr := RecursiveReturn.initialize_repr ArrayProbe.Checks.bad_repr 8 7 (by decide) (by decide)
 have failed := target_failure ArrayProbe.Checks.bad 2 (by decide) rfl P.base _ repr 8 7 ArrayProbe.Checks.bad_evaluated
 exact (run_append_ok (RecursiveReturn.initialize_run ArrayProbe.Checks.badMachine 8 7)).trans failed

theorem one_source_all (fuel : Nat) : (body (C:=P.C) (fuel+2)).run one=.ok ⟨one,List.prefix_refl _⟩ := by
 have guard : nonzero.evalT one=.ok true := by
   simpa only [show decide (0<1)=true from rfl] using guard_eval one 1 rfl
 have done : (body (C:=P.C) (fuel+1)).run zero=.ok ⟨zero,List.prefix_refl _⟩ := by
   apply source_zero zero fuel
   simpa only [show decide (0<0)=false from rfl] using guard_eval zero 0 rfl
 rw [source_positive one (fuel+1) _ guard one_probe]
 exact child_returns one 0 (by decide) P.r0 rfl rfl (fuel+1) done

theorem nested_source_all (fuel : Nat) : (body (C:=P.C) (fuel+3)).run callee=.ok ⟨callee,List.prefix_refl _⟩ := by
 have guard : nonzero.evalT callee=.ok true := by
   simpa only [show decide (0<2)=true from rfl] using guard_eval callee 2 rfl
 rw [source_positive callee (fuel+2) _ guard ArrayProbe.Checks.good_evaluated]
 exact child_returns callee 1 (by decide) P.r0 rfl rfl (fuel+2) (one_source_all fuel)

/-- SAME emitted image at every sufficient native quotation horizon. -/
theorem successful_pair (fuel : Nat) :
 GrowingResult 1 2 16 0 F callee P.base AllocatorReturn.Checks.input
   ((body (C:=P.C) (fuel+3)).run callee)
   (run (entry (C:=P.C) 2 F 8 7) AllocatorReturn.Checks.input) := by
 obtain ⟨last,executed,repr,stack,cursor,owned,words,growth⟩ := good_target
 exact .inl ⟨⟨callee,List.prefix_refl _⟩,last,P.base,nested_source_all fuel,executed,repr,stack,BaseExtends.refl _,growth⟩

theorem reverting_pair (fuel : Nat) :
 GrowingResult 1 2 16 0 F ArrayProbe.Checks.bad P.base ArrayProbe.Checks.badMachine
   ((body (C:=P.C) (fuel+1)).run ArrayProbe.Checks.bad)
   (run (entry (C:=P.C) 2 F 8 7) ArrayProbe.Checks.badMachine) :=
 .inr ⟨bad_source fuel,bad_entry⟩

/-- A live read followed by insufficient child unrolling still exhausts;
that boundary is NOT the bounds failure of the counter-three input. -/
theorem live_exhaustion : (body (C:=P.C) 2).run callee=.error .exhausted := by
 have guardOne : nonzero.evalT one=.ok true := by
   simpa only [show decide (0<1)=true from rfl] using guard_eval one 1 rfl
 have child : (body (C:=P.C) 1).run one=.error .exhausted := by
   rw [source_positive one 0 _ guardOne one_probe]
   exact child_failure one 0 (by decide) P.r0 rfl rfl 0 .exhausted (base_exhausts zero)
 have guardTwo : nonzero.evalT callee=.ok true := by
   simpa only [show decide (0<2)=true from rfl] using guard_eval callee 2 rfl
 rw [source_positive callee 1 _ guardTwo ArrayProbe.Checks.good_evaluated]
 exact child_failure callee 1 (by decide) P.r0 rfl rfl 1 .exhausted child

theorem exhaustion_unmatched :
 ¬ GrowingResult 1 2 16 0 F callee P.base AllocatorReturn.Checks.input
   ((body (C:=P.C) 2).run callee) (run (entry (C:=P.C) 2 F 8 7) AllocatorReturn.Checks.input) := by
 intro matched
 rcases matched with ⟨out,last,addresses,success,rest⟩ | ⟨failure,rest⟩
 · rw [live_exhaustion] at success;cases success
 · rw [live_exhaustion] at failure;cases failure

theorem bad_not_fault : run (entry (C:=P.C) 2 F 8 7) ArrayProbe.Checks.badMachine≠.fault := by
 rw [bad_entry];intro mismatch;cases mismatch

end Checks
end Solidity.Backend.InternalFlow.RuntimeFrame.GuardedRecursion
