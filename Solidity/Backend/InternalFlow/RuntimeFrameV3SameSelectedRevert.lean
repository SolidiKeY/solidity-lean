import Solidity.Backend.InternalFlow.RuntimeFrameV3EffectfulStorageRuntimeControls

/-! Successful and reverting entries for the SAME publicly selected call.
The second caller is reached by real fresh-empty-array rebinding, with the
original arguments, statement, code image and fragile alias unchanged.
Preparation observations are not states returned by revert. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
open OrderedEffectfulStorage.Controls (C Γ F caller before base reference count)
open EffectfulStorageRuntime.Controls (input selected)
open EffectfulRuntime (plan)

theorem free_tail (x : Nat) (high : 34≤x) : before.mem x=w[0] := by
 simp only [before,CallerStorageFrame.Controls.after,CallerStorageFrame.Controls.middle,
   CallerStorageFrame.Controls.before,CallerStorageFrame.Controls.blank,allocateMachine,writeMachine,upd,
   CallerStorageFrame.Controls.size,
   if_neg (show x≠0 by omega),if_neg (show x≠1 by omega),if_neg (show x≠2 by omega),
   if_neg (show x≠3 by omega),if_neg (show x≠5 by omega),if_neg (show x≠8 by omega),
   if_neg (show x≠9 by omega),if_neg (show x≠32 by omega),if_neg (show x≠33 by omega)]

theorem initial_owner : StructAllocatorRepr caller.heap base 32 (⟨34,by decide⟩ : Fin W) before := by
 apply AllocatorRepr.withoutStructs (hn:=fun r => OrderedEffectfulStorage.Controls.no_struct r)
 refine ⟨OrderedEffectfulStorage.Controls.initial.heap,⟨by decide,by decide,rfl,free_tail⟩,?_⟩
 intro p r
 change HRef [OrderedEffectfulScalar.A] (.array (.prim p)) at r
 rcases r with ⟨i,hi⟩
 cases i with
 | zero => cases hi;with_unfolding_all change (32+1+1:Nat)≤34;decide
 | succ i => cases hi

def size : Fin W := ⟨0,W_pos⟩
def length : Simple C Γ .uint := .lit 0 rfl
def preparation : Stmt C Γ Γ := .rebindMem reference (.newArr length rfl)
def compiled : CompiledStmt 1 F preparation := (Memory.compileStmt 1 F preparation).get (by rfl)
def fresh := (caller.alloc (defaultArray .uint size)).2
def reached_caller := (caller.alloc (defaultArray .uint size)).1.setLocal reference (some fresh)
def reached_base := upd base caller.H.length (⟨34,by decide⟩ : Fin W)
def reached_machine := writeMachine (allocateMachine before (⟨34,by decide⟩ : Fin W) size) (cellOf 1 reference) w[34]
def output : Solidity.Out C caller.H Γ := ⟨reached_caller,List.prefix_append _ _⟩

theorem public_root : Memory.compileStmt 1 F preparation=some compiled := by rfl

theorem code_eq : compiled.code=rebindNewCode 1 reference length := by rfl

theorem reached : preparation.run caller=.ok output ∧
 run compiled.code before=.ok reached_machine 0 ∧
 StateRepr 1 1 32 F reached_caller reached_base reached_machine ∧
 StructAllocatorRepr reached_caller.heap reached_base 32 (⟨35,by decide⟩ : Fin W) reached_machine ∧
 reached_machine.stack=before.stack ∧ Footprint.Words 8 32 before reached_machine :=
 Footprint.rebind OrderedEffectfulStorage.Controls.initial initial_owner (by decide)
   .uint reference length rfl size rfl (by decide) (lo:=8) (by decide)

theorem exact_cost : compiled.cert.cost caller=1 := by rfl

theorem preparation_capacity : AllocationInput 1 32 (compiled.cert.cost caller) caller base before :=
 .inr ⟨by decide,⟨34,by decide⟩,initial_owner,by decide⟩

theorem count_fails : count.evalT reached_caller=.error .revert := by with_unfolding_all rfl

theorem arena (depth : Nat) : (plan (selected depth) 5 9 8).arenaWords reached_caller=4 := by
 change ScalarDemand.reserve count reached_caller=4
 rw [ScalarDemand.reserve_error .revert count_fails]
 rfl

theorem cursor : reached_machine.mem 9=w[10] :=
 (reached.2.2.2.2.2 9 (by decide) (by decide)).trans OrderedEffectfulStorage.Controls.current

theorem entry (depth : Nat) :
 InterfaceV1.Entry (plan (selected depth) 5 9 8) 1 1 32 F reached_caller reached_base reached_machine 10 := by
 refine ⟨reached.2.2.1,(by change 1+Γ.length≤9;decide),(by change 1+Γ.length≤9;decide),
   (by change 1+(5+3-1)≤9;decide),(by change (9:Nat)≤9;decide),(by change (9:Nat)<32;decide),
   (by change (9:Nat)≤10;decide),?_,?_,.inl (by change (9:Nat)<10;decide),?_,cursor,.inl rfl⟩
 · change 10+(plan (selected depth) 5 9 8).arenaWords reached_caller≤32
   rw [arena];decide
 · change Γ.length+1≤(plan (selected depth) 5 9 8).arenaWords reached_caller
   rw [arena];decide
 · change 10+(plan (selected depth) 5 9 8).arenaWords reached_caller<W
   rw [arena];decide

theorem source_failure (depth : Nat) : (input count depth).run reached_caller=.error .revert :=
 ((selected depth).argument_failure (c:=5) reached_caller count_fails reached_base reached_machine
   reached.2.2.1 (by decide) (by decide) 9 8).1

theorem target_failure (depth : Nat) : run (plan (selected depth) 5 9 8).code reached_machine=.revert :=
 EffectfulStorageRuntime.bare_revert (selected depth) (by decide) (by decide) (by decide)
   1 32 reached_caller reached_base reached_machine 10 (entry depth) (source_failure depth)

/-- Both witnesses refer to exactly the same statement and plan. -/
theorem same_plan_entries (depth : Nat) (enough : 7<depth) :
 InterfaceV2.SuccessfulEntry 1 F (input count depth) (plan (selected depth) 5 9 8) ∧
 InterfaceV2.RevertingEntry 1 F (input count depth) (plan (selected depth) 5 9 8) :=
 ⟨EffectfulStorageRuntime.Controls.successful_entry depth enough,
  ⟨1,32,reached_caller,reached_base,reached_machine,10,entry depth,source_failure depth⟩⟩

def program (depth : Nat) : Prog C Γ Γ := .cons preparation (.cons (input count depth) .nil)

theorem whole_source (depth : Nat) : (program depth).run caller=.error .revert := by
 rw [program,Prog.run_cons_ok reached.1]
 change (TRun.seq (input count depth).runR TRun.nil reached_caller).map _=_
 simp only [TRun.seq,show (input count depth).runR reached_caller=.error .revert from source_failure depth,Except.map]

theorem whole_target (depth : Nat) : run (compiled.code++(plan (selected depth) 5 9 8).code) before=.revert :=
 (run_append_ok reached.2.1).trans (target_failure depth)


/-- Complete preparation snapshot, BEFORE entering the reverting call. -/
theorem preparation_observations :
 (reached_machine.stack,(List.range 35).map (fun i => reached_machine.mem i))=
 ([w[77]],[w[35],.slot CallerStorageFrame.Controls.slot,w[34],w[99],w[0],w[32],w[0],w[0],w[99],w[10],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[1],w[7],w[0]]) := by rfl

theorem source_observations :
 ((TEnv.get (.here : Idx Γ (.val .uint)) reached_caller.env).val,
  (TEnv.get reference reached_caller.env).map (fun r => r.id),
  reached_caller.H.length,
  (reached_caller.heap.get (OrderedEffectfulStorage.Controls.ref.wk (List.prefix_append caller.H [OrderedEffectfulScalar.A]))).val.map (fun v => v.val),
  (reached_caller.heap.get fresh).val.map (fun v => v.val))=
 (99,some 1,2,[7],[]) := by with_unfolding_all rfl

theorem storage_unchanged : reached_caller.storage=caller.storage := by rfl

theorem fragile_retained :
 ∃ r s,Look.ofTEnv reached_caller.env (.there (.there .here) : Idx Γ (.alias OrderedEffectfulScalar.A))=some r ∧
 reached_machine.mem 1=.slot s ∧ PathSlot C false r s ∧ ∃ v,reached_caller.storage.findLive r=some v :=
 reached.2.2.1.core.fragile (.there (.there .here)) rfl

theorem different_callers : caller≠reached_caller := by
 intro same
 have sizes := congrArg (fun state : State C Γ => state.H.length) same
 change (1:Nat)=2 at sizes
 cases sizes

theorem wrong_frontier : reached_machine.mem 0≠w[34] := by
 have actual : reached_machine.mem 0=w[35] := Option.some.inj
   (congrArg (fun obs : List Word × List Word => obs.2[0]?) preparation_observations)
 rw [actual]
 decide

end Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.free_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.free_tail

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.initial_owner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.initial_owner

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.public_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.public_root

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.code_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.code_eq

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.reached

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.exact_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.exact_cost

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.preparation_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.preparation_capacity

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.count_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.count_fails

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.arena' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.arena

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.cursor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.cursor

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.entry

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.source_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.source_failure

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.target_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.target_failure

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.same_plan_entries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.same_plan_entries

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.whole_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.whole_source

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.whole_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.whole_target

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.preparation_observations' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.preparation_observations

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.source_observations' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.source_observations

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.storage_unchanged' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.storage_unchanged

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.fragile_retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.fragile_retained

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.different_callers' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.different_callers

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.wrong_frontier' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.SameSelectedRevert.wrong_frontier
