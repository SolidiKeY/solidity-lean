import Solidity.Backend.InternalFlow.RuntimeFrameV3EffectfulStorageRuntime
import Solidity.Backend.InternalFlow.RuntimeFrameV3OrderedEffectfulStorageControls

/-! Publicly selected success and argument-revert witnesses with a genuinely
fragile caller alias. This is the same metadata, source and target image as
the stronger endpoint; no profile or general recursive-body claim. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource EffectfulSourceSelection
open EffectfulRuntime (plan)
open OrderedEffectfulStorage.Controls (C Γ F caller before base ref reference count value)

def input (argument : Val C Γ .uint) (depth : Nat) : Stmt C Γ Γ :=
 EffectfulSourceSelection.call reference argument .here (.user "alias") (.user "count") (.user "result")
   "fragileEffectful" depth (fun _ => EffectfulScalarSource.body depth)

def select (argument : Val C Γ .uint) (compiled : CompiledVal 1 F argument)
 (root : Memory.compileVal 1 F argument=some compiled) (depth : Nat) : Selected 1 F (input argument depth) :=
 make reference argument (.here : Idx Γ (.val .uint)) (.user "alias") (.user "count") (.user "result")
   "fragileEffectful" depth (fun _ => EffectfulScalarSource.body depth) rfl (EffectfulSourceCheck.complete depth) compiled root

def selected (depth : Nat) := select count value OrderedEffectfulStorage.Controls.public_root depth

theorem root (depth : Nat) : EffectfulSourceSelection.compile 1 F (input count depth)=some (selected depth) :=
 compile_call reference count (.here : Idx Γ (.val .uint)) (.user "alias") (.user "count") (.user "result")
   "fragileEffectful" depth (fun _ => EffectfulScalarSource.body depth) rfl
   (EffectfulSourceCheck.complete depth) value OrderedEffectfulStorage.Controls.public_root

theorem arena (depth : Nat) : (plan (selected depth) 5 9 8).arenaWords caller=14 := by
 change ScalarDemand.reserve count caller=14
 rw [ScalarDemand.reserve_value _ OrderedEffectfulStorage.Controls.evaluated]
 rfl

theorem entry (depth : Nat) : InterfaceV1.Entry (plan (selected depth) 5 9 8) 1 1 32 F caller base before 10 := by
 refine ⟨OrderedEffectfulStorage.Controls.initial,(by change 1+Γ.length≤9;decide),(by change 1+Γ.length≤9;decide),
   (by change 1+(5+3-1)≤9;decide),(by change (9:Nat)≤9;decide),(by change (9:Nat)<32;decide),
   (by change (9:Nat)≤10;decide),?_,?_,.inl (by change (9:Nat)<10;decide),?_,?_,.inl rfl⟩
 · change 10+(plan (selected depth) 5 9 8).arenaWords caller≤32
   rw [arena];decide
 · change Γ.length+1≤(plan (selected depth) 5 9 8).arenaWords caller
   rw [arena];decide
 · change 10+(plan (selected depth) 5 9 8).arenaWords caller<W
   rw [arena];decide
 · exact OrderedEffectfulStorage.Controls.current

noncomputable def result := (OrderedEffectfulScalar.changed caller ref).setLocal (.here : Idx Γ (.val .uint)) (countValue 7 (by decide))

theorem source (depth : Nat) (enough : 7<depth) : (input count depth).run caller=.ok ⟨result,List.prefix_refl _⟩ := by
 apply (selected depth).source_run caller |>.trans
 simpa only [if_pos enough] using OrderedEffectfulStorage.Controls.specification.2.1 "fragileEffectful" depth

theorem returned (depth : Nat) (enough : 7<depth) :
 InterfaceV1.Returned (plan (selected depth) 5 9 8) 1 1 32 caller base before 10 ⟨result,List.prefix_refl _⟩ :=
 returns (selected depth) (by decide) (by decide) (by decide) 1 32 caller base before 10 (entry depth) _ (source depth enough)

theorem successful_entry (depth : Nat) (enough : 7<depth) :
 InterfaceV2.SuccessfulEntry 1 F (input count depth) (plan (selected depth) 5 9 8) :=
 ⟨1,32,caller,base,before,10,⟨result,List.prefix_refl _⟩,entry depth,source depth enough⟩

theorem named_target (depth : Nat) (enough : 7<depth) :
 ∃ addresses,StateRepr 1 1 32 F result addresses OrderedEffectfulStorage.Controls.machine ∧
 Footprint.Words 9 10 before OrderedEffectfulStorage.Controls.machine ∧
 GrowsAllocator 1 32 0 caller base before result addresses OrderedEffectfulStorage.Controls.machine := by
 obtain ⟨after,addresses,executed,reached,stack,extended,growth,cursor,words⟩ := returned depth enough
 have same : after=OrderedEffectfulStorage.Controls.machine :=
   (Evm.Out.ok.inj (executed.symm.trans OrderedEffectfulStorage.Controls.specification.1)).1
 subst after
 exact ⟨addresses,reached,words,growth⟩

theorem violates_old_condition : ¬(∀ {R : RefTy} (i : Idx Γ (.alias R)),F.get i≠.fragile) :=
 OrderedEffectfulStorage.Controls.outside_old_condition

def bad_count : Val C Γ .uint := .readMem (.index .dyn (.var reference rfl) (.simple (.lit 1 rfl)))
def bad_value : CompiledVal 1 F bad_count := (Memory.compileVal 1 F bad_count).get (by rfl)
def bad_selected (depth : Nat) := select bad_count bad_value (by rfl) depth

theorem bad_root (depth : Nat) : EffectfulSourceSelection.compile 1 F (input bad_count depth)=some (bad_selected depth) :=
 compile_call reference bad_count (.here : Idx Γ (.val .uint)) (.user "alias") (.user "count") (.user "result")
   "fragileEffectful" depth (fun _ => EffectfulScalarSource.body depth) rfl
   (EffectfulSourceCheck.complete depth) bad_value (by rfl)

theorem bad_eval : bad_count.evalT caller=.error .revert := by with_unfolding_all rfl

theorem bad_arena (depth : Nat) : (plan (bad_selected depth) 5 9 8).arenaWords caller=4 := by
 change ScalarDemand.reserve bad_count caller=4
 rw [ScalarDemand.reserve_error .revert bad_eval]
 rfl

theorem bad_entry (depth : Nat) : InterfaceV1.Entry (plan (bad_selected depth) 5 9 8) 1 1 32 F caller base before 10 := by
 refine ⟨OrderedEffectfulStorage.Controls.initial,(by change 1+Γ.length≤9;decide),(by change 1+Γ.length≤9;decide),
   (by change 1+(5+3-1)≤9;decide),(by change (9:Nat)≤9;decide),(by change (9:Nat)<32;decide),
   (by change (9:Nat)≤10;decide),?_,?_,.inl (by change (9:Nat)<10;decide),?_,?_,.inl rfl⟩
 · change 10+(plan (bad_selected depth) 5 9 8).arenaWords caller≤32
   rw [bad_arena];decide
 · change Γ.length+1≤(plan (bad_selected depth) 5 9 8).arenaWords caller
   rw [bad_arena];decide
 · change 10+(plan (bad_selected depth) 5 9 8).arenaWords caller<W
   rw [bad_arena];decide
 · exact OrderedEffectfulStorage.Controls.current

theorem bad_source (depth : Nat) : (input bad_count depth).run caller=.error .revert :=
 ((bad_selected depth).argument_failure (c:=5) caller bad_eval base before OrderedEffectfulStorage.Controls.initial
   (by decide) (by decide) 9 8).1

theorem reverting_entry (depth : Nat) :
 InterfaceV2.RevertingEntry 1 F (input bad_count depth) (plan (bad_selected depth) 5 9 8) :=
 ⟨1,32,caller,base,before,10,bad_entry depth,bad_source depth⟩

theorem bad_target (depth : Nat) : run (plan (bad_selected depth) 5 9 8).code before=.revert :=
 bare_revert (bad_selected depth) (by decide) (by decide) (by decide) 1 32 caller base before 10 (bad_entry depth) (bad_source depth)

end Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.root

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.arena' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.arena

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.entry

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.source

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.returned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.returned

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.successful_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.successful_entry

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.named_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.named_target

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.violates_old_condition' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.violates_old_condition

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.bad_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.bad_root

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.bad_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.bad_eval

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.bad_arena' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.bad_arena

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.bad_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.bad_entry

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.bad_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.bad_source

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.reverting_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.reverting_entry

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.bad_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.Controls.bad_target
