import tests.h62.item2.«audit-v09-passes».P20InterfaceV2Controls
import Solidity.Backend.Passes.Stack

/-! Regression: zero-cost disjunctions must not masquerade as positive allocator
capacity, and an array/core relation must not be upgraded into object ownership.
This fixture constructs a real empty object heap, nonzero allocator cursor and
positive-cost capacity jointly for the three private frozen Stack premise
bundles. It does not expose or invoke private declarations. Source identities
and exact signatures stay in the map; other heaps and whole adequacy stay open. -/
namespace Solidity.Backend.Passes.AuditPrivateStack
open Evm Evm.Memory
abbrev C := Yul.Compilation.P20.InterfaceV2.Controls.C

def initial : State C [] := State.init C

def bases : Nat → Fin W := fun _ => wmod 0

def machine : Machine :=
  {Machine.init with mem := fun n => if n = 0 then w[16] else w[0]}

private theorem noRefs {R : RefTy} (r : HRef initial.H R) : False := by
  simpa only [initial, State.init, List.getElem?_nil, reduceCtorEq] using r.get?

theorem heap : Objects.HeapRepr initial.heap bases 8 machine := by
  exact ⟨⟨fun r => (noRefs r).elim, fun r => (noRefs r).elim, fun r _ _ => (noRefs r).elim⟩,
    (fun _ r => (noRefs r).elim), (fun r => (noRefs r).elim), (fun r _ => (noRefs r).elim)⟩

theorem state : Objects.StateRepr 1 1 8 (Frag.init []) initial bases machine := by
  have core := Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  refine ⟨⟨core.store, ?_, ?_, core.net, core.netSelf, core.bound, ?_, core.env,
    core.funds, core.oracle⟩, heap, ?_, by decide⟩
  all_goals intro p i; nomatch i

theorem allocator : Objects.AllocatorRepr initial.heap bases 8 ⟨16,by decide⟩ machine := by
  refine ⟨heap, ⟨by decide, by decide, rfl, ?_⟩, fun r => (noRefs r).elim⟩
  intro address above
  change 16 ≤ address at above
  simp only [machine, if_neg (show address ≠ 0 by omega)]

theorem positive_object_input : Objects.AllocationInput 1 8 1 initial bases machine :=
  .inr ⟨by decide, ⟨16,by decide⟩, allocator, by decide⟩

theorem positive_legacy_input : Memory.AllocationInput 1 8 1 initial bases machine :=
  .inr ⟨by decide, ⟨16,by decide⟩, allocator.legacy, by decide⟩

/-- All three original h premises hold on the same actual tuple. -/
theorem joint (_tail : List Word) :
    Memory.AllocationInput 1 8 1 initial bases machine ∧
    Objects.AllocationInput 1 8 1 initial bases machine ∧
    Objects.StateRepr 1 1 8 (Frag.init []) initial bases machine :=
  ⟨positive_legacy_input, positive_object_input, state⟩

/-- Both allocator relations and full object state retain every saved tail. -/
theorem transported (tail : List Word) :
    Memory.AllocationInput 1 8 1 initial bases {machine with stack := tail} ∧
    Objects.AllocationInput 1 8 1 initial bases {machine with stack := tail} ∧
    Objects.StateRepr 1 1 8 (Frag.init []) initial bases {machine with stack := tail} :=
  ⟨.inr ⟨by decide, ⟨16,by decide⟩, allocator.legacy.stack tail, by decide⟩,
   .inr ⟨by decide, ⟨16,by decide⟩, allocator.stack tail, by decide⟩,
   ⟨state.core.stack tail, state.heap.stack tail, state.pointers, state.locals⟩⟩

theorem zero_inputs : Memory.AllocationInput 1 8 0 initial bases machine ∧
    Objects.AllocationInput 1 8 0 initial bases machine :=
  ⟨.inl rfl, .inl rfl⟩

/-- General capacity refusal does not assume allocator validity or a cursor. -/
theorem full_cost_refused {D : Contract} {Γ : Ctx} (b frame : Nat) (σ : State D Γ)
    (base : Nat → Fin W) (m : Machine) :
    ¬ Objects.AllocationInput b frame W σ base m := by
  intro input
  rcases input with zero | ⟨_, cursor, _, space⟩
  · exact (Nat.ne_of_gt W_pos) zero
  · omega

/-- info: 'Solidity.Backend.Passes.AuditPrivateStack.heap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPrivateStack.heap
/-- info: 'Solidity.Backend.Passes.AuditPrivateStack.state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPrivateStack.state
/-- info: 'Solidity.Backend.Passes.AuditPrivateStack.allocator' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPrivateStack.allocator
/-- info: 'Solidity.Backend.Passes.AuditPrivateStack.positive_object_input' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPrivateStack.positive_object_input
/-- info: 'Solidity.Backend.Passes.AuditPrivateStack.positive_legacy_input' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPrivateStack.positive_legacy_input
/-- info: 'Solidity.Backend.Passes.AuditPrivateStack.joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPrivateStack.joint
/-- info: 'Solidity.Backend.Passes.AuditPrivateStack.transported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPrivateStack.transported
/-- info: 'Solidity.Backend.Passes.AuditPrivateStack.zero_inputs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPrivateStack.zero_inputs
/-- info: 'Solidity.Backend.Passes.AuditPrivateStack.full_cost_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPrivateStack.full_cost_refused
end Solidity.Backend.Passes.AuditPrivateStack
