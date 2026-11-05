import Solidity.Backend.MemoryCopies.RuntimeGrowth
import Solidity.Evm.MemoryObjectArrayExamples

/-! Actual nested defaults inhabit compiler growth and transport checked room
through two emitted statements. Room refusal is not a runtime panic theorem. -/
namespace Solidity.Backend.MemoryCopies.RuntimeGrowthControls
open Evm Evm.Memory
private def element : Ty := .ref (.array (.prim .uint))
private def dimensions : List Nat := [2,3]
private abbrev parent : RefTy := .array (.ref (nestedArrayType element dimensions))
private structure Input where
  contract : Contract
  context : Ctx
  frag : Frag context
  state : State contract context
  base : Nat → Fin W
  machine : Machine
  represented : Objects.StateRepr 1 1 8 frag state base machine
  allocator : Objects.AllocatorRepr state.heap base 8 ⟨40,by decide⟩ machine
private def input : Input := ⟨_,_,_,_,_,_,ObjectArrayExamples.initial_repr,ObjectArrayExamples.initial_allocator⟩
private def chosen (size : Fin W) (fits : 40 + runtimeNestedCost element dimensions size < W) :
    RuntimeNestedDefault element dimensions rfl size :=
  selectedRuntimeNestedDefault element dimensions rfl size ⟨_,_,_,8,⟨40,by decide⟩,_,input.allocator,fits⟩
private def first := Objects.referenceArrayCopy input.state.heap (nestedArrayType element dimensions) rfl (wmod 2)
private def state := (input.state.adopt first).1.push (t := .mem parent) (some first.val)
private def frag := input.frag.push (.mem parent) .ok
private def initialLength : Simple input.contract input.context .uint := .lit 2 rfl
private def nextLength (size : Fin W) : Simple input.contract (.mem parent :: input.context) .uint :=
  .lit (indexValue size).val (indexValue size).property
private def firstCode : List Instr :=
  Objects.referenceDeclareCode (chosen (wmod 2) (by decide)).child.code 1 initialLength
private def secondCode (size : Fin W) (fits : 40 + runtimeNestedCost element dimensions size < W) : List Instr :=
  Objects.referenceRebindCode (chosen size fits).child.code 1 .here (nextLength size)

theorem certificate_inhabited : AllocatorGrowthCertificate := allocatorGrowth

theorem cursor_determined (cursor : Fin W)
    (represented : Objects.AllocatorRepr input.state.heap input.base 8 cursor input.machine) :
    cursor = ⟨40,by decide⟩ := allocator_cursor_unique represented input.allocator

theorem declaration_growth :
    RuntimeGrowthExecution 1 1 8 31 frag input.state state input.base input.machine firstCode :=
  ((chosen (wmod 2) (by decide)).declare_growth input.represented input.allocator (by decide)
    initialLength rfl (by decide) rfl (by decide) (by decide)).2

theorem budget_transfer (size : Fin W) (fits : 71 + runtimeNestedCost element dimensions size < W) :
    ∃ base' middle, run firstCode input.machine = .ok middle 0 ∧
      Objects.StateRepr 1 1 8 frag state base' middle ∧
      Objects.GrowsAllocator 1 8 31 input.state input.base input.machine state base' middle ∧
      Objects.AllocationInput 1 8 (runtimeNestedCost element dimensions size) state base' middle ∧
      BaseExtends input.state.H input.base base' ∧ middle.stack = input.machine.stack :=
  declaration_growth.next_input (.inr ⟨by decide,⟨40,by decide⟩,input.allocator,by change 40 + (31 + runtimeNestedCost element dimensions size) < W; omega⟩)

theorem composed_growth (size : Fin W) (fits : 71 + runtimeNestedCost element dimensions size < W) :
    let second := Objects.referenceArrayCopy state.heap (nestedArrayType element dimensions) rfl size
    ∃ base' target,
      run (firstCode ++ secondCode size (by omega)) input.machine = .ok target 0 ∧
      Objects.GrowsAllocator 1 8 (31 + runtimeNestedCost element dimensions size)
        input.state input.base input.machine ((state.adopt second).1.setLocal .here (some second.val)) base' target ∧
      target.mem 0 = .val (wmod (71 + runtimeNestedCost element dimensions size)) ∧
      target.stack = input.machine.stack := by
  dsimp only
  obtain ⟨base1,middle,run1,represented1,growth1,budget,_,stack1⟩ := budget_transfer size fits
  have positiveCost : 0 < runtimeNestedCost element dimensions size := by
    unfold runtimeNestedCost
    omega
  rcases budget with zero | ⟨positive,cursor,allocator,room⟩
  · omega
  · obtain ⟨_,base2,target,run2,_,growth2,_,stack2⟩ :=
      (chosen size (by omega)).rebind_growth represented1 allocator positive .here (nextLength size)
        rfl (by decide) rfl room
    have growth : Objects.GrowsAllocator 1 8 (31 + runtimeNestedCost element dimensions size)
        input.state input.base input.machine
        ((state.adopt (Objects.referenceArrayCopy state.heap (nestedArrayType element dimensions) rfl size)).1.setLocal .here
          (some (Objects.referenceArrayCopy state.heap (nestedArrayType element dimensions) rfl size).val)) base2 target :=
      growth1.comp growth2
    have allocated : Objects.AllocatorRepr
        ((state.adopt (Objects.referenceArrayCopy state.heap (nestedArrayType element dimensions) rfl size)).1.setLocal .here
          (some (Objects.referenceArrayCopy state.heap (nestedArrayType element dimensions) rfl size).val)).heap
        base2 8 ⟨40 + (31 + runtimeNestedCost element dimensions size),by omega⟩ target :=
      growth ⟨40,by decide⟩ (by decide) input.allocator
        (by change 40 + (31 + runtimeNestedCost element dimensions size) < W; omega)
    refine ⟨base2,target,?_,growth,?_,stack2.trans stack1⟩
    · rw [run_append_ok run1]
      exact run2
    · simpa only [← Nat.add_assoc,wmod_of_lt fits] using allocated.free.cell

theorem empty_composition :
    ∃ target, run (firstCode ++ secondCode (wmod 0) (by decide)) input.machine = .ok target 0 ∧
      target.mem 0 = w[72] := by
  obtain ⟨_,target,ran,_,cursor,_⟩ := composed_growth (wmod 0) (by decide)
  exact ⟨target,ran,cursor⟩

theorem long_composition :
    ∃ target, run (firstCode ++ secondCode (wmod 64) (by decide)) input.machine = .ok target 0 ∧
      target.mem 0 = w[1032] := by
  obtain ⟨_,target,ran,_,cursor,_⟩ := composed_growth (wmod 64) (by decide)
  exact ⟨target,ran,cursor⟩

theorem wrong_growth_rejected {base' : Nat → Fin W} {target : Machine}
    (correct : Objects.GrowsAllocator 1 8 31 input.state input.base input.machine state base' target) :
    ¬ Objects.GrowsAllocator 1 8 30 input.state input.base input.machine state base' target := by
  intro wrong
  have impossible : (71 : Nat) = 70 := congrArg Fin.val
    (allocator_cursor_unique (correct ⟨40,by decide⟩ (by decide) input.allocator (by decide))
      (wrong ⟨40,by decide⟩ (by decide) input.allocator (by decide)))
  omega

theorem no_room : ¬ Objects.AllocationInput 1 8 W input.state input.base input.machine := by
  intro room
  have positive : 0 < W := by decide
  rcases room with zero | ⟨_,cursor,_,fits⟩ <;> omega

theorem skipped_code_rejected :
    ¬ ∃ target, run ([] : List Instr) input.machine = .ok target 0 ∧ target.mem 0 = w[72] := by
  rintro ⟨target,ran,cursor⟩
  cases ran
  have different : input.machine.mem 0 ≠ w[72] := by decide +kernel
  exact different cursor

#print axioms certificate_inhabited
#print axioms cursor_determined
#print axioms declaration_growth
#print axioms budget_transfer
#print axioms composed_growth
#print axioms empty_composition
#print axioms long_composition
#print axioms wrong_growth_rejected
#print axioms no_room
#print axioms skipped_code_rejected
end Solidity.Backend.MemoryCopies.RuntimeGrowthControls
