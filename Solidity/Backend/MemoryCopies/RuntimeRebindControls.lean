import Solidity.Backend.MemoryCopies.RuntimeRebind
import Solidity.Evm.MemoryObjectArrayExamples

/-! Two actual allocating executions, retaining the replaced parent object. -/
namespace Solidity.Backend.MemoryCopies.RuntimeRebindControls
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
private def input : Input :=
  ⟨_,_,_,_,_,_,ObjectArrayExamples.initial_repr,ObjectArrayExamples.initial_allocator⟩
private def chosen (size : Fin W) (fits : 40 + runtimeNestedCost element dimensions size < W) :
    RuntimeNestedDefault element dimensions rfl size :=
  selectedRuntimeNestedDefault element dimensions rfl size ⟨_,_,_,8,⟨40,by decide⟩,_,input.allocator,fits⟩
private def first := Objects.referenceArrayCopy input.state.heap (nestedArrayType element dimensions) rfl (wmod 2)
private def state := (input.state.adopt first).1.push (t := .mem parent) (some first.val)
private def initialLength : Simple input.contract input.context .uint := .lit 2 rfl
private def nextLength (size : Fin W) : Simple input.contract (.mem parent :: input.context) .uint :=
  .lit (indexValue size).val (indexValue size).property

/-- Both source statements and both emitted runs are derived on a populated
input. The replaced parent remains readable through its old identity. -/
theorem two_steps (size : Fin W) (fits : 71 + runtimeNestedCost element dimensions size < W) :
    let second := Objects.referenceArrayCopy state.heap (nestedArrayType element dimensions) rfl size
    ∃ intermediate target,
      TRun.declMem parent (some (.newArr initialLength (by decide))) (by decide) input.state =
        .ok ⟨state,first.ext⟩ ∧
      run (Objects.referenceDeclareCode (chosen (wmod 2) (by decide)).child.code 1 initialLength)
        input.machine = .ok intermediate 0 ∧
      TRun.rebindMem (.here : Idx (.mem parent :: input.context) (.mem parent))
        (.newArr (nextLength size) (by decide)) state =
        .ok ⟨(state.adopt second).1.setLocal .here (some second.val),second.ext⟩ ∧
      run (Objects.referenceRebindCode
        (chosen size (by omega)).child.code 1 .here (nextLength size))
        intermediate = .ok target 0 ∧
      target.mem 0 = .val ⟨71 + runtimeNestedCost element dimensions size,fits⟩ ∧
      target.stack = input.machine.stack ∧
      second.heap.get (first.val.wk second.ext) = MObj.wk second.ext parent (state.heap.get first.val) ∧
      (first.val.wk second.ext).id ≠ second.val.id := by
  dsimp only
  obtain ⟨base1,middle,source1,execution1,represented1,allocator1,_,stack1⟩ :=
    (chosen (wmod 2) (by decide)).declare_correct input.represented input.allocator (by decide)
      initialLength (by decide) (by decide) rfl (by decide) (by decide)
  have fits40 : 40 + runtimeNestedCost element dimensions size < W := by omega
  obtain ⟨base2,target,source2,execution2,_,allocator2,_,stack2,keeps,fresh⟩ :=
    (chosen size fits40).rebind_correct represented1 allocator1 (by decide)
      .here (nextLength size) rfl (by decide) rfl fits
  exact ⟨middle,target,source1,execution1,source2,execution2,allocator2.free.cell,
    stack2.trans stack1,keeps first.val,fresh first.val⟩

/-- Empty replacement still allocates one fresh header and retains old content. -/
theorem empty_replacement :
    ∃ intermediate target,
      run (Objects.referenceDeclareCode (chosen (wmod 2) (by decide)).child.code 1 initialLength)
        input.machine = .ok intermediate 0 ∧
      run (Objects.referenceRebindCode (chosen (wmod 0) (by decide)).child.code 1 .here
        (nextLength (wmod 0))) intermediate = .ok target 0 ∧ target.mem 0 = w[72] := by
  obtain ⟨middle,target,_,firstRun,_,secondRun,cursor,_,_,_⟩ := two_steps (wmod 0) (by decide)
  exact ⟨middle,target,firstRun,secondRun,cursor⟩

private def code (size : Fin W) (fits : 71 + runtimeNestedCost element dimensions size < W) : List Instr :=
  Objects.referenceDeclareCode (chosen (wmod 2) (by decide)).child.code 1 initialLength ++
    Objects.referenceRebindCode (chosen size (by omega)).child.code 1 .here (nextLength size)
private def observe : Evm.Out → Option Word
  | .ok target _ => some (target.mem 0)
  | _ => none

/-- A single composed instruction list has the same exact allocation cursor. -/
theorem combined_cursor (size : Fin W) (fits : 71 + runtimeNestedCost element dimensions size < W) :
    observe (run (code size fits) input.machine) =
      some (.val ⟨71 + runtimeNestedCost element dimensions size,fits⟩) := by
  obtain ⟨middle,target,_,firstRun,_,secondRun,cursor,_,_,_⟩ := two_steps size fits
  rw [code,run_append_ok firstRun,secondRun]
  exact congrArg some cursor

theorem long_replacement :
    observe (run (code (wmod 64) (by decide)) input.machine) = some w[1032] :=
  combined_cursor (wmod 64) (by decide)

/-- Omitting the fresh empty header cannot satisfy the actual composed run. -/
theorem wrong_cursor_rejected :
    observe (run (code (wmod 0) (by decide)) input.machine) ≠ some w[71] := by
  rw [combined_cursor]
  decide

theorem skipped_code_rejected :
    observe (run ([] : List Instr) input.machine) ≠
      observe (run (code (wmod 0) (by decide)) input.machine) := by
  rw [combined_cursor]
  decide +kernel

#print axioms two_steps
#print axioms empty_replacement
#print axioms combined_cursor
#print axioms long_replacement
#print axioms wrong_cursor_rejected
#print axioms skipped_code_rejected
end Solidity.Backend.MemoryCopies.RuntimeRebindControls
