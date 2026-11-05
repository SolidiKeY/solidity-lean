import Solidity.Backend.MemoryCopies.RuntimeArrays
import Solidity.Evm.MemoryObjectArrayExamples

/-! Actual runtime-size executions over populated ownership. The structured
loop semantics are used through checked simulation, never evaluated as code. -/
namespace Solidity.Backend.MemoryCopies.RuntimeArrayControls
open Evm Evm.Memory
private def element : Ty := .ref (.array (.prim .uint))
private def dimensions : List Nat := [2,3]
private def feasible {cost : Nat} (fits : 40 + cost < W) : V2.AllocatorWitness cost :=
  ⟨_, _, _, 8, ⟨40, by decide⟩, _, ObjectArrayExamples.initial_allocator, fits⟩
private def machine : Machine := (feasible (cost := 1) (by decide)).machine
private def compiled (size : Fin W) (fits : 40 + runtimeNestedCost element dimensions size < W) :
    RuntimeNestedDefault element dimensions rfl size :=
  selectedRuntimeNestedDefault element dimensions rfl size (feasible fits)
private def observe : Evm.Out → Option (Nat × Nat × Nat)
  | .ok target _ => match target.stack, target.mem 0, target.mem 17 with
    | .val root :: _, .val next, .val old => some (root.val, next.val, old.val)
    | _, _, _ => none
  | _ => none

theorem runtime_observation (size : Fin W) (fits : 40 + runtimeNestedCost element dimensions size < W) :
    observe (run (compiled size fits).code (machine.push (.val size))) =
      some (40,40 + runtimeNestedCost element dimensions size,7) := by
  let chosen : RuntimeNestedDefault element dimensions rfl size := compiled size fits
  let input : V2.AllocatorWitness (runtimeNestedCost element dimensions size) := chosen.feasible
  obtain ⟨base, target, execution, represented, _, _, _, preserved, _⟩ :=
    chosen.execute input.heap input.base input.frame input.cursor input.machine input.represented input.fits
  change observe (run chosen.code (input.machine.push (.val size))) = _
  rw [execution]
  simp only [observe, Machine.push]
  rw [represented.free.cell, preserved 17 (by decide) (by change 17 < 40; decide)]
  rfl

theorem empty_parent :
    observe (run (compiled (wmod 0) (by decide)).code (machine.push (.val (wmod 0)))) =
      some (40,41,7) := runtime_observation (wmod 0) (by decide)

theorem two_nested_children :
    observe (run (compiled (wmod 2) (by decide)).code (machine.push (.val (wmod 2)))) =
      some (40,71,7) := runtime_observation (wmod 2) (by decide)

theorem long_parent :
    observe (run (compiled (wmod 64) (by decide)).code (machine.push (.val (wmod 64)))) =
      some (40,1001,7) := runtime_observation (wmod 64) (by decide)

theorem same_code_different_lengths :
    (compiled (wmod 0) (by decide)).code = (compiled (wmod 2) (by decide)).code :=
  (compiled (wmod 0) (by decide)).code_size_independent (compiled (wmod 2) (by decide))

theorem empty_any_child (dims : List Nat) :
    Nonempty (RuntimeNestedDefault element dims (nested_mapFree element dims) (wmod 0)) :=
  ⟨emptyRuntimeNestedDefault element dims (nested_mapFree element dims) (feasible (by decide))⟩

theorem wrong_cursor_rejected :
    observe (run (compiled (wmod 2) (by decide)).code (machine.push (.val (wmod 2)))) ≠
      some (40,70,7) := by
  rw [two_nested_children]
  decide

/-- A package of actual existing represented scoped-state inputs, not desired
source or target outcomes. Private fixture indices are inferred from proofs. -/
private structure DeclarationInput where
  contract : Contract
  context : Ctx
  frag : Frag context
  state : State contract context
  base : Nat → Fin W
  target : Machine
  represented : Objects.StateRepr 1 1 8 frag state base target
  allocator : Objects.AllocatorRepr state.heap base 8 ⟨40,by decide⟩ target
private def declarationInput : DeclarationInput :=
  ⟨_,_,_,_,_,_, ObjectArrayExamples.initial_repr, ObjectArrayExamples.initial_allocator⟩
private def length : Simple declarationInput.contract declarationInput.context .uint := .lit 2 rfl

/-- Actual declaration success, actual emitted execution, reached allocation
cursor and caller stack preservation are all inhabited on a populated input. -/
theorem declaration_execution :
    let input := declarationInput
    let chosen := compiled (wmod 2) (by decide)
    let grown := Objects.referenceArrayCopy input.state.heap
      (nestedArrayType element dimensions) rfl (wmod 2)
    ∃ target, TRun.declMem (.array (.ref (nestedArrayType element dimensions)))
      (some (.newArr length (by decide))) (by decide) input.state =
        .ok ⟨(input.state.adopt grown).1.push
          (t := .mem (.array (.ref (nestedArrayType element dimensions)))) (some grown.val),grown.ext⟩ ∧
      run (Objects.referenceDeclareCode chosen.child.code 1 length) input.target = .ok target 0 ∧
      target.mem 0 = w[71] ∧ target.stack = input.target.stack := by
  dsimp only
  obtain ⟨base, target, source, execution, _, allocator, _, stack⟩ :=
    (compiled (wmod 2) (by decide)).declare_correct declarationInput.represented
      declarationInput.allocator (by decide) length (by decide) (by decide) rfl (by decide) (by decide)
  exact ⟨target, source, execution, allocator.free.cell, stack⟩

#print axioms runtime_observation
#print axioms empty_parent
#print axioms two_nested_children
#print axioms long_parent
#print axioms same_code_different_lengths
#print axioms empty_any_child
#print axioms wrong_cursor_rejected
#print axioms declaration_execution
end Solidity.Backend.MemoryCopies.RuntimeArrayControls
