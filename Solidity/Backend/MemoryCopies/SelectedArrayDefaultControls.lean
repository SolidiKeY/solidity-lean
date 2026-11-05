import Solidity.Backend.MemoryCopies.SelectedArrayDefaults
import Solidity.Evm.MemoryObjectArrayExamples

/-! Actual selected emitted arrays of structs and fixed arrays of structs. -/
namespace Solidity.Backend.MemoryCopies.SelectedArrayDefaultControls
open Evm Evm.Memory
private def root : RefTy := .struct "Pair"
private theorem memory (dimensions : List Nat) : (Ty.ref (fixedDefaultType root dimensions)).mapFree = true :=
  (fixedDefault_mapFree root dimensions).trans (by decide)
private theorem available (proof : (Ty.ref root).mapFree = true) :
    (ReferenceDefaults.compileDefault root proof).isSome = true :=
  primitive_struct_selected "Pair" (by decide) proof
private def feasible {cost : Nat} (fits : 40 + cost < W) : V2.AllocatorWitness cost :=
  ⟨_,_,_,8,⟨40,by decide⟩,_,ObjectArrayExamples.initial_allocator,fits⟩
private def machine : Machine := (feasible (cost := 1) (by decide)).machine
private def compiled (dimensions : List Nat) (size : Fin W)
    (fits : 40 + selectedArrayCost root dimensions size < W) :
    SelectedArrayDefault root dimensions (memory dimensions) size :=
  selectedArrayDefault root dimensions (memory dimensions) size available (feasible fits)
private def observe : Evm.Out → Option (Nat × Nat × Nat)
  | .ok target _ => match target.stack,target.mem 0,target.mem 17 with
    | .val parent :: _,.val next,.val old => some (parent.val,next.val,old.val)
    | _,_,_ => none
  | _ => none

theorem actual_selection (dimensions : List Nat) (size : Fin W)
    (fits : 40 + selectedArrayCost root dimensions size < W) :
    ReferenceDefaults.compileDefault (fixedDefaultType root dimensions) (memory dimensions) =
      some (compiled dimensions size fits).child := (compiled dimensions size fits).selected

theorem runtime_observation (dimensions : List Nat) (size : Fin W)
    (fits : 40 + selectedArrayCost root dimensions size < W) :
    observe (run (compiled dimensions size fits).code (machine.push (.val size))) =
      some (40,40 + selectedArrayCost root dimensions size,7) := by
  let chosen : SelectedArrayDefault root dimensions (memory dimensions) size := compiled dimensions size fits
  let input : V2.AllocatorWitness (selectedArrayCost root dimensions size) := chosen.feasible
  obtain ⟨base,target,execution,represented,_,_,_,preserved,_⟩ :=
    chosen.execute input.heap input.base input.frame input.cursor input.machine input.represented input.fits
  change observe (run chosen.code (input.machine.push (.val size))) = _
  rw [execution]
  simp only [observe,Machine.push]
  rw [represented.free.cell,preserved 17 (by decide) (by change 17 < 40; decide)]
  rfl

theorem array_of_structs :
    observe (run (compiled [] (wmod 2) (by decide)).code (machine.push (.val (wmod 2)))) =
      some (40,47,7) := runtime_observation [] (wmod 2) (by decide)

theorem array_of_fixed_structs :
    observe (run (compiled [2] (wmod 2) (by decide)).code (machine.push (.val (wmod 2)))) =
      some (40,55,7) := runtime_observation [2] (wmod 2) (by decide)

theorem long_parent :
    observe (run (compiled [2] (wmod 64) (by decide)).code (machine.push (.val (wmod 64)))) =
      some (40,489,7) := runtime_observation [2] (wmod 64) (by decide)

theorem empty_parent :
    observe (run (compiled [2] (wmod 0) (by decide)).code (machine.push (.val (wmod 0)))) =
      some (40,41,7) := runtime_observation [2] (wmod 0) (by decide)

theorem empty_any_dimensions (dimensions : List Nat) :
    Nonempty (SelectedArrayDefault root dimensions (memory dimensions) (wmod 0)) :=
  ⟨compiled dimensions (wmod 0) (by rw [selectedArrayCost_zero]; decide)⟩

theorem same_code_different_lengths :
    (compiled [2] (wmod 0) (by decide)).code = (compiled [2] (wmod 2) (by decide)).code :=
  (compiled [2] (wmod 0) (by decide)).code_size_independent (compiled [2] (wmod 2) (by decide))

theorem wrong_cursor_rejected :
    observe (run (compiled [2] (wmod 2) (by decide)).code (machine.push (.val (wmod 2)))) ≠ some (40,54,7) := by
  rw [array_of_fixed_structs]
  decide

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
  ⟨_,_,_,_,_,_,ObjectArrayExamples.initial_repr,ObjectArrayExamples.initial_allocator⟩
private def length : Simple declarationInput.contract declarationInput.context .uint := .lit 2 rfl
private def grown := Objects.referenceArrayCopy declarationInput.state.heap (fixedDefaultType root [2]) (memory [2]) (wmod 2)

theorem source_nested_identities :
    (MObj.elems .dyn (grown.heap.get grown.val)).map (fun reference => reference.id) = [5,8] ∧
      (MObj.elems .dyn (grown.heap.get grown.val)).map (fun reference =>
        (MObj.elems .fixed (grown.heap.get reference)).map (fun child => child.id)) = [[3,4],[6,7]] := by decide +kernel

theorem source_struct_defaults :
    (MObj.elems .dyn (grown.heap.get grown.val)).map
      (fun (reference : HRef grown.H' (.fixed (.ref (.struct "Pair")) 2)) =>
      (MObj.elems .fixed (grown.heap.get reference)).map (fun (child : HRef grown.H' (.struct "Pair")) =>
        ((show PrimTy.uint.Denote from MFields.get (T := .prim .uint) (Semantics.structDef "Pair")
          (grown.heap.get child) (f := "a") (by decide)).val,
         (show PrimTy.uint.Denote from MFields.get (T := .prim .uint) (Semantics.structDef "Pair")
          (grown.heap.get child) (f := "b") (by decide)).val))) =
      [[(0,0),(0,0)],[(0,0),(0,0)]] := by decide +kernel

theorem declaration_execution :
    let input := declarationInput
    let chosen := compiled [2] (wmod 2) (by decide)
    ∃ target, TRun.declMem (.array (.ref (fixedDefaultType root [2])))
      (some (.newArr length (by decide))) (by decide) input.state =
        .ok ⟨(input.state.adopt grown).1.push
          (t := .mem (.array (.ref (fixedDefaultType root [2])))) (some grown.val),grown.ext⟩ ∧
      run (Objects.referenceDeclareCode chosen.child.code 1 length) input.target = .ok target 0 ∧
      target.mem 0 = w[55] ∧ target.stack = input.target.stack := by
  dsimp only
  obtain ⟨base,target,source,execution,_,allocator,_,stack⟩ :=
    (compiled [2] (wmod 2) (by decide)).declare_correct declarationInput.represented
      declarationInput.allocator (by decide) length (by decide) (by decide) rfl (by decide) (by decide)
  exact ⟨target,source,execution,allocator.free.cell,stack⟩

#print axioms actual_selection
#print axioms runtime_observation
#print axioms array_of_structs
#print axioms array_of_fixed_structs
#print axioms long_parent
#print axioms empty_parent
#print axioms empty_any_dimensions
#print axioms same_code_different_lengths
#print axioms wrong_cursor_rejected
#print axioms source_nested_identities
#print axioms source_struct_defaults
#print axioms declaration_execution
end Solidity.Backend.MemoryCopies.SelectedArrayDefaultControls
