import Solidity.Backend.MemoryCopies.MemoryCopyDemand
import Solidity.Backend.MemoryCopies.AliasBinding
import Solidity.Evm.MemoryObjectArrayExamples

/-! Shared-HRef heaps, actual deep copies, real alias rebinding and its existing
compiled code. Sharing counts each copied edge, not only unique old objects. -/
namespace Solidity.Backend.MemoryCopies.MemoryCopyDemandControls
open Evm Evm.Memory

private abbrev Leaf : RefTy := .array (.prim .uint)
private abbrev Parent : RefTy := .fixed (.ref Leaf) 2
private abbrev H : HTy := [Leaf, Parent]
private def child : HRef H Leaf := ⟨0, rfl⟩
private def root : HRef H Parent := ⟨1, rfl⟩
private def seven : PrimTy.uint.Denote := ⟨7, by decide⟩
private def eleven : PrimTy.uint.Denote := ⟨11, by decide⟩
private def heap : Heap H := (⟨[seven, eleven], by decide⟩, (⟨[child, child], by decide⟩, ()))
private def snapshot := MVal.copyMToSt heap (T := .ref Parent) root
private def copied := snapshot.copyStToM heap rfl
private def again := (MVal.copyMToSt copied.heap (T := .ref Parent) copied.val).copyStToM copied.heap rfl

theorem initial_sharing :
    (MObj.elems .fixed (heap.get root)).map (fun reference => reference.id) = [0, 0] ∧
    heapWords heap = 5 ∧ liveWordCount snapshot = 8 := by decide +kernel

theorem certificates_inhabited : MemoryCopyDemandCertificate heap root rfl ∧ MemoryAliasDemandCertificate :=
  ⟨memoryCopyDemand heap root rfl, memoryAliasDemand⟩

theorem copied_children_are_distinct :
    (MObj.elems .fixed (copied.heap.get copied.val)).map (fun reference => reference.id) = [2, 3] ∧
    copied.val.id = 4 ∧ again.val.id = 7 := by decide +kernel

theorem actual_growth : heapWords copied.heap = 13 ∧ heapWords again.heap = 21 ∧
    liveWordCount (MVal.copyMToSt copied.heap (T := .ref Parent) copied.val) = 8 := by decide +kernel

theorem old_cells_and_contents :
    Evm.Memory.Objects.cells copied.heap (child.wk copied.ext) = Evm.Memory.Objects.cells heap child ∧
    (MObj.elems .dyn (copied.heap.get (child.wk copied.ext))).map (fun value => value.val) = [7, 11] :=
  ⟨copy_old_cells snapshot rfl heap child, by decide +kernel⟩

theorem wrong_unique_child_demand : liveWordCount snapshot ≠ 5 ∧
    (MObj.elems .fixed (copied.heap.get copied.val)).map (fun reference => reference.id) ≠ [2, 2] := by
  rw [initial_sharing.2.2, copied_children_are_distinct.1]
  decide

private abbrev EmptyParent : RefTy := .fixed (.ref Leaf) 0
private abbrev EmptyH : HTy := [Leaf, EmptyParent]
private def emptyRoot : HRef EmptyH EmptyParent := ⟨1, rfl⟩
private def emptyHeap : Heap EmptyH := (⟨[seven, eleven], by decide⟩, (⟨[], rfl⟩, ()))
private def emptySnapshot := MVal.copyMToSt emptyHeap (T := .ref EmptyParent) emptyRoot

theorem empty_parent_demand : liveWordCount emptySnapshot = 1 ∧
    heapWords (emptySnapshot.copyStToM emptyHeap rfl).heap = 5 ∧
    (emptySnapshot.copyStToM emptyHeap rfl).val.id = 2 := by decide +kernel

private abbrev LongParent : RefTy := .fixed (.ref Leaf) 64
private abbrev LongH : HTy := [Leaf, LongParent]
private def longChild : HRef LongH Leaf := ⟨0, rfl⟩
private def longRoot : HRef LongH LongParent := ⟨1, rfl⟩
private def longHeap : Heap LongH := (⟨[seven, eleven], by decide⟩,
  (⟨List.replicate 64 longChild, List.length_replicate⟩, ()))
private def longSnapshot := MVal.copyMToSt longHeap (T := .ref LongParent) longRoot

theorem long_shared_demand : liveWordCount longSnapshot = 256 ∧
    heapWords (longSnapshot.copyStToM longHeap rfl).heap = 323 := by
  have demand : liveWordCount longSnapshot = 256 := by decide +kernel
  have before : heapWords longHeap = 67 := by decide +kernel
  refine ⟨demand, ?_⟩
  rw [valueCopy_words, demand, before]

private structure AliasInput where
  contract : Contract
  context : Ctx
  frag : Frag context
  state : State contract context
  base : Nat → Fin W
  machine : Machine
  represented : Evm.Memory.Objects.StateRepr 1 1 8 frag state base machine
  allocator : Evm.Memory.Objects.AllocatorRepr state.heap base 8 (wmod 40) machine
  parent : Idx context (.mem Parent)
  destination : Idx context (.mem Leaf)
private def aliasInput : AliasInput :=
  ⟨_, _, _, _, _, _, ObjectArrayExamples.initial_repr, ObjectArrayExamples.initial_allocator,
    .here, .there (.there .here)⟩
private def path : MPath aliasInput.contract aliasInput.context (.ref Leaf) :=
  .loc (.index .fixed (.var aliasInput.parent rfl) (.simple (.lit 0 rfl)))
private def reference : HRef aliasInput.state.H Leaf := ⟨0, rfl⟩
private def selected : SelectedAlias 1 aliasInput.frag path := selectedAlias 1 aliasInput.frag path rfl
private theorem resolved : path.mvalT aliasInput.state = .ok reference := by with_unfolding_all rfl
private def aliasObserve (result : TRes (Solidity.Out aliasInput.contract aliasInput.state.H aliasInput.context)) :
    Option (Nat × Nat) := do
  let out ← result.toOption
  let reference ← TEnv.get aliasInput.destination out.st.env
  pure (reference.id, heapWords out.st.heap)
private def targetObserve : Evm.Out → Option (Nat × Nat × List Word)
  | .ok machine _ => match machine.mem 0, machine.mem 1 with
    | .val cursor, .val bound => some (cursor.val, bound.val, machine.stack)
    | _, _ => none
  | _ => none

theorem actual_alias_zero_growth :
    TRun.rebindMem aliasInput.destination (.alias path) aliasInput.state =
      .ok ⟨aliasInput.state.setLocal aliasInput.destination (some reference), List.prefix_refl _⟩ ∧
    heapWords (aliasInput.state.setLocal aliasInput.destination (some reference)).heap =
      heapWords aliasInput.state.heap :=
  alias_rebind_words aliasInput.state path aliasInput.destination reference resolved

theorem alias_observations : heapWords aliasInput.state.heap = 6 ∧
    aliasObserve (TRun.rebindMem aliasInput.destination (.alias path) aliasInput.state) = some (0, 6) ∧
    targetObserve (run (selected.code aliasInput.destination) aliasInput.machine) = some (40, 16, [w[77]]) := by
  decide +kernel

theorem compiled_alias_contract :
    AliasBindingOutcome 1 1 8 aliasInput.frag aliasInput.state aliasInput.base aliasInput.machine
      path aliasInput.destination (selected.code aliasInput.destination) :=
  selected.execute aliasInput.represented aliasInput.destination

theorem alias_is_not_deep_growth :
    let value := MVal.copyMToSt aliasInput.state.heap (T := .ref Leaf) reference
    heapWords (value.copyStToM aliasInput.state.heap rfl).heap = 8 ∧
    heapWords (value.copyStToM aliasInput.state.heap rfl).heap ≠ heapWords aliasInput.state.heap := by
  decide +kernel

#print axioms initial_sharing
#print axioms certificates_inhabited
#print axioms copied_children_are_distinct
#print axioms actual_growth
#print axioms old_cells_and_contents
#print axioms wrong_unique_child_demand
#print axioms empty_parent_demand
#print axioms long_shared_demand
#print axioms actual_alias_zero_growth
#print axioms alias_observations
#print axioms compiled_alias_contract
#print axioms alias_is_not_deep_growth
end Solidity.Backend.MemoryCopies.MemoryCopyDemandControls
