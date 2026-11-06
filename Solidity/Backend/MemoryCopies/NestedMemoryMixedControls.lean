import Solidity.Backend.MemoryCopies.NestedMemoryLoop
import Solidity.Backend.MemoryCopies.NestedStorageHeaderControls

/-! An actual mixed-length source is supplied by the existing storage producer.
The memory consumer derives its rows, reserves a separate parent and retains
all earlier source payloads. This does not supply Source or physical adequacy. -/
namespace Solidity.Backend.MemoryCopies.NestedMemoryMixedControls
open Evm Evm.Memory
private def values (payloads : List (Fin W)) : List PrimTy.uint.Denote := payloads.map indexValue
private def row (payloads : List (Fin W)) (bounded : payloads.length < W) : PrimitiveStorageRow .uint :=
  ⟨values payloads, by rw [values, List.length_map]; exact bounded⟩
private def long : List (Fin W) := List.ofFn (fun i : Fin 64 => wmod (i.val + 1))
private def rows : List (PrimitiveStorageRow .uint) :=
  [row [wmod 11,wmod 23] (by decide), row [] (by decide), row long (by rw [long, List.length_ofFn]; decide)]
private def expected : SVal (.ref (.array (.ref (.array (.prim .uint))))) := nestedStorageParentValue .uint rows (by decide)

structure MixedRuntimeWitness where
  H : HTy
  heap : Heap H
  source : HRef H (.array (.ref (.array (.prim .uint))))
  base : Nat → Fin W
  before : Machine
  target : Machine
  sourceCount : heap.len source .dyn = 3
  sourceSnapshot : MVal.copyMToSt heap (T := .ref (.array (.ref (.array (.prim .uint))))) source = expected.strip
  sourceRoot : base source.id = wmod 40
  allocator : Objects.AllocatorRepr heap base 8 (wmod 113) before
  ran : run (nestedMemoryLoopCode .uint)
    (nestedMemoryControl (allocateMachine before (wmod 113) (wmod 3)) (wmod 40) (wmod 113) (wmod 3) (wmod 0)) =
    .ok (nestedMemoryControl target (wmod 40) (wmod 113) (wmod 3) (wmod 3)) 0
  pointers : ∃ left middle right : Fin W,
    target.mem 114 = .val left ∧ target.mem 115 = .val middle ∧ target.mem 116 = .val right
  payloads : target.mem 45 = w[11] ∧ target.mem 46 = w[23] ∧ target.mem 49 = w[1] ∧ target.mem 112 = w[64]
  copyFits : (wmod 117).val + nestedStorageDemand (memoryChildRows heap .uint source) < W
  finalBase : Nat → Fin W
  destinationAllocator : Objects.AllocatorRepr
    ((nestedStorageValues .uint (memoryChildRows heap .uint source)).copyStToM heap rfl).heap finalBase 8
    ⟨(wmod 117).val + nestedStorageDemand (memoryChildRows heap .uint source), copyFits⟩ target
  destinationContents : ∀ offset reference,
    ((nestedStorageValues .uint (memoryChildRows heap .uint source)).copyStToM heap rfl).val.1[offset]? = some reference →
    target.mem (114 + offset) = .val (finalBase reference.id)
  destinationFresh : TraversalFreshCertificate heap (nestedStorageValues .uint (memoryChildRows heap .uint source)) rfl

private theorem consume_mixed {H : HTy} (hp : Heap H)
    (source : HRef H (.array (.ref (.array (.prim .uint))))) (base : Nat → Fin W) (before : Machine)
    (allocated : Objects.AllocatorRepr hp base 8 (wmod 113) before)
    (sourceCount : hp.len source .dyn = 3) (sourceRoot : base source.id = wmod 40)
    (sourceSnapshot : MVal.copyMToSt hp (T := .ref (.array (.ref (.array (.prim .uint))))) source = expected.strip)
    (words : before.mem 45 = w[11] ∧ before.mem 46 = w[23] ∧ before.mem 49 = w[1] ∧ before.mem 112 = w[64]) :
    Nonempty MixedRuntimeWitness := by
  have reservation : Objects.AllocatorRepr hp base 8 (wmod 117)
      (allocateMachine before (wmod 113) (wmod 3)) ∧ Objects.Gap hp base 113 117 :=
    allocated.reserveArray (wmod 3) (by decide)
  have gap : Objects.Gap hp base 113 117 := reservation.2
  have demand : nestedStorageDemand (memoryChildRows hp .uint source) ≤ 113 * 3 := by
    simpa only [sourceCount] using memory_rows_demand_bound hp .uint source base 8 (wmod 113) before allocated
  have copyFits : (wmod 117).val + nestedStorageDemand (memoryChildRows hp .uint source) < W := by
    change 117 + nestedStorageDemand (memoryChildRows hp .uint source) < W
    have large : 1024 < W := by decide
    omega
  obtain ⟨base2, target, iteration, ran, finalAllocator, finalExtension, finalGap, contents, targetShape, below,
    gaps, keeps, freshChildren, retained⟩ := nested_memory_loop_success hp .uint
      (memoryChildRows hp .uint source) base 8 (wmod 117)
      (allocateMachine before (wmod 113) (wmod 3)) source (wmod 113) (wmod 3) (wmod 0)
      reservation.1 gap (by decide) (by decide)
      (by change 0 + (memoryChildRows hp .uint source).length = 3; rw [Nat.zero_add, memory_rows_length, sourceCount])
      (memory_rows_repr _ _ _) copyFits
  let copied := (nestedStorageValues .uint (memoryChildRows hp .uint source)).copyStToM hp rfl
  have vectorLength : copied.val.1.length = 3 := copied.val.property.trans ((memory_rows_length _ _ _).trans sourceCount)
  let left : HRef copied.H' (.array (.prim .uint)) := copied.val.1[0]'(by rw [vectorLength]; decide)
  let middle : HRef copied.H' (.array (.prim .uint)) := copied.val.1[1]'(by rw [vectorLength]; decide)
  let right : HRef copied.H' (.array (.prim .uint)) := copied.val.1[2]'(by rw [vectorLength]; decide)
  have pointer0 : target.mem 114 = .val (base2 left.id) := contents 0 left (List.getElem?_eq_getElem _)
  have pointer1 : target.mem 115 = .val (base2 middle.id) := contents 1 middle (List.getElem?_eq_getElem _)
  have pointer2 : target.mem 116 = .val (base2 right.id) := contents 2 right (List.getElem?_eq_getElem _)
  rw [sourceRoot] at ran
  have preserved : ∀ address, 0 < address → address < 113 → target.mem address = before.mem address := by
    intro address positive lower
    exact (below address positive (by change address < 117; omega) (.inl (by change address < 114; omega))).trans
      (allocateMachine_other _ _ _ _ (by change address ≠ 113; omega) (by omega))
  refine ⟨⟨_, hp, source, base, before, target, sourceCount, sourceSnapshot, sourceRoot, allocated, ran,
    ⟨_, _, _, pointer0, pointer1, pointer2⟩, ?_, copyFits, base2, finalAllocator, ?_, freshChildren⟩⟩
  · rw [preserved 45 (by decide) (by decide), preserved 46 (by decide) (by decide),
      preserved 49 (by decide) (by decide), preserved 112 (by decide) (by decide)]
    exact words
  · intro offset reference chosen
    exact contents offset reference chosen

private theorem mixed_from_header {H : HTy} {heap : Heap H} {entries : List (PrimitiveStorageRow .uint)}
    {bounded : entries.length < W} {shadow : SList (.ref (.array (.prim .uint)))} {base : Nat → Fin W}
    {machine : Machine} {slot : Slot} {fits : (wmod 40).val + nestedStorageParentDemand entries < W}
    (produced : NestedStorageHeaderResult heap .uint entries bounded shadow base 8 (wmod 40) machine slot fits)
    (count : entries.length = 3) (cost : nestedStorageParentDemand entries = 73)
    (shape : nestedStorageParentValue .uint entries bounded = expected)
    (physical : ∃ known : Machine, run nestedStorageHeaderCode (machine.push (.slot slot)) = .ok (known.push w[40]) 0 ∧
      known.mem 45 = w[11] ∧ known.mem 46 = w[23] ∧ known.mem 49 = w[1] ∧ known.mem 112 = w[64]) :
    Nonempty MixedRuntimeWitness := by
  obtain ⟨base1, before, headerRun, allocated, root, extension, machineShape, oldCells, oldGaps, oldKeeps,
    fresh, length, mirror, shadowCopy⟩ := produced
  let sourceCopy := (nestedStorageParentValue .uint entries bounded).copyStToM heap rfl
  have sourceCount : sourceCopy.heap.len sourceCopy.val .dyn = 3 := length.trans count
  have cursorEq : (⟨(wmod 40).val + nestedStorageParentDemand entries, fits⟩ : Fin W) = wmod 113 := by
    apply Fin.ext
    change 40 + nestedStorageParentDemand entries = 113
    rw [cost]
  rw [cursorEq] at allocated
  have sourceRoot : base1 sourceCopy.val.id = wmod 40 := root
  obtain ⟨known, knownRun, word0, word1, word2, word3⟩ := physical
  rw [headerRun] at knownRun
  have sameMemory : before.mem = known.mem := by
    have pushed : (before.push w[40]).mem = (known.push w[40]).mem := congrArg Machine.mem (Out.ok.inj knownRun).1
    exact pushed
  apply consume_mixed sourceCopy.heap sourceCopy.val base1 before allocated sourceCount sourceRoot
    (mirror.trans (congrArg SVal.strip shape))
  rw [sameMemory]
  exact ⟨word0, word1, word2, word3⟩

theorem mixed_runtime : Nonempty MixedRuntimeWitness := by
  obtain ⟨fits, produced⟩ := NestedStorageHeaderControls.actual_typed
    [⟨[wmod 11,wmod 23], by decide⟩, ⟨[], by decide⟩, ⟨long, by rw [long, List.length_ofFn]; decide⟩] (by decide) .nil
  apply mixed_from_header produced rfl (by decide +kernel) rfl
  obtain ⟨known, ran, _, _, _, _, word0, word1, word2, word3⟩ := NestedStorageHeaderControls.mixed_runtime
  exact ⟨known, ran, word0, word1, word2, word3⟩

#print axioms mixed_runtime
end Solidity.Backend.MemoryCopies.NestedMemoryMixedControls
