import Solidity.Evm.MemoryAlloc

/-! Actual repeated allocations from an inhabited allocator state, with a
reserved local cell, distinct typed identities and an empty second array. -/
namespace Solidity.Evm.Memory.AllocExamples

private def cursor : Fin W := ⟨16, by decide⟩
private def nextCursor : Fin W := ⟨19, by decide⟩
private def machine : Machine :=
  { Machine.init with mem := fun addr =>
      if addr = 0 then w[16] else if addr = 2 then w[99] else w[0] }
private def bases : Nat → Fin W := fun _ => ⟨0, W_pos⟩

/-- The allocator assumptions have a concrete witness and reserve an actual local. -/
theorem initial_repr : AllocatorRepr (H := []) () bases 4 cursor machine := by
  have hn {p : PrimTy} (r : HRef [] (.array (.prim p))) : False := by
    simpa only [List.getElem?_nil, reduceCtorEq] using r.get?
  refine ⟨⟨fun r => (hn r).elim, fun r => (hn r).elim, fun r _ _ => (hn r).elim⟩,
    ?_, fun r => (hn r).elim⟩
  refine ⟨by decide, by decide, rfl, ?_⟩
  intro addr ha
  change 16 ≤ addr at ha
  simp only [machine]
  split <;> rename_i he
  · omega
  · split <;> rename_i he
    · omega
    · rfl

private def heap1 : Heap [.array (.prim .uint)] :=
  (Heap.alloc (H := []) () (defaultArray .uint ⟨2, by decide⟩)).1
private def machine1 : Machine := allocateMachine machine cursor ⟨2, by decide⟩
private def bases1 : Nat → Fin W := upd bases 0 cursor
private def ref1 : HRef [.array (.prim .uint)] (.array (.prim .uint)) := ⟨0, rfl⟩
private def heapWritten : Heap [.array (.prim .uint)] :=
  heap1.set ref1 (MObj.setElem .dyn (heap1.get ref1) 0 (indexValue ⟨7, by decide⟩))
private def machineWritten : Machine := writeMachine machine1 17 w[7]

/-- An actual nonzero old array still satisfies the allocation input relation. -/
theorem written_repr : AllocatorRepr heapWritten bases1 4 nextCursor machineWritten :=
  (initial_repr.allocate .uint ⟨2, by decide⟩ (by decide)).set ref1 0 (by decide +kernel)
    (indexValue ⟨7, by decide⟩) w[7] (ReprV.uint_of rfl)

private def heap2 : Heap [.array (.prim .uint), .array (.prim .bool)] :=
  (heapWritten.alloc (defaultArray .bool ⟨0, W_pos⟩)).1
private def machine2 : Machine := allocateMachine machineWritten nextCursor ⟨0, W_pos⟩
private def bases2 : Nat → Fin W := upd bases1 1 nextCursor

/-- Both actual source allocations fit, preserve the old address and remain separated. -/
theorem twoArrays_repr : AllocatorRepr heap2 bases2 4 ⟨20, by decide⟩ machine2 :=
  written_repr.allocate .bool ⟨0, W_pos⟩ (by decide)

private def code : List Instr :=
  [.push w[2]] ++ allocateArrayCode ++ [.push w[7], .swap 1, .push w[0]] ++
    writeArrayStackCode ++ [.push w[0]] ++ allocateArrayCode

private def value : Word → Option Nat
  | .val v => some v.val
  | .slot _ => none

private def observe : Out → Option (List Nat)
  | .ok m _ => do
    let stack ← m.stack.mapM value
    let cells ← [m.mem 0, m.mem 2, m.mem 16, m.mem 17, m.mem 18, m.mem 19].mapM value
    pure (stack ++ cells)
  | _ => none

private def reverted : Out → Bool
  | .revert => true
  | _ => false

/-- Machine execution agrees on the returned pointer, cursor, frame, lengths
and zero default elements of the two distinct arrays. -/
example : observe (run code machine) =
    some [19, 20, 99, 2, 7, 0, 0] := by
  decide +kernel

/-- An older alias reads its nonzero value after the second allocation. -/
example : observe (run (code ++ [.pop, .push w[0]] ++ readArrayCode cursor) machine) =
    some [7, 20, 99, 2, 7, 0, 0] := by
  decide +kernel

/-- Index zero of the freshly allocated empty array reverts. -/
example : reverted (run (code ++ [.push w[0]] ++ readArrayStackCode) machine) = true := by
  decide +kernel

/-- Dirty unused memory cannot supply the allocator's default-value premise. -/
example : ¬ FreeMemory 4 cursor (writeMachine machine 16 w[1]) :=
  fun h => Nat.noConfusion (congrArg Fin.val (Word.val.inj (h.zero 16 (Nat.le_refl 16))))

/-- The last word cannot be a header while keeping the next cursor a word. -/
example : ¬ (wMax.val + 0 + 1 < W) := by
  decide +kernel

end Solidity.Evm.Memory.AllocExamples
