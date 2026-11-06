import Solidity.Yul.Compilation.NestedWrites

/-! Target-only nested contents, physical range, underflow and capacity controls. -/
namespace Solidity.Yul.Compilation
open Backend Scalar
private def dirty : Word := BitVec.ofNat 256 (2 ^ 200 + 257)
private def ws : NestedWrites 3 2 :=
  [(⟨⟨1, by decide⟩, by decide⟩, 513),
   (⟨⟨0, by decide⟩, by decide⟩, 1025),
   (⟨⟨1, by decide⟩, by decide⟩, dirty)]

example : run (writeSlot ⟨3, by decide⟩) (dirty :: [100, 101, 4, 5, 6, 77, 88]) =
    some [100, 101, 4, dirty, 6, 77, 88] :=
  write_under_prefix #v[4, 5, 6] #v[100, 101] ⟨1, by decide⟩ (by decide) dirty [77, 88]
example : run (writeSlot ⟨2, by decide⟩) (dirty :: [100, 101, 4, 5, 6, 77, 88]) =
    some [100, 101, dirty, 5, 6, 77, 88] :=
  write_under_prefix #v[4, 5, 6] #v[100, 101] ⟨0, by decide⟩ (by decide) dirty [77, 88]
example : run (writeSlot ⟨15, by decide⟩)
    (dirty :: ([100, 101] ++ ((Vector.replicate 14 0).toList ++ [77, 88]))) =
    some ([100, 101] ++ (((Vector.replicate 14 0).set 13 dirty (by decide)).toList ++ [77, 88])) :=
  write_under_prefix (Vector.replicate 14 0) #v[100, 101] ⟨13, by decide⟩
    (by decide) dirty [77, 88]
example : run (writeSlot ⟨3, by decide⟩ ++ [readSlot ⟨3, by decide⟩])
    (dirty :: [100, 101, 4, 5, 6, 77, 88]) =
    some [dirty, 100, 101, 4, dirty, 6, 77, 88] :=
  read_after_write_under_prefix #v[4, 5, 6] #v[100, 101] ⟨1, by decide⟩
    (by decide) dirty [77, 88]
example : run (writeSlot ⟨3, by decide⟩ ++ [readSlot ⟨4, by decide⟩])
    (dirty :: [100, 101, 4, 5, 6, 77, 88]) = some [6, 100, 101, 4, dirty, 6, 77, 88] :=
  read_other_after_write_under_prefix #v[4, 5, 6] #v[100, 101]
    ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide) (by decide) (by decide) dirty [77, 88]

example : run (writeSequence (shiftedWrites ws)) [100, 101, 4, 5, 6, 77, 88] =
    some [100, 101, 1025, dirty, 6, 77, 88] :=
  nested_writes_run ws #v[4, 5, 6] #v[100, 101] [77, 88]
example : run (writeSequence (shiftedWrites ws) ++ [readSlot ⟨3, by decide⟩])
    [100, 101, 4, 5, 6, 77, 88] = some [dirty, 100, 101, 1025, dirty, 6, 77, 88] :=
  nested_writes_read ws #v[4, 5, 6] #v[100, 101] ⟨1, by decide⟩ (by decide) [77, 88]
example : (run (writeSequence (shiftedWrites ws)) [100, 101, 4, 5, 6, 77, 88]).map
    (List.drop 5) = some [77, 88] := nested_writes_caller ws #v[4, 5, 6] #v[100, 101] [77, 88]
example : run (writeSequence (shiftedWrites ws) ++ popPrefix 2)
    [100, 101, 4, 5, 6, 77, 88] = some [1025, dirty, 6, 77, 88] :=
  nested_writes_remove_prefix ws #v[4, 5, 6] #v[100, 101] [77, 88]
example : run (pushPrefix [100, 101] ++ writeSequence (shiftedWrites ws) ++ popPrefix 2)
    [4, 5, 6, 77, 88] = some [1025, dirty, 6, 77, 88] :=
  nested_scope_updates ws #v[4, 5, 6] #v[100, 101] [77, 88]
example : run (pushPrefix [4, 5, 6] ++
    (pushPrefix [100, 101] ++ writeSequence (shiftedWrites ws) ++ popPrefix 2) ++ popPrefix 3)
    [77, 88] = some [77, 88] := nested_scope_exit ws #v[4, 5, 6] #v[100, 101] [77, 88]
example : ∃ depth : Fin 16,
    depth.val = (2 + 3 + 2 - 1) - Slots.at (n := 3) ⟨2⟩ ⟨1, by decide⟩ ∧
    run (writeSlot depth) (dirty :: [100, 101, 4, 5, 6, 77, 88]) =
      some [100, 101, 4, dirty, 6, 77, 88] :=
  write_at_allocated_depth ⟨2⟩ #v[4, 5, 6] #v[100, 101] ⟨1, by decide⟩
    [77, 88] rfl (by decide) dirty

example : ¬ ∃ i : {i : Fin 15 // 2 + i.val < 16}, i.val.val = 14 := by
  rintro ⟨i, h⟩
  have hb : 2 + i.val.val < 16 := i.property
  omega
example : run (writeSlot ⟨3, by decide⟩) (dirty :: [100, 101, 4]) = none :=
  write_slot_underflow _ _ _ (by decide)
example : run (writeSequence (shiftedWrites ws)) [100, 101] = none := by
  simp only [ws, shiftedWrites, List.map_cons, writeSequence, writeSlot,
    List.cons_append, List.nil_append, run, step_pushWord, Option.bind_some]
  rfl
example : (run (writeSlot ⟨2, by decide⟩)
    (dirty :: ([100, 101] ++ ((Vector.replicate 17 0).toList ++ [77, 88])))).map
    (fun stack => stack[18]?) = some (some 0) :=
  write_under_prefix_other (Vector.replicate 17 0) #v[100, 101]
    ⟨0, by decide⟩ ⟨16, by decide⟩ (by decide) (by decide) dirty [77, 88]
example : dirty.toNat = 2 ^ 200 + 257 := by decide +kernel
example : stackBound (writeSequence (shiftedWrites ws)) 1023 = true := by decide +kernel
example : stackBound (writeSequence (shiftedWrites ws)) 1024 = false := by decide +kernel
example : run (writeSequence (shiftedWrites ws))
    ([100, 101] ++ ([4, 5, 6] ++ List.replicate 1019 9)) =
    some ([100, 101] ++ ([1025, dirty, 6] ++ List.replicate 1019 9)) :=
  nested_writes_run ws #v[4, 5, 6] #v[100, 101] _
example : stackBound (writeSequence (shiftedWrites ws))
    ([100, 101] ++ ([4, 5, 6] ++ List.replicate 1019 9)).length = false := by decide +kernel
end Solidity.Yul.Compilation
