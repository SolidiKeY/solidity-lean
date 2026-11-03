import Solidity.Yul.Compilation.ScopeSemantics

/-! Nontrivial target-only prefix/update controls. No frontend admission,
function call, source simulation or general EVM validity is asserted. -/
namespace Solidity.Yul.Compilation
open Backend Scalar

private def dirty : Word := BitVec.ofNat 256 (2 ^ 200 + 257)
private def writes3 : LocalWrites 3 :=
  [(⟨⟨1, by decide⟩, by decide⟩, dirty),
   (⟨⟨0, by decide⟩, by decide⟩, 513),
   (⟨⟨1, by decide⟩, by decide⟩, 1025)]

example : run (pushPrefix [dirty, 9, 513]) [77, 88] =
    some [dirty, 9, 513, 77, 88] := pushPrefix_run _ _
example : run (popPrefix 3) [dirty, 9, 513, 77, 88] = some [77, 88] :=
  popPrefix_run [dirty, 9, 513] [77, 88]
example : run (pushPrefix [0, 0, 0]) [77, 88] = some [0, 0, 0, 77, 88] :=
  pushPrefix_run _ _
example : run (popPrefix 3 ++ pushPrefix [dirty, 513]) [4, 5, 6, 77, 88] =
    some [dirty, 513, 77, 88] := prefix_replace #v[4, 5, 6] #v[dirty, 513] [77, 88]
example : run (pushPrefix [4, 5] ++ pushPrefix [dirty, 9, 513] ++ popPrefix 3)
    [77, 88] = some [4, 5, 77, 88] :=
  nested_prefix #v[4, 5] #v[dirty, 9, 513] [77, 88]
example : run (pushPrefix [4, 5, 6] ++ writeSequence writes3 ++ popPrefix 3)
    [77, 88] = some [77, 88] := scope_updates_exit #v[4, 5, 6] writes3 [77, 88]
example : run (writeSequence writes3) [4, 5, 6, 77, 88] =
    some [513, 1025, 6, 77, 88] := writeSequence_run writes3 #v[4, 5, 6] [77, 88]
example : (run (writeSequence writes3) [4, 5, 6, 77, 88]).map (List.drop 3) =
    some [77, 88] := writeSequence_caller writes3 #v[4, 5, 6] [77, 88]
example : run (writeSequence (n := 3)
    [(⟨⟨1, by decide⟩, by decide⟩, 7), (⟨⟨1, by decide⟩, by decide⟩, dirty)])
    [4, 5, 6, 77, 88] = some [4, dirty, 6, 77, 88] :=
  writeSequence_same #v[4, 5, 6] ⟨⟨1, by decide⟩, by decide⟩ 7 dirty [77, 88]

/-- Slot15 writes the16th local; PUSH32 adds its separate value operand. -/
example : run (writeSequence (n := 16) [(⟨⟨15, by decide⟩, by decide⟩, dirty)])
    ((Vector.replicate 16 0).toList ++ [77, 88]) =
    some (((Vector.replicate 16 0).set 15 dirty (by decide)).toList ++ [77, 88]) :=
  writeSequence_run _ _ _
example : ¬ ∃ i : {i : Fin 17 // i.val < 16}, i.val.val = 16 := by
  rintro ⟨i, h⟩
  have hb := i.property
  omega

/-- Newer words shift a formerly accessible local out of DUP16's range. -/
example : step (readSlot ⟨15, by decide⟩)
    ([100, 101] ++ ((Vector.replicate 14 0).toList ++ [77, 88])) =
    some (0 :: ([100, 101] ++ ((Vector.replicate 14 0).toList ++ [77, 88]))) :=
  read_under_prefix (Vector.replicate 14 0) #v[100, 101] ⟨13, by decide⟩ (by decide) _
example : ¬ ∃ depth : Fin 16, depth.val = 2 + (⟨14, by decide⟩ : Fin 15).val := by
  rintro ⟨depth, eq⟩
  change depth.val = 16 at eq
  have hb := depth.isLt
  omega
example : (Slots.at (n := 3) ⟨2⟩ ⟨1, by decide⟩) = 3 := rfl
example : (2 + 3 + 2 - 1) - Slots.at (n := 3) ⟨2⟩ ⟨1, by decide⟩ = 3 :=
  Slots.live_depth ⟨2⟩ ⟨1, by decide⟩ 2
example : ∃ depth : Fin 16,
    depth.val = (2 + 3 + 2 - 1) - Slots.at (n := 3) ⟨2⟩ ⟨1, by decide⟩ ∧
    step (readSlot depth) ([100, 101] ++ ([4, dirty, 6] ++ [77, 88])) =
      some (dirty :: ([100, 101] ++ ([4, dirty, 6] ++ [77, 88]))) :=
  read_at_allocated_depth ⟨2⟩ #v[4, dirty, 6] #v[100, 101]
    ⟨1, by decide⟩ [77, 88] rfl (by decide)

example : run (popPrefix 4) [4, 5, 6] = none := popPrefix_underflow _ _ (by decide)
example : run (popPrefix 1) [] = none := rfl
example : run (writeSequence (n := 3) [(⟨⟨2, by decide⟩, by decide⟩, dirty)]) [4, 5] =
    none := by
  simp only [writeSequence, writeSlot, List.append_nil, List.cons_append,
    List.nil_append, run, step_pushWord, Option.bind_some]
  rfl
example : run (writeSequence (n := 3)
    [(⟨⟨0, by decide⟩, by decide⟩, dirty), (⟨⟨2, by decide⟩, by decide⟩, 513)])
    [4, 5, 6, 77, 88] =
    run (writeSequence (n := 3)
    [(⟨⟨2, by decide⟩, by decide⟩, 513), (⟨⟨0, by decide⟩, by decide⟩, dirty)])
    [4, 5, 6, 77, 88] :=
  writeSequence_distinct_commute #v[4, 5, 6] ⟨⟨0, by decide⟩, by decide⟩
    ⟨⟨2, by decide⟩, by decide⟩ (by decide) dirty 513 [77, 88]
example : dirty.toNat = 2 ^ 200 + 257 := by decide +kernel
example : stackBound (writeSequence writes3) 1023 = true := by decide +kernel
example : stackBound (writeSequence writes3) 1024 = false := by decide +kernel
example : stackBound (popPrefix 3 ++ pushPrefix [dirty, 513]) 1024 = true :=
  by decide +kernel
example : stackBound (pushPrefix [dirty, 513]) 1023 = false := by decide +kernel

/-- Unbounded scalar success and failed capacity on the same oversized caller. -/
example : run (writeSequence (n := 1) [(⟨⟨0, by decide⟩, by decide⟩, dirty)])
    ([4] ++ List.replicate 1023 9) = some ([dirty] ++ List.replicate 1023 9) :=
  writeSequence_run _ #v[4] _
example : stackBound (writeSequence (n := 1) [(⟨⟨0, by decide⟩, by decide⟩, dirty)])
    ([4] ++ List.replicate 1023 9).length = false := by decide +kernel
end Solidity.Yul.Compilation
