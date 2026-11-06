import Solidity.Yul.Compilation.SlotSemantics

/-! Inhabited target-only slot controls. Full-word data, exact local/caller order,
physical DUP/SWAP bounds, scalar underflow and capacity are tested separately. -/
namespace Solidity.Yul.Compilation
open Backend Scalar

private def dirtyWord : Word := BitVec.ofNat 256 (2 ^ 200 + 257)
private def locals16 : Vector Word 16 :=
  #v[256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271]

example : run (writeSlot ⟨1, by decide⟩) (dirtyWord :: [257, 5, 9, 77, 88]) =
    some [257, dirtyWord, 9, 77, 88] :=
  write_local #v[257, 5, 9] ⟨1, by decide⟩ (by decide) dirtyWord [77, 88]

example : run (writeSlot ⟨0, by decide⟩) (dirtyWord :: [257, 5, 9, 77, 88]) =
    some [dirtyWord, 5, 9, 77, 88] :=
  write_local #v[257, 5, 9] ⟨0, by decide⟩ (by decide) dirtyWord [77, 88]

example : step (readSlot ⟨0, by decide⟩) [dirtyWord, 5, 9, 77, 88] =
    some [dirtyWord, dirtyWord, 5, 9, 77, 88] :=
  read_local #v[dirtyWord, 5, 9] ⟨0, by decide⟩ (by decide) [77, 88]

example : run (writeSlot ⟨15, by decide⟩) (dirtyWord :: (locals16.toList ++ [77, 88])) =
    some ([256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270,
      dirtyWord] ++ [77, 88]) :=
  write_local locals16 ⟨15, by decide⟩ (by decide) dirtyWord [77, 88]

example : step (readSlot ⟨15, by decide⟩) (locals16.toList ++ [77, 88]) =
    some (271 :: (locals16.toList ++ [77, 88])) :=
  read_local locals16 ⟨15, by decide⟩ (by decide) [77, 88]

example : run (writeSlot ⟨1, by decide⟩ ++ [readSlot ⟨1, by decide⟩])
    (dirtyWord :: [257, 5, 9, 77, 88]) =
    some [dirtyWord, 257, dirtyWord, 9, 77, 88] :=
  read_after_write_local #v[257, 5, 9] ⟨1, by decide⟩ (by decide) dirtyWord [77, 88]

example : run (writeSlot ⟨1, by decide⟩ ++ [readSlot ⟨2, by decide⟩])
    (dirtyWord :: [257, 5, 9, 77, 88]) = some [9, 257, dirtyWord, 9, 77, 88] :=
  read_other_after_write_local #v[257, 5, 9] ⟨1, by decide⟩ ⟨2, by decide⟩
    (by decide) (by decide) (by decide) dirtyWord [77, 88]

example : dirtyWord.toNat = 2 ^ 200 + 257 := by decide +kernel
example : step (readSlot ⟨0, by decide⟩) [] = none := rfl
example : run (writeSlot ⟨0, by decide⟩) [dirtyWord] = none := rfl
example : step (readSlot ⟨15, by decide⟩) (List.replicate 15 0) = none := by decide +kernel
example : run (writeSlot ⟨15, by decide⟩) (dirtyWord :: List.replicate 15 0) = none :=
  write_slot_underflow _ _ _ (by decide)
example : ¬ ∃ i : Fin 17, i.val = 16 ∧ i.val < 16 := by
  rintro ⟨i, atBoundary, accessible⟩
  omega

example : stackBound (writeSlot ⟨15, by decide⟩) 1024 = true := by decide +kernel
example : stackBound (writeSlot ⟨15, by decide⟩) 1025 = false := by decide +kernel
example : stackBound [readSlot ⟨15, by decide⟩] 1023 = true := by decide +kernel
example : stackBound [readSlot ⟨15, by decide⟩] 1024 = false := by decide +kernel

/-- Scalar success does not by itself imply the 1024-word resource obligation. -/
example : ∃ out : Stack,
    run (writeSlot ⟨0, by decide⟩) (dirtyWord :: ([257] ++ List.replicate 1024 9)) =
      some out :=
  ⟨_, write_local #v[257] ⟨0, by decide⟩ (by decide) dirtyWord (List.replicate 1024 9)⟩

example : stackBound (writeSlot ⟨0, by decide⟩)
    (dirtyWord :: ([257] ++ List.replicate 1024 9)).length = false := by decide +kernel

end Solidity.Yul.Compilation
