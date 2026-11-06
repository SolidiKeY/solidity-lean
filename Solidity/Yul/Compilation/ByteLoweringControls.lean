import Solidity.Yul.Compilation.ByteLowering

namespace Solidity.Yul.Compilation
open Backend Scalar
private def dirty : Word := BitVec.ofNat 256 (2 ^ 255 + 2 ^ 200 + 257)
private def dirtyIndex : Word := BitVec.ofNat 256 (2 ^ 200 + 6)

example (tail : Stack) : run byteExpansion (0 :: dirty :: tail) = some (128 :: tail) :=
  byteExpansion_run 0 dirty tail
example (tail : Stack) : run byteExpansion (6 :: dirty :: tail) = some (1 :: tail) :=
  byteExpansion_run 6 dirty tail
example (tail : Stack) : run byteExpansion (30 :: dirty :: tail) = some (1 :: tail) :=
  byteExpansion_run 30 dirty tail
example (tail : Stack) : run byteExpansion (31 :: dirty :: tail) = some (1 :: tail) :=
  byteExpansion_run 31 dirty tail
example (tail : Stack) : run byteExpansion (32 :: dirty :: tail) = some (0 :: tail) :=
  byteExpansion_run 32 dirty tail
example (tail : Stack) : run byteExpansion (dirtyIndex :: dirty :: tail) = some (0 :: tail) :=
  byteExpansion_run dirtyIndex dirty tail

example : ∃ p, (lowerByte (lowerLocal (n := 2) ⟨0, by decide⟩)
    (lowerLocal (n := 2) ⟨1, by decide⟩)).code 2 = some p ∧
    run p [100, 101, 6, dirty, 77, 88] = some [1, 100, 101, 6, dirty, 77, 88] :=
  by
    refine ⟨_, rfl, ?_⟩
    have h := (lowerByte (lowerLocal (n := 2) ⟨0, by decide⟩)
      (lowerLocal (n := 2) ⟨1, by decide⟩)).correct 2 _ rfl #v[6, dirty] #v[100, 101] [77, 88]
    have computed : indexedByteWindow 6 dirty = 1 := by decide +kernel
    change run _ _ = some (indexedByteWindow 6 dirty :: [100, 101, 6, dirty, 77, 88]) at h
    exact h.trans (congrArg (fun w : Word => some (w :: [100, 101, 6, dirty, 77, 88])) computed)
example : (lowerByte (lowerLocal (n := 16) ⟨15, by decide⟩)
    (lowerLiteral 9)).code 0 = none := rfl
example : run [.op .BYTE] [0, dirty] = none := rfl
example : run byteExpansion [] = none := rfl
example : run byteExpansion [1] = none := rfl

example : stackBound byteExpansion 1020 = true := by decide +kernel
example : stackBound byteExpansion 1021 = false := by decide +kernel
example : run byteExpansion (6 :: dirty :: List.replicate 1019 9) =
    some (1 :: List.replicate 1019 9) := byteExpansion_run 6 dirty _
example : stackBound byteExpansion (6 :: dirty :: List.replicate 1019 (9 : Word)).length = false :=
  by decide +kernel
/-- Composition with a later write preserves the other local and caller. -/
example : ∃ p, (lowerAssign ⟨1, by decide⟩
    (lowerByte (lowerLocal (n := 2) ⟨0, by decide⟩) (lowerLiteral dirty))).code 1 = some p ∧
    run p [100, 6, 700, 77, 88] = some [100, 6, 1, 77, 88] := by
  refine ⟨_, rfl, ?_⟩
  have h := (lowerAssign ⟨1, by decide⟩
    (lowerByte (lowerLocal (n := 2) ⟨0, by decide⟩) (lowerLiteral dirty))).correct
    1 _ rfl #v[6, 700] #v[100] [77, 88]
  have computed : indexedByteWindow 6 dirty = 1 := by decide +kernel
  change run _ _ = some [100, 6, indexedByteWindow 6 dirty, 77, 88] at h
  exact h.trans (congrArg (fun w : Word => some [100, 6, w, 77, 88]) computed)

/-- BYTE nested under arithmetic runs under an already evaluated right operand. -/
example : ∃ p, (lowerBinary selectAdd
    (lowerByte (lowerLiteral (n := 0) 0) (lowerLiteral dirty)) (lowerLiteral 1)).code 0 = some p ∧
    run p [77, 88] = some [129, 77, 88] := by
  refine ⟨_, rfl, ?_⟩
  have h := (lowerBinary selectAdd
    (lowerByte (lowerLiteral (n := 0) 0) (lowerLiteral dirty)) (lowerLiteral 1)).correct
    0 _ rfl #v[] #v[] [77, 88]
  have computed : indexedByteWindow 0 dirty + 1 = 129 := by decide +kernel
  change run _ _ = some ((indexedByteWindow 0 dirty + 1) :: [77, 88]) at h
  exact h.trans (congrArg (fun w : Word => some (w :: [77, 88])) computed)

example : encode byteExpansion =
    [0x60, 0xff, 0x82, 0x82, 0x60, 0x1f, 0x03, 0x60, 0x08, 0x02,
     0x1c, 0x16, 0x60, 0x20, 0x82, 0x10, 0x02, 0x91, 0x50, 0x50] := rfl
example : size byteExpansion = 20 := byteExpansion_size
example : stackBound byteExpansion 1 = true := by decide +kernel
end Solidity.Yul.Compilation
