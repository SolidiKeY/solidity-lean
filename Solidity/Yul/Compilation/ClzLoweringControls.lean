import Solidity.Yul.Compilation.ClzBounds

namespace Solidity.Yul.Compilation
open Backend Scalar
private def dirty : Word := BitVec.ofNat 256 (2 ^ 200 + 257)

example (tail : Stack) : run clzExpansion ((0 : Word) :: tail) = some (256 :: tail) :=
  by
    have value : (0 : Word).clz = 256 := by decide +kernel
    exact (clzExpansion_run 0 tail).trans (congrArg (fun v : Word => some (v :: tail)) value)
example (tail : Stack) : run clzExpansion ((1 : Word) :: tail) = some (255 :: tail) :=
  by
    have value : (1 : Word).clz = 255 := by decide +kernel
    exact (clzExpansion_run 1 tail).trans (congrArg (fun v : Word => some (v :: tail)) value)
example (tail : Stack) : run clzExpansion ((257 : Word) :: tail) = some (247 :: tail) :=
  by
    have value : (257 : Word).clz = 247 := by decide +kernel
    exact (clzExpansion_run 257 tail).trans (congrArg (fun v : Word => some (v :: tail)) value)
example (tail : Stack) : run clzExpansion (dirty :: tail) = some (55 :: tail) :=
  by
    have value : dirty.clz = 55 := by decide +kernel
    exact (clzExpansion_run dirty tail).trans (congrArg (fun v : Word => some (v :: tail)) value)
example (tail : Stack) : run clzExpansion (BitVec.ofNat 256 (2 ^ 255) :: tail) = some (0 :: tail) :=
  by
    have value : (BitVec.ofNat 256 (2 ^ 255)).clz = 0 := by decide +kernel
    exact (clzExpansion_run (BitVec.ofNat 256 (2 ^ 255)) tail).trans (congrArg (fun v : Word => some (v :: tail)) value)

example : ∃ p, (lowerClzExpanded (lowerLocal (n := 2) ⟨0, by decide⟩)).code 2 = some p ∧
    run p [100, 101, dirty, 7, 77, 88] = some [55, 100, 101, dirty, 7, 77, 88] :=
  by
    refine ⟨_, rfl, ?_⟩
    have h := (lowerClzExpanded (lowerLocal (n := 2) ⟨0, by decide⟩)).correct
      2 _ rfl #v[dirty, 7] #v[100, 101] [77, 88]
    have value : dirty.clz = 55 := by decide +kernel
    change run _ _ = some (dirty.clz :: [100, 101, dirty, 7, 77, 88]) at h
    simpa only [value] using h
example : ∃ p, (lowerAssign ⟨1, by decide⟩
    (lowerClzExpanded (lowerLocal (n := 2) ⟨0, by decide⟩))).code 2 = some p ∧
    run p [100, 101, dirty, 7, 77, 88] = some [100, 101, dirty, 55, 77, 88] := by
  refine ⟨_, rfl, ?_⟩
  have h := (lowerAssign ⟨1, by decide⟩
    (lowerClzExpanded (lowerLocal (n := 2) ⟨0, by decide⟩))).correct
      2 _ rfl #v[dirty, 7] #v[100, 101] [77, 88]
  have value : dirty.clz = 55 := by decide +kernel
  change run _ _ = some [100, 101, dirty, dirty.clz, 77, 88] at h
  simpa only [value] using h
example : (lowerClzExpanded (lowerLocal (n := 16) ⟨15, by decide⟩)).code 1 = none := rfl

/-- Native CLZ remains unsupported in this old scalar dispatcher, but the
expanded compiler uses only already supported primitives. -/
example : run [.op .CLZ] [257] = none := rfl
example : run clzExpansion [] = none := clzExpansion_underflow

example : stackBound clzExpansion 1019 = true := clzExpansion_bound 1019 (by decide) (by decide)
example : stackBound clzExpansion 1020 = false := by
  have bad : stackBound clzExpansion 1020 ≠ true := by
    intro hb
    have bound := (clzExpansion_bound_iff 1020).mp hb
    omega
  exact Bool.eq_false_iff.mpr bad
example : run clzExpansion ((257 : Word) :: List.replicate 1019 9) =
    some (247 :: List.replicate 1019 9) := by
  have value : (257 : Word).clz = 247 := by decide +kernel
  simpa only [value] using clzExpansion_run 257 (List.replicate 1019 9)
example : stackBound clzExpansion ((257 : Word) :: List.replicate 1019 9).length = false := by
  apply Bool.eq_false_iff.mpr
  intro hb
  have bound := (clzExpansion_bound_iff _).mp hb
  simp only [List.length_cons, List.length_replicate] at bound
  omega
example : size clzExpansion = 6435 := clzExpansion_size
end Solidity.Yul.Compilation
