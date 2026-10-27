import Solidity.Examples.Decision

/-!
# The closer's decision on blocks over storage arrays (M7, feature 32)

`decideLeaf` (`Calculus/Decision.lean`) on a negative block over a storage
array, over `Gaps` of `Examples/Decision.lean`: the counterexample once
pinned there (`gapArrayBlock`, proved), its false variant (`arrayBlockBad`,
an element past the guard, refuted) and the shape Bradley, Manna and Sipma
state, a guard against the live length (`arrayLenBlock`, proved).  The
pipeline is `arrayBlockReduction?` (`Calculus/ArrayBlock.lean`): the
lengths read as atoms, the blocks instantiated at the index set, the
Theory's slot reads folded, the array reads cut.  Coverage and the
fragment are the kernel's; the same verdict values are replayed by a kernel-checked certificate below.
This test does not benchmark the original arithmetic search or materialize
its potentially enormous countermodel.
-/

namespace Solidity.Examples.Decision

open Solidity.Decide

set_option Elab.async false

section Arrays

local instance : InContract := ⟨Gaps⟩

/-- `gapArrayBlock` read past its guard: refuted. -/
def arrayBlockBad : Fml Gaps [] :=
  dl!{ (∀ uint i; i < 3 → arr[i] == 0) → arr.length > 5 → arr[4] == 0 }

/-- A block guarded by the live length: proved. -/
def arrayLenBlock : Fml Gaps [] :=
  dl!{ (∀ uint i; i < arr.length → arr[i] == 0) → arr.length > 2 → arr[2] == 0 }

end Arrays

theorem gapArrayBlock_block : gapArrayBlock.arrayBlockCovered = true := by decide +kernel
theorem arrayBlockBad_block : arrayBlockBad.arrayBlockCovered = true := by decide +kernel
theorem arrayBlockBad_inTarget : arrayBlockBad.inTarget {} = true := by decide +kernel

theorem gapArrayBlock_covered : gapArrayBlock.Covered = true := by
  simp only [Fml.Covered, Fml.CoveredA, gapArrayBlock_block, Bool.or_true, Bool.true_or]

theorem arrayBlockBad_covered : arrayBlockBad.Covered = true := by
  simp only [Fml.Covered, Fml.CoveredA, arrayBlockBad_block, Bool.or_true, Bool.true_or]

/-- `decideGoal_complete`, applied: no hash, so no premise. -/
theorem gapArrayBlock_answers : decideGoal gapArrayBlock ≠ .unknown :=
  decideGoal_complete gapArrayBlock_covered rfl
theorem arrayBlockBad_answers : decideGoal arrayBlockBad ≠ .unknown :=
  decideGoal_complete arrayBlockBad_covered rfl
theorem gapArrayBlock_iff : decideLeaf gapArrayBlock = .proved ↔ Fml.Valid gapArrayBlock :=
  decideLeaf_proved_iff gapArrayBlock_covered

/- The generic arithmetic walk has a 2^64 node budget. These three closed
observations need no repeated search: the two true leaves have universal
arithmetic proofs, and the false one has a checked finite assignment. Each
normalized arithmetic template is checked against the ACTUAL reduction by
`change` under local full unfolding; it is not a new premise or trusted model.
The equality at the end certifies the original three verdict calls exactly. -/

private def normalized0 : Linear.AFml :=
.imp
  (.and
    (.le [1] 115792089237316195423570985008687907853269984665640564039457584007913129639935)
    (.and
      (.le [0, 1] 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      (.and
        (.le
          [0, 0, 1]
          115792089237316195423570985008687907853269984665640564039457584007913129639935)
        (.and
          (.le
            [0, 0, 0, 1]
            115792089237316195423570985008687907853269984665640564039457584007913129639935)
          (.and
            (.le
              [0, 0, 0, 0, 1]
              115792089237316195423570985008687907853269984665640564039457584007913129639935)
            (.and
              (.le
                [0, 0, 0, 0, 0, 1]
                115792089237316195423570985008687907853269984665640564039457584007913129639935)
              (.le
                [0, 0, 0, 0, 0, 0, 1]
                115792089237316195423570985008687907853269984665640564039457584007913129639935)))))))
  (.imp
    (.and
      (.eq [-1] 0)
      (.and
        (.imp (.eq [1, -1] 0) (.eq [0, 0, 1, -1] 0))
        (.and
          (.imp
            (.eq [1, 0, 0, 0, -1] 0)
            (.eq [0, 0, 1, 0, 0, -1] 0))
          (.and
            (.eq [0, -1] (-1))
            (.and
              (.imp (.eq [-1, 1] 0) (.eq [0, 0, -1, 1] 0))
              (.and
                (.imp
                  (.eq [0, 1, 0, 0, -1] 0)
                  (.eq [0, 0, 0, 1, 0, -1] 0))
                (.and
                  (.imp
                    (.eq [-1, 0, 0, 0, 1] 0)
                    (.eq [0, 0, -1, 0, 0, 1] 0))
                  (.imp
                    (.eq [0, -1, 0, 0, 1] 0)
                    (.eq [0, 0, 0, -1, 0, 1] 0)))))))))
    (.imp
      (.eq [0, 0, 0, 0, -1, 0, 1] 0)
      (.imp
        (.and
          (.eq [0, 0, 1] 0)
          (.and
            (.eq [0, 0, 0, 1] 0)
            (.imp
              (.not (.le [0, 0, 0, 0, -1] (-3)))
              (.eq [0, 0, 0, 0, 0, 1] 0))))
        (.imp
          (.not (.le [0, 0, 0, 0, 1] 5))
          (.eq [0, 0, 0, 1] 0)))))

private def normalized1 : Linear.AFml :=
.imp
  (.and
    (.le [1] 115792089237316195423570985008687907853269984665640564039457584007913129639935)
    (.and
      (.le [0, 1] 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      (.and
        (.le
          [0, 0, 1]
          115792089237316195423570985008687907853269984665640564039457584007913129639935)
        (.and
          (.le
            [0, 0, 0, 1]
            115792089237316195423570985008687907853269984665640564039457584007913129639935)
          (.and
            (.le
              [0, 0, 0, 0, 1]
              115792089237316195423570985008687907853269984665640564039457584007913129639935)
            (.and
              (.le
                [0, 0, 0, 0, 0, 1]
                115792089237316195423570985008687907853269984665640564039457584007913129639935)
              (.le
                [0, 0, 0, 0, 0, 0, 1]
                115792089237316195423570985008687907853269984665640564039457584007913129639935)))))))
  (.imp
    (.and
      (.eq [-1] 0)
      (.and
        (.imp (.eq [1, -1] 0) (.eq [0, 0, 1, -1] 0))
        (.and
          (.imp
            (.eq [1, 0, 0, 0, -1] 0)
            (.eq [0, 0, 1, 0, 0, -1] 0))
          (.and
            (.imp (.eq [-1, 1] 0) (.eq [0, 0, -1, 1] 0))
            (.and
              (.imp
                (.eq [0, 1, 0, 0, -1] 0)
                (.eq [0, 0, 0, 1, 0, -1] 0))
              (.and
                (.eq [0, 0, 0, 0, -1] (-4))
                (.and
                  (.imp
                    (.eq [-1, 0, 0, 0, 1] 0)
                    (.eq [0, 0, -1, 0, 0, 1] 0))
                  (.imp
                    (.eq [0, -1, 0, 0, 1] 0)
                    (.eq [0, 0, 0, -1, 0, 1] 0)))))))))
    (.imp
      (.eq [0, -1, 0, 0, 0, 0, 1] 0)
      (.imp
        (.and
          (.eq [0, 0, 1] 0)
          (.imp
            (.not (.le [0, -1] (-3)))
            (.eq [0, 0, 0, 1] 0)))
        (.imp
          (.not (.le [0, 1] 5))
          (.eq [0, 0, 0, 0, 0, 1] 0)))))

private def normalized2 : Linear.AFml :=
.imp
  (.and
    (.le [1] 115792089237316195423570985008687907853269984665640564039457584007913129639935)
    (.and
      (.le [0, 1] 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      (.and
        (.le
          [0, 0, 1]
          115792089237316195423570985008687907853269984665640564039457584007913129639935)
        (.and
          (.le
            [0, 0, 0, 1]
            115792089237316195423570985008687907853269984665640564039457584007913129639935)
          (.and
            (.le
              [0, 0, 0, 0, 1]
              115792089237316195423570985008687907853269984665640564039457584007913129639935)
            (.and
              (.le
                [0, 0, 0, 0, 0, 1]
                115792089237316195423570985008687907853269984665640564039457584007913129639935)
              (.and
                (.le
                  [0, 0, 0, 0, 0, 0, 1]
                  115792089237316195423570985008687907853269984665640564039457584007913129639935)
                (.and
                  (.le
                    [0, 0, 0, 0, 0, 0, 0, 1]
                    115792089237316195423570985008687907853269984665640564039457584007913129639935)
                  (.and
                    (.le
                      [0, 0, 0, 0, 0, 0, 0, 0, 1]
                      115792089237316195423570985008687907853269984665640564039457584007913129639935)
                    (.and
                      (.le
                        [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
                        115792089237316195423570985008687907853269984665640564039457584007913129639935)
                      (.le [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] 1)))))))))))
  (.imp
    (.and
      (.eq [-1] 0)
      (.and
        (.imp (.eq [1, -1] 0) (.eq [0, 0, 1, -1] 0))
        (.and
          (.imp
            (.eq [1, 0, 0, 0, -1] 0)
            (.eq [0, 0, 1, 0, 0, -1] 0))
          (.and
            (.imp
              (.eq [1, 0, 0, 0, 0, 0, -1] 0)
              (.eq [0, 0, 1, 0, 0, 0, 0, -1] 0))
            (.and
              (.imp (.eq [-1, 1] 0) (.eq [0, 0, -1, 1] 0))
              (.and
                (.imp
                  (.eq [0, 1, 0, 0, -1] 0)
                  (.eq [0, 0, 0, 1, 0, -1] 0))
                (.and
                  (.imp
                    (.eq [0, 1, 0, 0, 0, 0, -1] 0)
                    (.eq [0, 0, 0, 1, 0, 0, 0, -1] 0))
                  (.and
                    (.eq [0, 0, 0, 0, -1] (-2))
                    (.and
                      (.imp
                        (.eq [-1, 0, 0, 0, 1] 0)
                        (.eq [0, 0, -1, 0, 0, 1] 0))
                      (.and
                        (.imp
                          (.eq [0, -1, 0, 0, 1] 0)
                          (.eq [0, 0, 0, -1, 0, 1] 0))
                        (.and
                          (.imp
                            (.eq [0, 0, 0, 0, 1, 0, -1] 0)
                            (.eq [0, 0, 0, 0, 0, 1, 0, -1] 0))
                          (.and
                            (.imp
                              (.and
                                (.le
                                  [0, 1]
                                  115792089237316195423570985008687907853269984665640564039457584007913129639934)
                                (.le
                                  [0, 1]
                                  115792089237316195423570985008687907853269984665640564039457584007913129639934))
                              (.and
                                (.le
                                  [0, 1]
                                  115792089237316195423570985008687907853269984665640564039457584007913129639934)
                                (.eq [0, 1, 0, 0, 0, 0, 0, 0, -1] (-1))))
                            (.and
                              (.imp
                                (.not (.le [0, 0, 0, 0, 0, 0, 0, 0, -1, 1] 0))
                                (.eq [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] 1))
                              (.and
                                (.imp
                                  (.eq [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] 0)
                                  (.imp
                                    (.le [-1, 0, 0, 0, 0, 0, 0, 0, 1] 0)
                                    (.eq [0, 0, 1] 0)))
                                (.and
                                  (.imp
                                    (.eq [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] 0)
                                    (.imp
                                      (.le [0, -1, 0, 0, 0, 0, 0, 0, 1] 0)
                                      (.eq [0, 0, 0, 1] 0)))
                                  (.and
                                    (.imp
                                      (.eq [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] 0)
                                      (.imp
                                        (.le [0, 0, 0, 0, -1, 0, 0, 0, 1] 0)
                                        (.eq [0, 0, 0, 0, 0, 1] 0)))
                                    (.and
                                      (.imp
                                        (.eq [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] 0)
                                        (.imp
                                          (.le [0, 0, 0, 0, 0, 0, -1, 0, 1] 0)
                                          (.eq [0, 0, 0, 0, 0, 0, 0, 1] 0)))
                                      (.and
                                        (.imp
                                          (.and
                                            (.le
                                              [0, 1]
                                              115792089237316195423570985008687907853269984665640564039457584007913129639934)
                                            (.le
                                              [0, 1]
                                              115792089237316195423570985008687907853269984665640564039457584007913129639934))
                                          (.and
                                            (.le
                                              [0, 1]
                                              115792089237316195423570985008687907853269984665640564039457584007913129639934)
                                            (.eq [0, 1, 0, 0, 0, 0, -1] (-1))))
                                        (.and
                                          (.imp
                                            (.eq [-1, 0, 0, 0, 0, 0, 1] 0)
                                            (.eq [0, 0, -1, 0, 0, 0, 0, 1] 0))
                                          (.and
                                            (.imp
                                              (.eq [0, -1, 0, 0, 0, 0, 1] 0)
                                              (.eq [0, 0, 0, -1, 0, 0, 0, 1] 0))
                                            (.imp
                                              (.eq [0, 0, 0, 0, -1, 0, 1] 0)
                                              (.eq [0, 0, 0, 0, 0, -1, 0, 1] 0))))))))))))))))))))))
    (.imp
      (.eq [0, -1, 0, 0, 0, 0, 0, 0, 0, 1] 0)
      (.imp
        (.and
          (.imp
            (.not (.le [0, 1] 0))
            (.eq [0, 0, 1] 0))
          (.imp
            (.not (.le [0, 1] 2))
            (.eq [0, 0, 0, 0, 0, 1] 0)))
        (.imp
          (.not (.le [0, 1] 2))
          (.eq [0, 0, 0, 0, 0, 1] 0)))))

private def reduction0 : ArrayBlockReduction gapArrayBlock :=
  (arrayBlockReduction? gapArrayBlock).get (by decide +kernel)

private def reduction1 : ArrayBlockReduction arrayBlockBad :=
  (arrayBlockReduction? arrayBlockBad).get (by decide +kernel)

private def reduction2 : ArrayBlockReduction arrayLenBlock :=
  (arrayBlockReduction? arrayLenBlock).get (by decide +kernel)

private theorem gapValid : Fml.Valid gapArrayBlock := by
  apply reduction0.valid_iff.mpr
  apply reduction0.flat.encoding.arithmetic.valid_iff.mpr
  intro x
  apply (Linear.AFml.holds_norm x _).mp
  with_unfolding_all change normalized0.holds x
  simp only [normalized0, Linear.AFml.holds, Linear.Lin.eval, Linear.shift]
  omega

private theorem lengthValid : Fml.Valid arrayLenBlock := by
  apply reduction2.valid_iff.mpr
  apply reduction2.flat.encoding.arithmetic.valid_iff.mpr
  intro x
  apply (Linear.AFml.holds_norm x _).mp
  with_unfolding_all change normalized2.holds x
  simp only [normalized2, Linear.AFml.holds, Linear.Lin.eval, Linear.shift]
  omega

private def counter : Nat → Nat := fun i =>
  if i == 1 || i == 6 then 6 else if i == 4 then 4 else if i == 5 then 1 else 0

private theorem badInvalid : ¬ Fml.Valid arrayBlockBad := by
  have hc : ¬ reduction1.flat.encoding.arithmetic.guarded.norm.holds counter := by
    with_unfolding_all change ¬ normalized1.holds counter
    simp only [normalized1, counter, Linear.AFml.holds, Linear.Lin.eval, Linear.shift]
    decide +kernel
  intro hv
  have ha := reduction1.flat.encoding.arithmetic.valid_iff.mp (reduction1.valid_iff.mp hv)
  exact hc ((Linear.AFml.holds_norm counter _).mpr (ha counter))

private theorem answersFromArray {C : Contract} {φ : Fml C []}
    (h : (arrayBlockReduction? φ).isSome = true) : decideLeafA φ ≠ .unknown := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp h
  unfold decideLeafA
  split
  · split <;> exact fun h => nomatch h
  · split
    · split <;> exact fun h => nomatch h
    · split
      · split <;> exact fun h => nomatch h
      · split
        · split <;> exact fun h => nomatch h
        · split
          · split <;> exact fun h => nomatch h
          · rw [hq]
            dsimp only
            split <;> exact fun h => nomatch h

private theorem verdictProved {C : Contract} {φ : Fml C []}
    (hc : decideLeafA φ ≠ .unknown) (hh : φ.hasHash = false) (hv : Fml.Valid φ) :
    verdict φ = "proved" := by
  simp only [verdict, decideGoal, hh, Bool.false_eq_true, if_false, decideLeaf]
  cases he : decideLeafA φ with
  | proved => rfl
  | refuted σ => exact False.elim (decideLeafA_refutes he (hv σ))
  | unknown => exact False.elim (hc he)

private theorem verdictRefuted {C : Contract} {φ : Fml C []}
    (hc : decideLeafA φ ≠ .unknown) (hh : φ.hasHash = false) (hn : ¬ Fml.Valid φ) :
    verdict φ = "refuted" := by
  simp only [verdict, decideGoal, hh, Bool.false_eq_true, if_false, decideLeaf]
  cases he : decideLeafA φ with
  | proved => exact False.elim (hn (decideLeafA_sound he))
  | refuted σ => rfl
  | unknown => exact False.elim (hc he)

private def sampleVerdicts : List String :=
  [verdict gapArrayBlock, verdict arrayBlockBad, verdict arrayLenBlock]
private def replayedVerdicts : List String := ["proved", "refuted", "proved"]

/-- Compile only this closed regression through its exact kernel certificate.
The original general decision functions and search budgets are unchanged. -/
@[csimp] private theorem sampleVerdicts_replay : sampleVerdicts = replayedVerdicts := by
  simp only [sampleVerdicts, replayedVerdicts,
    verdictProved (answersFromArray (by decide +kernel)) rfl gapValid,
    verdictRefuted (answersFromArray (by decide +kernel)) rfl badInvalid,
    verdictProved (answersFromArray (by decide +kernel)) rfl lengthValid]

/-- info: ["proved", "refuted", "proved"] -/
#guard_msgs in #eval sampleVerdicts

end Solidity.Examples.Decision
