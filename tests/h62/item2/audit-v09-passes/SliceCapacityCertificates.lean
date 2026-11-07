import Solidity.Yul.Compilation.ClzBounds

/-! Guard composing arity-indexed slices at an invented intermediate height or
checking final height while ignoring an overflowing prefix. Reuse Slice.comp,
its actual runs, run_height and the existing generic stackBound_comp law. This
adds certificates, not a new artifact/interface or Source/native semantics;
1024 capacity is unchanged and gas/physical realization remain separate. -/
namespace Solidity.Yul.Compilation
open Backend Scalar

/-- Derive the actual intermediate vector and its height before composing the
two capacity checks. No successful run or desired intermediate state is assumed. -/
theorem Slice.comp_capacity {a b c : Nat} (f : Slice a b) (g : Slice b c)
    (xs : Vector Word a) (tail : Stack)
    (first : stackBound f.code ((a + tail.length : Nat) : Int) = true)
    (second : stackBound g.code ((b + tail.length : Nat) : Int) = true) :
    ∃ middle : Vector Word b, ∃ result : Vector Word c,
      run f.code (xs.toList ++ tail) = some (middle.toList ++ tail) ∧
      run g.code (middle.toList ++ tail) = some (result.toList ++ tail) ∧
      run (f.comp g).code (xs.toList ++ tail) = some (result.toList ++ tail) ∧
      stackBound (f.comp g).code ((a + tail.length : Nat) : Int) = true ∧
      b + tail.length ≤ 1024 ∧ c + tail.length ≤ 1024 := by
  obtain ⟨middle, hf⟩ := f.correct xs tail
  obtain ⟨result, hg⟩ := g.correct middle tail
  have shifted : ((a + tail.length : Nat) : Int) + (f.code.map stackDelta).sum =
      ((b + tail.length : Nat) : Int) := by
    simpa only [List.length_append, Vector.length_toList] using (run_height hf).symm
  refine ⟨middle, result, hf, hg, run_comp hf hg, ?_,
    f.capacity xs tail first, g.capacity middle tail second⟩
  exact stackBound_comp first (by rw [shifted]; exact second)

/-- The composed certificate controls every actual successful prefix, not only
its intermediate and final vectors. Reuse the existing prefix law. -/
theorem Slice.comp_prefix_capacity {a b c : Nat} (f : Slice a b) (g : Slice b c)
    (xs : Vector Word a) (tail : Stack)
    (first : stackBound f.code ((a + tail.length : Nat) : Int) = true)
    (second : stackBound g.code ((b + tail.length : Nat) : Int) = true)
    (before after : Program) (code : before ++ after = (f.comp g).code)
    (mid : Stack) (executed : run before (xs.toList ++ tail) = some mid) :
    mid.length ≤ 1024 := by
  obtain ⟨middle, result, hf, hg, whole, bound, ends⟩ :=
    f.comp_capacity g xs tail first second
  apply prefix_capacity before after executed
  rw [code]
  simpa only [List.length_append, Vector.length_toList] using bound

/-- Every decomposition of the successful composed code has an actual
successful intermediate stack, whose capacity is derived rather than assumed. -/
theorem Slice.comp_prefix_witness {a b c : Nat} (f : Slice a b) (g : Slice b c)
    (xs : Vector Word a) (tail : Stack)
    (first : stackBound f.code ((a + tail.length : Nat) : Int) = true)
    (second : stackBound g.code ((b + tail.length : Nat) : Int) = true)
    (before after : Program) (code : before ++ after = (f.comp g).code) :
    ∃ mid : Stack, run before (xs.toList ++ tail) = some mid ∧ mid.length ≤ 1024 := by
  obtain ⟨middle, result, hf, hg, whole, bound, ends⟩ :=
    f.comp_capacity g xs tail first second
  have split : (run before (xs.toList ++ tail)).bind (run after) =
      some (result.toList ++ tail) := by
    rw [← run_append, code]
    exact whole
  obtain ⟨mid, executed, continued⟩ := Option.bind_eq_some_iff.mp split
  refine ⟨mid, executed, ?_⟩
  apply prefix_capacity before after executed
  rw [code]
  simpa only [List.length_append, Vector.length_toList] using bound

/-- A nontrivial full-word addition and all its prefixes fit with two spare
words; the arbitrary caller tail is preserved exactly. -/
theorem pair_add_safe (tail : Stack) (room : tail.length + 2 ≤ 1024) :
    run ((literalPair 250 9).comp addWords).code tail = some (259 :: tail) ∧
    stackBound ((literalPair 250 9).comp addWords).code (tail.length : Int) = true := by
  have first : stackBound (literalPair 250 9).code (tail.length : Int) = true := by
    change (safeHeight (tail.length : Int) &&
      (safeHeight ((tail.length : Int) + 1) &&
      (safeHeight ((tail.length : Int) + 1 + 1) && true))) = true
    simp only [Bool.and_true, Bool.and_eq_true, safeHeight, decide_eq_true_eq]
    omega
  have second : stackBound addWords.code ((2 + tail.length : Nat) : Int) = true := by
    change (safeHeight ((2 + tail.length : Nat) : Int) &&
      (safeHeight (((2 + tail.length : Nat) : Int) + -1) && true)) = true
    simp only [Bool.and_true, Bool.and_eq_true, safeHeight, decide_eq_true_eq]
    omega
  obtain ⟨middle, result, hf, hg, whole, bound, ends⟩ :=
    (literalPair 250 9).comp_capacity addWords #v[] tail
      (by simpa only [Nat.zero_add] using first) second
  refine ⟨?_, by simpa only [Nat.zero_add] using bound⟩
  rfl

/-- The addition finishes at1024 but the preceding two pushes reach1025.
A final-height-only argument cannot discharge the composed prefix check. -/
theorem pair_add_overflow (tail : Stack) (full : tail.length = 1023) :
    run ((literalPair 250 9).comp addWords).code tail = some (259 :: tail) ∧
    stackBound ((literalPair 250 9).comp addWords).code (tail.length : Int) = false := by
  refine ⟨by rfl, ?_⟩
  cases checked : stackBound ((literalPair 250 9).comp addWords).code
      (tail.length : Int) with
  | false => rfl
  | true =>
    have initial : stackBound (literalPair 250 9).code
        ((0 + tail.length : Nat) : Int) = true := by
      have hp := stackBound_prefix (literalPair 250 9).code addWords.code
        (tail.length : Int) checked
      simpa only [Nat.zero_add] using hp
    have capacity := (literalPair 250 9).capacity #v[] tail initial
    omega

/-- info: 'Solidity.Yul.Compilation.Slice.comp_capacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Slice.comp_capacity
/-- info: 'Solidity.Yul.Compilation.Slice.comp_prefix_capacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Slice.comp_prefix_capacity
/-- info: 'Solidity.Yul.Compilation.pair_add_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pair_add_safe
/-- info: 'Solidity.Yul.Compilation.pair_add_overflow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pair_add_overflow
/-- info: 'Solidity.Yul.Compilation.Slice.comp_prefix_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Slice.comp_prefix_witness
end Solidity.Yul.Compilation
