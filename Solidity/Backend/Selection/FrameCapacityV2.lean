import Solidity.Backend.Selection.InterfaceV2

/-! Consequences of the required V2 capacity field. No proof here uses the
legacy conditional prefix field as physical-capacity evidence. -/
namespace Solidity.Backend.Selection.V2

/-- The empty tail is a real capacity instance, not a conditional empty domain. -/
theorem FrameCertificate.capacity_empty {input output : Scalar.Stack}
    (c : FrameCertificate input output) :
    Scalar.stackBound c.code (input.length : Int) = true := by
  have room : (input ++ []).length + c.peak ≤ 1024 := by
    simpa only [List.append_nil] using c.inputRoom
  simpa only [List.append_nil] using c.capacity [] room

/-- Every admitted physical prefix is bounded, without assuming stackBound. -/
theorem FrameCertificate.prefixes {input output : Scalar.Stack}
    (c : FrameCertificate input output) (tail : Scalar.Stack)
    (room : (input ++ tail).length + c.peak ≤ 1024)
    (before after : Program) (reached : Scalar.Stack)
    (split : before ++ after = c.code)
    (ran : Scalar.run before (input ++ tail) = some reached) :
    reached.length ≤ 1024 := by
  apply Scalar.prefix_capacity before after ran
  rw [split]
  exact c.capacity tail room

/-- The result bound includes the physical protected tail. -/
theorem FrameCertificate.output_capacity {input output : Scalar.Stack}
    (c : FrameCertificate input output) (tail : Scalar.Stack)
    (room : (input ++ tail).length + c.peak ≤ 1024) :
    (output ++ tail).length ≤ 1024 :=
  Scalar.run_capacity (c.frame tail) (c.capacity tail room)

theorem FrameCertificate.output_bound {input output : Scalar.Stack}
    (c : FrameCertificate input output) : output.length ≤ 1024 := by
  have ran : Scalar.run c.code input = some output := by
    simpa only [List.append_nil] using c.frame []
  exact Scalar.run_capacity ran c.capacity_empty

/-- No V2 certificate can conceal an overfull result by choosing its peak. -/
theorem no_overfull_output (input output : Scalar.Stack)
    (large : 1024 < output.length) : ¬ Nonempty (FrameCertificate input output) := by
  rintro ⟨c⟩
  exact (Nat.not_lt_of_ge c.output_bound) large

/-- Inhabited identity transformation at any physically admitted input height. -/
def identityFrame (input : Scalar.Stack) (room : input.length ≤ 1024) :
    FrameCertificate input input where
  code := []
  peak := 0
  inputRoom := by simpa only [Nat.add_zero] using room
  frame := fun _ => rfl
  capacity := by
    intro tail admitted
    simp only [Nat.add_zero] at admitted
    simp only [Scalar.stackBound, Scalar.heightTrace, List.all_cons,
      List.all_nil, Bool.and_true, Scalar.safeHeight, decide_eq_true_eq]
    omega

/-- Actual DUP1, retaining every protected tail and checking its extra word. -/
def duplicateHead (word : Scalar.Word) : FrameCertificate [word] [word,word] where
  code := [.op (.DUP 0)]
  peak := 1
  inputRoom := by
    simp only [List.length_cons, List.length_nil]
    decide
  frame := fun _ => rfl
  capacity := by
    intro tail admitted
    simp only [Scalar.stackBound, Scalar.heightTrace, Scalar.stackDelta,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      Scalar.safeHeight, decide_eq_true_eq]
    omega

#print axioms FrameCertificate.capacity_empty
#print axioms FrameCertificate.prefixes
#print axioms FrameCertificate.output_bound
#print axioms no_overfull_output
#print axioms duplicateHead

end Solidity.Backend.Selection.V2
