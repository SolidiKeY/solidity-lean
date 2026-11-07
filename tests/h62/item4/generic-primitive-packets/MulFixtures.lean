import «tests».h62.item4.«generic-primitive-packets».SubFixtures

/-! Regression: checked-multiply fixtures must classify overflow instead of wrapping.
The seven rows name the existing CheckedMul target-input controls; this arithmetic
layer alone proves no Source or EVM execution. MulCorrespondence supplies that
separate live bridge. Other original controls remain separate obligations. -/
namespace H62.PrimitivePackets

abbrev MulFixture := SubFixture

def multiply {bound : Nat} (f : MulFixture bound) : Except Unit (Fin bound) :=
  if small : f.lhs.val * f.rhs.val < bound then
    .ok ⟨f.lhs.val * f.rhs.val, small⟩
  else .error ()

theorem multiply_success {bound : Nat} (f : MulFixture bound)
    (small : f.lhs.val * f.rhs.val < bound) :
    multiply f = .ok ⟨f.lhs.val * f.rhs.val, small⟩ := dif_pos small

theorem multiply_refusal {bound : Nat} (f : MulFixture bound)
    (large : ¬ f.lhs.val * f.rhs.val < bound) : multiply f = .error () := dif_neg large

theorem multiply_wrong_result {bound : Nat} (f : MulFixture bound)
    (small : f.lhs.val * f.rhs.val < bound) (result : Fin bound)
    (wrong : result.val ≠ f.lhs.val * f.rhs.val) : multiply f ≠ .ok result := by
  rw [multiply_success f small]
  intro same
  exact wrong (congrArg Fin.val (Except.ok.inj same)).symm

inductive OriginalMulCase where
  | minimum | zero_left | zero_right | maximum | overflow | regular | double_overflow
  deriving DecidableEq, Repr

def mulFixture : OriginalMulCase → MulFixture wordBound
  | .minimum => ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  | .zero_left => ⟨⟨0, by decide⟩, ⟨wordBound-1, by decide⟩⟩
  | .zero_right => ⟨⟨wordBound-1, by decide⟩, ⟨0, by decide⟩⟩
  | .maximum => ⟨⟨wordBound-1, by decide⟩, ⟨1, by decide⟩⟩
  | .overflow => ⟨⟨wordBound-1, by decide⟩, ⟨2, by decide⟩⟩
  | .regular => ⟨⟨7, by decide⟩, ⟨9, by decide⟩⟩
  | .double_overflow => ⟨⟨wordBound-1, by decide⟩, ⟨wordBound-1, by decide⟩⟩

#print axioms multiply_success
#print axioms multiply_refusal
#print axioms multiply_wrong_result
end H62.PrimitivePackets
