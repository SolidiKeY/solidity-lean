import «tests».h62.item4.«generic-primitive-packets».SubFixtures

/-! Regression: checked-add fixtures must classify overflow instead of wrapping.
The five rows name the existing CheckedAdd target-input controls; this arithmetic
layer alone proves no Source or EVM execution. AddCorrespondence supplies that
separate live bridge. Other original controls remain separate obligations. -/
namespace H62.PrimitivePackets

abbrev AddFixture := SubFixture

def add {bound : Nat} (f : AddFixture bound) : Except Unit (Fin bound) :=
  if small : f.lhs.val + f.rhs.val < bound then
    .ok ⟨f.lhs.val + f.rhs.val, small⟩
  else .error ()

theorem add_success {bound : Nat} (f : AddFixture bound)
    (small : f.lhs.val + f.rhs.val < bound) :
    add f = .ok ⟨f.lhs.val + f.rhs.val, small⟩ := dif_pos small

theorem add_refusal {bound : Nat} (f : AddFixture bound)
    (large : ¬ f.lhs.val + f.rhs.val < bound) : add f = .error () := dif_neg large

theorem add_wrong_result {bound : Nat} (f : AddFixture bound)
    (small : f.lhs.val + f.rhs.val < bound) (result : Fin bound)
    (wrong : result.val ≠ f.lhs.val + f.rhs.val) : add f ≠ .ok result := by
  rw [add_success f small]
  intro same
  exact wrong (congrArg Fin.val (Except.ok.inj same)).symm

inductive OriginalAddCase where
  | minimum | maximum | overflow | regular | double_overflow
  deriving DecidableEq, Repr

def addFixture : OriginalAddCase → AddFixture wordBound
  | .minimum => ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  | .maximum => ⟨⟨wordBound-1, by decide⟩, ⟨0, by decide⟩⟩
  | .overflow => ⟨⟨wordBound-1, by decide⟩, ⟨1, by decide⟩⟩
  | .regular => ⟨⟨7, by decide⟩, ⟨9, by decide⟩⟩
  | .double_overflow => ⟨⟨wordBound-1, by decide⟩, ⟨wordBound-1, by decide⟩⟩

#print axioms add_success
#print axioms add_refusal
#print axioms add_wrong_result
end H62.PrimitivePackets
