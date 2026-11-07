import Init

/-! Regression: checked signed addition must reject both overflow directions
and retain negative operands. This typed arithmetic classifier alone is not
Source or selected-code execution; SignedAddCorrespondence supplies that link. -/
namespace H62.PrimitivePackets

structure SignedFixture (lo hi : Int) where
  lhs : {z : Int // lo ≤ z ∧ z ≤ hi}
  rhs : {z : Int // lo ≤ z ∧ z ≤ hi}

def signedAdd {lo hi : Int} (f : SignedFixture lo hi) :
    Except Unit {z : Int // lo ≤ z ∧ z ≤ hi} :=
  if small : lo ≤ f.lhs.val+f.rhs.val ∧ f.lhs.val+f.rhs.val ≤ hi then
    .ok ⟨f.lhs.val+f.rhs.val,small⟩
  else .error ()

theorem signedAdd_success {lo hi : Int} (f : SignedFixture lo hi)
    (small : lo ≤ f.lhs.val+f.rhs.val ∧ f.lhs.val+f.rhs.val ≤ hi) :
    signedAdd f = .ok ⟨f.lhs.val+f.rhs.val,small⟩ := dif_pos small

theorem signedAdd_refusal {lo hi : Int} (f : SignedFixture lo hi)
    (outside : ¬ (lo ≤ f.lhs.val+f.rhs.val ∧ f.lhs.val+f.rhs.val ≤ hi)) :
    signedAdd f = .error () := dif_neg outside

theorem signedAdd_wrong_result {lo hi : Int} (f : SignedFixture lo hi)
    (small : lo ≤ f.lhs.val+f.rhs.val ∧ f.lhs.val+f.rhs.val ≤ hi)
    (result : {z : Int // lo ≤ z ∧ z ≤ hi})
    (wrong : result.val ≠ f.lhs.val+f.rhs.val) : signedAdd f ≠ .ok result := by
  rw [signedAdd_success f small]
  intro same
  exact wrong (congrArg Subtype.val (Except.ok.inj same)).symm

def signedLower : Int := -((2^255 : Nat) : Int)
def signedUpper : Int := ((2^255 : Nat) : Int)-1

inductive OriginalSignedAddCase where
  | maximum | minimum | positive_overflow | negative_overflow | mixed_signs
  deriving DecidableEq, Repr

/-- The five original SignedCheckedAdd Source input rows, without extra cases. -/
def signedAddFixture : OriginalSignedAddCase → SignedFixture signedLower signedUpper
  | .maximum => ⟨⟨signedUpper,by decide⟩,⟨0,by decide⟩⟩
  | .minimum => ⟨⟨signedLower,by decide⟩,⟨0,by decide⟩⟩
  | .positive_overflow => ⟨⟨signedUpper,by decide⟩,⟨1,by decide⟩⟩
  | .negative_overflow => ⟨⟨signedLower,by decide⟩,⟨-1,by decide⟩⟩
  | .mixed_signs => ⟨⟨-7,by decide⟩,⟨9,by decide⟩⟩

#print axioms signedAdd_success
#print axioms signedAdd_refusal
#print axioms signedAdd_wrong_result
end H62.PrimitivePackets
