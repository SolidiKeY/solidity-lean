import «tests».h62.item4.«generic-primitive-packets».SignedFixtures

/-! Regression: signed checked subtraction and multiplication must reject both
overflow directions, including both orders of min-int times minus one. This
shared typed arithmetic classifier is not an execution interpreter; separate
correspondence modules run the published Source and selected-code semantics. -/
namespace H62.PrimitivePackets

def checkedSignedResult {lo hi : Int} (op : Int → Int → Int) (f : SignedFixture lo hi) :
    Except Unit {z : Int // lo ≤ z ∧ z ≤ hi} :=
  if fits : lo ≤ op f.lhs.val f.rhs.val ∧ op f.lhs.val f.rhs.val ≤ hi then
    .ok ⟨op f.lhs.val f.rhs.val,fits⟩
  else .error ()

theorem checkedSigned_success {lo hi : Int} (op : Int → Int → Int) (f : SignedFixture lo hi)
    (fits : lo ≤ op f.lhs.val f.rhs.val ∧ op f.lhs.val f.rhs.val ≤ hi) :
    checkedSignedResult op f = .ok ⟨op f.lhs.val f.rhs.val,fits⟩ := dif_pos fits

theorem checkedSigned_refusal {lo hi : Int} (op : Int → Int → Int) (f : SignedFixture lo hi)
    (outside : ¬ (lo ≤ op f.lhs.val f.rhs.val ∧ op f.lhs.val f.rhs.val ≤ hi)) :
    checkedSignedResult op f = .error () := dif_neg outside

theorem checkedSigned_wrong_result {lo hi : Int} (op : Int → Int → Int)
    (f : SignedFixture lo hi)
    (fits : lo ≤ op f.lhs.val f.rhs.val ∧ op f.lhs.val f.rhs.val ≤ hi)
    (result : {z : Int // lo ≤ z ∧ z ≤ hi})
    (wrong : result.val ≠ op f.lhs.val f.rhs.val) : checkedSignedResult op f ≠ .ok result := by
  rw [checkedSigned_success op f fits]
  intro same
  exact wrong (congrArg Subtype.val (Except.ok.inj same)).symm

abbrev signedSubtract {lo hi : Int} := checkedSignedResult (lo:=lo) (hi:=hi) Int.sub
abbrev signedMultiply {lo hi : Int} := checkedSignedResult (lo:=lo) (hi:=hi) Int.mul

inductive OriginalSignedSubCase where
  | upper | lower | regular | minimum_success | maximum_success
  deriving DecidableEq, Repr

def signedSubFixture : OriginalSignedSubCase → SignedFixture signedLower signedUpper
  | .upper => ⟨⟨signedUpper,by decide⟩,⟨-1,by decide⟩⟩
  | .lower => ⟨⟨signedLower,by decide⟩,⟨1,by decide⟩⟩
  | .regular => ⟨⟨7,by decide⟩,⟨2,by decide⟩⟩
  | .minimum_success => ⟨⟨signedLower,by decide⟩,⟨0,by decide⟩⟩
  | .maximum_success => ⟨⟨signedUpper,by decide⟩,⟨0,by decide⟩⟩

inductive OriginalSignedMulCase where
  | minimum_minus | minus_minimum | upper | upper_negative | lower | lower_swapped | lower_maximum | regular | regular_positive | regular_both_positive | regular_swapped | minimum_one | one_minimum | maximum_minus | minus_maximum | minimum_zero | zero_minimum
  deriving DecidableEq, Repr

def signedMulFixture : OriginalSignedMulCase → SignedFixture signedLower signedUpper
  | .minimum_minus => ⟨⟨signedLower,by decide⟩,⟨-1,by decide⟩⟩
  | .minus_minimum => ⟨⟨-1,by decide⟩,⟨signedLower,by decide⟩⟩
  | .upper => ⟨⟨signedUpper,by decide⟩,⟨2,by decide⟩⟩
  | .upper_negative => ⟨⟨signedLower,by decide⟩,⟨signedLower,by decide⟩⟩
  | .lower => ⟨⟨signedLower,by decide⟩,⟨2,by decide⟩⟩
  | .lower_swapped => ⟨⟨2,by decide⟩,⟨signedLower,by decide⟩⟩
  | .lower_maximum => ⟨⟨signedUpper,by decide⟩,⟨-9,by decide⟩⟩
  | .regular => ⟨⟨-7,by decide⟩,⟨9,by decide⟩⟩
  | .regular_positive => ⟨⟨-7,by decide⟩,⟨-9,by decide⟩⟩
  | .regular_both_positive => ⟨⟨7,by decide⟩,⟨9,by decide⟩⟩
  | .regular_swapped => ⟨⟨9,by decide⟩,⟨-7,by decide⟩⟩
  | .minimum_one => ⟨⟨signedLower,by decide⟩,⟨1,by decide⟩⟩
  | .one_minimum => ⟨⟨1,by decide⟩,⟨signedLower,by decide⟩⟩
  | .maximum_minus => ⟨⟨signedUpper,by decide⟩,⟨-1,by decide⟩⟩
  | .minus_maximum => ⟨⟨-1,by decide⟩,⟨signedUpper,by decide⟩⟩
  | .minimum_zero => ⟨⟨signedLower,by decide⟩,⟨0,by decide⟩⟩
  | .zero_minimum => ⟨⟨0,by decide⟩,⟨signedLower,by decide⟩⟩

#print axioms checkedSigned_success
#print axioms checkedSigned_refusal
#print axioms checkedSigned_wrong_result
end H62.PrimitivePackets
