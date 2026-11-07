import «tests».h62.item4.«generic-primitive-packets».SubFixtures

/-! Regression: unsigned division and remainder must reject zero divisors even
when unchecked, rather than exposing the bare opcode's zero result. This is a
typed arithmetic classifier; execution is proved in UnsignedDivCorrespondence. -/
namespace H62.PrimitivePackets

def guardedUnsignedResult {bound : Nat} (op : Nat → Nat → Nat)
    (shrinks : ∀ n d, op n d ≤ n) (f : SubFixture bound) : Except Unit (Fin bound) :=
  if f.rhs.val = 0 then .error ()
  else .ok ⟨op f.lhs.val f.rhs.val, Nat.lt_of_le_of_lt (shrinks _ _) f.lhs.isLt⟩

theorem guardedUnsigned_success {bound : Nat} (op : Nat → Nat → Nat)
    (shrinks : ∀ n d, op n d ≤ n) (f : SubFixture bound) (nonzero : f.rhs.val ≠ 0) :
    guardedUnsignedResult op shrinks f =
      .ok ⟨op f.lhs.val f.rhs.val, Nat.lt_of_le_of_lt (shrinks _ _) f.lhs.isLt⟩ :=
  if_neg nonzero

theorem guardedUnsigned_refusal {bound : Nat} (op : Nat → Nat → Nat)
    (shrinks : ∀ n d, op n d ≤ n) (f : SubFixture bound) (zero : f.rhs.val = 0) :
    guardedUnsignedResult op shrinks f = .error () := if_pos zero

theorem guardedUnsigned_wrong_result {bound : Nat} (op : Nat → Nat → Nat)
    (shrinks : ∀ n d, op n d ≤ n) (f : SubFixture bound) (nonzero : f.rhs.val ≠ 0)
    (result : Fin bound) (wrong : result.val ≠ op f.lhs.val f.rhs.val) :
    guardedUnsignedResult op shrinks f ≠ .ok result := by
  rw [guardedUnsigned_success op shrinks f nonzero]
  intro same
  exact wrong (congrArg Fin.val (Except.ok.inj same)).symm

abbrev unsignedQuotient {bound : Nat} :=
  guardedUnsignedResult (bound:=bound) Nat.div Nat.div_le_self
abbrev unsignedRemainder {bound : Nat} :=
  guardedUnsignedResult (bound:=bound) Nat.mod Nat.mod_le

#print axioms guardedUnsigned_success
#print axioms guardedUnsigned_refusal
#print axioms guardedUnsigned_wrong_result
end H62.PrimitivePackets
