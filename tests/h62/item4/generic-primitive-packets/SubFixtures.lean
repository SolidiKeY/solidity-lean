/-!
Isolated arithmetic backfill for the seven original CheckedSub target cases.
This dependency-free fixture layer does not claim EVM/Source correspondence;
the separate SubCorrespondence module supplies a live intrinsic bridge; the
pinned-v4.35 migration checks remain separate. In particular,
Except Unit is a local arithmetic classification, not a replacement for Evm.Out.
-/
namespace H62.PrimitivePackets

/-- Both operands carry their range, so malformed fixture inputs are impossible. -/
structure SubFixture (bound : Nat) where
  lhs : Fin bound
  rhs : Fin bound

/-- Checked subtraction: a successful result remains intrinsically in range. -/
def subtract {bound : Nat} (f : SubFixture bound) : Except Unit (Fin bound) :=
  if _enough : f.rhs.val ≤ f.lhs.val then
    .ok ⟨f.lhs.val - f.rhs.val, Nat.lt_of_le_of_lt (Nat.sub_le _ _) f.lhs.isLt⟩
  else .error ()

/-- One parameterized equation for every successful typed fixture. -/
theorem subtract_success {bound : Nat} (f : SubFixture bound)
    (enough : f.rhs.val ≤ f.lhs.val) :
    subtract f = .ok ⟨f.lhs.val - f.rhs.val,
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) f.lhs.isLt⟩ := by
  exact dif_pos enough

/-- Failure is retained instead of silently wrapping or truncating. -/
theorem subtract_refusal {bound : Nat} (f : SubFixture bound)
    (underflow : ¬ f.rhs.val ≤ f.lhs.val) : subtract f = .error () := by
  exact dif_neg underflow

/-- The result is the exact natural difference, with no table-based decision. -/
theorem subtract_exact {bound : Nat} (f : SubFixture bound)
    (enough : f.rhs.val ≤ f.lhs.val) :
    ∃ result : Fin bound, subtract f = .ok result ∧ result.val + f.rhs.val = f.lhs.val := by
  exact ⟨⟨f.lhs.val - f.rhs.val,
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) f.lhs.isLt⟩,
    subtract_success f enough, Nat.sub_add_cancel enough⟩

/-- A failing input cannot masquerade as any in-range successful word. -/
theorem subtract_no_success {bound : Nat} (f : SubFixture bound)
    (underflow : ¬ f.rhs.val ≤ f.lhs.val) (result : Fin bound) :
    subtract f ≠ .ok result := by
  rw [subtract_refusal f underflow]
  intro impossible
  cases impossible

/-- Correct classification cannot silently accept a corrupted result. -/
theorem subtract_wrong_result {bound : Nat} (f : SubFixture bound)
    (enough : f.rhs.val ≤ f.lhs.val) (result : Fin bound)
    (wrong : result.val ≠ f.lhs.val - f.rhs.val) : subtract f ≠ .ok result := by
  rw [subtract_success f enough]
  intro same
  exact wrong (congrArg Fin.val (Except.ok.inj same)).symm

/-- Names match the original declarations; no extra cases inflate coverage. -/
inductive OriginalSubCase where
  | minimum | maximum | equal | regular | underflow | far_underflow | wrong_order_refused
  deriving DecidableEq, Repr

abbrev wordBound : Nat := 2^256

/-- The entire original CheckedSub concrete target-input table (seven rows).
Other controls (tail corruption, panic bytes, alias/value refusal, fuel, frame)
remain separate obligations in the census; these rows do not replace them. -/
def fixture : OriginalSubCase → SubFixture wordBound
  | .minimum => ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  | .maximum => ⟨⟨wordBound-1, by decide⟩, ⟨0, by decide⟩⟩
  | .equal => ⟨⟨7, by decide⟩, ⟨7, by decide⟩⟩
  | .regular => ⟨⟨9, by decide⟩, ⟨7, by decide⟩⟩
  | .underflow => ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩
  | .far_underflow => ⟨⟨0, by decide⟩, ⟨wordBound-1, by decide⟩⟩
  | .wrong_order_refused => ⟨⟨7, by decide⟩, ⟨9, by decide⟩⟩

/-- All table rows inherit exactness from the same parameterized proof. -/
theorem fixture_exact (c : OriginalSubCase)
    (enough : (fixture c).rhs.val ≤ (fixture c).lhs.val) :
    ∃ result : Fin wordBound, subtract (fixture c) = .ok result ∧
      result.val + (fixture c).rhs.val = (fixture c).lhs.val :=
  subtract_exact (fixture c) enough

theorem fixture_refusal (c : OriginalSubCase)
    (underflow : ¬ (fixture c).rhs.val ≤ (fixture c).lhs.val) :
    subtract (fixture c) = .error () := subtract_refusal (fixture c) underflow

/-- One positive and one negative specialization exercise both branches. -/
example : subtract (fixture .regular) = .ok ⟨2, by decide⟩ :=
  subtract_success (fixture .regular) (by decide)
example : subtract (fixture .wrong_order_refused) = .error () :=
  subtract_refusal (fixture .wrong_order_refused) (by decide)

#print axioms subtract_success
#print axioms subtract_refusal
#print axioms subtract_exact
#print axioms subtract_no_success
#print axioms subtract_wrong_result
#print axioms fixture_exact
#print axioms fixture_refusal
end H62.PrimitivePackets
