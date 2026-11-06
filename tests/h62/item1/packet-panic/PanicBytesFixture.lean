import Init

/-! Isolated list fixture. This does not define or prove anything about
`Solidity.Source.panicData`, execution or the target machine. -/
namespace H62.PacketPanic.Fixture

def canonical : List UInt8 :=
  [0x4e,0x48,0x7b,0x71] ++ List.replicate 31 0 ++ [0x11]

def truncated : List UInt8 := [0x4e,0x48,0x7b,0x71,0x11]

/-- Local copy of the byte recurrence for a bounded isolated test; it is not
linked to the repository's `Solidity.Source.beBytes`. -/
def fixtureBeBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => fixtureBeBytes k (n / 256) ++ [UInt8.ofNat (n % 256)]

def fixturePanicData (code : Nat) : List UInt8 :=
  [0x4e,0x48,0x7b,0x71] ++ fixtureBeBytes 32 (code % 2 ^ 256)

theorem fixture_arithmetic_encoding : fixturePanicData 0x11 = canonical := by
  decide

theorem fixture_panic_codes_differ : fixturePanicData 0x11 ≠ fixturePanicData 0x12 := by
  decide

theorem canonical_length : canonical.length = 36 := by
  decide

theorem canonical_ne_truncated : canonical ≠ truncated := by
  decide

theorem canonical_ne_empty : canonical ≠ [] := by
  decide

theorem length_from_exact (data : List UInt8) (h : data = canonical) :
    data.length = 36 := by
  rw [h]
  exact canonical_length

theorem not_truncated_from_exact (data : List UInt8) (h : data = canonical) :
    data ≠ truncated := by
  rw [h]
  exact canonical_ne_truncated

theorem not_empty_from_exact (data : List UInt8) (h : data = canonical) :
    data ≠ [] := by
  rw [h]
  exact canonical_ne_empty

#print axioms fixture_arithmetic_encoding
#print axioms fixture_panic_codes_differ
#print axioms canonical_length
#print axioms canonical_ne_truncated
#print axioms canonical_ne_empty
#print axioms length_from_exact
#print axioms not_truncated_from_exact
#print axioms not_empty_from_exact
end H62.PacketPanic.Fixture
