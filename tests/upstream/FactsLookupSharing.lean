import Solidity.Calculus.Closer.Facts

/-! Internal lookup performance controls, independent of compiler/EVM evidence.
The native implementation and the kernel recursor retain the same typed,
first-match lookup. -/
namespace Solidity.Tests.FactsLookupSharing
open Decide

private def v (C : Contract) (k : Nat) : LTm C (.val .bool) := .var k
private def e (C : Contract) (a b : Nat) : EqF C := ⟨.bool, v C a, v C b⟩

theorem emptyLookup (C : Contract) : Facts.rwWith (v C 0) [] = v C 0 := by rfl

theorem firstMatch (C : Contract) :
    Facts.rwWith (v C 0) [e C 0 1, e C 0 2] = v C 1 := by rfl

theorem wrongSortHead (C : Contract) :
    Facts.rwWith (v C 0) [⟨.uint, .var 0, .var 2⟩, e C 0 1] = v C 1 := by rfl

theorem noMatch (C : Contract) :
    Facts.rwWith (v C 0) [e C 1 2] = v C 0 := by rfl

theorem noChaining (C : Contract) :
    Facts.rwWith (v C 0) [e C 0 1, e C 1 2] = v C 1 := by rfl

theorem nonValueSort (C : Contract) :
    Facts.rwWith (LTm.err : LTm C .st) [e C 0 1] = .err := by rfl

#print axioms emptyLookup
#print axioms firstMatch
#print axioms wrongSortHead
#print axioms noMatch
#print axioms noChaining
#print axioms nonValueSort

#eval do
  let C : Contract := { vars := [] }
  let rows := [([], v C 0), ([e C 0 1, e C 0 2], v C 1),
    ([⟨.uint, .var 0, .var 2⟩, e C 0 1], v C 1),
    ([e C 1 2], v C 0), ([e C 0 1, e C 1 2], v C 1)]
  for (facts, expected) in rows do
    unless (Facts.rwWith (v C 0) facts).beqR expected do
      throw (IO.userError "native first-match lookup changed")
  unless (Facts.rwWith (LTm.err : LTm C .st) [e C 0 1]).beqR (.err : LTm C .st) do
    throw (IO.userError "native non-value lookup changed")
  IO.println "six native lookup controls passed; kernel controls checked separately"

end Solidity.Tests.FactsLookupSharing
