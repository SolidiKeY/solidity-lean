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

private def wrapperFacts (C : Contract) : Facts C :=
  { eqs := [e C 0 1, e C 0 2, e C 1 2] }

theorem wrapperFirstMatch (C : Contract) : (wrapperFacts C).rw (v C 0) = v C 1 := by rfl

theorem wrapperNoChaining (C : Contract) :
    (Facts.rw { eqs := [e C 0 1, e C 1 2] } (v C 0)) = v C 1 := by rfl

theorem wrapperStorage (C : Contract) :
    (wrapperFacts C).rw (LTm.app0 .storage : LTm C .st) = .app0 .storage := by rfl

theorem wrapperMemory (C : Contract) :
    (wrapperFacts C).rw (LTm.app0 .memory : LTm C .mem) = .app0 .memory := by rfl

theorem wrapperInteger (C : Contract) :
    (wrapperFacts C).rw (LTm.app0 (.zlit 7) : LTm C .kint) = .app0 (.zlit 7) := by rfl

theorem wrapperPath (C : Contract) :
    (wrapperFacts C).rw (LTm.err : LTm C (.path (.prim .uint))) = .err := by rfl

#print axioms Facts.rw_eq_rwWith
#print axioms wrapperFirstMatch
#print axioms wrapperNoChaining
#print axioms wrapperStorage
#print axioms wrapperMemory
#print axioms wrapperInteger
#print axioms wrapperPath

#eval do
  let C : Contract := { vars := [] }
  let F := wrapperFacts C
  unless (F.rw (v C 0)).beqR (v C 1) && (Facts.rw { eqs := [e C 0 1, e C 1 2] } (v C 0)).beqR (v C 1) do
    throw (IO.userError "native wrapper value lookup changed")
  let terms : List ((s : Srt) × LTm C s) :=
    [⟨.st, .app0 .storage⟩, ⟨.mem, .app0 .memory⟩,
      ⟨.kint, .app0 (.zlit 7)⟩, ⟨.path (.prim .uint), .err⟩]
  for ⟨_, t⟩ in terms do
    unless (F.rw t).beqR t do
      throw (IO.userError "native wrapper nonvalue lookup changed")
  IO.println "six native wrapper controls passed; kernel wrapper controls checked separately"

end Solidity.Tests.FactsLookupSharing
