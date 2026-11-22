import Solidity.FreshNames

/-! Universal fresh-name laws and rejected-scheme checks. -/
namespace Solidity.Examples.FreshNamesLaw

/-- The default spelling reads back at every index, including zero. -/
example (base : String) (hb : base ∈ ["se", "sp", "ie", "mv", "cnt", "brk", "first", "ret"])
    (index : Nat) :
    (inferInstance : FreshNames).parse ((inferInstance : FreshNames).name base index) =
      some (base, index) :=
  FreshNames.roundTrip base hb index

private def table : FreshNames := .ofTable [("value", "se1"), ("path", "sp2")]

/-- A table certifies unchanged names as well as its explicit aliases. -/
example (base : String) (hb : base ∈ ["se", "sp", "ie", "mv", "cnt", "brk", "first", "ret"])
    (index : Nat) : table.parse (table.name base index) = some (base, index) :=
  table.roundTrip base hb index

/-- An alias that masks another default spelling fails the finite table check. -/
example : FreshNames.tableValid [("se2", "se1")] = false := by decide

/-- Reusing a prefix for two required identities fails the finite prefix check. -/
example : FreshNames.prefixesValid "tmp" "tmp" "idx" "mref" = false := by decide

/-- Configurable prefixes cannot steal the fixed source-capture spelling. -/
example : FreshNames.prefixesValid "source" "sp" "ie" "mv" = false := by decide

/-- No FreshNames value can pair a constant printer with a constant parser. -/
example : ¬ ∃ names : FreshNames,
    names.name = (fun _ _ => "alias") ∧ names.parse = (fun _ => some ("se", 0)) := by
  rintro ⟨names, hn, hp⟩
  have h := names.roundTrip "se" (by simp) 1
  rw [hn, hp] at h
  cases h

end Solidity.Examples.FreshNamesLaw
