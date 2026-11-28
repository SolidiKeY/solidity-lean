import Solidity.Goals.LoweringSession

/-! # `InFragment` does not restrict the Source program to t0's accepted fragment

**Claim.** `Shrink.Lowering.InFragment P` is documented as "a Source program of t0's
accepted fragment: one with a compilation whose programs are all in it", and is the only
premise of `SessionLift` (so of `loweringBySimulation` and `loweringBySimulationV2`).

**Culprit.** `Solidity/Goals/LoweringSession.lean:142` (`InFragment`), with
`Compilation.Accepted` (`:124`) and the free fields `ctorArgs`/`entries` of `Compilation` (`:96`).

**Witness.** `Compilation.Accepted` only speaks of the programs `ctorArgs`/`entries` select, and
`InFragment` quantifies the compilation existentially with those two fields free. The
compilation that selects nothing is accepted, so `InFragment P` is exactly "some raw contract
has `P`'s function names" (`inFragment_iff_names`): `ProgOk []` constrains nothing about `P`.
`SessionLift` therefore asks for a refining compilation of every name-matched Source program,
inside t0's fragment or not, and its own conjunct `c.Accepted` is met by a compilation with
no entries (`accepted_of_no_entries`); only `BodiesBound` and `Lift` carry content.

**Suggested fix.** State the fragment on the Source program itself, or bind `ctorArgs`/`entries`
to the Source program's ABI (every external function selected, `ctorArgs` total) before
asking `Accepted`. -/

namespace Solidity.Examples.RedTeam.Statements.InFragmentNames

open Solidity.Goals.Shrink.Lowering

variable [FreshNames]

/-- A compilation that selects no deployment and no entry is "accepted", whatever its contract. -/
theorem accepted_of_no_entries (C : Contract) :
    (⟨C, fun _ => none, fun _ => none⟩ : Compilation).Accepted :=
  ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h)⟩

/-- `InFragment` is name matching alone: the acceptance clause excludes no Source program. -/
theorem inFragment_iff_names {E : Source.Env} (P : Source.SrcProg E) :
    InFragment P ↔ ∃ c : Compilation, c.Names P :=
  ⟨fun ⟨c, h, _⟩ => ⟨c, h⟩,
   fun ⟨c, h⟩ => ⟨⟨c.C, fun _ => none, fun _ => none⟩, h, accepted_of_no_entries c.C⟩⟩

/-- info: 'Solidity.Examples.RedTeam.Statements.InFragmentNames.accepted_of_no_entries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms accepted_of_no_entries

/--
info: 'Solidity.Examples.RedTeam.Statements.InFragmentNames.inFragment_iff_names' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms inFragment_iff_names

end Solidity.Examples.RedTeam.Statements.InFragmentNames
