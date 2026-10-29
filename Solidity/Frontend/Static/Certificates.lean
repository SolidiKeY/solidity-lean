import Solidity.Roadmap.Frontend
import Solidity.Frontend.Static.Units
import Solidity.Frontend.Static.Consts
import Solidity.Frontend.Static.UserOps
import Solidity.Frontend.Static.Inheritance

/-!
# The static checkers as G05 `Checker` values

Values of G05's generic `Checker` structure (`Solidity/Roadmap/Frontend.lean`)
for the static frontend's judgments.  Each needs no certificate
(`Cert := Unit`): the checker decides its judgment outright, and is
complete.  They are not yet wired into a `FrontendSpec`/`Chain`: no
`FrontendSpec` instance exists, and assembling one from S00–S01 and G08–G14
is G15's (`docs/feature-work/frontend-static.md`, Handoff).

- `unitsChecker` (G12): a program and its remappings satisfy `UnitsOK`
  (distinct unit names, every import and imported symbol found, no clash in
  any file-level scope), the multi-unit part of what G05's resolution stage
  checks; S01's `Resolves'` is the per-unit part.
- `Program.libraries`: the `(unit name, library name)` pairs G05's
  `LinksResolved` reads.

- `metadataChecker` (G13): a resolved unit is S01-`WellFormed` (every
  body and initializer typed by `infer`/`inferS`) and in the syntax profile,
  decided exactly (`metadataChecker_complete`): the syntax and typing
  component of G05's metadata stage (the settings and links obligations of
  `FrontendSpec.SettingsRespected` stay G15's).  `strictMetadataChecker`
  adds G13's checks S01's `WellFormed` lacks (`StaticOK`): compile-time
  constant initializers, no cyclic constant, well-formed operator bindings.
- `inheritanceChecker` (G14): `InheritanceOK` (overrides, required
  overrides, implementations, base-constructor arguments, modifier
  invocations, `using for`), decided exactly.
-/

namespace Solidity.Frontend.Static

open Solidity.Source
open Solidity.Roadmap.Frontend (Checker)

/-- **G12's resolution checker**, sound by `unitsOK_iff`. -/
def unitsChecker : Checker (Program × List Remapping) Unit (fun pr _ => UnitsOK pr.1 pr.2) where
  Cert := Unit
  check pr _ _ := pr.1.unitsOK pr.2
  sound _ _ _ h := unitsOK_iff.mp h

/-- The checker is complete: it accepts every program G12's judgment admits. -/
theorem unitsChecker_complete (P : Program) (R : List Remapping) (h : UnitsOK P R) :
    unitsChecker.check (P, R) () () = true := unitsOK_iff.mpr h

/-- The library declarations of a program, by unit and name (G05's
`FrontendSpec.libraries`). -/
def _root_.Solidity.Source.Program.libraries (P : Program) : List (String × String) :=
  P.units.flatMap fun (u, s) =>
    (s.decls.filter fun d => d.kind == .library && d.scope == Option.none).map fun d => (u, d.name)

/-- **G13's metadata checker**: well-formedness (with all body typing) and
the syntax profile, sound and complete. -/
def metadataChecker : Checker Resolution Unit (fun r _ => WellFormed r ∧ InProfileSyntax r) where
  Cert := Unit
  check r _ _ := wellFormedB r && inProfileSyntaxB r
  sound r _ _ h := by
    simp only [Bool.and_eq_true] at h
    exact ⟨wellFormed_iff.mp h.1, inProfileSyntaxB_iff.mp h.2⟩

theorem metadataChecker_complete (r : Resolution) (h : WellFormed r ∧ InProfileSyntax r) :
    metadataChecker.check r () () = true := by
  show (wellFormedB r && inProfileSyntaxB r) = true
  rw [wellFormed_iff.mpr h.1, inProfileSyntaxB_iff.mpr h.2]
  rfl

/-- **G14's inheritance checker**, sound and complete. -/
def inheritanceChecker : Checker Resolution Unit (fun r _ => InheritanceOK r) where
  Cert := Unit
  check r _ _ := inheritanceB r
  sound _ _ _ h := inheritance_iff.mp h

theorem inheritanceChecker_complete (r : Resolution) (h : InheritanceOK r) :
    inheritanceChecker.check r () () = true :=
  inheritance_iff.mpr h

/-- G13's checks beyond S01's well-formedness: compile-time constant
initializers, no cyclic constant, well-formed operator bindings. -/
def StaticOK (r : Resolution) : Prop :=
  ConstInitsPure r ∧ ConstsAcyclic r.env ∧ UsingOpsOK r.env r.unit

/-- The metadata checker with G13's checks. -/
def strictMetadataChecker :
    Checker Resolution Unit (fun r _ => (WellFormed r ∧ InProfileSyntax r) ∧ StaticOK r) where
  Cert := Unit
  check r _ _ := wellFormedB r && inProfileSyntaxB r && constInitsB r && acyclicB r.env &&
    usingOpsB r.env r.unit
  sound r _ _ h := by
    simp only [Bool.and_eq_true] at h
    exact ⟨⟨wellFormed_iff.mp h.1.1.1.1, inProfileSyntaxB_iff.mp h.1.1.1.2⟩,
      constInitsB_iff.mp h.1.1.2, acyclic_iff.mp h.1.2, usingOpsB_iff.mp h.2⟩

end Solidity.Frontend.Static
/-- info: 'Solidity.Frontend.Static.metadataChecker_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.metadataChecker_complete
/-- info: 'Solidity.Frontend.Static.inheritanceChecker_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.inheritanceChecker_complete
