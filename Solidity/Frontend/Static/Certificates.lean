import Solidity.Roadmap.Frontend
import Solidity.Frontend.Static.Units

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

G13's typing checker and G14's inheritance checker add their instances in
their own modules.
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

end Solidity.Frontend.Static
