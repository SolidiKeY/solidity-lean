import Solidity.Lowering.P8.SourceResolutions
import Solidity.Frontend.Static.Certificates

/-! Composition of existing G12/G13/G14 component metadata judgments over
all actual source resolutions. This is not the full G00/G15 profile or a
proof of global imported-name typing, source execution or SourceSpec. -/
namespace Solidity.Lowering.P8.SourceMetadata
open Solidity.Source
open Solidity.Roadmap.Frontend
open Solidity.Frontend.Static
open SourceResolutions CheckedSyntax

/-- Existing component judgments, without adding or weakening any field. -/
def UnitOK (r : Resolution) : Prop :=
  ((WellFormed r ∧ InProfileSyntax r) ∧ StaticOK r) ∧ InheritanceOK r

def unitCheck (r : Resolution) : Bool :=
  strictMetadataChecker.check r () () && inheritanceChecker.check r () ()

theorem strict_iff (r : Resolution) :
    strictMetadataChecker.check r () () = true ↔
      (WellFormed r ∧ InProfileSyntax r) ∧ StaticOK r := by
  simp only [strictMetadataChecker, Bool.and_eq_true, wellFormed_iff,
    inProfileSyntaxB_iff, constInitsB_iff, acyclic_iff, usingOpsB_iff, StaticOK, and_assoc]

theorem unitCheck_iff (r : Resolution) : unitCheck r = true ↔ UnitOK r := by
  simp only [unitCheck, Bool.and_eq_true, strict_iff, inheritanceChecker, inheritance_iff, UnitOK]

/-- Syntax comes from each actual resolution; checked resolution connects
these trees back to the original-byte parse, separately from metadata. -/
def unitSet (r : Packet) : UnitSet := ⟨r.units.map (fun u => (u.1, u.2.unit))⟩

/-- No remapping field exists in the current raw Input; this uses the existing
empty-remapping unit relation rather than inventing an extra input setting. -/
def ComponentOK (r : Packet) : Prop :=
  r.settings.Ok ∧ r.main ∈ r.units.map Prod.fst ∧
    UnitsOK (unitSet r) [] ∧ ∀ u ∈ r.units, UnitOK u.2

def metadata (r : Packet) : Bool :=
  settingsB r.settings && decide (r.main ∈ r.units.map Prod.fst) &&
    (unitSet r).unitsOK [] && r.units.all (fun u => unitCheck u.2)

theorem metadata_iff (r : Packet) : metadata r = true ↔ ComponentOK r := by
  simp only [metadata, Bool.and_eq_true, settingsB_iff, decide_eq_true_eq,
    unitsOK_iff, List.all_eq_true, unitCheck_iff, ComponentOK, and_assoc]

def checker : Checker Packet Unit (fun r _ => ComponentOK r) where
  Cert := Unit
  check r _ _ := metadata r
  sound r _ _ h := (metadata_iff r).mp h

/-- Exact completeness for this conjunction of existing component judgments,
not completeness of a parser, whole frontend or approved source profile. -/
theorem metadata_complete (r : Packet) (h : ComponentOK r) : metadata r = true :=
  (metadata_iff r).mpr h

def checkInput (i : Input) (p : Parsed) (r : Packet) (c : CheckedSyntax.Cert) : Bool :=
  SourceResolutions.checkInput i p r c && metadata r

theorem input_sound (i : Input) (p : Parsed) (r : Packet) (c : CheckedSyntax.Cert)
    (h : checkInput i p r c = true) :
    i.Ok ∧ Parses i p ∧ SourceResolutions.Resolves p r ∧ ComponentOK r := by
  simp only [checkInput, Bool.and_eq_true] at h
  obtain ⟨hi, hp, hr⟩ := SourceResolutions.input_sound i p r c h.1
  exact ⟨hi, hp, hr, (metadata_iff r).mp h.2⟩

theorem every_unit_checked {r : Packet} (h : metadata r = true)
    {u : String × Resolution} (hu : u ∈ r.units) : UnitOK u.2 :=
  (metadata_iff r).mp h |>.2.2.2 u hu

/-- A resolved output's actual syntax roster equals the checked parser's
roster. A metadata certificate cannot quietly substitute different trees. -/
theorem parsed_units_preserved {p : Parsed} {r : Packet}
    (h : SourceResolutions.Resolves p r) : (unitSet r).units = p.units := by
  have he : r = produce p := SourceResolutions.unique h (produce_resolves p)
  rw [he]
  simp only [unitSet, SourceResolutions.produce, List.map_map, Source.resolveUnit, Function.comp_def]
  exact List.map_id'' (fun u => by cases u; rfl) p.units

#print axioms unitCheck_iff
#print axioms metadata_iff
#print axioms input_sound
#print axioms every_unit_checked
end Solidity.Lowering.P8.SourceMetadata
