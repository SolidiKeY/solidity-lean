import Solidity.Lowering.P8.SourceMetadata

/-! Settings closure of the existing COMPONENT stage chain. This does not
instantiate SourceSpec.AllPipelines or prove full G00/G15 profile closure.
Source bytes, syntax, names, main and certificates are kept fixed. -/
namespace Solidity.Lowering.P8.SourceAllSettings
open Solidity.Roadmap.Frontend

/-- Existing static component checks inspect original trees/environments,
not the changing pipeline/coder fields. Both settings values are admitted;
there is no claim about arbitrary unsupported order/coder combinations. -/
theorem metadata_settings (p : CheckedSyntax.Parsed) (s : Settings)
    (hp : p.settings.Ok) (hs : s.Ok) :
    SourceMetadata.metadata (SourceResolutions.produce {p with settings := s}) =
      SourceMetadata.metadata (SourceResolutions.produce p) := by
  simp only [SourceMetadata.metadata, SourceResolutions.produce,
    (CheckedSyntax.settingsB_iff p.settings).mpr hp,
    (CheckedSyntax.settingsB_iff s).mpr hs,
    SourceMetadata.unitSet, List.map_map, Function.comp_def, List.all_map,
    Source.resolveUnit, SourceMetadata.unitCheck, Frontend.Static.strictMetadataChecker,
    Frontend.Static.inheritanceChecker, Frontend.Static.wellFormedB,
    Frontend.Static.inProfileSyntaxB, Frontend.Static.constInitsB,
    Frontend.Static.usingOpsB, Frontend.Static.inheritanceB]

/-- The actual composed component stages stay accepted under every admitted
settings value. No equality of execution outcomes is asserted: pipeline and
coder fields intentionally change, while original source/certificates do not. -/
theorem input_settings (i : Input) (p : CheckedSyntax.Parsed) (r : SourceResolutions.Packet)
    (c : CheckedSyntax.Cert) (s : Settings)
    (h : SourceMetadata.checkInput i p r c = true) (hs : s.Ok) :
    SourceMetadata.checkInput {i with settings := s} {p with settings := s}
      (SourceResolutions.produce {p with settings := s}) c = true := by
  simp only [SourceMetadata.checkInput, SourceResolutions.checkInput, Bool.and_eq_true] at h
  have hr : SourceResolutions.Resolves p r := (SourceResolutions.check_iff p r).mp h.1.2
  have he : r = SourceResolutions.produce p :=
    SourceResolutions.unique hr (SourceResolutions.produce_resolves p)
  subst r
  have hp : p.settings.Ok := (SourceMetadata.metadata_iff _).mp h.2 |>.1
  have hraw : CheckedSyntax.rawB {i with settings := s} = true := by
    have hold := h.1.1.1
    simp_all only [CheckedSyntax.rawB, Bool.and_eq_true, CheckedSyntax.settingsB_iff,
      decide_eq_true_eq, and_true]
  have hparse : CheckedSyntax.check {i with settings := s} {p with settings := s} c = true := by
    have hold := h.1.1.2
    simp_all only [CheckedSyntax.check, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq, and_true]
  simp only [SourceMetadata.checkInput, SourceResolutions.checkInput, hraw, hparse,
    SourceResolutions.produce_checked, metadata_settings p s hp hs, h.2, Bool.and_true]

#print axioms input_settings
#print axioms metadata_settings
end Solidity.Lowering.P8.SourceAllSettings
