import Solidity.Lowering.P8.SourceProgramAcceptance
import Solidity.Lowering.P8.SourceProgramControls

/-! Actual source acceptance-bit controls. Original ordered-name controls
remain unchanged; a success bit does not replace their output-identity proofs. -/
namespace Solidity.Lowering.P8.SourceProgramAcceptanceControls
open Source Roadmap.Frontend

def resolution (q : Solidity.Frontend.Source.Pipeline) : Resolution :=
  resolveUnit (SourceResolutions.sourceSettings (Settings.ofPipeline q)) CheckedSyntax.Controls.tree

abbrev BaseAcceptance : Prop := ∀ q, (elabBaseArgs (resolution q).env "C").isSome = true
abbrev ContractAcceptance : Prop := ∀ q, elaborates (resolution q).env = true
theorem base_acceptance : BaseAcceptance := by
  intro q
  have hi : ((Solidity.Lowering.P8.SourceProgramAcceptanceControls.resolution q).env.inheritOf "C").inheritList = [] := by
    rw [show (Solidity.Lowering.P8.SourceProgramAcceptanceControls.resolution q).env.inheritOf "C" = .nil from rfl, Solidity.Source.Syn.inheritList]
  have hs : (Solidity.Source.elabInherit (Solidity.Lowering.P8.SourceProgramAcceptanceControls.resolution q).env "C"
      ((Solidity.Lowering.P8.SourceProgramAcceptanceControls.resolution q).env.inheritOf "C").inheritList).isSome = true := by
    rw [hi, Solidity.Source.elabInherit]
    rfl
  unfold Solidity.Source.elabBaseArgs
  cases he : Solidity.Source.elabInherit (Solidity.Lowering.P8.SourceProgramAcceptanceControls.resolution q).env "C"
      ((Solidity.Lowering.P8.SourceProgramAcceptanceControls.resolution q).env.inheritOf "C").inheritList with
  | none => rw [he] at hs; cases hs
  | some v => cases v; rfl

theorem contract_acceptance : ContractAcceptance := by
  intro q
  change ((true && true) && ((Solidity.Source.elabBaseArgs (Solidity.Lowering.P8.SourceProgramAcceptanceControls.resolution q).env "C").isSome && true)) = true
  rw [Solidity.Lowering.P8.SourceProgramAcceptanceControls.base_acceptance q]
  rfl

abbrev SingleControl : Prop := ∀ q, (SourceProgramControls.admitted q).map
  (fun es => es.map Prod.fst) = some ["C.sol"]

theorem single_control : SingleControl := by
  intro q
  have hm : Solidity.Lowering.P8.SourceMetadata.checkInput
      (Solidity.Lowering.P8.SourceMetadataControls.input q)
      (Solidity.Lowering.P8.SourceMetadataControls.parsed q)
      (Solidity.Lowering.P8.SourceResolutions.produce (Solidity.Lowering.P8.SourceMetadataControls.parsed q))
      Solidity.Lowering.P8.CheckedSyntax.Controls.layout = true := by
    cases q
    · exact Solidity.Lowering.P8.SourceMetadataControls.legacy_stages
    · exact Solidity.Lowering.P8.SourceMetadataControls.viaIR_stages
  have hf : (Solidity.Source.elaborate (Solidity.Lowering.P8.SourceProgramAcceptanceControls.resolution q)).isSome = true :=
    (Solidity.Lowering.P8.SourceProgramAcceptance.elaborate_acceptance _).trans
      (Solidity.Lowering.P8.SourceProgramAcceptanceControls.contract_acceptance q)
  unfold Solidity.Lowering.P8.SourceProgramControls.admitted Solidity.Lowering.P8.SourcePrograms.accept
  rw [hm]
  change (Solidity.Lowering.P8.SourcePrograms.elaborateUnits [("C.sol", Solidity.Lowering.P8.SourceProgramAcceptanceControls.resolution q)]).map (fun es => es.map Prod.fst) = some ["C.sol"]
  cases he : Solidity.Source.elaborate (Solidity.Lowering.P8.SourceProgramAcceptanceControls.resolution q) with
  | none => rw [he] at hf; cases hf
  | some el => simp only [Solidity.Lowering.P8.SourcePrograms.elaborateUnits, he, bind, pure, Option.bind, Option.map, List.map_cons, List.map_nil]

abbrev TwoControl : Prop := SourceProgramControls.admittedTwo.map (fun es => es.map Prod.fst) = some ["A.sol", "B.sol"]
abbrev CorruptedControl : Prop := SourceProgramControls.corrupted.isSome = false

theorem two_control : TwoControl := by
  have hf : (Solidity.Source.elaborate (Solidity.Lowering.P8.SourceProgramAcceptanceControls.resolution .legacy)).isSome = true :=
    (Solidity.Lowering.P8.SourceProgramAcceptance.elaborate_acceptance _).trans
      (Solidity.Lowering.P8.SourceProgramAcceptanceControls.contract_acceptance .legacy)
  unfold Solidity.Lowering.P8.SourceProgramAcceptanceControls.TwoControl Solidity.Lowering.P8.SourceProgramControls.admittedTwo Solidity.Lowering.P8.SourcePrograms.accept
  rw [Solidity.Lowering.P8.SourceMetadataControls.two_unit_stages]
  change (Solidity.Lowering.P8.SourcePrograms.elaborateUnits
    [("A.sol", Solidity.Lowering.P8.SourceProgramAcceptanceControls.resolution .legacy),
     ("B.sol", Solidity.Lowering.P8.SourceProgramAcceptanceControls.resolution .legacy)]).map
       (fun es => es.map Prod.fst) = some ["A.sol", "B.sol"]
  cases he : Solidity.Source.elaborate (Solidity.Lowering.P8.SourceProgramAcceptanceControls.resolution .legacy) with
  | none => rw [he] at hf; cases hf
  | some el => simp only [Solidity.Lowering.P8.SourcePrograms.elaborateUnits, he, bind, pure, Option.bind, Option.map, List.map_cons, List.map_nil]

theorem corrupted_control : CorruptedControl := rfl

/-- The original conjunction, with unchanged expectations. -/
abbrev PackedControls : Prop := SourceProgramControls.ContractControls

theorem packed_controls : PackedControls := by
  exact ⟨single_control .legacy, single_control .viaIR, two_control, corrupted_control⟩

/-- info: 'Solidity.Lowering.P8.SourceProgramAcceptanceControls.packed_controls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms packed_controls


/-- info: 'Solidity.Lowering.P8.SourceProgramAcceptanceControls.base_acceptance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms base_acceptance
/-- info: 'Solidity.Lowering.P8.SourceProgramAcceptanceControls.two_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms two_control
/-- info: 'Solidity.Lowering.P8.SourceProgramAcceptanceControls.corrupted_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms corrupted_control
/-- info: 'Solidity.Lowering.P8.SourceProgramAcceptanceControls.single_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms single_control
/-- info: 'Solidity.Lowering.P8.SourceProgramAcceptanceControls.contract_acceptance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms contract_acceptance
end Solidity.Lowering.P8.SourceProgramAcceptanceControls
