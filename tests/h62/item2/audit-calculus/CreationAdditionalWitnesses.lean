import Solidity.Backend.Creation.LawChecks
import Solidity.Backend.Creation.ImmutableChecks
import Solidity.Backend.Creation.PlacementChecks
import tests.h62.item2.«audit-calculus».PrivateCommands

/-! Exact joint fixtures for patch/layout/provenance/link/immutable interfaces.
Private source helpers remain explicitly accounted. These encoding/layout
witnesses do not assert frontend source-map fidelity, source constructor
evaluation, gas adequacy or historical-fork execution. -/
namespace H62.AuditCalculus.CreationAdditional
open Solidity.Backend Solidity.Backend.Creation

private theorem outside_zero :
    ∀ p ∈ immutableTable.patches, 0 < p.location.offset ∨ p.location.offset + 32 ≤ 0 := by
  intro p hp
  change p ∈ [patchOne, patchTwo] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> exact Or.inl (by decide)

#joint_premises Solidity.Backend.Creation.patchAt_length as case_1_premises
/-- All dependent inputs and hypotheses of the exact unchanged declaration. -/
theorem case_1_joint : case_1_premises := ⟨[0, 0, 0, 0], [0x11], 1, by decide, True.intro⟩

#joint_premises Solidity.Backend.Creation.patchAt_get as case_2_premises
/-- All dependent inputs and hypotheses of the exact unchanged declaration. -/
theorem case_2_joint : case_2_premises := ⟨[0, 0, 0, 0], [0x11], 1, 1, by decide, True.intro⟩

#joint_premises Solidity.Backend.Creation.patchAt_frame as case_3_premises
/-- All dependent inputs and hypotheses of the exact unchanged declaration. -/
theorem case_3_joint : case_3_premises := ⟨[0, 0, 0, 0], [0x11], 1, 0, by decide, Or.inl (by decide), True.intro⟩

#joint_premises Solidity.Backend.Creation.patchAt_commute as case_4_premises
/-- All dependent inputs and hypotheses of the exact unchanged declaration. -/
theorem case_4_joint : case_4_premises := ⟨[0, 0, 0, 0], [0x11], [0x22], 1, 3, by decide, by decide, Or.inl (by decide), True.intro⟩

#joint_premises Solidity.Backend.Creation.section_slice as case_5_premises
/-- All dependent inputs and hypotheses of the exact unchanged declaration. -/
theorem case_5_joint : case_5_premises := ⟨String, sample, .runtime, True.intro⟩

#joint_premises Solidity.Backend.Creation.section_bounds as case_6_premises
/-- All dependent inputs and hypotheses of the exact unchanged declaration. -/
theorem case_6_joint : case_6_premises := ⟨String, sample, .arguments, True.intro⟩

#joint_premises Solidity.Backend.Creation.Provenance.global_bounds as case_7_premises
/-- All dependent inputs and hypotheses of the exact unchanged declaration. -/
theorem case_7_joint : case_7_premises := ⟨String, sample, sampleOrigin, True.intro⟩

#joint_premises Solidity.Backend.Creation.Provenance.bytes_exact as case_8_premises
/-- All dependent inputs and hypotheses of the exact unchanged declaration. -/
theorem case_8_joint : case_8_premises := ⟨String, sample, sampleOrigin, True.intro⟩

#joint_premises Solidity.Backend.Creation.link_permutation as case_9_premises
/-- All dependent inputs and hypotheses of the exact unchanged declaration. -/
theorem case_9_joint : case_9_premises := ⟨Nat, tripleCode, [siteA, siteB, siteC], [siteC, siteA, siteB], by decide, List.perm_append_comm (l₁ := [siteA, siteB]) (l₂ := [siteC]), tripleAddress, True.intro⟩

#joint_premises Solidity.Backend.Creation.Artifact.payload_deterministic as case_10_premises
/-- All dependent inputs and hypotheses of the exact unchanged declaration. -/
theorem case_10_joint : case_10_premises := ⟨String, sample, sampleOtherMetadata, rfl, rfl, True.intro⟩

#joint_premises Solidity.Backend.Creation.Artifact.sections_unique as case_11_premises
/-- All dependent inputs and hypotheses of the exact unchanged declaration. -/
theorem case_11_joint : case_11_premises := ⟨String, sample, sampleOtherMetadata, rfl, rfl, True.intro⟩

#joint_premises Solidity.Backend.Creation.wrapper_decode as case_12_premises
/-- All dependent inputs and hypotheses of the exact unchanged declaration. -/
theorem case_12_joint : case_12_premises := ⟨sample.lengthWord, True.intro⟩

#joint_private_premises Solidity.Backend.Creation.ArtifactLaws Solidity.Backend.Creation.fold_bytes as case_13_premises
/-- All dependent inputs and hypotheses of the exact unchanged declaration. -/
theorem case_13_joint : case_13_premises := ⟨tripleCode.length, Nat, [siteA, siteB, siteC], ⟨tripleCode, rfl⟩, tripleAddress, True.intro⟩

#joint_private_premises Solidity.Backend.Creation.ArtifactLaws Solidity.Backend.Creation.separated_members as case_14_premises
/-- All dependent inputs and hypotheses of the exact unchanged declaration. -/
theorem case_14_joint : case_14_premises := ⟨tripleCode.length, Nat, [siteA, siteB, siteC], by decide, siteA, siteC, List.mem_cons_self, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), True.intro⟩

#joint_premises Solidity.Backend.Creation.patchImmutables_length as case_15_premises
/-- All dependent inputs and hypotheses of the exact unchanged declaration. -/
theorem case_15_joint : case_15_premises := ⟨immutableArtifact.runtime.length, String, immutableTable.patches, immutableArtifact.runtime, rfl, True.intro⟩

#joint_premises Solidity.Backend.Creation.patchImmutables_frame as case_16_premises
/-- All dependent inputs and hypotheses of the exact unchanged declaration. -/
theorem case_16_joint : case_16_premises := ⟨immutableArtifact.runtime.length, String, immutableTable.patches, immutableArtifact.runtime, rfl, 0, outside_zero, True.intro⟩

#joint_premises Solidity.Backend.Creation.patchImmutables_read as case_17_premises
/-- All dependent inputs and hypotheses of the exact unchanged declaration. -/
theorem case_17_joint : case_17_premises := ⟨immutableArtifact.runtime.length, String, immutableTable.patches, immutableArtifact.runtime, rfl, immutableTable.disjoint, patchTwo, List.mem_cons_of_mem _ List.mem_cons_self, 31, by decide, True.intro⟩

#joint_premises Solidity.Backend.Creation.ImmutableTable.read as case_18_premises
/-- All dependent inputs and hypotheses of the exact unchanged declaration. -/
theorem case_18_joint : case_18_premises := ⟨immutableArtifact.runtime.length, String, immutableTable, immutableArtifact.runtime, rfl, patchOne, List.mem_cons_self, True.intro⟩

#joint_premises Solidity.Backend.Creation.compatible_iff as case_19_premises
/-- All dependent inputs and hypotheses of the exact unchanged declaration. -/
theorem case_19_joint : case_19_premises := ⟨mixedCode.length, Unit, Unit, mixedTable, mixedLinks.sites, True.intro⟩

#joint_premises Solidity.Backend.Creation.combined_installs as case_20_premises
/-- All dependent inputs and hypotheses of the exact unchanged declaration. -/
theorem case_20_joint : case_20_premises := ⟨Unit, Unit, mixedArtifact, mixedLinks, mixedTable, (fun _ => Vector.replicate 20 0x55), by decide, True.intro⟩

#joint_premises Solidity.Backend.Creation.patched_installs as case_21_premises
/-- All dependent inputs and hypotheses of the exact unchanged declaration. -/
theorem case_21_joint : case_21_premises := ⟨Unit, String, immutableArtifact, immutableTable, True.intro⟩

#joint_premises Solidity.Backend.Creation.patched_frame as case_22_premises
/-- All dependent inputs and hypotheses of the exact unchanged declaration. -/
theorem case_22_joint : case_22_premises := ⟨Unit, String, immutableArtifact, immutableTable, 0, outside_zero, True.intro⟩

#joint_premises Solidity.Backend.Creation.immutable_link_commute as case_23_premises
/-- All dependent inputs and hypotheses of the exact unchanged declaration. -/
theorem case_23_joint : case_23_premises := ⟨Unit, Unit, mixedCode, mixedImmutable, mixedSite, Vector.replicate 20 0x55, by decide, True.intro⟩

#joint_premises Solidity.Backend.Creation.placed_size as case_24_premises
/-- All dependent inputs and hypotheses of the exact unchanged declaration. -/
theorem case_24_joint : case_24_premises := ⟨placement255.lengthWord, placement255.offsetWord, True.intro⟩

#joint_premises Solidity.Backend.Creation.placed_exec as case_25_premises
/-- All dependent inputs and hypotheses of the exact unchanged declaration. -/
theorem case_25_joint : case_25_premises := ⟨placement257.lengthWord, placement257.offsetWord, List.replicate 246 0 ++ encode (placedWrapper placement257.lengthWord placement257.offsetWord) ++ [0x60, 0x2a, 0] ++ [0xaa], [0x60, 0x2a, 0, 0xaa], True.intro⟩

#joint_premises Solidity.Backend.Creation.Placement.installs as case_26_premises
/-- All dependent inputs and hypotheses of the exact unchanged declaration. -/
theorem case_26_joint : case_26_premises := ⟨List.replicate 246 0, [0x60, 0x2a, 0], placement257, [0xaa, 0xbb], True.intro⟩

#verify_joint Solidity.Backend.Creation.patchAt_length with case_1_joint
#verify_joint Solidity.Backend.Creation.patchAt_get with case_2_joint
#verify_joint Solidity.Backend.Creation.patchAt_frame with case_3_joint
#verify_joint Solidity.Backend.Creation.patchAt_commute with case_4_joint
#verify_joint Solidity.Backend.Creation.section_slice with case_5_joint
#verify_joint Solidity.Backend.Creation.section_bounds with case_6_joint
#verify_joint Solidity.Backend.Creation.Provenance.global_bounds with case_7_joint
#verify_joint Solidity.Backend.Creation.Provenance.bytes_exact with case_8_joint
#verify_joint Solidity.Backend.Creation.link_permutation with case_9_joint
#verify_joint Solidity.Backend.Creation.Artifact.payload_deterministic with case_10_joint
#verify_joint Solidity.Backend.Creation.Artifact.sections_unique with case_11_joint
#verify_joint Solidity.Backend.Creation.wrapper_decode with case_12_joint
#verify_private_joint Solidity.Backend.Creation.ArtifactLaws Solidity.Backend.Creation.fold_bytes with case_13_joint
#verify_private_joint Solidity.Backend.Creation.ArtifactLaws Solidity.Backend.Creation.separated_members with case_14_joint
#verify_joint Solidity.Backend.Creation.patchImmutables_length with case_15_joint
#verify_joint Solidity.Backend.Creation.patchImmutables_frame with case_16_joint
#verify_joint Solidity.Backend.Creation.patchImmutables_read with case_17_joint
#verify_joint Solidity.Backend.Creation.ImmutableTable.read with case_18_joint
#verify_joint Solidity.Backend.Creation.compatible_iff with case_19_joint
#verify_joint Solidity.Backend.Creation.combined_installs with case_20_joint
#verify_joint Solidity.Backend.Creation.patched_installs with case_21_joint
#verify_joint Solidity.Backend.Creation.patched_frame with case_22_joint
#verify_joint Solidity.Backend.Creation.immutable_link_commute with case_23_joint
#verify_joint Solidity.Backend.Creation.placed_size with case_24_joint
#verify_joint Solidity.Backend.Creation.placed_exec with case_25_joint
#verify_joint Solidity.Backend.Creation.Placement.installs with case_26_joint

end H62.AuditCalculus.CreationAdditional
