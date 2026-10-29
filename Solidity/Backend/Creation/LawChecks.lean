import Solidity.Backend.Creation.Provenance
import Solidity.Backend.Creation.ArtifactChecks

namespace Solidity.Backend.Creation

def tripleCode : List UInt8 := List.replicate 64 0
def siteA : LinkSite tripleCode.length Nat := ⟨⟨1, by decide⟩, 1⟩
def siteB : LinkSite tripleCode.length Nat := ⟨⟨22, by decide⟩, 2⟩
def siteC : LinkSite tripleCode.length Nat := ⟨⟨43, by decide⟩, 3⟩
def tripleAddress (n : Nat) : Vector UInt8 20 := toBytesBE 20 n

example : linkBytes tripleCode (localRefs [siteA, siteB, siteC]) tripleAddress =
    linkBytes tripleCode (localRefs [siteC, siteA, siteB]) tripleAddress :=
  link_permutation _ _ _ (by decide) (List.perm_append_comm (l₁ := [siteA, siteB]) (l₂ := [siteC])) _

example : patchAt (patchAt tripleCode 1 (tripleAddress 1).toList) 2 (tripleAddress 2).toList ≠
    patchAt (patchAt tripleCode 2 (tripleAddress 2).toList) 1 (tripleAddress 1).toList := by decide

def sampleOtherMetadata : Artifact String := { sample with runtimeLinks := [(1, "unresolved")] }
example : sample.payload = sampleOtherMetadata.payload := Artifact.payload_deterministic _ _ rfl rfl
example : sample.runtime = sampleOtherMetadata.runtime ∧ sample.args = sampleOtherMetadata.args :=
  Artifact.sections_unique _ _ rfl (Artifact.payload_deterministic _ _ rfl rfl)
example : sample ≠ sampleOtherMetadata := by
  intro he
  have hr : sample.runtimeLinks = sampleOtherMetadata.runtimeLinks := congrArg Artifact.runtimeLinks he
  cases hr
example : decode (encode (wrapper sample.lengthWord)) = some (wrapper sample.lengthWord) := wrapper_decode _

def sampleSource : SourceFile := ⟨"C.sol", [0x43, 0x28, 0x29, 0x7b, 0x7d]⟩
def sampleOrigin : Provenance sample where
  part := .runtime
  width := 2
  location := ⟨1, by decide⟩
  source := sampleSource
  sourceWidth := 3
  sourceRange := ⟨1, by decide⟩

example : (sample.payload.drop sampleOrigin.globalOffset).take 2 = [0x2a, 0] := sampleOrigin.bytes_exact
example : sampleOrigin.globalOffset + 2 ≤ sample.payload.length := sampleOrigin.global_bounds
example : ¬ Nonempty (Location 3 4) := by
  intro ⟨location⟩
  have hb : location.offset + 4 ≤ 3 := location.bounds
  omega

/-- info: 'Solidity.Backend.Creation.link_permutation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms link_permutation
/-- info: 'Solidity.Backend.Creation.Artifact.payload_deterministic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Artifact.payload_deterministic
/-- info: 'Solidity.Backend.Creation.Artifact.sections_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Artifact.sections_unique
/-- info: 'Solidity.Backend.Creation.wrapper_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wrapper_decode
/-- info: 'Solidity.Backend.Creation.Provenance.global_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Provenance.global_bounds
/-- info: 'Solidity.Backend.Creation.Provenance.bytes_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Provenance.bytes_exact
end Solidity.Backend.Creation
