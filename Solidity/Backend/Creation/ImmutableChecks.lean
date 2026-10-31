import Solidity.Backend.Creation.Immutables

namespace Solidity.Backend.Creation

def immutableArtifact : Artifact Unit := ⟨List.replicate 66 0, [0xaa, 0xbb], by decide, 0, []⟩
def patchOne : ImmutablePatch immutableArtifact.runtime.length String :=
  ⟨"x", ⟨1, by decide⟩, Vector.replicate 32 0x11⟩
def patchTwo : ImmutablePatch immutableArtifact.runtime.length String :=
  ⟨"y", ⟨33, by decide⟩, Vector.replicate 32 0x22⟩
def overlapPatch : ImmutablePatch immutableArtifact.runtime.length String :=
  ⟨"bad", ⟨32, by decide⟩, Vector.replicate 32 0xff⟩
def immutableTable : ImmutableTable immutableArtifact.runtime.length String :=
  ⟨[patchOne, patchTwo], by decide⟩

example : (checkImmutableTable [patchOne, patchTwo]).isSome = true := by decide
example : (checkImmutableTable [patchOne, overlapPatch]).isNone = true := by decide
example : (immutablePatch? 66 "bad" 35 (Vector.replicate 32 0)).isNone = true := by decide
example : (immutablePatch? 66 "edge" 34 (Vector.replicate 32 0)).isSome = true := by decide
example : (patchedArtifact immutableArtifact immutableTable).runtime =
    [0] ++ List.replicate 32 0x11 ++ List.replicate 32 0x22 ++ [0] := by decide
example : (patchedArtifact immutableArtifact immutableTable).runtime[0]? = some 0 := by
  apply patched_frame
  intro p hp
  change p ∈ [patchOne, patchTwo] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> exact Or.inl (by decide)
example : (patchedArtifact immutableArtifact immutableTable).runtime[65]? = some 0 := by decide
example : (patchedArtifact immutableArtifact immutableTable).args = [0xaa, 0xbb] := rfl
example : Exec (patchedArtifact immutableArtifact immutableTable).payload
    (patchedArtifact immutableArtifact immutableTable).payload [] []
    (.returned (patchImmutables immutableArtifact.runtime immutableTable.patches)) := patched_installs _ _
example : ¬ Exec (patchedArtifact immutableArtifact immutableTable).payload
    (patchedArtifact immutableArtifact immutableTable).payload [] [] (.returned immutableArtifact.runtime) := by
  intro h
  have he : Outcome.returned (patchImmutables immutableArtifact.runtime immutableTable.patches) =
      .returned immutableArtifact.runtime := Exec.deterministic (patched_installs _ _) h
  have hn : Outcome.returned (patchImmutables immutableArtifact.runtime immutableTable.patches) ≠
      .returned immutableArtifact.runtime := by decide
  exact hn he

-- Combined link/immutable region: address occupies [1,21), immutable [22,54).
def mixedCode : List UInt8 := [0x73] ++ List.replicate 53 0
def mixedSite : LinkSite mixedCode.length Unit := ⟨⟨1, by decide⟩, ()⟩
def mixedImmutable : ImmutablePatch mixedCode.length Unit :=
  ⟨(), ⟨22, by decide⟩, Vector.replicate 32 0x44⟩
example : patchAt (patchAt mixedCode 22 mixedImmutable.value.toList) 1 (Vector.replicate 20 0x55).toList =
    patchAt (patchAt mixedCode 1 (Vector.replicate 20 0x55).toList) 22 mixedImmutable.value.toList :=
  immutable_link_commute mixedCode mixedImmutable mixedSite (Vector.replicate 20 0x55) (by decide)

example : ((patchedArtifact immutableArtifact immutableTable).runtime.drop 1).take 32 = patchOne.value.toList :=
  immutableTable.read _ rfl patchOne (by exact List.mem_cons_self)

def mixedArtifact : Artifact Unit := ⟨mixedCode, [0xaa], by decide, 0, [(1, ())]⟩
def mixedLinks : LinkTable mixedArtifact := ⟨[mixedSite], rfl, by decide⟩
def mixedTable : ImmutableTable mixedArtifact.runtime.length Unit := ⟨[mixedImmutable], by decide⟩
def mixedBadTable : ImmutableTable mixedArtifact.runtime.length Unit :=
  ⟨[⟨(), ⟨1, by decide⟩, Vector.replicate 32 0x44⟩], by decide⟩
example : compatible mixedTable mixedLinks.sites = true := by decide
example : compatible mixedBadTable mixedLinks.sites = false := by decide
example : Exec (combinedArtifact mixedArtifact mixedLinks mixedTable (fun _ => Vector.replicate 20 0x55) (by decide)).payload
    (combinedArtifact mixedArtifact mixedLinks mixedTable (fun _ => Vector.replicate 20 0x55) (by decide)).payload [] []
    (.returned (combinedArtifact mixedArtifact mixedLinks mixedTable (fun _ => Vector.replicate 20 0x55) (by decide)).runtime) :=
  combined_installs _ _ _ _ _

/-- info: 'Solidity.Backend.Creation.ImmutableTable.read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ImmutableTable.read
/-- info: 'Solidity.Backend.Creation.compatible_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms compatible_iff
/-- info: 'Solidity.Backend.Creation.combined_installs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms combined_installs
/-- info: 'Solidity.Backend.Creation.patchImmutables_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms patchImmutables_length
/-- info: 'Solidity.Backend.Creation.patchImmutables_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms patchImmutables_frame
/-- info: 'Solidity.Backend.Creation.patched_installs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms patched_installs
/-- info: 'Solidity.Backend.Creation.immutable_link_commute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms immutable_link_commute
end Solidity.Backend.Creation
