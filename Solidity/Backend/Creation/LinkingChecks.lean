import Solidity.Backend.Creation.LinkLayout

namespace Solidity.Backend.Creation

def libraryArtifact : Artifact String :=
  ⟨[0x73] ++ List.replicate 20 0 ++ [0], [0xaa, 0xbb], by decide, 0, [(1, "L")]⟩

def libraryTable : LinkTable libraryArtifact where
  sites := [⟨⟨1, by decide⟩, "L"⟩]
  origin := rfl
  disjoint := by decide

def libraryAddress (_ : String) : Vector UInt8 20 := Vector.replicate 20 0x11

example : deployable libraryArtifact = none := unresolved_refused _ (by decide)
example : (linkedArtifact libraryArtifact libraryTable libraryAddress).runtime =
    [0x73] ++ List.replicate 20 0x11 ++ [0] := by decide
example : (linkedArtifact libraryArtifact libraryTable libraryAddress).args = [0xaa, 0xbb] := rfl
example : Exec (linkedArtifact libraryArtifact libraryTable libraryAddress).payload
    (linkedArtifact libraryArtifact libraryTable libraryAddress).payload [] []
    (.returned (linkBytes libraryArtifact.runtime (localRefs libraryTable.sites) libraryAddress)) :=
  linked_installs _ _ _
example : libraryArtifact.runtimeLinks ≠ [(2, "L")] := by decide
example : checkedArguments libraryArtifact 3 = none := truncated_arguments_refused _ _ (by decide)
example : checkedArguments libraryArtifact 2 = some [0xaa, 0xbb] := by decide
example : resolve libraryTable.sites (fun _ => none) = none := by decide
example : resolve libraryTable.sites (fun _ => some (Vector.replicate 20 0x11)) =
    some [Vector.replicate 20 0x11] := by decide
example : ¬ (1 + 20 ≤ 2 ∨ 2 + 20 ≤ 1) := by decide
example : ¬ (3 + 20 ≤ libraryArtifact.runtime.length) := by decide

def twoSiteCode : List UInt8 :=
  [0x73] ++ List.replicate 20 0 ++ [0x73] ++ List.replicate 20 0 ++ [0]

def firstSite : LinkSite twoSiteCode.length String := ⟨⟨1, by decide⟩, "A"⟩
def secondSite : LinkSite twoSiteCode.length String := ⟨⟨22, by decide⟩, "B"⟩

example : linkBytes twoSiteCode [(1, "A"), (22, "B")] libraryAddress =
    linkBytes twoSiteCode [(22, "B"), (1, "A")] libraryAddress :=
  two_links_commute twoSiteCode firstSite secondSite (by decide) libraryAddress

-- Wrong relocation actually overwrites different bytes, including a placeholder boundary.
example : patchAt libraryArtifact.runtime 2 (libraryAddress "L").toList ≠
    (linkedArtifact libraryArtifact libraryTable libraryAddress).runtime := by decide

/-- A nontrivial actual assembler input, not a hand-written Assembled record. -/
def actualItems : List (Item Unit String) :=
  [.pushLibraryAddress "A", .pushLibraryAddress "B", .instr (.op .STOP)]

theorem actual_assembly_combination :
    ∃ out, ∃ _h : assemble 0 (fun _ => none) actualItems = some out,
      ∃ fits : (encode out.code).length < 256 ^ 32,
      Nonempty (LinkTable (fromAssembly 0 out [0xaa, 0xbb] fits)) ∧
      ∃ out', ∃ fits' : (encode out'.code).length < 256 ^ 32,
        assemble 0 (fillLink (fun _ => none) libraryAddress) actualItems = some out' ∧
        out'.linkRefs = [] ∧
        let a := fromAssembly 0 out [0xaa, 0xbb] fits
        let b := fromAssembly 0 out' [0xaa, 0xbb] fits'
        b.payload = encode (wrapper a.lengthWord) ++ linkBytes a.runtime out.linkRefs libraryAddress ++ [0xaa, 0xbb] ∧
        Exec b.payload b.payload [] [] (.returned (linkBytes a.runtime out.linkRefs libraryAddress)) := by
  have hsome : (assemble 0 (fun _ : String => none) actualItems).isSome :=
    assemble_isSome _ (by decide) (by intro l hl; cases hl) (by intro l hl; cases hl)
  obtain ⟨out, h⟩ := Option.isSome_iff_exists.mp hsome
  have hlength : (encode out.code).length = 43 := by
    rw [length_encode, (assemble_layout h).2.2]
    rfl
  have fits : (encode out.code).length < 256 ^ 32 := by rw [hlength]; decide
  exact ⟨out, h, fits, ⟨tableOfAssembly h _ fits⟩,
    assembler_link_package h libraryAddress [0xaa, 0xbb] fits⟩

/-- info: 'Solidity.Backend.Creation.assembler_regions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms assembler_regions
/-- info: 'Solidity.Backend.Creation.tableOfAssembly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tableOfAssembly
/-- info: 'Solidity.Backend.Creation.assembler_link_package' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms assembler_link_package
/-- info: 'Solidity.Backend.Creation.actual_assembly_combination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms actual_assembly_combination
/-- info: 'Solidity.Backend.Creation.assembler_link_wrapper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms assembler_link_wrapper
/-- info: 'Solidity.Backend.Creation.linkSites_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms linkSites_length
/-- info: 'Solidity.Backend.Creation.two_links_commute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms two_links_commute
/-- info: 'Solidity.Backend.Creation.linked_installs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms linked_installs
/-- info: 'Solidity.Backend.Creation.unresolved_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unresolved_refused
/-- info: 'Solidity.Backend.Creation.truncated_arguments_refused' depends on axioms: [propext] -/
#guard_msgs in
#print axioms truncated_arguments_refused
end Solidity.Backend.Creation
