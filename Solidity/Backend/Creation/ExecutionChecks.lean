import Solidity.Backend.Creation.Execution
import Solidity.Backend.Creation.ArtifactChecks

/-! Inhabited installation witnesses and independent byte-range controls. -/
namespace Solidity.Backend.Creation

def boundary (n : Immediate) : Artifact Unit where
  runtime := List.replicate n.value 0x5b
  args := [0xaa, 0xbb]
  runtimeFits := by simpa only [List.length_replicate] using n.fits
  linkBase := 0
  runtimeLinks := []

example : Exec sample.payload sample.payload [] [] (.returned sample.runtime) := installs_runtime _
example : Exec emptyWithArgs.payload emptyWithArgs.payload [] [] (.returned []) := installs_runtime _
example : ∃ a : Artifact Unit, a.runtime.length = 31 ∧
    Exec a.payload a.payload [] [] (.returned a.runtime) :=
  ⟨boundary ⟨31, by decide⟩, List.length_replicate, installs_runtime _⟩
example : ∃ a : Artifact Unit, a.runtime.length = 32 ∧
    Exec a.payload a.payload [] [] (.returned a.runtime) :=
  ⟨boundary ⟨32, by decide⟩, List.length_replicate, installs_runtime _⟩
example : ∃ a : Artifact Unit, a.runtime.length = 33 ∧
    Exec a.payload a.payload [] [] (.returned a.runtime) :=
  ⟨boundary ⟨33, by decide⟩, List.length_replicate, installs_runtime _⟩
example : ∃ a : Artifact Unit, a.runtime.length = 255 ∧
    Exec a.payload a.payload [] [] (.returned a.runtime) :=
  ⟨boundary ⟨255, by decide⟩, List.length_replicate, installs_runtime _⟩
example : ∃ a : Artifact Unit, a.runtime.length = 256 ∧
    Exec a.payload a.payload [] [] (.returned a.runtime) :=
  ⟨boundary ⟨256, by decide⟩, List.length_replicate, installs_runtime _⟩

-- Independent known bytes: wrong length, source and return offsets do not match.
example : readBytes [0x60, 0x2a, 0] 0 2 ≠ [0x60, 0x2a, 0] := by decide
example : readBytes [0x60, 0x2a, 0, 0xaa, 0xbb] 1 3 ≠ [0x60, 0x2a, 0] := by decide
example : readBytes [0x60, 0x2a, 0, 0xaa, 0xbb] 0 4 ≠ [0x60, 0x2a, 0] := by decide
example : readBytes [0x60, 0x2a, 0] 2 3 = [0, 0, 0] := by decide
example : writeBytes [1, 2, 3] 1 [9, 8] = [1, 9, 8] := by decide

def wrongSource : List UInt8 :=
  [0x60, 3, 0x60, 11, 0x5f, 0x39, 0x60, 3, 0x5f, 0xf3, 0x60, 0x2a, 0, 0xaa, 0xbb]

theorem wrongSource_exec : Exec wrongSource wrongSource [] [] (.returned [0x2a, 0, 0xaa]) :=
  ⟨7, by decide⟩

example : ¬ Exec wrongSource wrongSource [] [] (.returned [0x60, 0x2a, 0]) := by
  intro h
  have he : Outcome.returned [0x2a, 0, 0xaa] = .returned [0x60, 0x2a, 0] :=
    Exec.deterministic wrongSource_exec h
  have hn : Outcome.returned [0x2a, 0, 0xaa] ≠ .returned [0x60, 0x2a, 0] := by decide
  exact hn he

example : ¬ Exec sample.payload sample.payload [] [] (.returned []) := by
  intro h
  have he : Outcome.returned sample.runtime = .returned [] :=
    Exec.deterministic (installs_runtime sample) h
  have hn : Outcome.returned sample.runtime ≠ .returned [] := by decide
  exact hn he

/-- info: 'Solidity.Backend.Creation.wrapper_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wrapper_exec
/-- info: 'Solidity.Backend.Creation.installs_runtime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms installs_runtime
/-- info: 'Solidity.Backend.Creation.Exec.deterministic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exec.deterministic
end Solidity.Backend.Creation
