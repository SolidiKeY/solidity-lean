import Solidity.Yul.Composition.CorrectnessPublic
import Solidity.Yul.Composition.CorrectnessControls

/-! The conditional public constructor is inhabited by G01's existing toy
fixture. This does not instantiate the missing admitted assembly source. -/
namespace Solidity.Yul.Composition.CorrectnessControls
open Solidity.Roadmap Solidity.Roadmap.Controls CorrectnessInstances

theorem compiler_eq : stages.compiler table = toyCompiler := by
  funext i
  unfold Stages.compiler Stages.compileAt
  split
  next hn =>
    change accept i = none at hn
    simp only [toyCompiler, compilerWith, hn, Option.map_none]
  next r hr =>
    change accept i = some r at hr
    change some (artOf r.prog.text) = toyCompiler i
    simp only [toyCompiler, compilerWith, hr, Option.map_some, id_eq]

def boundary : PublicBoundary stages table (fun _ _ => none) where
  bothPipelines := toy_publicCorrectness.bothPipelines
  fixed := rfl
  session := fun _ => rfl
  ifixed := rfl
  isession := fun _ => rfl
  creates_table := by simpa only [compiler_eq] using toy_publicCorrectness.creates_table
  hashes_source := by simpa only [compiler_eq] using toy_publicCorrectness.hashes_source
  decode_reach := by simpa only [compiler_eq] using toy_publicCorrectness.decode_reach
  decode_commutes := by simpa only [compiler_eq] using toy_publicCorrectness.decode_commutes

theorem public_instance :
    PublicCorrectness toySource toyEvm (stages.compiler table) stages.env
      (stages.stateExport (fun _ _ => none)) :=
  stages.publicCorrectness table (fun _ _ => none) linked boundary
/-- Equal runtime bytes do not excuse incorrect constructor bytes in linking. -/
theorem stale_creation_table :
    ¬ stages.Linked ⟨.fail [222, 173], .legacy, .v2⟩ trivial trivial
      { contracts := [{ initcode := [255], runtime := [1, 222, 173] }], main := 0 } := by
  intro h
  have hn : ([] : Bytes) ≠ [255] := by decide
  exact hn (congrArg (fun a : Artifact => a.initcode 0) h)
end Solidity.Yul.Composition.CorrectnessControls
