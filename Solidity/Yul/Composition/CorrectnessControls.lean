import Solidity.Yul.Composition.CorrectnessInstances
import Solidity.Roadmap.Controls

/-! Inhabited tests of the instance constructor using G01's existing toy source
and EVM. These are adapter controls, not assembly semantics or EVM proofs. -/
namespace Solidity.Yul.Composition.CorrectnessControls
open Solidity.Roadmap Solidity.Roadmap.Controls CorrectnessInstances

def encodePass : Pass toyLang toyEvmLang where
  Dom := fun _ => True
  run := fun t _ => artOf t.text
  envAbs := id

def encodeCert : Cert encodePass where
  envSound := fun _ h => h
  envOnto := fun e h => ⟨e, h, rfl⟩
  need := fun _ _ _ r => ⟨r.horizon, fun _ => 0⟩
  need_ok t _ _ r _ _ hf hg := by
    refine ⟨trivial, trivial, ?_, ?_⟩
    · simpa only [encodePass, toyEvmLang, mainRuntime_artOf, decode_text] using hg
    · change (t.run r.exhausted).Le ((decode (mainRuntime (artOf t.text))).run false)
      rw [hf.1, mainRuntime_artOf, decode_text]
      exact Prefix.Le.refl _
  back t _ _ r _ _ hg := by
    refine ⟨⟨r.horizon, false⟩, trivial, ?_, ?_⟩
    · simpa only [encodePass, toyEvmLang, toyLang, mainRuntime_artOf, decode_text] using hg
    · change ((decode (mainRuntime (artOf t.text))).run false).Le (t.run false)
      rw [mainRuntime_artOf, decode_text]
      exact Prefix.Le.refl _

def compilation : Compilation toyIntrinsic toyEvmLang where
  compile := fun t => artOf t.text
  pass := encodePass
  dom := fun _ => trivial
  agrees := fun _ => rfl
  cert := encodeCert

def executionPass : Pass toyEvmLang toyEvmLang where
  Dom := fun _ => True
  run := fun a _ => a
  envAbs := id

def executionCert : Cert executionPass where
  envSound := fun _ h => h
  envOnto := fun e h => ⟨e, h, rfl⟩
  need := fun _ _ _ r => r
  need_ok := fun _ _ _ _ _ ha hf hg => ⟨ha, hf, hg, Prefix.Le.refl _⟩
  back := fun _ _ _ r _ ha hg => ⟨r, ha, hg, Prefix.Le.refl _⟩

def execution : Execution toyEvmLang toyEvm where
  assemble := id
  pass := executionPass
  dom := fun _ => trivial
  agrees := fun _ => rfl
  cert := executionCert

def stages : Stages toySource toyIntrinsic toyEvmLang toyEvm :=
  ⟨toyAdmission, toyLowering, compilation, execution⟩

def table (i : ToyInput) : Artifact := (toyCompiler i).getD (artOf [])

theorem linked : stages.TablesLinked table := by
  intro i r ha w p
  have hf := toyAdmission.complete i r ha
  change accept i = some r at hf
  change artOf r.prog.text = (toyCompiler i).getD (artOf [])
  simp only [toyCompiler, compilerWith, hf, Option.map_some, id_eq, Option.getD_some]

theorem transfer : SpecTransfer toySource toyEvm (stages.compiler table) stages.env :=
  stages.specTransfer table linked

/-- Both settings really run the executable frontend/encoding adapter. -/
theorem compile_full_revert (q : Pipeline) :
    stages.compiler table { text := [1, 222, 173, 190, 239], pipeline := q } =
      some (artOf [1, 222, 173, 190, 239]) := by
  cases q <;> rfl

theorem compile_full_success (q : Pipeline) :
    stages.compiler table { text := [0, 171, 0, 205], pipeline := q } =
      some (artOf [0, 171, 0, 205]) := by
  cases q <;> rfl

theorem reject_malformed (q : Pipeline) :
    stages.compiler table { text := [], pipeline := q } = none := by
  cases q <;> rfl

theorem wrong_payload :
    stages.compiler table { text := [1, 222, 173], pipeline := .legacy } ≠ some (artOf [1, 170, 187]) := by
  intro h
  have hn : some ([1, 222, 173] : Bytes) ≠ some [1, 170, 187] := by decide
  exact hn (congrArg (Option.map mainRuntime) h)

theorem always_revert_wrong :
    stages.compiler table { text := [0, 171, 0, 205], pipeline := .viaIR } ≠ some (artOf [1]) := by
  intro h
  have hn : some ([0, 171, 0, 205] : Bytes) ≠ some [1] := by decide
  exact hn (congrArg (Option.map mainRuntime) h)

/-- A wrong table cannot meet linking, even if parsing and code generation run. -/
theorem stale_table :
    ¬ stages.Linked ⟨.fail [222, 173], .legacy, .v2⟩ trivial trivial (artOf [1, 170, 187]) := by
  intro h
  have hn : ([1, 222, 173] : Bytes) ≠ [1, 170, 187] := by decide
  exact hn (congrArg mainRuntime h)

theorem full_failure (e : SessionEnv) (r : EvmBound) :
    (toyEvm.lang.sem (stages.emit ⟨.fail [222, 173], .legacy, .v2⟩
      trivial trivial (artOf [])) e r).final = some (.revert [222, 173]) := rfl

theorem full_success (e : SessionEnv) (r : EvmBound) :
    (toyEvm.lang.sem (stages.emit ⟨.succeed [171, 0, 205], .viaIR, .v2⟩
      trivial trivial (artOf [])) e r).final = some (.success [171, 0, 205]) := rfl
end Solidity.Yul.Composition.CorrectnessControls
