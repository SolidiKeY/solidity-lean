import Solidity.Tools.Upstream

/-! Finite kernel executions of original compilation units, with preserved
compiler identities. This is not compiler/lowering equivalence evidence. -/
solc_import "../../../tests/solc/source-units/SourceUnits.ast.json" hash 0x62efdcb1c40244dc
  as Imported.SourceUnits entrypoints
solc_import "../../../tests/solc/source-units/SourceUnitsIR.ast.json" hash 0x9ea6f1c7a47ad9c9
  as Imported.IR.SourceUnits entrypoints

solc_import "../../../tests/solc/source-units/SourceModes.ast.json" hash 0x15e5f49e2ee8f331
  as Imported.SourceModes entrypoints
solc_import "../../../tests/solc/source-units/SourceModesIR.ast.json" hash 0x3075f234da1a41ca
  as Imported.IR.SourceModes entrypoints
solc_import "../../../tests/solc/source-units/ErrorScope.ast.json" hash 0x1732972bb6c3d981
  as Imported.ErrorScope entrypoints

solc_import "../../../tests/solc/source-units/SourceUnits0834.ast.json" hash 0x53b30c4f07b1899e
  as Imported.Compiler34.SourceUnits entrypoints
solc_import "../../../tests/solc/source-units/SourceUnits0834IR.ast.json" hash 0x884bc95a34d32cf1
  as Imported.Compiler34.IR.SourceUnits entrypoints

namespace Solidity.Examples.Tactics.SourceUnitsImport

#guard Imported.SourceUnits.report.all (fun row => row.admissionChecked && row.status == .elaborated)
#guard Imported.IR.SourceUnits.report.all (fun row => row.admissionChecked && row.status == .elaborated)
#guard Imported.SourceUnits.report.provenance.sources.map (·.name) ==
  ["lib/Math.sol", "lib/Errors.sol", "app/Main.sol"]
#guard Imported.SourceUnits.report.provenance.sources.map (·.sourceId) == [2, 1, 0]

#guard (Imported.SourceModes.report.find? (·.name == "clean")).any (·.status == .elaborated)
#guard (Imported.SourceModes.report.find? (·.name == "use")).any fun row =>
  (row.sourceDiagnostic.map (·.name)) == some `solidity.abiCoderV1
#guard (Imported.IR.SourceModes.report.find? (·.name == "use")).any (·.status == .elaborated)
#guard ["value", "requireValue"].all fun name =>
  (Imported.ErrorScope.report.find? (·.name == name)).any (·.status == .elaborated)

theorem module_condition_effects :
    (Prog.run (State.init Imported.SourceUnits) Imported.SourceUnits.moduleEffect).toOption.isSome = true ∧
    (Prog.run (State.init Imported.IR.SourceUnits) Imported.IR.SourceUnits.moduleEffect).toOption.isSome = true ∧
    (Prog.run (State.init Imported.SourceUnits) Imported.SourceUnits.moduleConditionFailure).halt? = some .panic ∧
    (Prog.run (State.init Imported.IR.SourceUnits) Imported.IR.SourceUnits.moduleConditionFailure).halt? = some .panic := by
  decide +kernel

theorem normal_legacy :
    (Prog.run (State.init Imported.SourceUnits) Imported.SourceUnits.ordinary).toOption.isSome = true ∧
    (Prog.run (State.init Imported.SourceUnits) Imported.SourceUnits.usingAlias).toOption.isSome = true ∧
    (Prog.run (State.init Imported.SourceUnits) Imported.SourceUnits.constants).toOption.isSome = true ∧
    (Prog.run (State.init Imported.SourceUnits) Imported.SourceUnits.receiverOnce).toOption.isSome = true := by
  decide +kernel

theorem normal_viaIR :
    (Prog.run (State.init Imported.IR.SourceUnits) Imported.IR.SourceUnits.ordinary).toOption.isSome = true ∧
    (Prog.run (State.init Imported.IR.SourceUnits) Imported.IR.SourceUnits.usingAlias).toOption.isSome = true ∧
    (Prog.run (State.init Imported.IR.SourceUnits) Imported.IR.SourceUnits.constants).toOption.isSome = true ∧
    (Prog.run (State.init Imported.IR.SourceUnits) Imported.IR.SourceUnits.receiverOnce).toOption.isSome = true := by
  decide +kernel

theorem false_controls :
    (Prog.run (State.init Imported.SourceUnits) Imported.SourceUnits.falseControl).halt? = some .panic ∧
    (Prog.run (State.init Imported.IR.SourceUnits) Imported.IR.SourceUnits.falseControl).halt? = some .panic := by
  decide +kernel

open Lean Elab Term in
elab "source_entry(" c:term "," n:str ")" : term => do
  let name := Lean.quote n.getString
  Solidity.elabAgainst c fun q =>
    `((do
      let statement ← Solidity.Tools.runStmt $c $name []
      Solidity.Tools.Upstream.entryProg $c [statement]).map
        fun (b : Solidity.Blk $c []) => (Solidity.Prog.quoteShared $q b.2).1)

private noncomputable def qualifiedLegacyEntry : Prog Imported.SourceUnits [] [] :=
  source_entry(Imported.SourceUnits, "qualified")
private noncomputable def nestedLegacyEntry : Prog Imported.SourceUnits [] [] :=
  source_entry(Imported.SourceUnits, "nested")
private noncomputable def qualifiedIREntry : Prog Imported.IR.SourceUnits [] [] :=
  source_entry(Imported.IR.SourceUnits, "qualified")
private noncomputable def nestedIREntry : Prog Imported.IR.SourceUnits [] [] :=
  source_entry(Imported.IR.SourceUnits, "nested")

/-- The ordinary calculus still abstracts failure data. -/
theorem ordinary_error_scope :
    (Prog.run (State.init Imported.SourceUnits) Imported.SourceUnits.qualified).halt? = some .revert ∧
    (Prog.run (State.init Imported.IR.SourceUnits) Imported.IR.SourceUnits.qualified).halt? = some .revert := by
  decide +kernel

private noncomputable def scopedError : Prog Imported.ErrorScope [] [] :=
  source_entry(Imported.ErrorScope, "value")
private noncomputable def scopedRequire : Prog Imported.ErrorScope [] [] :=
  source_entry(Imported.ErrorScope, "requireValue")

private noncomputable def aliasLegacyEntry : Prog Imported.SourceUnits [] [] :=
  source_entry(Imported.SourceUnits, "aliasedError")
private noncomputable def aliasIRRequire : Prog Imported.IR.SourceUnits [] [] :=
  source_entry(Imported.IR.SourceUnits, "aliasedRequire")

private noncomputable def alias34L : Prog Imported.Compiler34.SourceUnits [] [] :=
  source_entry(Imported.Compiler34.SourceUnits, "aliasedRequire")
private noncomputable def alias34IR : Prog Imported.Compiler34.IR.SourceUnits [] [] :=
  source_entry(Imported.Compiler34.IR.SourceUnits, "aliasedError")

private def badPayload : List UInt8 := [162, 244, 49, 48] ++ List.replicate 31 0 ++ [7]

/-- The existing external-entry observation retains the exact compiler payload. -/
theorem qualified_errors :
    (Prog.run (State.init Imported.SourceUnits) qualifiedLegacyEntry).halt? =
      some (.revertWith badPayload) ∧
    (Prog.run (State.init Imported.SourceUnits) nestedLegacyEntry).halt? =
      some (.revertWith badPayload) ∧
    (Prog.run (State.init Imported.IR.SourceUnits) qualifiedIREntry).halt? =
      some (.revertWith badPayload) ∧
    (Prog.run (State.init Imported.IR.SourceUnits) nestedIREntry).halt? =
      some (.revertWith badPayload) := by
  decide +kernel

/-- An unrelated nested error cannot change a selected native signature. -/
theorem selected_error_scope :
    (Prog.run (State.init Imported.ErrorScope) scopedError).halt? =
      some (.revertWith badPayload) ∧
    (Prog.run (State.init Imported.ErrorScope) scopedRequire).halt? =
      some (.revertWith badPayload) := by
  decide +kernel

theorem aliased_errors :
    (Prog.run (State.init Imported.SourceUnits) aliasLegacyEntry).halt? = some (.revertWith badPayload) ∧
    (Prog.run (State.init Imported.IR.SourceUnits) aliasIRRequire).halt? = some (.revertWith badPayload) := by
  decide +kernel

theorem compiler34_controls :
    (Prog.run (State.init Imported.Compiler34.SourceUnits) Imported.Compiler34.SourceUnits.moduleEffect).toOption.isSome = true ∧
    (Prog.run (State.init Imported.Compiler34.IR.SourceUnits) Imported.Compiler34.IR.SourceUnits.moduleEffect).toOption.isSome = true ∧
    (Prog.run (State.init Imported.Compiler34.SourceUnits) alias34L).halt? = some (.revertWith badPayload) ∧
    (Prog.run (State.init Imported.Compiler34.IR.SourceUnits) alias34IR).halt? = some (.revertWith badPayload) := by
  decide +kernel

/-- info: 'Solidity.Examples.Tactics.SourceUnitsImport.compiler34_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms compiler34_controls
/-- info: 'Solidity.Examples.Tactics.SourceUnitsImport.aliased_errors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aliased_errors
/-- info: 'Solidity.Examples.Tactics.SourceUnitsImport.module_condition_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms module_condition_effects
/-- info: 'Solidity.Examples.Tactics.SourceUnitsImport.normal_legacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms normal_legacy
/-- info: 'Solidity.Examples.Tactics.SourceUnitsImport.normal_viaIR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms normal_viaIR
/-- info: 'Solidity.Examples.Tactics.SourceUnitsImport.false_controls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms false_controls
/-- info: 'Solidity.Examples.Tactics.SourceUnitsImport.ordinary_error_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ordinary_error_scope
/-- info: 'Solidity.Examples.Tactics.SourceUnitsImport.qualified_errors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms qualified_errors
/-- info: 'Solidity.Examples.Tactics.SourceUnitsImport.selected_error_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms selected_error_scope

end Solidity.Examples.Tactics.SourceUnitsImport
