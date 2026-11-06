import Solidity.Frontend.Testing

/-! The audit memo must never approve a fresh declaration merely because an
older declaration used the same name. All synthetic declarations are confined
to restored command states; no extra axiom enters this module's environment. -/

open Lean Elab Command Solidity.Frontend

run_elab do
  let agrees (name : Name) (expected : Bool) : CoreM Unit := do
    let fast ← usesOnlyStandardAxioms name
    let exact := (← collectAxioms name).all (standardAxioms.contains ·)
    unless fast == exact && fast == expected do
      throwError "audit policy mismatch for {name}: cached={fast}, full={exact}, expected={expected}"
  let good : Declaration := .thmDecl {
    name := `AuditProbe.reused, levelParams := [],
    type := mkConst ``True, value := mkConst ``True.intro }
  let bad : Declaration := .axiomDecl {
    name := `AuditProbe.nonstandard, levelParams := [], type := mkConst ``True, isUnsafe := false }
  let tainted : Declaration := .thmDecl {
    name := `AuditProbe.reused, levelParams := [],
    type := mkConst ``True, value := mkConst `AuditProbe.nonstandard }
  agrees ``Classical.em true
  withoutModifyingEnv do
    addDecl good
    agrees `AuditProbe.reused true
  withoutModifyingEnv do
    addDecl bad
    addDecl tainted
    agrees `AuditProbe.reused false
    agrees `AuditProbe.reused false
  withoutModifyingEnv do
    addDecl good
    agrees `AuditProbe.reused true
  let other ← importModules #[{module := `Init}] {} 0 (loadExts := true)
  withEnv other do
    agrees ``True.intro true
    withoutModifyingEnv do
      addDecl bad
      addDecl tainted
      agrees `AuditProbe.reused false
  -- Equal names and counts do not identify loaded declaration contents.
  -- Serialize tiny checked fixtures, then import the same module name from
  -- distinct artifacts. Every synthetic axiom stays in a restored environment.
  IO.FS.withTempDir fun dir => do
    let base := other.setMainModule `AuditSnapshot
    let writeFixture (file : System.FilePath) (value : Expr) : CoreM Unit :=
      withEnv base do
        addDecl bad
        addDecl (.thmDecl {
          name := `AuditProbe.reused
          levelParams := []
          type := mkConst ``True
          value := value })
        saveModuleData file `AuditSnapshot (← mkModuleData (← getEnv))
    let goodFile := dir / "good.olean"
    let badFile := dir / "bad.olean"
    writeFixture goodFile (mkConst ``True.intro)
    writeFixture badFile (mkConst `AuditProbe.nonstandard)
    let load (file : System.FilePath) : IO Environment :=
      importModules #[{module := `AuditSnapshot}] {} 0 (loadExts := true)
        (arts := ({} : NameMap ImportArtifacts).insert `AuditSnapshot (.ofArray #[file]))
    let first ← load goodFile
    let changed ← load badFile
    unless first.header.moduleNames == changed.header.moduleNames &&
        first.constants.map₁.size == changed.constants.map₁.size do
      throwError "collision control must have identical import names and counts"
    withEnv first do
      agrees `AuditProbe.reused true
      agrees `AuditProbe.reused true
    withEnv changed do
      agrees `AuditProbe.reused false
      agrees `AuditProbe.reused false
  agrees ``Classical.em true
  unless !(← getEnv).contains `AuditProbe.nonstandard && !(← getEnv).contains `AuditProbe.reused do
    throwError "audit test leaked synthetic declarations"
