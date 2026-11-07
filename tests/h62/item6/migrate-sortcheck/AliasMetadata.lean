import Solidity.SortCheck.Annotations
import Lean.Meta.CompletionName
import Lean.Linter.Deprecated

/-! Check the frozen 4.24 alias metadata on either compiler. These command
checks complement ConstructorTags' independent numeric kernel proofs. -/
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let aliases := [
    (``Solidity.TacletAnnotations.ReadDomain.toCtorIdx, ``Solidity.TacletAnnotations.ReadDomain.ctorIdx),
    (``Solidity.TacletAnnotations.ReadSite.toCtorIdx, ``Solidity.TacletAnnotations.ReadSite.ctorIdx),
    (``Solidity.TacletAnnotations.SortVarcond.toCtorIdx, ``Solidity.TacletAnnotations.SortVarcond.ctorIdx)]
  for (aliasName, target) in aliases do
    unless isProtected env aliasName do throwError "not protected: {aliasName}"
    unless Meta.completionBlackListExt.isTagged env aliasName do
      throwError "not completion-blacklisted: {aliasName}"
    unless getReducibilityStatusCore env aliasName matches .reducible do
      throwError "not reducible: {aliasName}"
    let some entry := Linter.deprecatedAttr.getParam? env aliasName
      | throwError "not deprecated: {aliasName}"
    unless entry.newName? == some target && entry.since? == some "2025-08-25" && entry.text?.isNone do
      throwError "deprecation metadata drift: {aliasName}"
    let some (.defnInfo info) := env.find? aliasName
      | throwError "not a definition: {aliasName}"
    let some targetInfo := env.find? target | throwError "missing target: {target}"
    let .forallE binder _ _ _ := info.type | throwError "alias is not a function: {aliasName}"
    let .forallE targetBinder _ _ _ := targetInfo.type | throwError "target is not a function: {target}"
    unless info.type == targetInfo.type && binder == targetBinder do
      throwError "target signature/binder metadata drift: {aliasName}"
    unless info.value.consumeMData == mkConst target do
      throwError "alias body drift: {aliasName}"
    logInfo m!"ALIAS_METADATA_PASS {aliasName}"
