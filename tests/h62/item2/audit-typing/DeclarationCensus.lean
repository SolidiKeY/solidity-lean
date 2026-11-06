import Lean

/-! Audit-only reflection. No core imports depend on this module.
The kernel expression representation retains binder information; display text
is supplementary. This enumerates theorem constants belonging to the requested
imported module, including private/generated declarations for reconciliation.
-/
open Lean Elab Command Meta

elab "#audit_module " mod:ident : command => do
  let env ← getEnv
  let some idx := env.getModuleIdx? mod.getId
    | throwError "module is not imported: {mod.getId}"
  let names := env.constants.toList.filterMap fun (name, info) =>
    match info with
    | .thmInfo _ => if env.getModuleIdxFor? name == some idx then some name else none
    | _ => none
  logInfo m!"AUDIT-MODULE {mod.getId} theorem-count={names.length}"
  for name in names.mergeSort Name.quickLt do
    let some info := env.find? name
      | throwError "missing declaration: {name}"
    liftTermElabM do
      let display ← withOptions (fun o => o.setBool `pp.universes true |>.setBool `pp.explicit true) do
        ppExpr info.type
      let binders ← forallTelescope info.type fun xs _ => do
        xs.toList.mapM fun x => do
          let d ← x.fvarId!.getDecl
          let prop ← isProp d.type
          return Json.mkObj [("name", toJson d.userName.toString),
            ("isProp", toJson prop), ("typeExpr", toJson (reprStr d.type))]
      let record := Json.mkObj [("module", toJson mod.getId.toString),
        ("name", toJson name.toString), ("levelParams", toJson (info.levelParams.map Name.toString)),
        ("typeExpr", toJson (reprStr info.type)), ("display", toJson display.pretty),
        ("binders", toJson binders)]
      logInfo m!"AUDIT-DECL {record.compress}"

/-- Check a simultaneous witness against the original elaborated premises.
Specialize only the carrier and its equality instance; retain every other data
binder and all proposition binders, including premises after the result colon.
-/
elab "#audit_witness " original:ident " via " witness:ident : command => do
  liftTermElabM do
    let originalInfo ← getConstInfo original.getId
    let witnessInfo ← getConstInfo witness.getId
    let .forallE _ carrier _ _ := originalInfo.type
      | throwError "expected carrier binder"
    unless ← isDefEq carrier (← inferType (mkConst ``Bool)) do
      throwError "unsupported carrier shape"
    let env ← getEnv
    let some closureIdx := env.getModuleIdx? `Solidity.Frontend.Static.Closure
      | throwError "Closure must be imported"
    let listNames := [`Solidity.lookupBy_isSome_of_mem', `Solidity.lookupBy_of_nodup,
      `Solidity.mem_setBy, `Solidity.lookupBy_none_setBy, `Solidity.nodupKeysB_setBy',
      `Solidity.setBy_of_lookupBy, `Solidity.lookupBy_append_none,
      `Solidity.setBy_append_none, `Solidity.nodupKeysB_mid]
    unless env.getModuleIdxFor? original.getId == some closureIdx || listNames.contains original.getId do
      throwError "witness checker is restricted to reviewed signatures"
    let mut type := originalInfo.type
    -- Only the reviewed one/two-carrier families may use Bool specialization.
    for _ in [0:2] do
      if let .forallE _ domain body _ := type then
        if ← isDefEq domain (← inferType (mkConst ``Bool)) then
          type := body.instantiate1 (mkConst ``Bool)
    if let .forallE _ domain body _ := type then
      if ← isDefEq domain (← mkAppM ``DecidableEq #[mkConst ``Bool]) then
        type := body.instantiate1 (← synthInstance domain)
    let expected ← forallTelescope type fun xs _ => do
      let mut data := #[]
      let mut hypotheses := #[]
      for x in xs do
        let domain ← inferType x
        if ← isProp domain then hypotheses := hypotheses.push domain
        else data := data.push x
      let mut conjunction := hypotheses.toList.getLastD (mkConst ``True)
      for h in hypotheses.toList.reverse.drop 1 do
        conjunction ← mkAppM ``And #[h, conjunction]
      for x in data.toList.reverse do
        conjunction ← mkAppM ``Exists #[← mkLambdaFVars #[x] conjunction]
      pure conjunction
    unless ← isDefEq expected witnessInfo.type do
      throwError "premise mismatch for {original.getId}"
    logInfo m!"AUDIT-WITNESS {original.getId} via {witness.getId}: exact premise bundle"

/-- Preserve every original input, including proof binders and dependencies,
in one existential telescope. Restricted to the explicitly reviewed source statements. -/
elab "#audit_full_inputs " original:ident " via " witness:ident : command => do
  liftTermElabM do
    let names := [`Solidity.SVal.dfltBelow_irrel, `Solidity.SVal.dfltBelow_dflt,
      `Solidity.SFields.dfltBelow_eq, `Solidity.SVal.dflt_all,
      `Solidity.SFields.dflt_all, `Solidity.SVal.dfltBelow_all,
      `Solidity.Frontend.Static.unitsChecker_complete,
      `Solidity.SVal.all_mono, `Solidity.SFields.all_mono, `Solidity.SList.all_mono, `Solidity.SVec.all_mono, `Solidity.SMap.all_mono, `Solidity.SVal.allB_iff, `Solidity.SFields.allB_iff, `Solidity.SList.allB_iff, `Solidity.SVec.allB_iff, `Solidity.SMap.allB_iff, `Solidity.SVal.strip_all, `Solidity.SFields.strip_all, `Solidity.SVec.strip_all, `Solidity.SVal.defaultOf_all, `Solidity.SFields.defaultOf_all, `Solidity.SVec.defaultOf_all, `Solidity.SVal.overlay_all, `Solidity.SFields.overlay_all, `Solidity.SVec.overlayOn_all]
    unless names.contains original.getId do
      throwError "unreviewed full-input signature"
    let originalInfo ← getConstInfo original.getId
    let witnessInfo ← getConstInfo witness.getId
    unless originalInfo.levelParams.isEmpty do
      throwError "unreviewed universe parameters"
    let expected ← forallTelescope originalInfo.type fun xs _ => do
      let mut bundle := mkConst ``True
      for x in xs.toList.reverse do
        bundle ← mkAppM ``Exists #[← mkLambdaFVars #[x] bundle]
      pure bundle
    unless ← isDefEq expected witnessInfo.type do
      throwError "full-input mismatch for {original.getId}"
    logInfo m!"AUDIT-FULL-INPUTS {original.getId} via {witness.getId}: exact input telescope"
