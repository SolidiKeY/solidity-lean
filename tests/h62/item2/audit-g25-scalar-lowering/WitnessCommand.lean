import Lean

/-! Audit elaborators build existential telescopes directly from unchanged
kernel declarations. They create ordinary proof terms, checked by Lean's
kernel. No theorem binder is dropped, inferred away, or replaced by a premise.
The original conclusion remains the leaf of every existential telescope. -/
namespace Solidity.Backend.Scalar.H62Audit
open Lean Meta Elab Term Command

/-- Preserve explicit binders and logical negative conclusions. Reject custom
aliases hiding additional hypotheses rather than silently omit their domains.
Reducing Not/Ne as input binders would misclassify a proved negative control as
an infeasible premise, so these standard logical conclusions stay intact. -/
private def exactTelescope {α : Type} (type : Expr)
    (k : Array Expr → Expr → MetaM α) : MetaM α :=
  forallTelescope type fun xs conclusion => do
    let head := conclusion.getAppFn.constName?.getD Name.anonymous
    unless head == ``Not || head == ``Ne do
      if (← whnf conclusion).isForall then
        throwError "audit conclusion hides forall binders behind an alias; explicit review required"
    k xs conclusion

private def jointType (name : Name) : MetaM Expr := do
  let original ← mkConstWithFreshMVarLevels name
  exactTelescope (← inferType original) fun xs conclusion => do
    unless ← isProp conclusion do throwError "audit target must conclude a proposition"
    let mut result := conclusion
    for x in xs.reverse do
      result ← mkAppM ``Exists #[← mkLambdaFVars #[x] result]
    pure result

elab "jointType% " original:ident : term => do
  jointType (← realizeGlobalConstNoOverload original)

elab "jointProof% " original:ident " [" args:term,* "]" : term => do
  let name ← realizeGlobalConstNoOverload original
  let count ← exactTelescope (← inferType (← mkConstWithFreshMVarLevels name)) fun xs _ => pure xs.size
  unless args.getElems.size == count do
    throwError "joint witness requires exactly {count} arguments; got {args.getElems.size}"
  let mut proof ← `(term| @$original $args*)
  for arg in args.getElems.reverse do
    proof ← `(term| Exists.intro $arg $proof)
  elabTermEnsuringType proof (← jointType name)

elab "#audit_census " destination:str " [" originals:ident,* "]" : command => do
  let rows : Array Json ← liftTermElabM do
    let mut rows : Array Json := #[]
    let mut seen : NameSet := {}
    for original in originals.getElems do
      let name ← realizeGlobalConstNoOverload original
      if seen.contains name then throwError "duplicate audit theorem {name}"
      seen := seen.insert name
      let info ← getConstInfo name
      match info with
      | .thmInfo _ => pure ()
      | _ => throwError "audit declaration is not a theorem: {name}"
      let row : Json ← exactTelescope info.type fun xs conclusion => do
        let mut binders : Array Json := #[]
        for x in xs do
          let decl ← getFVarLocalDecl x
          let ty ← inferType x
          let prop ← isProp ty
          let head := ty.getAppFn.constName?.getD Name.anonymous
          binders := binders.push <| Json.mkObj [
            ("name", .str decl.userName.toString),
            ("type", .str (toString (← ppExpr ty))),
            ("is_proposition", .bool prop),
            ("instance_implicit", .bool decl.binderInfo.isInstImplicit),
            ("type_head", .str head.toString)]
        pure <| Json.mkObj [("name", .str name.toString),
          ("kernel_type", .str (reprStr info.type)),
          ("level_parameters", toJson (info.levelParams.map Name.toString)),
          ("pretty_type", .str (toString (← ppExpr info.type))),
          ("conclusion", .str (toString (← ppExpr conclusion))),
          ("binder_count", toJson xs.size), ("binders", .arr binders)]
      rows := rows.push row
    pure rows
  liftIO <| IO.FS.writeFile destination.getString (Json.arr rows |>.pretty)
  logInfo m!"kernel census: {rows.size} unchanged public theorems"

elab "#audit_structures " destination:str " [" structures:ident,* "]" : command => do
  let rows : Array Json ← liftTermElabM do
    structures.getElems.mapM fun schemaIdent => do
      let name ← realizeGlobalConstNoOverload schemaIdent
      let info ← getConstInfo (name.str "mk")
      pure <| Json.mkObj [("name", .str name.toString),
        ("constructor_type", .str (reprStr info.type)),
        ("pretty_constructor_type", .str (toString (← ppExpr info.type)))]
  liftIO <| IO.FS.writeFile destination.getString (Json.arr rows |>.pretty)
  logInfo m!"premise structure schemas: {rows.size}"

/-- Independent domain-by-domain fidelity check. This does not call jointType:
it opens the frozen forall telescope, checks every existential domain in order,
and checks the unmodified conclusion after substituting the same local inputs. -/
private def verifyDomains (original witness : Expr) : MetaM Nat :=
  forallTelescope original fun xs conclusion => do
    let mut remaining := witness
    for x in xs do
      let shape ← whnf remaining
      unless shape.isAppOfArity ``Exists 2 do
        throwError "missing existential input in witness telescope"
      let args := shape.getAppArgs
      unless ← isDefEq args[0]! (← inferType x) do
        throwError "witness input domain differs from frozen domain"
      remaining := mkApp args[1]! x
    unless ← isDefEq remaining conclusion do
      throwError "witness leaf differs from original conclusion"
    pure xs.size

elab "#audit_verify " destination:str " [" originals:ident,* "]"
    " [" witnesses:ident,* "]" : command => do
  unless originals.getElems.size == witnesses.getElems.size do
    throwError "original/witness census lengths differ"
  let rows : Array Json ← liftTermElabM do
    let mut rows : Array Json := #[]
    let mut originalsSeen : NameSet := {}
    let mut witnessesSeen : NameSet := {}
    for (original, witness) in originals.getElems.zip witnesses.getElems do
      let originalName ← realizeGlobalConstNoOverload original
      let witnessName ← realizeGlobalConstNoOverload witness
      if originalsSeen.contains originalName || witnessesSeen.contains witnessName then
        throwError "duplicate original or witness in final census"
      originalsSeen := originalsSeen.insert originalName
      witnessesSeen := witnessesSeen.insert witnessName
      let originalInfo ← getConstInfo originalName
      let witnessInfo ← getConstInfo witnessName
      match originalInfo, witnessInfo with
      | .thmInfo _, .thmInfo _ => pure ()
      | _, _ => throwError "both census entries must be checked theorem declarations"
      unless originalInfo.levelParams.isEmpty && witnessInfo.levelParams.isEmpty do
        throwError "polymorphic universe telescope requires explicit review"
      let checkedBinders ← verifyDomains originalInfo.type witnessInfo.type
      let axioms ← collectAxioms witnessName
      for axiomName in axioms do
        unless axiomName == ``propext || axiomName == ``Classical.choice || axiomName == ``Quot.sound do
          throwError "unexpected trust dependency {axiomName} in {witnessName}"
      rows := rows.push <| Json.mkObj [("name", .str originalName.toString),
        ("witness", .str witnessName.toString),
        ("checked_binders", toJson checkedBinders),
        ("kernel_type", .str (reprStr originalInfo.type)),
        ("witness_type", .str (reprStr witnessInfo.type)),
        ("axioms", toJson (axioms.toList.map Name.toString)),
        ("status", .str "verified-full-telescope-and-conclusion")]
    pure rows
  liftIO <| IO.FS.writeFile destination.getString (Json.arr rows |>.pretty)
  logInfo m!"verified joint witnesses and statement fidelity: {rows.size}"

end Solidity.Backend.Scalar.H62Audit
