#!/usr/bin/env python3
"""Generate the independent elaborated-type comparison for all177 statements."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode=True
import census
root=Path(__file__).resolve().parents[4]
folder=root/"tests/h62/item2/audit-abi-world/H62AbiWorld"
originals=[r for p in census.module_paths(census.frozen(census.MAP)) for r in census.declarations(p,census.frozen(p))]
links={}
modules=[]
for path in sorted(folder.glob("*Witnesses.lean")):
 modules.append("H62AbiWorld."+path.stem)
 for row in census.declarations(str(path.relative_to(root)),path.read_text()):
  match=re.search(r"hypotheses%\s+([\w.]+)",row["signature"])
  if match:
   assert match[1] not in links,match[1]
   links[match[1]]=row["name"]
assert len(links)==177 and set(links)=={r["name"] for r in originals}
header='''import Lean
IMPORTS

/-! Independent syntax-spine traversal, deliberately separate from the
forallTelescope-based hypotheses% implementation. Every witness type must
match the full package of its original elaborated binder types, and the
complete original type plus every binder is exported for the fidelity census.
This is audit tooling; no intrinsic core module imports it. -/
open Lean Meta Elab Term Command

namespace H62.AbiWorld.Fidelity
private def spinePackage : Nat → Expr → MetaM Expr
  | 0, _ => throwError "fidelity traversal budget exhausted"
  | fuel+1, .forallE name domain body binderInfo =>
      withLocalDecl name binderInfo domain fun fvar => do
        let nested ← spinePackage fuel (body.instantiate1 fvar)
        mkAppM ``Exists #[← mkLambdaFVars #[fvar] nested]
  | _+1, _ => pure (Lean.mkConst ``True)

elab "#audit_fidelity " original:ident " against " witness:ident : command => do
  liftTermElabM do
    let originalName ← realizeGlobalConstNoOverloadWithInfo original
    let witnessName ← realizeGlobalConstNoOverloadWithInfo witness
    let originalInfo ← getConstInfo originalName
    let witnessInfo ← getConstInfo witnessName
    unless originalInfo matches .thmInfo _ do throwError "original is not a theorem"
    unless witnessInfo matches .thmInfo _ do throwError "witness is not a theorem"
    let originalType ← inferType (← mkConstWithFreshMVarLevels originalName)
    let witnessType ← inferType (← mkConstWithFreshMVarLevels witnessName)
    let expected ← spinePackage 256 originalType
    unless ← isDefEq expected witnessType do
      throwError "witness type differs from original full-binder package"
    let originalText := (← ppExpr originalType).pretty
    let witnessText := (← ppExpr witnessType).pretty
    forallTelescope originalType fun binders _ => do
      let mut summaries : Array Json := #[]
      for binder in binders do
        let declaration ← binder.fvarId!.getDecl
        summaries := summaries.push (Json.mkObj [
          ("name",toJson declaration.userName.toString),
          ("type",toJson (← ppExpr declaration.type).pretty),
          ("proposition",toJson (← isProp declaration.type)),
          ("head_constant",toJson (declaration.type.getAppFn.constName?.map Name.toString))])
      logInfo m!"FIDELITY {(Json.mkObj [
        ("original",toJson originalName.toString),
        ("witness",toJson witnessName.toString),
        ("matched",toJson true),
        ("binder_count",toJson binders.size),
        ("binders",Json.arr summaries),
        ("original_type",toJson originalText),
        ("witness_type",toJson witnessText)]).compress}"
end H62.AbiWorld.Fidelity

'''
header=header.replace("IMPORTS","\n".join("import "+m for m in modules))
lines=[header]+["#audit_fidelity "+row["name"]+" against "+links[row["name"]] for row in originals]
(folder/"Fidelity.lean").write_text("\n".join(lines)+"\n")
print("Generated177 independent type comparisons")
