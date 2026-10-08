import Solidity.Calculus.Core.ChainGen
import Solidity.Calculus.LastLine

/-!
# `#last_line` on a scoped chain

`Calculus/LastLine.lean`'s check, for a chain whose first line is a scoped
formula: its last line is read in names — the last line past the program
as it is, a last scoped line by its erasure (`erasedLine`) — and checked as
`Calculus/LastLine.lean` checks one: no program left, one parallel update
in front of each goal, and no rewrite a chain takes still applying, under
either modality when the chain is over a modality variable.
-/

namespace Solidity.Core.Chain

open Lean Elab Term Meta

/-- What is left of a last line `L` (`Update.lean`'s, over the modalities
`ms`), as `#last_line` lists it. -/
def lastLineProblems (C L : Expr) : TermElabM (Array MessageData) := do
  let mut problems ← Solidity.Chain.shapeProblems L
  let ms ← Solidity.Chain.modalityVars L
  if ms.size ≥ 2 then throwError "#last_line: the last line is under two modalities{indentExpr L}"
  let lines : List (Option String × Expr) := match ms[0]? with
    | some m => [(some "under the box", L.replaceFVar (.fvar m) (mkConst ``Modality.box)),
                 (some "under the diamond", L.replaceFVar (.fvar m) (mkConst ``Modality.diamond))]
    | none => [(none, L)]
  let hasConst (e : Expr) (n : Lean.Name) : Bool := (e.find? (·.isConstOf n)).isSome
  let back (q : Expr) : Expr := match ms[0]? with
    | some m =>
      if hasConst L ``Modality.box || hasConst L ``Modality.diamond then q else
        q.replace fun e =>
          if e.isConstOf ``Modality.box || e.isConstOf ``Modality.diamond then some (.fvar m)
          else none
    | none => q
  let mut found : Array (String × Expr × Array String) := #[]
  for (where?, L) in lines do
    for (r, q) in ← Solidity.Chain.stillApplies C L do
      let q := back q
      let tag := where?.getD ""
      if let some i := found.findIdx? fun (r', q', _) => r' == r && q' == q then
        found := found.modify i fun (r', q', ws) => (r', q', ws.push tag)
      else
        found := found.push (r, q, #[tag])
  for (r, q, ws) in found do
    let note := if ms.isEmpty then m!"" else
      if ws.size == 2 then m!" (under either modality)" else m!" ({ws[0]!})"
    problems := problems.push m!"{r} still applies{note}, and gives{indentD m!"{← ppLegacyLine q}"}"
  return problems

/-- `#last_line c` for a scoped chain: silent when it ends at a last line,
one error listing what is left otherwise. -/
elab_rules : command
  | `(command| #last_line $c:ident) => Command.runTermElabM fun _ => do
    let n ← realizeGlobalConstNoOverloadWithInfo c
    let info ← getConstInfo n
    forallTelescope info.type fun _ ty => do
      let some (B, isScoped) ← chainEnd? ty | throwUnsupportedSyntax
      let B ← instantiateMVars B
      let L ← if isScoped then do
          unless (← whnfR (← lineType B).2).isAppOf ``List.nil do
            throwError "#last_line: the last line of {c} has a context of its own"
          let run ← runChain B
          erasedLine run.splice run.erased
        else pure B
      let C := (← whnfR (← inferType L)).appArg!
      let problems ← lastLineProblems C L
      unless problems.isEmpty do
        throwError "#last_line: {c} does not end at a last line:{indentD m!"{← ppLegacyLine L}"}\n\
          {MessageData.joinSep problems.toList "\n"}"

end Solidity.Core.Chain
