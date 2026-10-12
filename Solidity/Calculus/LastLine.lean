import Solidity.Calculus.ChainGen
import Solidity.Calculus.RewriteChainGen

/-!
# `#last_line` on a scoped chain

`#last_line`'s check, for a chain whose first line is a scoped formula: its
last line (the line written, for `~~>` past the program) has no program
left, one parallel update in front of each goal (a scope end or a frame end
alone does not count: it prints as nothing), and no rewrite a chain takes
still applies (`pastSteps`), under either modality when the chain is over a
modality variable.
-/

namespace Solidity.Chain

open Lean Elab Term Meta

/-- An update that only ends scopes or frames (`Upd.pop`, `Upd.drop` over
`Upd.nil`): it prints as nothing. -/
partial def bookkeepingUpd (U : Expr) : Bool :=
  if U.isAppOf ``Upd.nil then true
  else if U.isAppOf ``Upd.pop || U.isAppOf ``Upd.drop then
    let args := U.getAppArgs
    args.size ≥ 2 && bookkeepingUpd args[args.size - 2]!
  else false

/-- The goals of a scoped line, each with the number of updates on the path
to it: through `{U}` (one that ends scopes alone does not count), both sides
of `∧`, the consequent of `→`, `¬`, `havoc`, `∀`, a hidden binder and
`anon`. -/
partial def goalsOfS (e : Expr) (n : Nat) : MetaM (Array (Nat × Expr)) := do
  let e ← instantiateMVars e
  let args := e.getAppArgs
  if e.isAppOf ``Fml.upd && args.size == 6 then
    goalsOfS args[5]! (if bookkeepingUpd args[4]! then n else n + 1)
  else if e.isAppOf ``Fml.and && args.size == 4 then
    return (← goalsOfS args[2]! n) ++ (← goalsOfS args[3]! n)
  else if (e.isAppOf ``Fml.imp || e.isAppOf ``Fml.not || e.isAppOf ``Fml.havoc ||
      e.isAppOf ``Fml.all || e.isAppOf ``Fml.bind || e.isAppOf ``Fml.anon) && !args.isEmpty then
    goalsOfS args.back! n
  else return #[(n, e)]

/-- What is left of the scoped last line `L`, as `#last_line` lists it. -/
def lastLineProblems (L : Expr) : TermElabM (Array MessageData) := do
  let mut problems := #[]
  for (n, g) in ← goalsOfS L 0 do
    if n ≥ 2 then
      problems := problems.push m!"{n} updates stand in front of{← indentLine g}\n\
        (one parallel update does: `~[sequentialToParallel]~>`)"
  let ms ← NFml.Chain.modalityVars L
  if ms.size ≥ 2 then throwError "#last_line: the last line is under two modalities{← indentLine L}"
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
    for st in ← pastSteps L do
      let q := back st.fml
      let tag := where?.getD ""
      if let some i := found.findIdx? fun (r', q', _) => r' == st.name && q' == q then
        found := found.modify i fun (r', q', ws) => (r', q', ws.push tag)
      else
        found := found.push (st.name, q, #[tag])
  for (r, q, ws) in found do
    let note := if ms.isEmpty then m!"" else
      if ws.size == 2 then m!" (under either modality)" else m!" ({ws[0]!})"
    problems := problems.push m!"{r} still applies{note}, and gives{← indentLine q}"
  return problems

/-- `#last_line c` for a scoped chain: silent when it ends at a last line,
one error listing what is left otherwise. -/
elab_rules : command
  | `(command| #last_line $c:ident) => Command.runTermElabM fun _ => do
    let n ← realizeGlobalConstNoOverloadWithInfo c
    let info ← getConstInfo n
    forallTelescope info.type fun _ ty => do
      let some B ← scopedEnd? ty | throwUnsupportedSyntax
      let B ← instantiateMVars B
      unless (← whnfR (← lineType B).2).isAppOf ``List.nil do
        throwError "#last_line: the last line of {c} has a context of its own"
      let problems ← lastLineProblems B
      unless problems.isEmpty do
        throwError "#last_line: {c} does not end at a last line:{← indentLine B}\n\
          {MessageData.joinSep problems.toList "\n"}"

end Solidity.Chain
