import Solidity.Calculus.Core.Chains
import Solidity.Calculus.ChainGen

/-!
# Writing a scoped chain out: `#chain` and `#chain_rest`

`Calculus/ChainGen.lean`'s generator for a chain whose first line is a
scoped formula (`cdl![m]{ … }`): the strategy's steps, grouped as the worked chains
print them (`groupSteps`), each named by the rule `Stmt.step` fires
(`labelOfFocus?`); past the program, from the erasure of the last scoped
line, the rewrites to a last line, searched as `#chain` searches them
(`searchRewritesUsing`).  The commands are `Calculus/ChainGen.lean`'s, read
here when their formula (or chain) is scoped.

Each line is written as the text that reads back as it: `cdl![m]{ … }` over
a modality variable, otherwise the first of `cdl!{ … }`, `cdl![.box]{ … }`,
`cdl![.diamond]{ … }` whose reading is the line's (`matchWritten` for a
scoped line, the line itself for one past the program).  A generated chain is
one declaration: a scoped chain is not cut into segments.
-/

namespace Solidity.Core.Chain

open Lean Elab Term Meta

/-- A generated chain: the strategy's lines with the rule that reached each
(and each line's erasures), the rewrites after with theirs, and why it
stopped early, if it did. -/
structure Gen where
  splice : Splice
  /-- The erasures of the first line. -/
  erased : Array Expr
  steps : Array (String × Expr × Array Expr)
  rewrites : Array (String × Expr)
  stop : Option MessageData

/-- Run the strategy from the scoped line `φ`, then, from the erasure of its
last line, the rewrites to a last line. -/
def generate (φ : Expr) : TermElabM Gen := do
  let run ← runChain φ
  let (_, Γ) ← lineType φ
  let mut steps := #[]
  for l in run.lines do
    let n ← try
        match ← withCurrHeartbeats (labelOfFocus? l.focus) with
        | some (n, _) => pure n.toString
        | none => pure ""
      catch _ => pure ""
    steps := steps.push (n, l.fml, l.erased)
  if run.stuck then
    return { splice := run.splice, erased := run.erased, steps, rewrites := #[],
             stop := some (stuckNote run) }
  if steps.size ≥ runFuel then
    return { splice := run.splice, erased := run.erased, steps, rewrites := #[],
             stop := some m!"the strategy ran {runFuel} steps: go on from the last line" }
  unless (← whnfR Γ).isAppOf ``List.nil do
    return { splice := run.splice, erased := run.erased, steps, rewrites := #[], stop := none }
  let erased := (steps.back?.map (·.2.2)).getD run.erased
  let L ← erasedLine run.splice erased
  let C := (← lineType φ).1
  let (rws, stop, _) ← Solidity.Chain.searchRewritesUsing C L none
  return { splice := run.splice, erased := run.erased, steps, rewrites := rws.getD #[], stop }

/-- The links of a generated chain: the strategy's steps grouped
(`groupSteps`), then one `~[r]~>` per rewrite; each with its line, and
whether that line is scoped. -/
def Gen.links (g : Gen) : Array (String × Expr × Bool) :=
  let grouped := Solidity.Chain.groupSteps (g.steps.map fun (n, l, _) => (n, l))
  grouped.map (fun (a, l) => (a, l, true)) ++ g.rewrites.map fun (n, l) => (s!"~[{n}]~>", l, false)

/-- The `dl_fml` of a printed line `dl{ φ }`. -/
def dlFmlOf? (t : Lean.Term) : Option (TSyntax `dl_fml) :=
  match t with
  | `(dl{ $φ:dl_fml }) => some φ
  | _ => none

/-- The texts a line may be written as, in order. -/
def wrappers (m? : Option Expr) (φ : TSyntax `dl_fml) : MetaM (Array Lean.Term) := do
  match m? with
  | some m => return #[← `(cdl![$(mkIdent (← m.fvarId!.getUserName))]{ $φ:dl_fml })]
  | none =>
    -- `.box`, `.diamond` with no macro scope, as written
    let dot (n : Lean.Name) : Lean.Term :=
      ⟨Syntax.node .none ``Lean.Parser.Term.dotIdent #[mkAtom ".", mkIdent n]⟩
    return #[← `(cdl!{ $φ:dl_fml }), ← `(cdl![$(dot `box)]{ $φ:dl_fml }),
      ← `(cdl![$(dot `diamond)]{ $φ:dl_fml })]

/-- A line as text: the first wrapper that reads back as it. -/
def lineText (sp : Splice) (C e : Expr) (isScoped : Bool) (erased : Array Expr) :
    TermElabM (Array String) := do
  let t ← if isScoped then ppCoreLine e else ppLegacyLine e
  let some φ := dlFmlOf? t | return ← Solidity.ProofTree.termLines t
  let cands ← wrappers sp.modality φ
  let mut pick := cands[0]!
  for c in cands do
    let ok ← withoutModifyingState do
      try
        if isScoped then matchWritten sp C (Written.of c) e erased
        else
          let q ← legacyWritten C sp.modality e (Written.of c)
          pure (!q.hasExprMVar && (← isDefEq q e))
      catch _ => pure false
    if ok then
      pick := c
      break
  Solidity.ProofTree.termLines pick

/-- The declaration stating a generated chain from `φ`. -/
def Gen.decl (g : Gen) (φ : Expr) (name : String := "chain") : TermElabM (Array String) := do
  let (C, _) ← lineType φ
  let erasedOf (l : Expr) : Array Expr :=
    ((g.steps.find? (·.2.1 == l)).map (·.2.2)).getD #[]
  let ind (ls : Array String) : Array String := ls.map ("    " ++ ·)
  let mut out := ind (← lineText g.splice C φ true g.erased)
  for (arrow, l, isScoped) in g.links do
    let line ← lineText g.splice C l isScoped (erasedOf l)
    out := out ++ ind (#[s!"{arrow} {line[0]!}"] ++ (line.extract 1 line.size).map ("  " ++ ·))
  let kw := if g.links.size == 1 && (g.links[0]!.1 == "~*>") then "def" else "theorem"
  return #[s!"{kw} {name} :"] ++ out.modify (out.size - 1) (· ++ " := by") |>.push "  sol_chain"

/-- The rows of a `FreshNames` table for the fresh variables of the lines. -/
def Gen.tableRows (g : Gen) (φ : Expr) : Array String := Id.run do
  let mut seen : Array String := #[]
  for e in #[φ] ++ g.steps.map (·.2.1) ++ g.rewrites.map (·.2) do
    for s in Solidity.Chain.freshSpellings e do
      unless seen.contains s do seen := seen.push s
  return seen.map fun s => s!"(\"?\", \"{s}\")"

/-- A note for a chain that stops early, if it does. -/
def Gen.stopNote (g : Gen) : MessageData :=
  match g.stop with
  | some m => m!"\n\nthe chain stops early: {m}"
  | none => m!""

/-- `#chain φ` for a scoped `φ`: the chain to its last line, as the
declaration to paste. -/
elab_rules : command
  | `(command| #chain $t) => Command.runTermElabM fun _ => do
    let φ ← instantiateMVars (← elabTerm t none)
    synthesizeSyntheticMVarsNoPostponing
    let φ ← instantiateMVars φ
    unless ← isCoreLine φ do throwUnsupportedSyntax
    let g ← generate φ
    if g.links.isEmpty then
      logInfo (m!"{← indentLine φ}\nis a last line: no step and no rewrite applies" ++ g.stopNote)
      return
    let rows := g.tableRows φ
    let table := if rows.isEmpty then m!"" else
      m!"\n\nfresh variables (a `FreshNames` table renames them):\n  [{", ".intercalate rows.toList}]"
    logInfo (m!"{"\n".intercalate (← g.decl φ).toList}" ++ table ++ g.stopNote)

/-- The last line of a scoped chain's statement, and whether it is scoped
(`false`: past the program, `Update.lean`'s). -/
def chainEnd? (ty : Expr) : MetaM (Option (Expr × Bool)) := do
  let ty ← instantiateMVars ty
  let lastOf (ws : Expr) (dflt : Expr) : MetaM (Option Expr) := do
    let some ws ← Solidity.listElems? ws | return none
    let some w := ws.back? | return some dflt
    let w ← whnfR w
    unless w.isAppOfArity ``Prod.mk 4 do return none
    return some (w.getArg! 3)
  match ty.getAppFnArgs with
  | (``Core.Fml.OneStep, #[_, _, _, B]) | (``Core.Fml.Steps, #[_, _, _, B])
  | (``Core.Fml.StepBy, #[_, _, _, _, B]) => return some (B, true)
  | (``Core.Fml.Via, #[_, _, A, ws]) => return (← lastOf ws A).map (·, true)
  | (``Core.Fml.ViaE, #[_, _, _, L, rs]) => return (← lastOf rs L).map (·, false)
  | _ => return none

/-- `#chain_rest c` for a scoped chain: the links still to append, from the
last line of its statement to a last line. -/
elab_rules : command
  | `(command| #chain_rest $c:ident) => Command.runTermElabM fun _ => do
    let n ← realizeGlobalConstNoOverloadWithInfo c
    let info ← getConstInfo n
    forallTelescope info.type fun _ ty => do
      let some (B, isScoped) ← chainEnd? ty | throwUnsupportedSyntax
      let B ← instantiateMVars B
      let (links, sp, C, stop) ← if isScoped then do
          let g ← generate B
          pure (g.links, g.splice, (← lineType B).1, g.stop)
        else do
          let ty ← whnfR (← inferType B)
          let C := ty.appArg!
          let (rws, stop, _) ← Solidity.Chain.searchRewritesUsing C B none
          let sp ← collectPosts B {}
          let m? ← (do
            for x in (collectFVars {} B).fvarIds do
              if (← instantiateMVars (← x.getType)).isConstOf ``Modality then return some (mkFVar x)
            return none : MetaM (Option Expr))
          pure ((rws.getD #[]).map (fun (n, l) => (s!"~[{n}]~>", l, false)),
            { sp with modality := m? }, C, stop)
      if links.isEmpty then
        logInfo m!"{c} ends at a last line"
        return
      let mut out : Array String := #[]
      for (arrow, l, sc) in links do
        let erased ← if sc then pure ((← runChain l).erased) else pure #[]
        let line ← lineText sp C l sc erased
        out := out ++ #[s!"    {arrow} {line[0]!}"] ++ (line.extract 1 line.size).map ("      " ++ ·)
      let note := match stop with
        | some m => m!"\n\nthe chain stops early: {m}"
        | none => m!""
      logInfo (m!"lines to append to the statement of {c}:\n{"\n".intercalate out.toList}" ++ note)

end Solidity.Core.Chain
