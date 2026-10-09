import Solidity.Calculus.Core.Chains
import Solidity.Calculus.RewriteChainGen

/-!
# Writing a scoped chain out: `#chain` and `#chain_rest`

The chain generator for a chain whose first line is a
scoped formula (`cdl![m]{ … }`): the strategy's steps, grouped as the worked chains
print them (`groupSteps`), each named by the rule `Stmt.step` fires
(`labelOfFocus?`); past the program, from the erasure of the last scoped
line, the rewrites to a last line, searched as `#chain` searches them
(`searchRewritesUsing`).  The commands are `Calculus/RewriteChainGen.lean`'s, read
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
  if run.modalStop then
    return { splice := run.splice, erased := run.erased, steps, rewrites := #[],
             stop := some (modalStopNote run) }
  if steps.size ≥ runFuel then
    return { splice := run.splice, erased := run.erased, steps, rewrites := #[],
             stop := some m!"the strategy ran {runFuel} steps: go on from the last line" }
  unless (← whnfR Γ).isAppOf ``List.nil do
    return { splice := run.splice, erased := run.erased, steps, rewrites := #[], stop := none }
  let erased := (steps.back?.map (·.2.2)).getD run.erased
  let L := dropAllsE (← erasedLine run.splice erased)
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
    if ← todaysNotation t then throwUnsupportedSyntax
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

/-- The last line of a scoped chain's statement (a chain term, or `A ~~> B`),
and whether it is scoped (`false`: past the program, `Update.lean`'s). -/
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
  | (``Core.Fml.StepBy, #[_, _, _, _, B]) | (``Core.Fml.Leads, #[_, _, _, B]) => return some (B, true)
  | (``Core.Fml.LeadsE, #[_, _, _, L]) => return some (L, false)
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

/-! ## `sol_chain`, `sol_chain?` and `sol_rws` on `~~>`

A goal `A ~~> B` on scoped lines (`Core.Fml.Leads`) is the derivation from `A`
to `B`, which `sol_chain` proves.  Past the program (`Core.Fml.LeadsE A Z L`)
it is the derivation to `Z`, then rewrites from `Z`'s erasure to `L`: the
file names them (`sol_rws [..]`), and only the `?` twins search for them
(`Calculus/RewriteChainGen.lean`'s `searchRewrites`), so a re-check does not
search; `sol_chain` refuses such a goal and points to them. -/

/-- The merges, one per name, from `A` to `B`: the first sequence of merge
candidates that ends at `B`, as `A ~~> B`. -/
partial def mergePath (A B : Expr) : Nat → MetaM (Option Expr)
  | 0 => do
    if A == B then return some (← mkAppM ``Core.Fml.Leads.self #[A]) else return none
  | n + 1 => do
    let (sp, cands) ← mergeCands A
    for c in cands do
      if let some rest ← mergePath c.fml B n then
        let (C, Γ) ← lineType A
        let lhs := mkAppN (mkConst ``Core.Fml.mergeRun) #[C, Γ, toExpr c.k, toExpr c.n, A]
        let rhs := mkApp2 (mkConst ``Option.some [0]) (mkApp2 (mkConst ``Core.Fml) C Γ) c.fml
        let h ← kernelReflOrCases sp.modality lhs rhs
        let lk ← mkAppM ``Core.Fml.mergeRun_leads #[toExpr c.k, toExpr c.n, A, h]
        return some (← mkAppM ``Core.Fml.Leads.comp #[lk, rest])
    return none

/-- The derivation from `A` to `B`, as `A ~~> B`: the strategy's steps, then a
merge of the line's update spine (`Fml.MergeBy`) if `B` is one. -/
partial def leadsSteps (A B : Expr) : TermElabM Expr := do
  let run ← runChain A
  match (if A == B then some 0 else (run.lines.findIdx? (·.fml == B)).map (· + 1)) with
  | some i => mkAppM ``Core.Fml.Steps.sound #[← stepsProof run.splice A (run.lines.take i)]
  | none =>
    for i in [0:run.lines.length + 1] do
      let L := if i == 0 then A else ((run.lines[i - 1]?).map (·.fml)).getD A
      if let some h ← mergePath L B 1 then
        let st ← mkAppM ``Core.Fml.Steps.sound #[← stepsProof run.splice A (run.lines.take i)]
        return ← mkAppM ``Core.Fml.Leads.comp #[st, h]
    throwError "sol_chain: the derivation of{← indentLine A}\ndoes not reach{← indentLine B}"


/-- The erasure of the derivation's last line `Z` from `A`, its parameters
free, with the postconditions `Update.lean` reads (`Post.erase`). -/
def lastErasure (A Z : Expr) : TermElabM Expr := do
  let run ← runChain A
  let erased ← if Z == A then pure run.erased else
    match run.lines.find? (·.fml == Z) with
    | some l => pure l.erased
    | none => throwError "sol_chain: the derivation of{← indentLine A}\ndoes not reach{← indentLine Z}"
  return dropAllsE (← erasedLine run.splice erased)

/-- `L₀ ~~> L` (`Update.lean`'s) by the rewrites `ns`. -/
def legacyLeads (C L₀ L : Expr) (ns : Array Lean.Name) : TermElabM Expr := do
  let g ← mkFreshExprMVar (mkApp3 (mkConst ``Solidity.NFml.Leads) C L₀ L)
  Solidity.Chain.proveRws g.mvarId! ns
  instantiateMVars g

/-- Prove a goal `A ~~> B`: scoped, by the derivation; past the program, by
the derivation and then the rewrites `ns`. -/
def solveLeads (g : MVarId) (ns : Array Lean.Name) : TermElabM Unit := do
  let ty ← instantiateMVars (← g.getType)
  match_expr ty with
  | Core.Fml.Leads _ _ A B => g.assign (← leadsSteps A B)
  | Core.Fml.LeadsE C A Z L =>
    let h₁ ← leadsSteps A Z
    let L₀ ← lastErasure A Z
    let h₂ ← legacyLeads C L₀ L ns
    let er ← mkAppM ``Core.Fml.erase #[mkApp (mkConst ``List.nil [0]) (mkConst ``Solidity.Var), Z]
    let h₂ ← mkExpectedTypeHint h₂ (mkApp3 (mkConst ``Solidity.NFml.Leads) C
      (mkApp2 (mkConst ``Solidity.NFml.dropAlls) C er) L)
    g.assign (← mkAppM ``And.intro #[h₁, h₂])
  | _ => throwError "not a `~~>` goal"

elab_rules : tactic
  | `(tactic| sol_chain) => Tactic.withMainContext do
    let g ← Tactic.getMainGoal
    let ty ← instantiateMVars (← g.getType)
    unless ty.isAppOf ``Core.Fml.Leads || ty.isAppOf ``Core.Fml.LeadsE do throwUnsupportedSyntax
    if ty.isAppOf ``Core.Fml.LeadsE then
      -- logged, not thrown: a throw falls through to `Calculus/RewriteChains.lean`'s
      -- `sol_chain`, whose error would be the one shown
      logError "sol_chain: past the program the rewrites are named, so that a re-check does \
        not search: `sol_rws [r₁, …]` (`sol_rws?` finds them), or the chain written out \
        (`sol_chain?`)"
      g.admit
    else solveLeads g #[]
    Tactic.replaceMainGoal []

/-- The text of a chain from `φ`: its first line, then each link's arrow and
line (`Gen.links`). -/
def chainText (g : Gen) (φ : Expr) : TermElabM (Array String) := do
  let (C, _) ← lineType φ
  let erasedOf (l : Expr) : Array Expr :=
    ((g.steps.find? (·.2.1 == l)).map (·.2.2)).getD #[]
  let mut out := ← lineText g.splice C φ true g.erased
  for (arrow, l, isScoped) in g.links do
    let line ← lineText g.splice C l isScoped (erasedOf l)
    out := out ++ #[s!"{arrow} {line[0]!}"] ++ (line.extract 1 line.size).map ("  " ++ ·)
  return out

/-- `sol_chain?` on a scoped chain: proved as `sol_chain` proves it,
`sol_chain` suggested, and the lines that go on to a last line printed if it
does not end at one.  On `A ~~> B`: the chain from `A` to `B` (to `L` past
the program, by the rewrites the search finds), written out as one term. -/
elab_rules : tactic
  | `(tactic| sol_chain?%$tk) => Tactic.withMainContext do
    let g ← Tactic.getMainGoal
    let ty ← instantiateMVars (← g.getType)
    if ← isCoreGoal ty then
      solveCore g
      Tactic.replaceMainGoal []
      Solidity.ProofTree.suggest tk #["sol_chain"]
      if let some (B, true) ← chainEnd? ty then
        let gen ← generate (← instantiateMVars B)
        unless gen.links.isEmpty do
          let lines ← chainText gen B
          let start := (← lineText gen.splice (← lineType B).1 B true gen.erased).size
          logInfoAt tk (m!"the chain goes on to a last line; append to its statement:\n\
            {"\n".intercalate (lines.extract start lines.size |>.map ("    " ++ ·)).toList}" ++
            gen.stopNote)
      return
    unless ty.isAppOf ``Core.Fml.Leads || ty.isAppOf ``Core.Fml.LeadsE do throwUnsupportedSyntax
    let A := if ty.isAppOf ``Core.Fml.Leads then ty.getArg! 2 else ty.getArg! 1
    let A ← instantiateMVars A
    let gen ← generate A
    let gen ← match_expr ty with
      | Core.Fml.Leads _ _ _ B =>
        let B ← instantiateMVars B
        let some i := if A == B then some 0 else
            (gen.steps.findIdx? (·.2.1 == B)).map (· + 1)
          | throwError "sol_chain?: the derivation of{← indentLine A}\ndoes not reach{← indentLine B}"
        pure { gen with steps := gen.steps.extract 0 i, rewrites := #[], stop := none }
      | Core.Fml.LeadsE C _ Z L =>
        let L₀ ← lastErasure A (← instantiateMVars Z)
        let (path, note) ← Solidity.Chain.searchRewrites C L₀ (some (← instantiateMVars L))
        let some path := path
          | throwError "sol_chain?: no run of rewrites from{indentExpr L₀}\nreaches{indentExpr L}\
              {(note.map (m!"\n" ++ ·)).getD m!""}"
        pure { gen with rewrites := path, stop := none }
      | _ => throwUnsupportedSyntax
    let links := gen.links
    let lines ← if links.isEmpty then
        pure #["exact Solidity.Core.Fml.Leads.self _"]
      else do
        let ls ← chainText gen A
        let head := if !gen.rewrites.isEmpty then "exact Solidity.Core.Fml.ViaE.leads (show "
          else if links.size == 1 then "exact Solidity.Core.Fml.SoundRel.leads (show "
          else "exact Solidity.Core.Fml.Via.leads (show "
        let body := #[head ++ ls[0]!] ++ (ls.extract 1 ls.size).map ("    " ++ ·)
        pure (body.modify (body.size - 1) (· ++ " by sol_chain)"))
    let text := "\n".intercalate lines.toList
    let stx ← match Parser.runParserCategory (← getEnv) `tactic text with
      | .ok s => pure s
      | .error e => throwError "sol_chain?: the written chain does not parse: {e}\n{text}"
    Tactic.evalTactic stx
    Solidity.ProofTree.suggest tk lines

/-! `sol_rws [r₁, …, rₙ]` on `A ~~> B`: scoped, each `sequentialToParallel`
merges the line's update spine (`Fml.MergeBy`, the merge that leads on to
`B`); past the program, the derivation to `Z`, then `Update.lean`'s rewrites
from its erasure (`Calculus/RewriteChainGen.lean`'s `sol_rws`). -/

/-- Prove `A ~~> B` by the rewrites `ns`. -/
def proveCoreRws (g : MVarId) (ns : Array Lean.Name) : TermElabM Unit := do
  let ty ← instantiateMVars (← g.getType)
  match_expr ty with
  | Core.Fml.Leads _ _ A B =>
    unless ns.all (· == `sequentialToParallel) do
      throwError "sol_rws: while the program is open only `sequentialToParallel` rewrites a scoped line"
    let some h ← mergePath (← instantiateMVars A) (← instantiateMVars B) ns.size
      | throwError "sol_rws: {ns.size} merges of{← indentLine A}\ndo not give{← indentLine B}"
    g.assign h
  | Core.Fml.LeadsE _ _ _ _ => solveLeads g ns
  | _ => throwUnsupportedSyntax

elab_rules : tactic
  | `(tactic| sol_rws [$ns,*]) => Tactic.withMainContext do
    let g ← Tactic.getMainGoal
    let ty ← instantiateMVars (← g.getType)
    unless ty.isAppOf ``Core.Fml.Leads || ty.isAppOf ``Core.Fml.LeadsE do throwUnsupportedSyntax
    proveCoreRws g (ns.getElems.map (·.getId))
    Tactic.replaceMainGoal []
  | `(tactic| sol_rws?%$tk) => Tactic.withMainContext do
    let g ← Tactic.getMainGoal
    let ty ← instantiateMVars (← g.getType)
    let ns ← match_expr ty with
      | Core.Fml.Leads _ _ A B =>
        let A ← instantiateMVars A
        let B ← instantiateMVars B
        let mut found : Option Nat := none
        for n in [1:5] do
          if (← mergePath A B n).isSome then
            found := some n
            break
        let some n := found
          | throwError "sol_rws?: no run of merges from{← indentLine A}\nreaches{← indentLine B}"
        pure (Array.replicate n `sequentialToParallel)
      | Core.Fml.LeadsE C A Z L =>
        let L₀ ← lastErasure (← instantiateMVars A) (← instantiateMVars Z)
        let (path, note) ← Solidity.Chain.searchRewrites C L₀ (some (← instantiateMVars L))
        let some path := path
          | throwError "sol_rws?: no run of rewrites from{indentExpr L₀}\nreaches{indentExpr L}\
              {(note.map (m!"\n" ++ ·)).getD m!""}"
        pure (path.map (Lean.Name.mkSimple ·.1))
      | _ => throwUnsupportedSyntax
    proveCoreRws g ns
    Tactic.replaceMainGoal []
    let ids := ns.map (mkIdent ·)
    Lean.Meta.Tactic.TryThis.addSuggestion tk (← `(tactic| sol_rws [$ids,*]))

end Solidity.Core.Chain
