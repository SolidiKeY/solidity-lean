import Solidity.Calculus.LastLine
import Solidity.Calculus.ProofTree

/-!
# Writing a whole chain out: `#chain`, `sol_chain?` on `~~>`, `sol_rws`

`#derivation` and `sol_chain?` on `φ ~*> ψ` stop where the program ends.
Past it, a worked chain goes on by rewrites (`Calculus/ChainRewrites.lean`):
the stack merges, each read is resolved, and the line ends at one update
(`#last_line`).  This module runs both halves and writes the result out, so a
chain is generated once, pasted, and then edited by hand — lines deleted,
fresh variables renamed by a `FreshNames` table — never searched for again on
every check:

* `#chain φ` prints the last line and the `calc` from `φ` to it: one link per
  rule of the strategy (`~[r]~>`), then one per rewrite, picked by
  `LastLine.stillApplies` until none applies, and the fresh variables the lines
  write, as the rows of a `FreshNames` table to fill in;
* `#chain_rest c` does the same from the last line of the chain `c`, as the
  links to append to it;
* `sol_chain?` on a goal `φ ~~> ψ` checks that this chain ends at `ψ`, proves
  the goal with it and suggests the `calc`;
* `sol_rws [r₁, …, rₙ]` proves a link `φ ~~> ψ` by the named rewrites in turn,
  each at the first place it applies but a read of the state as the program
  found it (the places `#last_line` and `#chain` look at): the link that
  stands for several rewrite lines deleted from a chain.  `sol_rws?` finds the
  names (the order `#chain` uses) and suggests them.

The rewrites are not confluent — the same line may leave by several — so the
generator fixes an order: `sequentialToParallel` first, `simplifyUpdate` last,
the rest as `~=>` tries them (`rwAnyArrows`).  It does not commit to that
order: a greedy run can end early, at a line no rewrite applies to that a
later choice would have resolved, so the rewrites are searched depth first in
that order (`searchRewrites`), each line once, at most `genNodes` of them, and
the smallest last line wins (`sol_rws?`: the first path to its goal).
-/

namespace Solidity

theorem Fml.Leads.comp {φ ψ χ : Fml C} (h₁ : φ ~~> ψ) (h₂ : ψ ~~> χ) : φ ~~> χ :=
  fun σ h => h₁ σ (h₂ σ h)

theorem Fml.Leads.self (φ : Fml C) : φ ~~> φ := fun _ h => h

namespace Chain

open Lean Elab Term Meta

/-- Where a rewrite comes in the generator's order: the merge first, the
dropping of dead captures last. -/
def genRank (n : String) : Nat :=
  if n == "sequentialToParallel" then 0 else if n == "simplifyUpdate" then 2 else 1

/-- The most lines the search past the program tries. -/
def genNodes : Nat := 150

/-- The rewrites that apply to the line `L`, each with the line it gives, in
the generator's order (`genRank`, then the order `~=>` tries them). -/
def rewritesOn (C L : Expr) : TermElabM (Array (String × Expr)) := do
  let cands ← stillApplies C L
  return (List.range 3).toArray.flatMap fun k => cands.filter (genRank ·.1 == k)

/-- The size of a line, which the search minimises: the smaller last line is
the one with more reads resolved. -/
partial def lineSize : Expr → Nat
  | .app f a => lineSize f + lineSize a + 1
  | .lam _ t b _ | .forallE _ t b _ => lineSize t + lineSize b + 1
  | .letE _ t v b _ => lineSize t + lineSize v + lineSize b + 1
  | .mdata _ e | .proj _ _ e => lineSize e + 1
  | _ => 1

/-- What the search keeps: the lines tried, the smallest last line found and
the path to it, the path to the goal once found, and a search step that
failed. -/
structure Search where
  nodes : Nat := 0
  seen : Std.HashSet Expr := {}
  best : Option (Nat × Array (String × Expr)) := none
  found : Option (Array (String × Expr)) := none
  failed : Option MessageData := none

/-- Depth first from `L`, in the generator's order: a line no rewrite
applies to is a last line, and the smallest wins; with a goal, the first
path to it ends the search.  Each line has its own heartbeats, and one whose
search fails is a leaf. -/
partial def searchFrom (C : Expr) (goal? : Option Expr) (path : Array (String × Expr))
    (L : Expr) : StateRefT Search TermElabM Unit := do
  let s ← get
  if s.found.isSome || s.nodes ≥ genNodes || s.seen.contains L then return
  set { s with nodes := s.nodes + 1, seen := s.seen.insert L }
  if let some g := goal? then
    if L == g || (← withReducible (isDefEq L g)) then
      modify fun s => { s with found := some path }
      return
  let r : Except Exception (Array (String × Expr)) ←
    tryCatchRuntimeEx (.ok <$> withCurrHeartbeats (rewritesOn C L)) fun e => pure (.error e)
  match r with
  | .error e => modify fun s => { s with failed := s.failed <|> some e.toMessageData }
  | .ok cands =>
    if cands.isEmpty then
      let n := lineSize L
      modify fun s => match s.best with
        | some (b, _) => if n < b then { s with best := some (n, path) } else s
        | none => { s with best := some (n, path) }
    else
      for (n, q) in cands do
        searchFrom C goal? (path.push (n, q)) q

/-- The rewrites from `L` to a last line (`goal? = none`) or to the goal, and
a note when the search did not finish. -/
def searchRewrites (C L : Expr) (goal? : Option Expr := none) :
    TermElabM (Option (Array (String × Expr)) × Option MessageData) := do
  let ((), s) ← (searchFrom C goal? #[] L).run {}
  let note := if s.nodes ≥ genNodes then
      some m!"the search stopped after {genNodes} lines; this is the best it found"
    else s.failed.map fun m => m!"a step of the search failed: {m}"
  match goal? with
  | some _ => return (s.found, note)
  | none => return (s.best.map (·.2), note)

/-- A generated chain: the lines of the strategy with the rule that reached
each, the rewrites after with theirs, and why it stopped early, if it did. -/
structure Gen where
  splice : Splice
  steps : Array (String × Expr)
  rewrites : Array (String × Expr)
  stop : Option MessageData

/-- The last line of a generated chain. -/
def Gen.last (g : Gen) (φ : Expr) : Expr :=
  (g.rewrites.back?.map (·.2)).getD ((g.steps.back?.map (·.2)).getD φ)

/-- Run the strategy from `φ`, then the rewrites from its last line. -/
def generate (C φ : Expr) : TermElabM Gen := do
  let run ← runChain C φ
  let mut steps := #[]
  let mut prev := φ
  for l in run.lines do
    let n ← try
        match ← withCurrHeartbeats (ruleOfLine prev) with
        | some (_, n) => pure (if n == `taclet then "" else n.toString)
        | none => pure ""
      catch _ => pure ""
    steps := steps.push (n, l.fml)
    prev := l.fml
  if run.stuck then
    return { splice := run.splice, steps, rewrites := #[], stop := some (stuckNote run) }
  if steps.size ≥ runFuel then
    return { splice := run.splice, steps, rewrites := #[],
             stop := some m!"the strategy ran {runFuel} steps: go on from the last line" }
  let (rws, stop) ← searchRewrites C prev
  return { splice := run.splice, steps, rewrites := rws.getD #[], stop }

/-- The fresh variables written in `e`, by their default spellings (`se1`):
the left column of a `FreshNames` table is the name to give each. -/
partial def freshSpellings (e : Expr) : Array String :=
  let rec go (e : Expr) (acc : Array String) : Array String :=
    match e with
    | .app f a =>
      let acc := if e.isAppOfArity ``Var.fresh 2 then
          match e.appFn!.appArg!, e.appArg!.nat? <|> e.appArg!.rawNatLit? with
          | .lit (.strVal b), some k =>
            let s := s!"{b}{k}"
            if acc.contains s then acc else acc.push s
          | _, _ => acc
        else acc
      go a (go f acc)
    | .lam _ t b _ | .forallE _ t b _ => go b (go t acc)
    | .letE _ t v b _ => go b (go v (go t acc))
    | .mdata _ e | .proj _ _ e => go e acc
    | _ => acc
  go e #[]

/-- The `calc` of a generated chain, from `φ`, as lines of text: `rfl` where
the kernel computes a link on its own, `by sol_chain` elsewhere. -/
def Gen.calcLines (g : Gen) (C φ : Expr) : TermElabM (Array String) := do
  let m? := g.splice.modality
  let closed := g.splice.fmls.isEmpty && m?.isNone
  let first ← ProofTree.termLines (← withCurrHeartbeats (ProofTree.writeLine C φ m?))
  let mut out := #["calc " ++ first[0]!] ++ (first.extract 1 first.size).map ("    " ++ ·)
  let link (arrow : String) (pf : String) (l : Expr) : TermElabM (Array String) := do
    let line ← ProofTree.termLines (← withCurrHeartbeats (ProofTree.writeLine C l m?))
    let line := line.modify (line.size - 1) (· ++ s!" := {pf}")
    return #[s!"  _ {arrow} {line[0]!}"] ++ (line.extract 1 line.size).map ("      " ++ ·)
  for (n, l) in g.steps do
    let arrow := if n.isEmpty then "~>" else s!"~[{n}]~>"
    out := out ++ (← link arrow (if closed then "rfl" else "by sol_chain") l)
  for (n, l) in g.rewrites do
    out := out ++ (← link s!"~[{n}]~>" "by sol_chain" l)
  return out

/-- The rows of a `FreshNames` table for the fresh variables of the lines. -/
def Gen.tableRows (g : Gen) (φ : Expr) : Array String := Id.run do
  let mut seen : Array String := #[]
  for e in #[φ] ++ g.steps.map (·.2) ++ g.rewrites.map (·.2) do
    for s in freshSpellings e do
      unless seen.contains s do seen := seen.push s
  return seen.map fun s => s!"(\"?\", \"{s}\")"

end Chain

namespace Chain
open Lean Elab Command Term Meta

/-- `#chain φ`: the chain from `φ` to its last line — the strategy's links,
then the rewrites, one per line — as a `calc` to paste, with the last line to
state and the rows of a `FreshNames` table for the fresh variables it writes.
The section's variables are in scope (`variable (m : Modality) (φ : Post C)`). -/
elab "#chain " t:term : command => runTermElabM fun _ => do
  let φ ← instantiateMVars (← elabTerm t none)
  synthesizeSyntheticMVarsNoPostponing
  let φ ← instantiateMVars φ
  let ty ← whnf (← inferType φ)
  unless ty.isAppOfArity ``Fml 1 do throwError "#chain: not a formula{indentExpr φ}"
  let C := ty.appArg!
  let g ← generate C φ
  let last ← ProofTree.termLines (← withCurrHeartbeats (ProofTree.writeLine C (g.last φ) g.splice.modality))
  let rows := g.tableRows φ
  let table := if rows.isEmpty then m!"" else
    m!"\n\nfresh variables (a `FreshNames` table renames them):\n  [{", ".intercalate rows.toList}]"
  let note := match g.stop with
    | some m => m!"\n\nthe chain stops early: {m}"
    | none => m!""
  logInfo (m!"last line:\n  {"\n  ".intercalate last.toList}\n\n\
    {"\n".intercalate (← g.calcLines C φ).toList}" ++ table ++ note)

/-- `#chain_rest c`: what the chain `c` still lacks — from the last line of its
statement (`A ~*> B` or `A ~~> B`), the strategy's steps and then the
rewrites to a last line, as links to append (`_ ~[r]~> _ := by sol_chain`,
the statement pinning every line) and the new last line to state.  The
statement's binders (a modality `m`, postconditions `φ : Post C`) are opened,
as `#last_line` opens them. -/
elab "#chain_rest " c:ident : command => runTermElabM fun _ => do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let info ← getConstInfo n
  forallTelescope info.type fun _ ty => do
    let ty ← instantiateMVars ty
    let (C, B) ← match ty.getAppFnArgs with
      | (``Fml.Steps, #[C, _, B]) | (``Fml.Leads, #[C, _, B]) => pure (C, B)
      | _ => throwError "#chain_rest: {c} is no chain: its statement is not `A ~*> B` \
          or `A ~~> B`{indentExpr ty}"
    let B ← instantiateMVars B
    let g ← generate C B
    if g.steps.isEmpty && g.rewrites.isEmpty then
      logInfo m!"{c} ends at a last line"
      return
    let last ← ProofTree.termLines
      (← withCurrHeartbeats (ProofTree.writeLine C (g.last B) g.splice.modality))
    let arrow (n : String) := if n.isEmpty then "~>" else s!"~[{n}]~>"
    let links := (g.steps.map (·.1) ++ g.rewrites.map (·.1)).map fun n =>
      s!"    _ {arrow n} _ := by sol_chain"
    let note := match g.stop with
      | some m => m!"\n\nthe chain stops early: {m}"
      | none => m!""
    logInfo (m!"last line:\n  {"\n  ".intercalate last.toList}\n\nlinks to append:\n\
      {"\n".intercalate links.toList}" ++ note)

end Chain

namespace ProofTree
open Lean Elab Tactic Meta

/-- `sol_chain?` on `φ ~~> ψ`: generate the chain from `φ` (`Chain.generate`),
check it ends at `ψ`, prove the goal with its `calc` and suggest it. -/
elab_rules : tactic
  | `(tactic| sol_chain?%$tk) => withMainContext do
    let g ← getMainGoal
    let ty ← instantiateMVars (← g.getType)
    unless ty.isAppOfArity ``Fml.Leads 3 do throwUnsupportedSyntax
    let #[C, φ, ψ] := ty.getAppArgs | throwUnsupportedSyntax
    let gen ← Chain.generate C φ
    let last := gen.last φ
    unless ← isDefEq last ψ do
      throwError "sol_chain?: the chain from the line before ends at{indentExpr last}\nnot{indentExpr ψ}"
    -- every arrow is a `SoundRel`, so `leads` takes a `calc` of any length to
    -- `~~>`: one link is its own relation, and steps alone compose to `~*>`
    let lines ← if gen.steps.isEmpty && gen.rewrites.isEmpty then
        pure #["exact Solidity.Fml.Leads.self _"]
      else do
        let ls ← gen.calcLines C φ
        let body := #["exact Solidity.Fml.SoundRel.leads (" ++ ls[0]!] ++
          (ls.extract 1 ls.size).map ("  " ++ ·)
        pure (body.modify (body.size - 1) (· ++ ")"))
    let text := "\n".intercalate lines.toList
    let stx ← match Parser.runParserCategory (← getEnv) `tactic text with
      | .ok s => pure s
      | .error e => throwError "sol_chain?: the written chain does not parse: {e}\n{text}"
    evalTactic stx
    suggest tk lines

end ProofTree

namespace Chain
open Lean Elab Tactic Meta

/-- The rewrite `n` on the line `A`, at the first place it applies: the line
after, and `A ~~> B`. -/
def rwStep (C A : Expr) (n : Lean.Name) : TermElabM (Expr × Expr) := do
  let some arrow ← rwArrow? (mkIdent n) | throwError "sol_rws: {n} is no rewrite"
  let ψ ← mkFreshExprMVar (mkApp (mkConst ``Fml) C)
  -- the candidates `stillApplies` chose among, so the replay meets the same
  -- instance: never a read of the state as the program found it
  let (rs, failed) ← rwCandidatesWith (fun t => !plainRead t) C A arrow
  let (r, q, pf) ← rwSelect C A ψ n.toString rs failed
  let q ← instantiateMVars q
  let h := pf.getD (someRefl C q)
  return (q, mkAppN (mkConst ``Fml.RwBy.sound) #[C, mkStrLit n.toString, r, A, q, h])

/-- The goal `φ ~~> ψ`, its contract and ends. -/
def leadsGoal (g : MVarId) : MetaM (Expr × Expr × Expr) := do
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOfArity ``Fml.Leads 3 do throwError "sol_rws: the goal is not `φ ~~> ψ`{indentExpr ty}"
  let #[C, φ, ψ] := ty.getAppArgs | unreachable!
  return (C, ← instantiateMVars φ, ← instantiateMVars ψ)

/-- Prove `φ ~~> ψ` by the rewrites `ns` in turn. -/
def proveRws (g : MVarId) (ns : Array Lean.Name) : TermElabM Unit := do
  let (C, φ, ψ) ← leadsGoal g
  let mut cur := φ
  let mut pf := mkApp2 (mkConst ``Fml.Leads.self) C φ
  for n in ns do
    let (q, h) ← rwStep C cur n
    pf := mkAppN (mkConst ``Fml.Leads.comp) #[C, φ, cur, q, pf, h]
    cur := q
  unless cur == ψ || (← withReducible (isDefEq cur ψ)) do
    throwError "sol_rws: the rewrites give{indentExpr cur}\nnot{indentExpr ψ}"
  g.assign pf

syntax "sol_rws" " [" ident,* "]" : tactic

/-- `sol_rws?`: the rewrites `#chain` takes from the line before to the line
after, suggested as `sol_rws [r₁, …, rₙ]`. -/
syntax (name := solRwsQ) "sol_rws?" : tactic

elab_rules : tactic
  | `(tactic| sol_rws [$ns,*]) => withMainContext do
    proveRws (← getMainGoal) (ns.getElems.map (·.getId))
    replaceMainGoal []
  | `(tactic| sol_rws?%$tk) => withMainContext do
    let g ← getMainGoal
    let (C, φ, ψ) ← leadsGoal g
    let (path, note) ← searchRewrites C φ (some ψ)
    let some path := path
      | throwError "sol_rws?: no run of rewrites from{indentExpr φ}\nreaches{indentExpr ψ}\
          {(note.map (m!"\n" ++ ·)).getD m!""}"
    let ns := path.map (Lean.Name.mkSimple ·.1)
    proveRws g ns
    replaceMainGoal []
    let ids := ns.map (mkIdent ·)
    Lean.Meta.Tactic.TryThis.addSuggestion tk (← `(tactic| sol_rws [$ids,*]))

end Chain

end Solidity
