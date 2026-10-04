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
* `sol_chain?` on a goal `φ ~~> ψ` checks that this chain ends at `ψ`, proves
  the goal with it and suggests the `calc`;
* `sol_rws [r₁, …, rₙ]` proves a link `φ ~~> ψ` by the named rewrites in turn,
  each at the first place it applies but a read of the state as the program
  found it (the places `#last_line` and `#chain` look at): the link that
  stands for several rewrite lines deleted from a chain.  `sol_rws?` finds the
  names (the order `#chain` uses) and suggests them.

The rewrites are not confluent — the same line may leave by several — so the
generator fixes an order: `sequentialToParallel` first, `simplifyUpdate` last,
the rest as `~=>` tries them (`rwAnyArrows`).  It stops after `genFuel`
rewrites, or at a line it has seen.
-/

namespace Solidity

theorem Fml.Leads.comp {φ ψ χ : Fml C} (h₁ : φ ~~> ψ) (h₂ : ψ ~~> χ) : φ ~~> χ :=
  fun σ h => h₁ σ (h₂ σ h)

theorem Fml.Leads.self (φ : Fml C) : φ ~~> φ := fun _ h => h

namespace Chain

open Lean Elab Term Meta

/-- The most rewrites a generated chain takes past the program. -/
def genFuel : Nat := 64

/-- Where a rewrite comes in the generator's order: the merge first, the
dropping of dead captures last. -/
def genRank (n : String) : Nat :=
  if n == "sequentialToParallel" then 0 else if n == "simplifyUpdate" then 2 else 1

/-- The rewrite the generator takes on the line `L`, and the line it gives. -/
def nextRewrite (C L : Expr) : TermElabM (Option (String × Expr)) := do
  let cands ← stillApplies C L
  let mut best : Option (Nat × String × Expr) := none
  for (n, q) in cands do
    let k := genRank n
    match best with
    | some (k', _, _) => if k < k' then best := some (k, n, q)
    | none => best := some (k, n, q)
  return best.map fun (_, n, q) => (n, q)

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
        match ← ruleOfLine prev with
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
  let mut rws := #[]
  let mut seen : Std.HashSet Expr := {}
  let mut stop := none
  for _ in [0:genFuel] do
    if seen.contains prev then
      stop := some m!"the rewrites came back to a line they had left"
      break
    seen := seen.insert prev
    let some (n, q) ← nextRewrite C prev | break
    rws := rws.push (n, q)
    prev := q
  if rws.size == genFuel then stop := some m!"stopped after {genFuel} rewrites"
  return { splice := run.splice, steps, rewrites := rws, stop }

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
  let first ← ProofTree.termLines (← ProofTree.writeLine C φ m?)
  let mut out := #["calc " ++ first[0]!] ++ (first.extract 1 first.size).map ("    " ++ ·)
  let link (arrow : String) (pf : String) (l : Expr) : TermElabM (Array String) := do
    let line ← ProofTree.termLines (← ProofTree.writeLine C l m?)
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
  let last ← ProofTree.termLines (← ProofTree.writeLine C (g.last φ) g.splice.modality)
  let rows := g.tableRows φ
  let table := if rows.isEmpty then m!"" else
    m!"\n\nfresh variables (a `FreshNames` table renames them):\n  [{", ".intercalate rows.toList}]"
  let note := match g.stop with
    | some m => m!"\n\nthe chain stops early: {m}"
    | none => m!""
  logInfo (m!"last line:\n  {"\n  ".intercalate last.toList}\n\n\
    {"\n".intercalate (← g.calcLines C φ).toList}" ++ table ++ note)

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
    let mut cur := φ
    let mut ns : Array Lean.Name := #[]
    for _ in [0:genFuel] do
      if cur == ψ || (← withReducible (isDefEq cur ψ)) then break
      let some (n, q) ← nextRewrite C cur
        | throwError "sol_rws?: no rewrite applies to{indentExpr cur}\nshort of{indentExpr ψ}"
      ns := ns.push (Lean.Name.mkSimple n)
      cur := q
    proveRws g ns
    replaceMainGoal []
    let ids := ns.map (mkIdent ·)
    Lean.Meta.Tactic.TryThis.addSuggestion tk (← `(tactic| sol_rws [$ids,*]))

end Chain

end Solidity
