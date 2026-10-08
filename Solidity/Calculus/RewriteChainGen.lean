import Solidity.Calculus.RewriteChains

/-!
# Chains past the program, written out: `#last_line`, `sol_rws`, the search

The rewrite half of a worked chain (`Calculus/RewriteChains.lean`): what the
scoped chains' commands (`Calculus/Core/ChainGen.lean`,
`Calculus/Core/LastLine.lean`) run past the program, on the erasure of the
strategy's last line.

* `#last_line chain` checks that a chain of rewrites (`Fml.Via`, one link,
  or `~~>`) ends at a last line — no program left, one parallel update in
  front of each goal (the shape), and no rewrite a chain takes still
  applies (`stillApplies`: every one `~=>` tries but `simplifyUpdate`,
  under either modality when the chain is over a modality variable).
  "Applies" is what `~=>` accepts (`Chain.rwSelect`): a rewrite that
  computes a line over an opaque postcondition but cannot be proved of it
  does not count.  `simplifyUpdate` is not among them: it drops bindings,
  and a chain keeps them all (`chainRewrite`).  The check runs on the
  chain's statement with its binders opened (a modality `m`,
  postconditions `φ : Post C`, a premise of the chain).
* `searchRewrites` runs the rewrites from a line to a last line or to a
  given line.  The rewrites are not confluent — the same line may leave by
  several — so the search fixes an order: `sequentialToParallel` first, the
  rest as `~=>` tries them (`rwAnyArrows`), depth first, each line once, at
  most `genNodes` of them, and the smallest last line wins (the first path
  to a given line).  `#chain`, `#chain_rest` and `sol_chain?` write the
  links it finds; `groupSteps` groups the scoped strategy's steps before
  them as the worked examples print them.
* `sol_rws [r₁, …, rₙ]` proves a link `φ ~~> ψ` by the named rewrites in
  turn, each at the first place it applies but a read of the state as the
  program found it.  `sol_rws?` finds the names and suggests them.
* `sol_chain?` on `φ ~~> ψ` writes the rewrites from `φ` to `ψ` as one
  chain term and proves the goal with it; on a chain of rewrites it proves
  it as `sol_chain` does and prints what goes on to a last line.

Today's strategy's steps before the rewrites (`#chain`, `#chain_rest` on
`Update.lean`'s formulas with a program) went with today's rule table (W4
`calc-del`, `docs/intrinsic.md`): the scoped commands take those.
-/

namespace Solidity

namespace Chain

open Lean Elab Term Meta

/-- The goals of a line, each with the number of updates on the path to it:
through `{U}`, both sides of `∧`, the consequent of `→`, `¬` (so the parts of
a branch's cover, `⟨[ revert(); ]⟩ false ∨ …`), `havoc` and `∀`. -/
partial def goalsOf (e : Expr) (n : Nat) : MetaM (Array (Nat × Expr)) := do
  let e ← instantiateMVars e
  match e.getAppFnArgs with
  | (``NFml.upd, #[_, _, _, ψ]) => goalsOf ψ (n + 1)
  | (``NFml.and, #[_, φ, ψ]) => return (← goalsOf φ n) ++ (← goalsOf ψ n)
  | (``NFml.imp, #[_, _, ψ]) => goalsOf ψ n
  | (``NFml.not, #[_, ψ]) => goalsOf ψ n
  | (``NFml.havoc, #[_, ψ]) => goalsOf ψ n
  | (``NFml.anon, #[_, _, ψ]) => goalsOf ψ n
  | (``NFml.all, #[_, _, _, ψ]) => goalsOf ψ n
  | _ => return #[(n, e)]

/-- What is wrong with the shape of the line, if anything. -/
def shapeProblems (B : Expr) : MetaM (Array MessageData) := do
  let mut out := #[]
  for (n, g) in ← goalsOf B 0 do
    if n ≥ 2 then
      out := out.push m!"{n} updates stand in front of{indentExpr g}\n\
        (one parallel update does: `~[sequentialToParallel]~>`)"
  return out

/-- A storage term holding no write: the state variable, a storage variable, or
a member of one. -/
partial def plainStorage (s : Expr) : Bool :=
  match s.getAppFnArgs with
  | (``STerm.storage, _) | (``STerm.pv, _) => true
  | (``STerm.select, #[_, s, _]) => plainStorage s
  | _ => false

/-- A read of the state as the program found it, `find(storage, p)` or
`find(select(storage, r), p)`: nothing resolves it, and the member-wise laws
that apply to it (`findMemberCons`) only respell it. -/
def plainRead (t : Expr) : Bool :=
  match t.getAppFnArgs with
  | (``Term.find, #[_, s, _]) => plainStorage s
  | _ => false

/-- A rewrite a chain takes past the program: every one `~=>` tries but
`simplifyUpdate`, which drops the bindings nothing reads.  A chain keeps every
binding to its last line, the fresh captures (`se1`, `sp1`) included, so a
reader sees where each value went. -/
def chainRewrite (n : String) : Bool := n != "simplifyUpdate"

/-- The rewrites a chain takes (`chainRewrite`; with `all`, every one `~=>`
tries, `simplifyUpdate` too) that `~=>` would accept on the line `L`, each
with the line it gives and the hypotheses of the chain its side conditions
use: the ones `rwSelect` selects with the line after left open, a law at
every instance but a read of the state as found. -/
def stillAppliesUsing (C L : Expr) (all : Bool := false) :
    TermElabM (Array (String × Expr × Array FVarId)) := do
  let mut out := #[]
  for (n, a) in (← rwAnyArrows).filter (all || chainRewrite ·.1) do
    let st ← saveState
    try
      let (rs, failed) ← rwCandidatesWith (fun t => !plainRead t) C L a
      if rs.isEmpty then
        st.restore
        continue
      let ψ ← mkFreshExprMVar (mkApp (mkConst ``NFml) C)
      let (r, q, pf) ← rwSelect C L ψ n rs failed
      let q ← instantiateMVars q
      let uses ← (collectFVars (collectFVars {} (← instantiateMVars r))
        (← instantiateMVars (pf.getD r))).fvarIds.filterM fun x => do isProp (← x.getType)
      st.restore
      out := out.push (n, q, uses)
    catch _ =>
      st.restore
  return out

/-- `stillAppliesUsing`, the lines alone. -/
def stillApplies (C L : Expr) : TermElabM (Array (String × Expr)) := do
  return (← stillAppliesUsing C L).map fun (n, q, _) => (n, q)

/-- The contract and the two ends of a chain's statement: one link (`~[n]~>`,
`~=>`), `~~>`, or a chain of links (`Fml.Via`), whose end is its last line. -/
def chainEnds? (ty : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let ty ← instantiateMVars ty
  match ty.getAppFnArgs with
  | (``NFml.Leads, #[C, A, B]) | (``NFml.RwAny, #[C, A, B]) | (``NFml.RwBy, #[C, _, _, A, B]) =>
    return some (C, A, B)
  | (``NFml.Via, #[C, A, ws]) =>
    let some ws ← listElems? ws | return none
    let some w := ws.back? | return some (C, A, A)
    let w ← whnfR w
    unless w.isAppOfArity ``Prod.mk 4 do return none
    return some (C, A, w.getArg! 3)
  | _ => return none

/-- The modality variables of a line. -/
def modalityVars (e : Expr) : MetaM (Array FVarId) := do
  let mut out := #[]
  for x in (collectFVars {} e).fvarIds do
    if (← instantiateMVars (← x.getType)).isConstOf ``Modality then out := out.push x
  return out

/-- Where a rewrite comes in the generator's order: the merge first, then
the rest.  `simplifyUpdate` is not among them (`chainRewrite`). -/
def genRank (n : String) : Nat :=
  if n == "sequentialToParallel" then 0 else 1

/-- The most lines the search past the program tries. -/
def genNodes : Nat := 150

/-- The rewrites that apply to the line `L`, each with the line it gives and
the hypotheses it uses, in the generator's order (`genRank`, then the order
`~=>` tries them).  With `all`, `simplifyUpdate` among them: a search for a
given line may need it, a chain to its last line never takes it. -/
def rewritesOn (C L : Expr) (all : Bool := false) :
    TermElabM (Array (String × Expr × Array FVarId)) := do
  let cands ← stillAppliesUsing C L all
  return (List.range 2).toArray.flatMap fun k => cands.filter (genRank ·.1 == k)

/-- The size of a line, which the search minimises: the smaller last line is
the one with more reads resolved. -/
partial def lineSize : Expr → Nat
  | .app f a => lineSize f + lineSize a + 1
  | .lam _ t b _ | .forallE _ t b _ => lineSize t + lineSize b + 1
  | .letE _ t v b _ => lineSize t + lineSize v + lineSize b + 1
  | .mdata _ e | .proj _ _ e => lineSize e + 1
  | _ => 1

/-- What the search keeps: the lines tried, with the hypotheses the rewrite
that reached each uses, the smallest last line found and the path to it, the
path to the goal once found, and a search step that failed. -/
structure Search where
  nodes : Nat := 0
  seen : Std.HashMap Expr (Array FVarId) := {}
  best : Option (Nat × Array (String × Expr)) := none
  found : Option (Array (String × Expr)) := none
  failed : Option MessageData := none

/-- Depth first from `L`, in the generator's order: a line no rewrite
applies to is a last line, and the smallest wins; with a goal, the first
path to it ends the search.  Each line has its own heartbeats, and one whose
search fails is a leaf. -/
partial def searchFrom (C : Expr) (goal? : Option Expr) (path : Array (String × Expr))
    (uses : Array FVarId) (L : Expr) : StateRefT Search TermElabM Unit := do
  let s ← get
  if s.found.isSome || s.nodes ≥ genNodes || s.seen.contains L then return
  set { s with nodes := s.nodes + 1, seen := s.seen.insert L uses }
  if let some g := goal? then
    if L == g || (← withReducible (isDefEq L g)) then
      modify fun s => { s with found := some path }
      return
  let r : Except Exception (Array (String × Expr × Array FVarId)) ←
    tryCatchRuntimeEx (.ok <$> withCurrHeartbeats (rewritesOn C L goal?.isSome)) fun e =>
      pure (.error e)
  match r with
  | .error e => modify fun s => { s with failed := s.failed <|> some e.toMessageData }
  | .ok cands =>
    if cands.isEmpty then
      let n := lineSize L
      modify fun s => match s.best with
        | some (b, _) => if n < b then { s with best := some (n, path) } else s
        | none => { s with best := some (n, path) }
    else
      for (n, q, us) in cands do
        searchFrom C goal? (path.push (n, q)) us q

/-- The rewrites from `L` to a last line (`goal? = none`) or to the goal, a
note when the search did not finish, and the hypotheses each line's rewrite
uses. -/
def searchRewritesUsing (C L : Expr) (goal? : Option Expr := none) :
    TermElabM (Option (Array (String × Expr)) × Option MessageData × Std.HashMap Expr (Array FVarId)) := do
  let ((), s) ← (searchFrom C goal? #[] #[] L).run {}
  let note := if s.nodes ≥ genNodes then
      some m!"the search stopped after {genNodes} lines; this is the best it found"
    else s.failed.map fun m => m!"a step of the search failed: {m}"
  match goal? with
  | some _ => return (s.found, note, s.seen)
  | none => return (s.best.map (·.2), note, s.seen)

/-- The rewrites from `L` to a last line (`goal? = none`) or to the goal, and
a note when the search did not finish. -/
def searchRewrites (C L : Expr) (goal? : Option Expr := none) :
    TermElabM (Option (Array (String × Expr)) × Option MessageData) := do
  let (p, note, _) ← searchRewritesUsing C L goal?
  return (p, note)

/-- The line `φ`'s Lean terms (`punch`) and its modality, when it is a
variable. -/
def spliceOf (C φ : Expr) : MetaM Splice := do
  let (φ', sp) ← (punch C (← instantiateMVars φ)).run {}
  return { sp with modality := ← modalityOf? φ' }

/-- A generated chain: the steps of the strategy before it with the rule that
reached each (the scoped chains' commands fill them; none here), the
rewrites after with theirs, and why it stopped early, if it did. -/
structure Gen where
  splice : Splice
  steps : Array (String × Expr) := #[]
  rewrites : Array (String × Expr)
  /-- the hypotheses of the chain each rewrite's side conditions use -/
  rwUses : Array (Array FVarId) := #[]
  stop : Option MessageData

/-- The last line of a generated chain. -/
def Gen.last (g : Gen) (φ : Expr) : Expr :=
  (g.rewrites.back?.map (·.2)).getD ((g.steps.back?.map (·.2)).getD φ)

/-- The rewrites from `φ`: to a last line, or, with a goal, to the goal. -/
def generate (C φ : Expr) (goal? : Option Expr := none) : TermElabM Gen := do
  let (rws, stop, uses) ← searchRewritesUsing C φ goal?
  let rws := rws.getD #[]
  return { splice := ← spliceOf C φ, rewrites := rws, stop,
           rwUses := rws.map fun (_, q) => uses.getD q #[] }

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

/-! ## The links, as the worked examples print them

The worked examples print a trace
with two arrows: `⇝` for a rule, `⇝*` for a run of steps it does not dwell
on — a declaration with the binding it leaves (`uint pv = 10; Account
storage acc = alice.account;` to `{pv := 10}{acc := alice.account}`), and
`uint v = total;` to `{v := find(storage, total)}`.  They never print the
`⟨[ ]⟩` line `emptyModality` leaves.  `groupSteps` follows them: `⇝` is
`~[r]~>`, `⇝*` is `~*>`.  A run the generator leaves as several links can
be joined by hand into one `~*>`, which `sol_chain` proves alike. -/

/-- How a worked example prints a step of the strategy, by the rule that took it. -/
inductive StepKind where
  /-- a declaration dropped to its assignment, or one with no initialiser -/
  | decl
  /-- a local bound: a value assigned, an alias bound to a path -/
  | bind
  /-- a read into a local, one rule: part of the declaration it follows -/
  | read
  /-- `emptyModality`: the `⟨[ ]⟩` is never printed -/
  | empty
  /-- every other rule: an unfold, a capture, a write, a split -/
  | other
  deriving BEq

/-- The rules that drop a declaration. -/
def declRules : List String :=
  ["localValueDeclInitDrop", "valueDeclSkip", "storageLocalDeclInitDrop", "storageLocalDeclSkip",
    "memoryLocalDeclInitDrop"]

/-- The rules that bind a local to a value or a path, reading nothing. -/
def bindRules : List String :=
  ["localValueAssign", "storageLocalRootRebind", "storageFieldReadBindLocalRoot",
    "storageIndexReadMappingBindLocalRoot", "storageIndexReadArrayBindLocalRoot",
    "storageIndexReadArrayBindLocalRootMappingElement", "memoryRootRebind",
    "memoryFieldReadAliasRoot", "memoryIndexReadArrayMemory"]

/-- The rules that read a value into a local in one step. -/
def readRules : List String :=
  ["storageRootReadSelect", "storageFieldReadFind", "storageIndexReadMappingFind",
    "storageIndexReadArrayFind", "storageFieldReadStoreRoot", "storageIndexReadMappingStoreRoot",
    "storageIndexReadArrayStoreRoot", "storageLengthRead", "memoryLengthRead",
    "memoryFieldRead", "memoryIndexReadArrayValue"]

/-- The kind of the step the rule `n` takes (`""` for a rule with no name). -/
def stepKind (n : String) : StepKind :=
  if n == "emptyModality" then .empty
  else if declRules.contains n then .decl
  else if bindRules.contains n then .bind
  else if readRules.contains n then .read
  else .other

/-- The strategy's steps as the links of a chain, each with its arrow and the
line it ends at:

* a run of declarations and bindings is one `~*>` (`⇝*`): a
  declaration dropped (`StepKind.decl`), a local bound (`.bind`), and a read
  straight after a declaration, which is that declaration's initialiser
  (`.read`);
* `emptyModality` joins the link before it, so a rule and the `⟨[ ]⟩` it
  leaves are one `~*>`;
* every other step is its own `~[r]~>` (`⇝`), as is a run of one
  step. -/
def groupSteps (steps : Array (String × Expr)) : Array (String × Expr) := Id.run do
  -- each group: its rules, its last line, and whether it is a run of
  -- declarations and bindings still open
  let mut groups : Array (Array String × Expr × Bool) := #[]
  let mut prev : Option StepKind := none
  for (n, l) in steps do
    let k := stepKind n
    let openRun := match groups.back? with
      | some (_, _, o) => o
      | none => false
    let joins := match k with
      | .empty => !groups.isEmpty
      | .decl | .bind => openRun
      | .read => openRun && prev == some StepKind.decl
      | .other => false
    if joins then
      groups := groups.modify (groups.size - 1) fun (ns, _, _) =>
        (ns.push n, l, k != StepKind.empty)
    else
      groups := groups.push (#[n], l, k == StepKind.decl || k == StepKind.bind)
    prev := some k
  return groups.map fun (ns, l, _) =>
    if ns.size == 1 then
      (if ns[0]!.isEmpty then "~>" else s!"~[{ns[0]!}]~>", l)
    else ("~*>", l)

/-- The links of a generated chain: the strategy's steps grouped
(`groupSteps`), then one `~[r]~>` per rewrite. -/
def Gen.links (g : Gen) : Array (String × Expr) :=
  groupSteps g.steps ++ g.rewrites.map fun (n, l) => (s!"~[{n}]~>", l)

/-- The most links one chain term is written with; a longer chain is split
into segments of at most this many links, each a declaration with its own
heartbeats, composed by `Fml.Leads.via`. -/
def segLinks : Nat := 10

/-- `xs` cut into `n` runs of nearly equal length, in order. -/
def cutEven (xs : Array α) (n : Nat) : Array (Array α) := Id.run do
  let n := max n 1
  let mut out := #[]
  let mut i := 0
  for j in List.range n do
    let len := xs.size / n + (if j < xs.size % n then 1 else 0)
    out := out.push (xs.extract i (i + len))
    i := i + len
  return out

/-- The line `e : NFml C` as a calc line is written: `dl!{ φ }`, or at a
modality `dl![m]{ φ }` (`m` the line's modality variable, or `.box` for a
box's update with no modality under it) — the first of these that reads
back as `e`; Lean's own printing where the notation escapes. -/
def writeLine (C e : Expr) (m? : Option Expr) : TermElabM Lean.Term := do
  let φ ← ppFml e
  if isEscape φ then return ← escapeTerm e
  let φ ← withDecls e φ
  let mods : Array (Option Lean.Term) ← match m? with
    | some m => pure #[some ⟨mkIdent (← m.fvarId!.getUserName)⟩]
    | none => pure #[none, some (ProofTree.dotIdent `box), some (ProofTree.dotIdent `diamond)]
  let cands : Array Lean.Term ← mods.mapM fun
    | none => `(dl!{ $φ:dl_fml })
    | some m => `(dl![$m]{ $φ:dl_fml })
  for t in cands do
    let ok ← withoutModifyingState do
      try
        let e' ← Term.withoutErrToSorry do
          let e' ← Term.elabTermEnsuringType t (mkApp (mkConst ``NFml) C)
          Term.synthesizeSyntheticMVarsNoPostponing
          instantiateMVars e'
        pure (!e'.hasExprMVar && (← isDefEq e' e))
      catch _ => pure false
    if ok then return t
  return cands[0]!

/-- A line as text, at the line's modality. -/
def lineText (C : Expr) (m? : Option Expr) (l : Expr) : TermElabM (Array String) := do
  ProofTree.termLines (← withCurrHeartbeats (writeLine C l m?))

/-- The chain term from `φ` through `links`, as lines of text: the first line,
then one line per link, `{arrow} {line}`, every line written. -/
def viaLines (C : Expr) (m? : Option Expr) (φ : Expr) (links : Array (String × Expr)) :
    TermElabM (Array String) := do
  let first ← lineText C m? φ
  let mut out := first
  for (arrow, l) in links do
    let line ← lineText C m? l
    out := out.push s!"{arrow} {line[0]!}" ++ (line.extract 1 line.size).map ("  " ++ ·)
  return out

/-- The keyword a chain of `links` is stated with: a chain (`Fml.Via`) and
a link of the strategy or a rewrite are propositions, a `theorem`; a single
`~*>` is the derivation itself (`Fml.Steps`), a `def`. -/
def chainKeyword (links : Array (String × Expr)) : String :=
  if links.size == 1 && links[0]!.1 == "~*>" then "def" else "theorem"

/-- The declarations that state a generated chain from `φ`: one
`theorem name : φ ~[r]~> … := by sol_chain`, or, past `segLinks` links, a
`theorem` per segment (`name1`, `name2`, …, each starting at the line the one before
ends at) and `theorem name : φ ~~> ψ` composing them.  A declaration whose
rewrites close a side condition by a hypothesis of the section
(`variable (hk : STerm.KindFreeAt …)`) includes it (`include hk in`), and
the composition passes it by name; the section's other variables are left to
unification (`..`). -/
def Gen.decls (g : Gen) (C φ : Expr) (name : String := "chain") : TermElabM (Array String) := do
  let m? := g.splice.modality
  let links := g.links
  -- the hypotheses the links use, by link: none for the strategy's steps
  let uses : Array (Array FVarId) :=
    (groupSteps g.steps).map (fun _ => #[]) ++ g.rewrites.mapIdx fun i _ => g.rwUses.getD i #[]
  let hypNames (us : Array (Array FVarId)) : MetaM (Array String) := do
    let mut out := #[]
    for d in ← getLCtx do
      if us.any (·.contains d.fvarId) then out := out.push d.userName.toString
    return out
  let incl (hs : Array String) : Array String :=
    if hs.isEmpty then #[] else #[s!"include {" ".intercalate hs.toList} in"]
  let ind (ls : Array String) : Array String := ls.map ("    " ++ ·)
  let stated (ls : Array String) : Array String :=
    ls.modify (ls.size - 1) (· ++ " := by") |>.push "  sol_chain"
  if links.size ≤ segLinks then
    return incl (← hypNames uses) ++ #[s!"{chainKeyword links} {name} :"] ++
      stated (ind (← viaLines C m? φ links))
  let n := (links.size + segLinks - 1) / segLinks
  let segs := cutEven (links.zip uses) n
  let mut out := #[]
  let mut start := φ
  let mut parts := #[]
  for seg in segs do
    let i := parts.size + 1
    let hs ← hypNames (seg.map (·.2))
    out := out ++ incl hs ++ #[s!"{chainKeyword (seg.map (·.1))} {name}{i} :"] ++
      stated (ind (← viaLines C m? start (seg.map (·.1)))) |>.push ""
    start := (seg.back?.map (·.1.2)).getD start
    parts := parts.push s!"({name}{i} {String.join (hs.toList.map fun h => s!"({h} := {h}) ")}..)"
  let comp := match parts.toList with
    | p :: q :: rest => s!"{p}.leads.via {q}" ++ String.join (rest.map (s!" |>.via " ++ ·))
    | _ => ""
  let firstL ← lineText C m? φ
  let lastL ← lineText C m? start
  let stmt := ind firstL ++
    ind (#["~~> " ++ lastL[0]!] ++ (lastL.extract 1 lastL.size).map ("  " ++ ·))
  return out ++ incl (← hypNames uses) ++ #[s!"theorem {name} :"] ++
    stmt.modify (stmt.size - 1) (· ++ " :=")
    |>.push s!"  {comp}"

/-- The rows of a `FreshNames` table for the fresh variables of the lines. -/
def Gen.tableRows (g : Gen) (φ : Expr) : Array String := Id.run do
  let mut seen : Array String := #[]
  for e in #[φ] ++ g.steps.map (·.2) ++ g.rewrites.map (·.2) do
    for s in freshSpellings e do
      unless seen.contains s do seen := seen.push s
  return seen.map fun s => s!"(\"?\", \"{s}\")"

/-- A note for a chain that stops early, if it does. -/
def Gen.stopNote (g : Gen) : MessageData :=
  match g.stop with
  | some m => m!"\n\nthe chain stops early: {m}"
  | none => m!""

end Chain

namespace Chain
open Lean Elab Command Term Meta

/-- `#last_line c`: the chain `c` ends at a last line — no program left, one
parallel update in front of each goal, and no rewrite a chain takes
(`chainRewrite`) still applies to it (under either modality, for a chain
over a modality variable).  Silent when it does; one error listing what is
left otherwise. -/
elab "#last_line " c:ident : command => Command.runTermElabM fun _ => do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let info ← getConstInfo n
  forallTelescope info.type fun _ ty => do
    let ty ← instantiateMVars ty
    let some (C, _, B) ← chainEnds? ty
      | throwError "#last_line: {c} is no chain: its statement is not a chain \
          `A ~[r]~> B ~*> …` or `A ~~> B`{indentExpr ty}"
    let B ← instantiateMVars B
    let mut problems ← shapeProblems B
    let ms ← modalityVars B
    if ms.size ≥ 2 then
      throwError "#last_line: the last line of {c} is under two modalities{indentExpr B}"
    let lines : List (Option String × Expr) := match ms[0]? with
      | some m => [(some "under the box", B.replaceFVar (.fvar m) (mkConst ``Modality.box)),
                   (some "under the diamond", B.replaceFVar (.fvar m) (mkConst ``Modality.diamond))]
      | none => [(none, B)]
    -- a line computed at a fixed modality, with `m` put back where it was
    let hasConst (e : Expr) (n : Lean.Name) : Bool := (e.find? (·.isConstOf n)).isSome
    let back (q : Expr) : Expr := match ms[0]? with
      | some m =>
        if hasConst B ``Modality.box || hasConst B ``Modality.diamond then q else
          q.replace fun e =>
            if e.isConstOf ``Modality.box || e.isConstOf ``Modality.diamond then some (.fvar m)
            else none
      | none => q
    let mut found : Array (String × Expr × Array String) := #[]
    for (where?, L) in lines do
      for (r, q) in ← stillApplies C L do
        let q := back q
        let tag := where?.getD ""
        if let some i := found.findIdx? fun (r', q', _) => r' == r && q' == q then
          found := found.modify i fun (r', q', ws) => (r', q', ws.push tag)
        else
          found := found.push (r, q, #[tag])
    for (r, q, ws) in found do
      let note := if ms.isEmpty then m!"" else
        if ws.size == 2 then m!" (under either modality)" else m!" ({ws[0]!})"
      problems := problems.push m!"{r} still applies{note}, and gives{indentExpr q}"
    unless problems.isEmpty do
      throwError "#last_line: {c} does not end at a last line:{indentExpr B}\n\
        {MessageData.joinSep problems.toList "\n"}"

/-- `#chain φ`: the chain from `φ` to its last line, as one chain term to
paste; the scoped chains' (`Calculus/Core/ChainGen.lean`). -/
syntax "#chain " term : command

/-- `#chain_rest c`: what the chain `c` still lacks to a last line; the
scoped chains' (`Calculus/Core/ChainGen.lean`). -/
syntax "#chain_rest " ident : command

end Chain

namespace ProofTree
open Lean Elab Tactic Meta

/-- `sol_chain?` on `φ ~~> ψ` past the program: the rewrites from `φ` to `ψ`
(`Chain.generate`), written as one chain term (`Fml.Via.leads`), the goal
proved with it, and suggested.  On a chain of rewrites: prove it as
`sol_chain` does, suggest `sol_chain`, and print the lines that go on to a
last line if its last line is not one. -/

elab_rules : tactic
  | `(tactic| sol_chain?%$tk) => withMainContext do
    let g ← getMainGoal
    let ty ← instantiateMVars (← g.getType)
    if ty.isAppOfArity ``NFml.Via 3 then
      let some (C, _, B) ← Chain.chainEnds? ty | throwUnsupportedSyntax
      Chain.solveChain g
      replaceMainGoal []
      suggest tk #["sol_chain"]
      let gen ← Chain.generate C (← instantiateMVars B)
      unless gen.links.isEmpty do
        let lines ← Chain.viaLines C gen.splice.modality B gen.links
        let start := (← Chain.lineText C gen.splice.modality B).size
        logInfoAt tk (m!"the chain goes on to a last line; append to its statement:\n\
          {"\n".intercalate (lines.extract start lines.size |>.map ("    " ++ ·)).toList}" ++
          gen.stopNote)
      return
    unless ty.isAppOfArity ``NFml.Leads 3 do throwUnsupportedSyntax
    let #[C, φ, ψ] := ty.getAppArgs | throwUnsupportedSyntax
    let gen ← Chain.generate C φ (some (← instantiateMVars ψ))
    let last := gen.last φ
    unless ← isDefEq last ψ do
      throwError "sol_chain?: the chain from the line before ends at{indentExpr last}\nnot{indentExpr ψ}"
    let links := gen.links
    -- one link is its own relation (`SoundRel.leads`), more are a `Fml.Via`
    let lines ← if links.isEmpty then
        pure #["exact Solidity.NFml.Leads.self _"]
      else do
        let ls ← Chain.viaLines C gen.splice.modality φ links
        let head := if links.size == 1 then "exact Solidity.NFml.SoundRel.leads (show "
          else "exact Solidity.NFml.Via.leads (show "
        let body := #[head ++ ls[0]!] ++ (ls.extract 1 ls.size).map ("    " ++ ·)
        pure (body.modify (body.size - 1) (· ++ " by sol_chain)"))
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
  let ψ ← mkFreshExprMVar (mkApp (mkConst ``NFml) C)
  -- the candidates `stillApplies` chose among, so the replay meets the same
  -- instance: never a read of the state as the program found it
  let (rs, failed) ← rwCandidatesWith (fun t => !plainRead t) C A arrow
  let (r, q, pf) ← rwSelect C A ψ n.toString rs failed
  let q ← instantiateMVars q
  let h := pf.getD (someRefl C q)
  return (q, mkAppN (mkConst ``NFml.RwBy.sound) #[C, mkStrLit n.toString, r, A, q, h])

/-- The goal `φ ~~> ψ`, its contract and ends. -/
def leadsGoal (g : MVarId) : MetaM (Expr × Expr × Expr) := do
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOfArity ``NFml.Leads 3 do throwError "sol_rws: the goal is not `φ ~~> ψ`{indentExpr ty}"
  let #[C, φ, ψ] := ty.getAppArgs | unreachable!
  return (C, ← instantiateMVars φ, ← instantiateMVars ψ)

/-- Prove `φ ~~> ψ` by the rewrites `ns` in turn. -/
def proveRws (g : MVarId) (ns : Array Lean.Name) : TermElabM Unit := do
  let (C, φ, ψ) ← leadsGoal g
  let mut cur := φ
  let mut pf := mkApp2 (mkConst ``NFml.Leads.self) C φ
  for n in ns do
    let (q, h) ← rwStep C cur n
    pf := mkAppN (mkConst ``NFml.Leads.comp) #[C, φ, cur, q, pf, h]
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
