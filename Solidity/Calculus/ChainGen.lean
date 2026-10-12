import Solidity.Calculus.Chains
import Solidity.Calculus.RewriteChainGen

/-!
# Writing a scoped chain out: `#chain` and `#chain_rest`

The chain generator for a chain whose first line is a
scoped formula (`cdl![m]{ … }`): the strategy's steps, grouped as the worked chains
print them (`groupSteps`), each named by the rule `Stmt.step` fires
(`labelOfFocus?`); past the program, the rewrites of the scoped line to a
last line (`pastSearch`: depth first, the merge first, the rest in `~=>`'s
order, each at the first place it applies, the smallest last line).  The
commands are `Calculus/RewriteChainGen.lean`'s, read here when their formula
(or chain) is scoped.

Each line is written as the text that reads back as it: `cdl![m]{ … }` over
a modality variable, otherwise the first of `cdl!{ … }`, `cdl![.box]{ … }`,
`cdl![.diamond]{ … }` whose reading is the line's (`matchWritten` for a
scoped line, the line itself for one past the program).  A generated chain is
one declaration: a scoped chain is not cut into segments.
-/

namespace Solidity.Chain

open Lean Elab Term Meta

/-! ## Past the program: the scoped rewrites -/

/-- A rewrite of a line past the program: its name, the line it leaves,
that line's erasures, and the rewrite (`FmlRw`). -/
structure PastStep where
  name : String
  fml : Expr
  erased : Array Expr
  rw : Expr

/-- The rewrite `a` named `n` on the line `L` past the program, at the
first place it applies (`scopedRwCands`), a read of the state as the program
found it left as it is (`plainReadAny`). -/
def pastStepOf? (L : Expr) (n : String) (a : NFml.Chain.RwArrow) : TermElabM (Option PastStep) := do
  let run ← runChain L
  let st ← saveState
  try
    let (_, cands, _) ← scopedRwCands L a run.erased[0]! (past := true) (keep := (!plainReadAny ·))
    -- a rewrite that leaves a line printed alike (a hidden binder absorbed) is no step
    return (cands.find? (·.erased != run.erased)).map fun c =>
      { name := n, fml := c.fml, erased := c.erased, rw := c.rw }
  catch _ =>
    st.restore
    return none

/-- The rewrites a chain takes past the program on the line `L`
(`NFml.Chain.chainRewrite`; with `every`, `simplifyUpdate` too), each at the
first place it applies, in the generator's order: the merge first, then
`~=>`'s. -/
def pastSteps (L : Expr) (every : Bool := false) : TermElabM (Array PastStep) := do
  let arrows := (← NFml.Chain.rwAnyArrows).toArray.filter fun (n, _) =>
    every || NFml.Chain.chainRewrite n
  let run ← runChain L
  let st ← saveState
  -- every arrow's rewrites computed at once (`scopedRwCandsMany`)
  let rs ← try
      pure (← scopedRwCandsMany L (arrows.map (·.2)) run.erased[0]! (past := true)
        (keep := (!plainReadAny ·))).2
    catch _ => st.restore; pure #[]
  let mut out := #[]
  for ((n, _), (cands, _)) in arrows.zip rs do
    -- a rewrite that leaves a line printed alike (a hidden binder absorbed) is no step
    if let some c := cands.find? (·.erased != run.erased) then
      out := out.push { name := n, fml := c.fml, erased := c.erased, rw := c.rw }
  return out.filter (·.name == "sequentialToParallel") ++ out.filter (·.name != "sequentialToParallel")

/-- What the search past the program keeps: the lines tried, the smallest
last line found and the path to it, the path to the goal once found, and a
search step that failed. -/
structure PastSearch where
  nodes : Nat := 0
  seen : Std.HashSet Expr := {}
  best : Option (Nat × Array PastStep) := none
  found : Option (Array PastStep) := none
  failed : Option MessageData := none

/-- Depth first from `L` (`NFml.Chain.searchFrom` on the scoped line): a
line no rewrite applies to is a last line, and the smallest wins; with a
goal, the first path to it ends the search.  Each line has its own
heartbeats, and one whose search fails is a leaf. -/
partial def pastSearchFrom (goal? : Option (Expr → TermElabM Bool)) (path : Array PastStep)
    (L : Expr) : StateRefT PastSearch TermElabM Unit := do
  let s ← get
  if s.found.isSome || s.nodes ≥ NFml.Chain.genNodes || s.seen.contains L then return
  set { s with nodes := s.nodes + 1, seen := s.seen.insert L }
  if let some g := goal? then
    if ← g L then
      modify fun s => { s with found := some path }
      return
  let r : Except Exception (Array PastStep) ←
    tryCatchRuntimeEx (.ok <$> withCurrHeartbeats (pastSteps L goal?.isSome)) fun e => pure (.error e)
  match r with
  | .error e => modify fun s => { s with failed := s.failed <|> some e.toMessageData }
  | .ok steps =>
    if steps.isEmpty then
      let n := NFml.Chain.lineSize L
      modify fun s => match s.best with
        | some (b, _) => if n < b then { s with best := some (n, path) } else s
        | none => { s with best := some (n, path) }
    else
      for st in steps do
        pastSearchFrom goal? (path.push st) st.fml

/-- The rewrites from `L` to a last line (`goal? = none`) or to a line the
goal accepts, and a note when the search did not finish. -/
def pastSearch (L : Expr) (goal? : Option (Expr → TermElabM Bool) := none) :
    TermElabM (Option (Array PastStep) × Option MessageData) := do
  let ((), s) ← (pastSearchFrom goal? #[] L).run {}
  let note := if s.nodes ≥ NFml.Chain.genNodes then
      some m!"the search stopped after {NFml.Chain.genNodes} lines; this is the best it found"
    else s.failed.map fun m => m!"a step of the search failed: {m}"
  match goal? with
  | some _ => return (s.found, note)
  | none => return (s.best.map (·.2), note)

/-- A line's key past the program: its erasure, its parameters free. -/
def pastKey (B : Expr) : MetaM Expr := do
  let (C, Γ) ← lineType B
  return mkApp2 (mkConst ``Solidity.NFml.dropAlls) C
    (mkAppN (mkConst ``Fml.erase) #[C, Γ, mkApp (mkConst ``List.nil [0]) (mkConst ``Solidity.Var), B])

/-- Whether the line `B` is the one the line written names, read as its
erasure `L` (`Fml.LeadsK`). -/
def namesLine (L B : Expr) : MetaM Bool := do
  kernelDefEq (← pastKey B) L

/-- The derivation's last line from `A` (`A` itself where no step applies). -/
def lastLineOf (A : Expr) : TermElabM Expr := do
  return ((← runChain A).lines.getLast?.map (·.fml)).getD A

/-- The scoped last line of a chain's statement: past the program
(`Fml.LeadsK`), the scoped line whose erasure is the one written, found again by the search
from the derivation's last line. -/
def scopedEnd? (ty : Expr) : TermElabM (Option Expr) := do
  let ty ← instantiateMVars ty
  if ty.isAppOfArity ``Fml.LeadsK 3 then
    let A ← instantiateMVars (ty.getArg! 1)
    let L ← instantiateMVars (ty.getArg! 2)
    let Z ← lastLineOf A
    let (path, _) ← pastSearch Z (some fun B => namesLine L B)
    return path.map fun p => (p.back?.map (·.fml)).getD Z
  match ty.getAppFnArgs with
  | (``Fml.OneStep, #[_, _, _, B]) | (``Fml.Steps, #[_, _, _, B])
  | (``Fml.StepBy, #[_, _, _, _, B]) | (``Fml.Leads, #[_, _, _, B]) => return some B
  | (``Fml.Via, #[_, _, A, ws]) =>
    let some ws ← Solidity.listElems? ws | return none
    let some w := ws.back? | return some A
    let w ← whnfR w
    unless w.isAppOfArity ``Prod.mk 4 do return none
    return some (w.getArg! 3)
  | _ => return none

/-- `L ~~> B` by the rewrite of the step `st` (`FmlRw.sound`), the kernel's. -/
def PastStep.leads (L : Expr) (st : PastStep) : TermElabM Expr := do
  let (C, Γ) ← lineType L
  let sp ← collectPosts L {}
  let m? ← modalityOf? (punch C sp L)
  let lhs := mkAppN (mkConst ``FmlRw.apply) #[C, st.rw, Γ, L]
  let rhs := mkApp2 (mkConst ``Option.some [0]) (mkApp2 (mkConst ``Fml) C Γ) st.fml
  let h ← kernelReflOrCases m? lhs rhs
  mkExpectedTypeHint (mkAppN (mkConst ``FmlRw.sound) #[C, st.rw, Γ, L, st.fml, h])
    (mkApp4 (mkConst ``Fml.Leads) C Γ L st.fml)

/-- A generated chain: the strategy's lines with the rule that reached each
(and each line's erasures), the rewrites after with theirs, and why it
stopped early, if it did. -/
structure Gen where
  splice : Splice
  /-- The erasures of the first line. -/
  erased : Array Expr
  steps : Array (String × Expr × Array Expr)
  /-- Rewrites of a line while its program is open, after `steps`
  (`openRwPath`), each with its line's erasures. -/
  openRws : Array (String × Expr × Array Expr) := #[]
  /-- Rewrites past the program, each with its line's erasures. -/
  rewrites : Array (String × Expr × Array Expr)
  stop : Option MessageData

/-- Run the strategy from the scoped line `φ`, then the rewrites of its last
line to a last line (`pastSearch`). -/
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
  let Z := (steps.back?.map (·.2.1)).getD φ
  let (rws, stop) ← pastSearch Z
  return { splice := run.splice, erased := run.erased, steps, stop,
           rewrites := (rws.getD #[]).map fun st => (st.name, st.fml, st.erased) }

/-- The links of a generated chain: the strategy's steps grouped
(`groupSteps`), then one `~[r]~>` per rewrite; each with its line. -/
def Gen.links (g : Gen) : Array (String × Expr) :=
  NFml.Chain.groupSteps (g.steps.map fun (n, l, _) => (n, l)) ++
    g.openRws.map (fun (n, l, _) => (s!"~[{n}]~>", l)) ++
    g.rewrites.map fun (n, l, _) => (s!"~[{n}]~>", l)

/-- The erasures of a line of a generated chain. -/
def Gen.erasedOf (g : Gen) (l : Expr) : Array Expr :=
  ((g.steps.find? (·.2.1 == l)).map (·.2.2) <|> (g.openRws.find? (·.2.1 == l)).map (·.2.2) <|>
    (g.rewrites.find? (·.2.1 == l)).map (·.2.2)).getD #[]

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
def lineText (sp : Splice) (C e : Expr) (erased : Array Expr) : TermElabM (Array String) := do
  let t ← ppCoreLine e
  let some φ := dlFmlOf? t | return ← Solidity.ProofTree.termLines t
  let cands ← wrappers sp.modality φ
  let mut pick := cands[0]!
  for c in cands do
    let ok ← withoutModifyingState do
      try matchWritten sp C (Written.of c) e erased
      catch _ => pure false
    if ok then
      pick := c
      break
  Solidity.ProofTree.termLines pick

/-- The declaration stating a generated chain from `φ`. -/
def Gen.decl (g : Gen) (φ : Expr) (name : String := "chain") : TermElabM (Array String) := do
  let (C, _) ← lineType φ
  let ind (ls : Array String) : Array String := ls.map ("    " ++ ·)
  let mut out := ind (← lineText g.splice C φ g.erased)
  for (arrow, l) in g.links do
    let line ← lineText g.splice C l (g.erasedOf l)
    out := out ++ ind (#[s!"{arrow} {line[0]!}"] ++ (line.extract 1 line.size).map ("  " ++ ·))
  let kw := if g.links.size == 1 && (g.links[0]!.1 == "~*>") then "def" else "theorem"
  return #[s!"{kw} {name} :"] ++ out.modify (out.size - 1) (· ++ " := by") |>.push "  sol_chain"

/-- The rows of a `FreshNames` table for the fresh variables of the lines. -/
def Gen.tableRows (g : Gen) (φ : Expr) : Array String := Id.run do
  let mut seen : Array String := #[]
  for e in #[φ] ++ g.steps.map (·.2.1) ++ g.rewrites.map (·.2.1) do
    for s in NFml.Chain.freshSpellings e do
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
    if ← todaysNotation t then notScopedNotation "#chain"
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
and whether it is scoped (`false`: past the program, the line written read
as its erasure, `Fml.LeadsK`). -/
def chainEnd? (ty : Expr) : MetaM (Option (Expr × Bool)) := do
  let ty ← instantiateMVars ty
  let lastOf (ws : Expr) (dflt : Expr) : MetaM (Option Expr) := do
    let some ws ← Solidity.listElems? ws | return none
    let some w := ws.back? | return some dflt
    let w ← whnfR w
    unless w.isAppOfArity ``Prod.mk 4 do return none
    return some (w.getArg! 3)
  match ty.getAppFnArgs with
  | (``Fml.OneStep, #[_, _, _, B]) | (``Fml.Steps, #[_, _, _, B])
  | (``Fml.StepBy, #[_, _, _, _, B]) | (``Fml.Leads, #[_, _, _, B]) => return some (B, true)
  | (``Fml.LeadsK, #[_, _, L]) => return some (L, false)
  | (``Fml.Via, #[_, _, A, ws]) => return (← lastOf ws A).map (·, true)
  | _ => return none

/-- `#chain_rest c` for a scoped chain: the links still to append, from the
last line of its statement to a last line. -/
elab_rules : command
  | `(command| #chain_rest $c:ident) => Command.runTermElabM fun _ => do
    let n ← realizeGlobalConstNoOverloadWithInfo c
    let info ← getConstInfo n
    forallTelescope info.type fun _ ty => do
      let some B ← scopedEnd? ty | throwUnsupportedSyntax
      let B ← instantiateMVars B
      let g ← generate B
      let (links, sp, C, stop) := (g.links, g.splice, (← lineType B).1, g.stop)
      if links.isEmpty then
        logInfo m!"{c} ends at a last line"
        return
      let mut out : Array String := #[]
      for (arrow, l) in links do
        let line ← lineText sp C l (← runChain l).erased
        out := out ++ #[s!"    {arrow} {line[0]!}"] ++ (line.extract 1 line.size).map ("      " ++ ·)
      let note := match stop with
        | some m => m!"\n\nthe chain stops early: {m}"
        | none => m!""
      logInfo (m!"lines to append to the statement of {c}:\n{"\n".intercalate out.toList}" ++ note)

/-! ## `sol_chain`, `sol_chain?` and `sol_rws` on `~~>`

A goal `A ~~> B` on scoped lines (`Fml.Leads`) is the derivation from `A`
to `B`, which `sol_chain` proves.  Past the program (`Fml.LeadsK A B`) it
is the derivation to its last line `Z`, then rewrites of the scoped line to
the line `B` names: the file names them (`sol_rws [..]`), and only the `?`
twins search for them (`pastSearch`), so a re-check does not search;
`sol_chain` refuses such a goal and points to them. -/

/-- The merges, one per name, from `A` to `B`: the first sequence of merge
candidates that ends at `B`, as `A ~~> B`. -/
partial def mergePath (A B : Expr) : Nat → MetaM (Option Expr)
  | 0 => do
    if A == B then return some (← mkAppM ``Fml.Leads.self #[A]) else return none
  | n + 1 => do
    let (sp, cands) ← mergeCands A
    for c in cands do
      if let some rest ← mergePath c.fml B n then
        let (C, Γ) ← lineType A
        let lhs := mkAppN (mkConst ``Fml.mergeRun) #[C, Γ, toExpr c.k, toExpr c.n, A]
        let rhs := mkApp2 (mkConst ``Option.some [0]) (mkApp2 (mkConst ``Fml) C Γ) c.fml
        let h ← kernelReflOrCases sp.modality lhs rhs
        let lk ← mkAppM ``Fml.mergeRun_leads #[toExpr c.k, toExpr c.n, A, h]
        return some (← mkAppM ``Fml.Leads.comp #[lk, rest])
    return none

/-- The rewrites while the program is open (`openRwPath`) from a line of
the derivation of `A` (`A` itself first) to `B`: how many of its steps come
before them, and the rewrites.  `B` with no program is not looked for: a
rewrite while the program is open keeps it. -/
def openRwFrom (A B : Expr) : TermElabM (Option (Nat × List OpenStep) × Option MessageData) := do
  unless (B.find? (·.isAppOf ``Fml.modal)).isSome do return (none, none)
  let run ← runChain A
  let mut note := none
  for i in [0:run.lines.length + 1] do
    let L := if i == 0 then A else ((run.lines[i - 1]?).map (·.fml)).getD A
    if !(← runChain L).isOpen then continue
    let (path?, n) ← openRwPath L (fun B' _ _ => pure (B' == B))
    note := note <|> n
    if let some path := path? then return (some (i, path), none)
  return (none, note)

/-- The derivation from `A` to `B`, as `A ~~> B`: the strategy's steps, then a
merge of the line's update spine (`Fml.MergeBy`) if `B` is one, else
rewrites while the program is open (`openRwFrom`). -/
partial def leadsSteps (A B : Expr) : TermElabM Expr := do
  let run ← runChain A
  match (if A == B then some 0 else (run.lines.findIdx? (·.fml == B)).map (· + 1)) with
  | some i => mkAppM ``Fml.Steps.sound #[← stepsProof run.splice A (run.lines.take i)]
  | none =>
    for i in [0:run.lines.length + 1] do
      let L := if i == 0 then A else ((run.lines[i - 1]?).map (·.fml)).getD A
      if let some h ← mergePath L B 1 then
        let st ← mkAppM ``Fml.Steps.sound #[← stepsProof run.splice A (run.lines.take i)]
        return ← mkAppM ``Fml.Leads.comp #[st, h]
    let (found, note) ← openRwFrom A B
    if let some (i, path) := found then
      let L := if i == 0 then A else ((run.lines[i - 1]?).map (·.fml)).getD A
      let st ← mkAppM ``Fml.Steps.sound #[← stepsProof run.splice A (run.lines.take i)]
      return ← mkAppM ``Fml.Leads.comp #[st, ← OpenStep.leads L path]
    throwError "sol_chain: the derivation of{← indentLine A}\ndoes not reach{← indentLine B}\
      {(note.map (m!"\n(" ++ · ++ m!")")).getD m!""}"


/-- `A ~~> B` past the program (`Fml.LeadsK`, `B` the line written read as
its erasure): the derivation to its last line, then the rewrites `ns` of
the scoped line in turn, each at the first place it applies, to the line
`B` names. -/
def pastLeads (A B : Expr) (ns : Array Lean.Name) : TermElabM Expr := do
  let Z ← lastLineOf A
  let mut pf ← leadsSteps A Z
  let mut cur := Z
  for n in ns do
    let some a ← NFml.Chain.rwArrow? (mkIdent n) | throwError "sol_rws: {n} is no rewrite"
    let some st ← pastStepOf? cur n.toString a
      | throwError "sol_rws: {n} does not apply to{← indentLine cur}"
    pf ← mkAppM ``Fml.Leads.comp #[pf, ← st.leads cur]
    cur := st.fml
  unless ← namesLine B cur do
    throwError "sol_rws: the rewrites give{← indentLine cur}\nnot{indentExpr B}"
  let he ← mkExpectedTypeHint (← mkEqRefl B) (← mkEq (← pastKey cur) B)
  mkAppM ``Fml.Leads.leadsK #[pf, he]

/-- Prove a goal `A ~~> B`: scoped, by the derivation; past the program, by
the derivation and then the rewrites `ns`. -/
def solveLeads (g : MVarId) (ns : Array Lean.Name) : TermElabM Unit := do
  let ty ← instantiateMVars (← g.getType)
  match_expr ty with
  | Fml.Leads _ _ A B => g.assign (← leadsSteps A B)
  | Fml.LeadsK _ A B => g.assign (← pastLeads (← instantiateMVars A) (← instantiateMVars B) ns)
  | _ => throwError "not a `~~>` goal"

elab_rules : tactic
  | `(tactic| sol_chain) => Tactic.withMainContext do
    let g ← Tactic.getMainGoal
    let ty ← instantiateMVars (← g.getType)
    unless ty.isAppOf ``Fml.Leads || ty.isAppOf ``Fml.LeadsK do throwUnsupportedSyntax
    if ty.isAppOf ``Fml.LeadsK then
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
  let mut out := ← lineText g.splice C φ g.erased
  for (arrow, l) in g.links do
    let line ← lineText g.splice C l (g.erasedOf l)
    out := out ++ #[s!"{arrow} {line[0]!}"] ++ (line.extract 1 line.size).map ("  " ++ ·)
  return out

/-- `sol_chain?` on a scoped chain: proved as `sol_chain` proves it,
`sol_chain` suggested, and the lines that go on to a last line printed if it
does not end at one.  On `A ~~> B`: the chain from `A` to `B` (past the
program to the line `B` names, by the rewrites the search finds), written
out as one term. -/
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
          let start := (← lineText gen.splice (← lineType B).1 B gen.erased).size
          logInfoAt tk (m!"the chain goes on to a last line; append to its statement:\n\
            {"\n".intercalate (lines.extract start lines.size |>.map ("    " ++ ·)).toList}" ++
            gen.stopNote)
      return
    unless ty.isAppOf ``Fml.Leads || ty.isAppOf ``Fml.LeadsK do throwUnsupportedSyntax
    let A := if ty.isAppOf ``Fml.Leads then ty.getArg! 2 else ty.getArg! 1
    let A ← instantiateMVars A
    let gen ← generate A
    let gen ← match_expr ty with
      | Fml.Leads _ _ _ B =>
        let B ← instantiateMVars B
        if let some i := if A == B then some 0 else
            (gen.steps.findIdx? (·.2.1 == B)).map (· + 1) then
          pure { gen with steps := gen.steps.extract 0 i, rewrites := #[], stop := none }
        else
          -- rewrites while the program is open, written out as links
          let (found, note) ← openRwFrom A B
          let some (i, path) := found
            | throwError "sol_chain?: the derivation of{← indentLine A}\ndoes not reach\
                {← indentLine B}{(note.map (m!"\n(" ++ · ++ m!")")).getD m!""}"
          let openRws := path.toArray.map fun st => (st.name.toString, st.fml, st.erased)
          pure { gen with steps := gen.steps.extract 0 i, rewrites := #[], stop := none, openRws }
      | Fml.LeadsK _ _ B =>
        let B ← instantiateMVars B
        let Z ← lastLineOf A
        let (path, note) ← pastSearch Z (some fun L => namesLine B L)
        let some path := path
          | throwError "sol_chain?: no run of rewrites from{← indentLine Z}\nreaches{← indentLine B}\
              {(note.map (m!"\n" ++ ·)).getD m!""}"
        pure { gen with rewrites := path.map (fun st => (st.name, st.fml, st.erased)), stop := none }
      | _ => throwUnsupportedSyntax
    let links := gen.links
    let lines ← if links.isEmpty then
        pure #["exact Solidity.Fml.Leads.self _"]
      else do
        let ls ← chainText gen A
        -- one link is its own relation (`SoundRel.leads`), more are a `Fml.Via`
        let past := ty.isAppOf ``Fml.LeadsK
        let (head, tail) := if past && links.size == 1 then
            ("exact Solidity.Fml.Leads.leadsK (Solidity.Fml.SoundRel.leads (show ", " by sol_chain))")
          else if past then ("exact Solidity.Fml.Via.leadsK (show ", " by sol_chain)")
          else if links.size == 1 then ("exact Solidity.Fml.SoundRel.leads (show ", " by sol_chain)")
          else ("exact Solidity.Fml.Via.leads (show ", " by sol_chain)")
        let body := #[head ++ ls[0]!] ++ (ls.extract 1 ls.size).map ("    " ++ ·)
        pure (body.modify (body.size - 1) (· ++ tail))
    let text := "\n".intercalate lines.toList
    let stx ← match Parser.runParserCategory (← getEnv) `tactic text with
      | .ok s => pure s
      | .error e => throwError "sol_chain?: the written chain does not parse: {e}\n{text}"
    Tactic.evalTactic stx
    Solidity.ProofTree.suggest tk lines

/-! `sol_rws [r₁, …, rₙ]` on `A ~~> B`: while the program is open, each
`sequentialToParallel` merges the line's update spine (`Fml.MergeBy`, the
merge that leads on to `B`); past the program, the derivation to its last
line, then the rewrites of the scoped line (`pastLeads`). -/

/-- Prove `A ~~> B` by the rewrites `ns`. -/
def proveCoreRws (g : MVarId) (ns : Array Lean.Name) : TermElabM Unit := do
  let ty ← instantiateMVars (← g.getType)
  match_expr ty with
  | Fml.Leads _ _ A B =>
    unless ns.all (· == `sequentialToParallel) do
      throwError "sol_rws: while the program is open only `sequentialToParallel` rewrites a scoped line"
    let some h ← mergePath (← instantiateMVars A) (← instantiateMVars B) ns.size
      | throwError "sol_rws: {ns.size} merges of{← indentLine A}\ndo not give{← indentLine B}"
    g.assign h
  | Fml.LeadsK _ _ _ => solveLeads g ns
  | _ => throwUnsupportedSyntax

elab_rules : tactic
  | `(tactic| sol_rws [$ns,*]) => Tactic.withMainContext do
    let g ← Tactic.getMainGoal
    let ty ← instantiateMVars (← g.getType)
    unless ty.isAppOf ``Fml.Leads || ty.isAppOf ``Fml.LeadsK do throwUnsupportedSyntax
    proveCoreRws g (ns.getElems.map (·.getId))
    Tactic.replaceMainGoal []
  | `(tactic| sol_rws?%$tk) => Tactic.withMainContext do
    let g ← Tactic.getMainGoal
    let ty ← instantiateMVars (← g.getType)
    let ns ← match_expr ty with
      | Fml.Leads _ _ A B =>
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
      | Fml.LeadsK _ A B =>
        let B ← instantiateMVars B
        let Z ← lastLineOf (← instantiateMVars A)
        let (path, note) ← pastSearch Z (some fun L => namesLine B L)
        let some path := path
          | throwError "sol_rws?: no run of rewrites from{← indentLine Z}\nreaches{← indentLine B}\
              {(note.map (m!"\n" ++ ·)).getD m!""}"
        pure (path.map (Lean.Name.mkSimple ·.name))
      | _ => throwUnsupportedSyntax
    proveCoreRws g ns
    Tactic.replaceMainGoal []
    let ids := ns.map (mkIdent ·)
    Lean.Meta.Tactic.TryThis.addSuggestion tk (← `(tactic| sol_rws [$ids,*]))

end Solidity.Chain
