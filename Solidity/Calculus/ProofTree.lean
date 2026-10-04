import Solidity.Calculus.Sequents

/-!
# The proof tree, and the tactics that write a proof out: `sol_derive?`, `sol_chain?`

solkey shows a proof as KeY does, as a tree of sequents: every node a goal
with the rule applied to it, a branch per goal a rule leaves, and every leaf
closed or open (`ProofSession.tree()`, `keyext.solidity.core`).  Its web
prover hands the tree out as rows `[serial, parent, name, branchLabel,
state]` and a node as its sequent and rule (`WebProver`'s `tree` and `node`
requests).  This module builds that tree for a goal `Γ ⊢ φ` (`Proves`), by
running the strategy as a derivation, as `sol_derive` does: at every goal
the rule `Stmt.step` picks, applied by the `apply` a walk would write
(`apply unfold .localValueDeclInitDrop`, `apply split .requireSimple`, …),
and at every leaf `refine close ?_; sol_symex; sol_close`.  Nothing is
trusted: each node is an elaborated `apply`, and the kernel checks the
proof term the tree's tactics build.

* `ProofTree.build` grows the tree on a goal, `ProofTree.ofFormula` on `⊢ φ`;
  `Tree.rows` is solkey's `tree()`, `Tree.toJson` its web shape,
  `Tree.display` the linearized view of its GUI (a linear run of steps is
  one flat branch, a split opens a labelled sub-branch per goal).
* `sol_derive?` grows the tree on the main goal and suggests it as the walk
  it is, one `apply` per rule and a `case` per branch (`case thn`, `case els`,
  `case cov`): the precise proof `sol_derive` stands for.  A leaf the closer
  does not close is left as a goal, and `sorry` in the suggestion.
* `sol_chain?` proves a derivation `φ ~*> ψ` as `sol_chain` does and suggests
  it as a `calc`, every line written and every step named, `~[r]~>`.

The branch labels are the goals' case names (`thn`, `els`, `cov` of
`Proves.split`), where solkey prints the taclet's
(`"if se true"`): they are what the suggested walk names.  The commands that
print the tree (`#proof_tree`, `#proof_node`, `#proof_tree_json`) are in
`Tools/ProofTree.lean`.
-/

namespace Solidity

namespace ProofTree

open Lean Meta Elab Tactic

/-! ## The tree -/

/-- What was done at a node. -/
inductive Act where
  /-- A rule, by its name (the taclet's, or KeY's: `impRight`, `allRight`,
  `emptyModality`), and the tactics that applied it. -/
  | rule (name : Lean.Name) (tacs : Array (TSyntax `tactic))
  /-- A leaf the tactics closed. -/
  | closed (tacs : Array (TSyntax `tactic))
  /-- A leaf left open. -/
  | opened
  deriving Inhabited

/-- A node: its goal and the goal's statement (`Γ ⊢ φ`), the label of the
branch it starts (its case name, when its parent has more than one goal),
what was done to it, and the goals that left. -/
inductive Tree where
  | node (goal : MVarId) (sequent : Expr) (label : Option Lean.Name) (act : Act) (children : Array Tree)

instance : Inhabited Tree := ⟨.node ⟨.anonymous⟩ default none .opened #[]⟩

namespace Tree

def goal : Tree → MVarId | .node g .. => g
def sequent : Tree → Expr | .node _ e .. => e
def label : Tree → Option Lean.Name | .node _ _ l .. => l
def act : Tree → Act | .node _ _ _ a _ => a
def children : Tree → Array Tree | .node _ _ _ _ cs => cs

/-- The node's name, as solkey's `Node.name()`: the rule, or for a leaf
whether it is closed. -/
def name (t : Tree) : String :=
  match t.act with
  | .rule n _ => n.toString
  | .closed _ => "Closed goal"
  | .opened => "OPEN GOAL"

/-- solkey's state of a node: `inner`, `closed` or `open`. -/
def state (t : Tree) : String :=
  match t.act with
  | .rule .. => "inner"
  | .closed _ => "closed"
  | .opened => "open"

/-- The goals left open, leftmost first. -/
partial def openGoals (t : Tree) : Array MVarId :=
  match t.act with
  | .opened => #[t.goal]
  | _ => t.children.foldl (· ++ ·.openGoals) #[]

/-- The leaves: KeY's branches, one per goal the proof ends in. -/
partial def leaves (t : Tree) : Nat :=
  if t.children.isEmpty then 1 else t.children.foldl (· + ·.leaves) 0

/-- Whether every leaf is closed. -/
def closed (t : Tree) : Bool := t.openGoals.isEmpty

/-! ## solkey's rows -/

/-- A row of solkey's `ProofSession.tree()`: the node's serial number (in
depth-first order, as KeY numbers them), its parent's, its name, the label
of the branch it starts, and its state; with the node's goal. -/
structure Row where
  serial : Nat
  parent : Option Nat
  name : String
  branchLabel : Option String
  state : String
  node : Tree

partial def rowsAux (parent : Option Nat) (t : Tree) : StateM (Array Row) Unit := do
  let serial := (← get).size
  modify (·.push { serial, parent, name := t.name, branchLabel := t.label.map (·.toString),
                   state := t.state, node := t })
  for c in t.children do rowsAux (some serial) c

/-- The rows, in depth-first order: row `n` is the node of serial `n`. -/
def rows (t : Tree) : Array Row := (rowsAux none t |>.run #[]).2

/-- The goal of a node, printed as its sequent `dl{ Γ ⟹ φ }`. -/
def ppSequent (t : Tree) : MetaM Std.Format :=
  t.goal.withContext do Lean.Meta.ppExpr (← instantiateMVars t.sequent)

/-- The tree in the shape of solkey's web prover: `nodes`, one row
`[serial, parent, name, branchLabel, state]` each (`-1` for the root's
parent, `null` for no label); `sequents`, each node's goal by serial; and
the summary `closed`, `openGoalCount`, `stats`. -/
def toJson (t : Tree) : MetaM Json := do
  let rows := t.rows
  let nodes := rows.map fun r => Json.arr #[Lean.toJson r.serial,
    Lean.toJson (match r.parent with | some p => (p : Int) | none => -1),
    Lean.toJson r.name, match r.branchLabel with | some l => Lean.toJson l | none => Json.null,
    Lean.toJson r.state]
  let sequents ← rows.mapM fun r => return Lean.toJson (toString (← r.node.ppSequent))
  return Json.mkObj [
    ("nodes", Json.arr nodes),
    ("sequents", Json.arr sequents),
    ("closed", Lean.toJson t.closed),
    ("openGoalCount", Lean.toJson t.openGoals.size),
    ("stats", Json.mkObj [("nodes", Lean.toJson rows.size), ("branches", Lean.toJson t.leaves)])]

/-- The summary line: closed or not, open goals, nodes and branches. -/
def summary (t : Tree) : MessageData :=
  m!"{if t.closed then "closed" else "open"}: {t.openGoals.size} open goal(s), \
    {t.rows.size} node(s), {t.leaves} branch(es)"

/-- The tree as solkey's GUI shows it, linearized: a run of steps is one flat
list, `serial: name`; a node with several goals opens a sub-branch per goal,
headed by its label; an open leaf shows its sequent. -/
partial def displayAux (t : Tree) (ind : Nat) : StateT Nat MetaM (Array MessageData) := do
  let n ← get
  set (n + 1)
  let pad := "".pushn ' ' ind
  let head : MessageData := m!"{pad}{n}: {t.name}"
  let head ← match t.act with
    | .opened => do
      let s ← t.ppSequent
      pure (head ++ .nest (ind + 4) (m!"\n" ++ s))
    | _ => pure head
  let mut out := #[head]
  match t.children with
  | #[c] => out := out ++ (← displayAux c ind)
  | cs =>
    for h : i in [0:cs.size] do
      let c := cs[i]
      let l := (c.label.map (·.toString)).getD s!"#{i + 1}"
      out := out.push m!"{pad}  [{l}]"
      out := out ++ (← displayAux c (ind + 4))
  return out

/-- The tree, displayed, and its summary. -/
def display (t : Tree) : MetaM MessageData := do
  let (ls, _) ← (displayAux t 0).run 0
  return MessageData.joinSep (ls.toList ++ [t.summary]) "\n"

end Tree

/-! ## Growing the tree -/

/-- How the tree is grown: whether the leaves are closed
(`refine close ?_; sol_symex; sol_close`), and at most how many nodes. -/
structure Config where
  close : Bool := true
  maxNodes : Nat := 10000

/-- `.r`: a constructor named against the expected type, as a walk names a
taclet. -/
def dotIdent (n : Lean.Name) : Lean.Term :=
  ⟨mkNode ``Lean.Parser.Term.dotIdent #[mkAtom ".", mkIdent n]⟩

/-- The constant `n` as the scope spells it (`update` under `open Proves`). -/
def short (n : Lean.Name) : MetaM Ident := return mkIdent (← unresolveNameGlobal n)

/-- The constant `n` as `Proves.n` when the scope reads it so, as a walk's
`apply Proves.valid` is written; else as the scope spells it. -/
def qualified (n : Lean.Name) : MetaM Ident := do
  let q := Lean.Name.mkSimple n.getPrefix.getString! ++ Lean.Name.mkSimple n.getString!
  if (← resolveGlobalName q).any (·.1 == n) then return mkIdent q
  short n

/-- The `Proves` constructor of a premise (`Premise.update` …) for a rule
of solkey's (`lean` false) or one it lacks, and the lemma that takes either
(`Proves.updateRule` …). -/
def provesCtor (premise : Lean.Name) (lean : Bool) : Option (Lean.Name × Lean.Name) :=
  if premise == ``Premise.update then some (``Proves.update, ``Proves.updateRule)
  else if premise == ``Premise.unfold then
    some (if lean then ``Proves.unfoldLean else ``Proves.unfold, ``Proves.unfoldRule)
  else if premise == ``Premise.split then some (``Proves.split, ``Proves.splitRule)
  else if premise == ``Premise.done then
    some (if lean then ``Proves.doneLean else ``Proves.done, ``Proves.doneRule)
  else if premise == ``Premise.branches then some (``Proves.branches, ``Proves.branchesRule)
  else none

/-- The premise `Stmt.step` gives the statement `s` (index `k`, modality
`m`), by the head of its constructor: of the derivation's type, or else of
`(Stmt.step k m s).premise`. -/
def premiseOf (C k m s d : Expr) : MetaM (Option Lean.Name) := do
  let p ← try
      let ty ← whnf (← inferType d)
      whnf ty.appArg!
    catch _ => pure (mkConst Lean.Name.anonymous)
  if let some n := p.getAppFn.constName? then
    if n.getPrefix == ``Premise then return some n
  let p ← whnf (← mkAppM ``Step.premise #[mkAppN (mkConst ``Stmt.step) #[C, k, m, s]])
  return p.getAppFn.constName?

/-- One way to take the step at a goal: the rule's name, the tactics, and
whether the goal a `branches` rule leaves still has to be split. -/
structure Move where
  name : Lean.Name
  tacs : Array (TSyntax `tactic)
  branches : Bool := false

/-- The moves the strategy makes at the goal `Γ ⊢ φ`, the named one first
and `sol_derive`'s (`(Stmt.step _ _ _).rule`) as its fallback; none at a
goal with no rule, a leaf. -/
def movesAt (g : MVarId) : MetaM (Array Move) := g.withContext do
  let ty ← whnfR (← instantiateMVars (← g.getType))
  let_expr Proves C _ Γ φ0 := ty | return #[]
  let φ ← whnf φ0
  match_expr φ with
  | Fml.imp _ _ _ => return #[{ name := `impRight, tacs := #[← `(tactic| apply $(← short ``Proves.intro))] }]
  | Fml.all _ _ _ _ =>
    return #[{ name := `allRight, tacs := #[← `(tactic| apply $(← short ``Proves.allIntro))] }]
  | Fml.upd _ _ _ _ =>
    return #[{ name := `updIntro, tacs := #[← `(tactic| apply $(← short ``Proves.updIntro))] }]
  | Fml.modal _ m P _ =>
    let P ← whnf P
    if P.isAppOf ``List.nil then
      return #[{ name := `emptyModality, tacs := #[← `(tactic| apply $(← short ``Proves.empty))] }]
    let_expr List.cons _ s _ := P | return #[]
    let k := mkAppN (mkConst ``Hyp.fresh) #[C, Γ, φ0]
    let (d, c?) ← Chain.stepTaclet C k m s
    let some premise ← premiseOf C k m s d | return #[]
    let lean := match c? with | some c => (`Solidity.LeanTaclet).isPrefixOf c | none => false
    let some (ctor, generic) := provesCtor premise lean | return #[]
    let branches := premise == ``Premise.branches
    let st ← short ``Stmt.step
    let generic ← `(tactic| apply $(← short generic) ($st _ _ _).rule)
    let fallback : Move :=
      { name := (c?.map Chain.lastName).getD `taclet, branches := branches, tacs := #[generic] }
    let some c := c? | return #[fallback]
    let named ← `(tactic| apply $(← short ctor) $(dotIdent (Chain.lastName c)))
    return #[{ name := Chain.lastName c, branches := branches, tacs := #[named] }, fallback]
  | _ => return #[]

/-- Run `tacs` on the goal `g`, errors as errors; the goals left. -/
def runOn (g : MVarId) (tacs : Array (TSyntax `tactic)) : TacticM (List MVarId) := do
  setGoals [g]
  for t in tacs do Term.withoutErrToSorry (evalTactic t)
  getUnsolvedGoals

/-- The tactics a leaf is closed by, as a walk ends. -/
def closeTacs : MetaM (Array (TSyntax `tactic)) := do
  return #[← `(tactic| refine $(← short ``Proves.close) ?_), ← `(tactic| sol_symex),
    ← `(tactic| sol_close)]

/-- After `apply branches r`: the goal `∀ b ∈ bs, …` taken apart, as
`sol_derive` does, one goal per outcome. -/
def splitBranches (g : MVarId) : TacticM (Array (TSyntax `tactic) × List MVarId) := do
  let names := #[``List.forall_mem_cons, ``List.not_mem_nil, ``false_implies, ``implies_true,
    ``and_true, ``Fml.alls, ``codeBinders, ``Option.toList, ``List.map]
  let lemmas ← names.mapM fun n => do `(Lean.Parser.Tactic.simpLemma| $(← short n):ident)
  let simp ← `(tactic| simp only [$lemmas,*])
  let gs ← runOn g #[simp]
  let [g'] := gs | return (#[simp], gs)
  -- the outcomes are a right-nested conjunction
  let rec count (e : Expr) (fuel : Nat) : Nat :=
    match fuel, e.app2? ``And with
    | f + 1, some (_, b) => count b f + 1
    | _, _ => 1
  let n := count (← whnfR (← instantiateMVars (← g'.getType))) 64
  if n < 2 then return (#[simp], gs)
  let holes ← (List.range n).toArray.mapM fun _ => `(term| ?_)
  let refine ← `(tactic| refine ⟨$holes,*⟩)
  return (#[simp, refine], ← runOn g' #[refine])

/-- Grow the tree at the goal `g`, whose branch is labelled `label`. -/
partial def grow (cfg : Config) (fuel : IO.Ref Nat) (label : Option Lean.Name) (g : MVarId) :
    TacticM Tree := g.withContext do
  let n ← fuel.get
  if n == 0 then throwError "proof tree: more than {cfg.maxNodes} nodes"
  fuel.set (n - 1)
  let sequent ← instantiateMVars (← g.getType)
  for mv in ← movesAt g do
    -- only the move is tried: an error in the goals it leaves is the tree's
    let s ← saveState
    let applied ← try
        let gs ← runOn g mv.tacs
        if mv.branches then
          match gs with
          | [g'] => some <$> splitBranches g'
          | _ => pure (some (#[], gs))
        else pure (some (#[], gs))
      catch _ => s.restore; pure none
    let some (more, gs) := applied | continue
    -- a `branches` rule's outcomes are `refine`'s holes, with no names of their own
    let labels ← if gs.length < 2 || mv.branches then pure (gs.map fun _ => none) else
      gs.mapM fun c => do
        let t ← c.getTag
        pure (match t with | .str _ l => some (Lean.Name.mkSimple l) | _ => none)
    let mut cs := #[]
    for (c, l) in gs.zip labels do cs := cs.push (← grow cfg fuel l c)
    return .node g sequent label (.rule mv.name (mv.tacs ++ more)) cs
  -- a leaf
  if cfg.close then
    let s ← saveState
    try
      let tacs ← closeTacs
      if (← runOn g tacs).isEmpty then return .node g sequent label (.closed tacs) #[]
      s.restore
    catch _ => s.restore
  return .node g sequent label .opened #[]

/-- The tree of the goal `g`; the goals it leaves open are its open leaves. -/
def build (g : MVarId) (cfg : Config := {}) : TacticM Tree := do
  let fuel ← IO.mkRef cfg.maxNodes
  let t ← grow cfg fuel none g
  setGoals t.openGoals.toList
  return t

/-- The tree of `⊢ φ`, `φ : Fml C`, on a goal of its own. -/
def ofFormula (C φ : Expr) (cfg : Config := {}) : TermElabM Tree := do
  let ty := mkAppN (mkConst ``Proves) #[C, mkConst ``RuleSet.all,
    mkApp (mkConst ``List.nil [0]) (mkApp (mkConst ``Hyp) C), φ]
  let g ← mkFreshExprSyntheticOpaqueMVar ty
  let out ← IO.mkRef (default : Tree)
  discard <| Tactic.run g.mvarId! do out.set (← build g.mvarId! cfg)
  out.get

/-! ## The script -/

/-- A tactic's lines. -/
def tacLines (t : TSyntax `tactic) : MetaM (Array String) := do
  return ((toString (← PrettyPrinter.ppTactic t)).splitOn "\n").toArray

/-- The walk the tree is, its lines indented relative to the first: one
`apply` per rule, a `case` per goal of a node with several (a `·` where the
goals have no distinct names), and `sorry` for an open leaf. -/
partial def Tree.script (t : Tree) : MetaM (Array String) := do
  match t.act with
  | .opened => return #["sorry"]
  | .closed tacs => return (← tacs.mapM tacLines).flatten
  | .rule _ tacs =>
    let head := (← tacs.mapM tacLines).flatten
    match t.children with
    | #[c] => return head ++ (← c.script)
    | cs =>
      let labels := cs.filterMap (·.label)
      let named := labels.size == cs.size && labels.toList.eraseDups.length == cs.size
      let mut out := head
      for c in cs do
        let body ← c.script
        if named then
          out := out.push s!"case {(c.label.getD .anonymous)} =>"
          out := out ++ body.map ("  " ++ ·)
        else
          out := out ++ body.mapIdx fun i l => (if i == 0 then "· " else "  ") ++ l
      return out

/-- Offer `lines` in place of the syntax `tk`, every line after the first at
`tk`'s column. -/
def suggest (tk : Syntax) (lines : Array String) : MetaM Unit := do
  let fm ← getFileMap
  let col := match tk.getPos? with
    | some p => (fm.toPosition p).column
    | none => 0
  let pad := "".pushn ' ' col
  let text := "\n".intercalate (lines.toList.mapIdx fun i l => if i == 0 then l else pad ++ l)
  TryThis.addSuggestion tk { suggestion := .string text }

/-! ## The tactics -/

/-- `sol_derive?`: build the proof tree of the goal `Γ ⊢ φ` and suggest it as
the walk it is, one `apply` per rule, a `case` per branch, each leaf closed by
`refine close ?_; sol_symex; sol_close`.  A leaf that does not close is left
as a goal (`sorry` in the suggestion).  On `⊨ φ` the walk starts with
`apply Proves.valid`. -/
elab tk:"sol_derive?" : tactic => withMainContext do
  let g ← getMainGoal
  let rest := (← getUnsolvedGoals).erase g
  let (pre, g) ← if (← whnfR (← instantiateMVars (← g.getType))).isAppOf ``Valid then
      let valid ← `(tactic| apply $(← qualified ``Proves.valid))
      let [g'] ← runOn g #[valid] | throwError "sol_derive?: `apply Proves.valid` failed"
      pure (#[valid], g')
    else pure (#[], g)
  let t ← build g
  setGoals (t.openGoals.toList ++ rest)
  let head ← pre.mapM fun t => tacLines t
  suggest tk (head.flatten ++ (← t.script))

/-- `t`'s lines. -/
def termLines (t : Lean.Term) : MetaM (Array String) := do
  return ((toString (← PrettyPrinter.ppTerm t)).splitOn "\n").toArray

/-- The line `e : Fml C` as a calc line is written: `dl!{ φ }`, or at a
modality `dl![m]{ φ }` (`m` the line's modality variable, or `.box` for a
box's update with no modality under it) — the first of these that reads
back as `e`; Lean's own printing where the notation escapes. -/
def writeLine (C e : Expr) (m? : Option Expr) : TermElabM Lean.Term := do
  let φ ← ppFml e
  if isEscape φ then return ← escapeTerm e
  let φ ← withDecls e φ
  let mods : Array (Option Lean.Term) ← match m? with
    | some m => pure #[some ⟨mkIdent (← m.fvarId!.getUserName)⟩]
    | none => pure #[none, some (dotIdent `box), some (dotIdent `diamond)]
  let cands : Array Lean.Term ← mods.mapM fun
    | none => `(dl!{ $φ:dl_fml })
    | some m => `(dl![$m]{ $φ:dl_fml })
  for t in cands do
    let ok ← withoutModifyingState do
      try
        let e' ← Term.withoutErrToSorry do
          let e' ← Term.elabTermEnsuringType t (mkApp (mkConst ``Fml) C)
          Term.synthesizeSyntheticMVarsNoPostponing
          instantiateMVars e'
        pure (!e'.hasExprMVar && (← isDefEq e' e))
      catch _ => pure false
    if ok then return t
  return cands[0]!

/-- The `calc` that proves `φ ~*> ψ` a line at a time, every step named,
when the goal is one and has two steps or more. -/
def chainCalc (ty : Expr) : TermElabM (Option (Array String)) := do
  let ty ← instantiateMVars ty
  unless ty.isAppOfArity ``Fml.Steps 3 do return none
  let #[C, φ, ψ] := ty.getAppArgs | return none
  let run ← Chain.runChain C φ
  let ls := run.lines.map (·.fml)
  let some i ← Chain.findLine φ ψ ls | return none
  if i < 2 then return none
  let m? := run.splice.modality
  let closed := run.splice.fmls.isEmpty && m?.isNone
  let pf := if closed then "rfl" else "by sol_chain"
  let first ← termLines (← writeLine C φ m?)
  let mut out := #["exact calc " ++ first[0]!] ++ (first.extract 1 first.size).map ("    " ++ ·)
  let mut prev := φ
  for l in ls.take i do
    let arrow ← try
        match ← Chain.ruleOfLine prev with
        | some (_, n) => pure (if n == `taclet then "~>" else s!"~[{n}]~>")
        | none => pure "~>"
      catch _ => pure "~>"
    let line ← termLines (← writeLine C l m?)
    let line := line.modify (line.size - 1) (· ++ s!" := {pf}")
    out := out.push s!"  _ {arrow} {line[0]!}"
    out := out ++ (line.extract 1 line.size).map ("      " ++ ·)
    prev := l
  return some out

/-- `sol_chain?`: prove `φ ~> ψ`, `φ ~[r]~> ψ`, `φ ~*> ψ` or a chain as
`sol_chain` does; on `φ ~*> ψ`, suggest the `calc` it stands for, every line
written and every step named. -/
elab tk:"sol_chain?" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← g.getType
  Chain.solveChain g
  replaceMainGoal []
  if let some lines ← chainCalc ty then suggest tk lines

end ProofTree

end Solidity
