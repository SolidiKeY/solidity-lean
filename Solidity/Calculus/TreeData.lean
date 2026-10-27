import Solidity.Calculus.RuleKit

/-!
# The proof tree as data, and the script it writes

solkey's proof tree (`ProofSession.tree()`), as `Calculus/ProofTree.lean`
grows it on today's goal and `Calculus/ProofTree.lean` on a scoped one:
a node's goal, sequent, branch label and what was done to it (`Tree`), solkey's rows and branch labels (`Tree.rows`, `Tree.branchLabel`),
the web prover's shape (`Tree.toJson`), the GUI's view (`Tree.display`), and
the walk a tree writes (`Tree.script`, `suggest`), with the helpers a
tactic writing a proof out uses (`runOn`, `short`, `qualified`,
`tacLines`, `termLines`).  Moved out of `ProofTree.lean`
(`docs/intrinsic.md`, W4 item 11), which keeps today's growing and tactics.
-/

namespace Solidity

namespace Chain

/-- The last component of a constructor's name, as `~[r]~>` shows it. -/
def lastName : Lean.Name → Lean.Name
  | .str _ s => .mkSimple s
  | n => n

end Chain

namespace ProofTree

open Lean Meta Elab Tactic

/-! ## The tree -/

/-- The goal, sequent and incoming branch label shared by every node. -/
structure NodeInfo where
  goal : MVarId
  sequent : Expr
  label : Option Lean.Name

/-- Open and solved leaves have no children by construction. Only a rule
node carries the subgoals produced by its tactics. -/
inductive Tree where
  | opened (info : NodeInfo)
  | solved (info : NodeInfo) (tacs : Array (TSyntax `tactic))
  | rule (info : NodeInfo) (name : Lean.Name) (tacs : Array (TSyntax `tactic))
      (se : Option String) (children : Array Tree)

instance : Inhabited Tree := ⟨.opened ⟨⟨.anonymous⟩, default, none⟩⟩

namespace Tree

def info : Tree → NodeInfo
  | .opened i | .solved i _ | .rule i .. => i

def goal (t : Tree) : MVarId := t.info.goal
def sequent (t : Tree) : Expr := t.info.sequent
def label (t : Tree) : Option Lean.Name := t.info.label

def children : Tree → Array Tree
  | .rule _ _ _ _ cs => cs
  | .opened _ | .solved .. => #[]

/-- The node's name, as solkey's `Node.name()`: the rule, or for a leaf
whether it is closed. -/
def name (t : Tree) : String :=
  match t with
  | .rule _ n _ _ _ => n.toString
  | .solved .. => "Closed goal"
  | .opened _ => "OPEN GOAL"

/-- solkey's state of a node: `inner`, `closed` or `open`. -/
def state (t : Tree) : String :=
  match t with
  | .rule .. => "inner"
  | .solved .. => "closed"
  | .opened _ => "open"

/-- The goals left open, leftmost first. -/
partial def openGoals (t : Tree) : Array MVarId :=
  match t with
  | .opened info => #[info.goal]
  | .solved .. => #[]
  | .rule _ _ _ _ cs => cs.foldl (· ++ ·.openGoals) #[]

/-- The leaves: KeY's branches, one per goal the proof ends in. -/
partial def leaves (t : Tree) : Nat :=
  if t.children.isEmpty then 1 else t.children.foldl (· + ·.leaves) 0

/-- Whether every leaf is closed. -/
def closed (t : Tree) : Bool := t.openGoals.isEmpty

/-! ## solkey's rows -/

/-- solkey's labels of a taclet's goals, in order (`Taclet.branchLabels`, as
the rules write them): `thn` and `els` of a split or a check, the outcomes of
`branches`. -/
def branchLabels : List (String × List String) := Taclet.branchLabels

/-- What `se` was at the node: its rule's instantiation. -/
def se? (t : Tree) : Option String :=
  match t with
  | .rule _ _ _ se _ => se
  | _ => none

/-- A label as KeY displays it (`NodeInfo.setBranchLabel`): the schema
variable `s#se` replaced by what it stands for at the node (KeY's own regex
leaves the `s` in place, `docs/solkey-feedback.md`). -/
def instLabel (l : String) (se : Option String) : String :=
  match se with
  | some v => l.replace "s#se" v
  | none => l.replace "s#se" "se"

/-- The label of `c`, the goal `i` of the node `p`: solkey's, chosen by its
case name (`thn`, `els`) or, for an outcome with none, by its place; else
the walk's case name. -/
def branchLabel (p : Tree) (i : Nat) (c : Tree) : Option String :=
  -- an invariant rule's first goal is `init`, and its split past `{anon}` the second
  let inv := p.name == "whileInvariantBox" || p.name == "whileInvariantDiamond" ||
    p.name == "whileInvariantLexDiamond"
  let idx := match c.label with
    | some l =>
      if l == `init then some 0
      else if inv && (l == `thn || l == `els) then some 1
      else if l == `thn then some 0 else if l == `els then some 1 else none
    | none => if p.children.size > 1 then some i else none
  let solkey := do (← (branchLabels.lookup p.name))[← idx]?
  (solkey.map (instLabel · p.se?)) <|> c.label.map (·.toString)

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

partial def rowsAux (parent : Option Nat) (label : Option String) (t : Tree) :
    StateM (Array Row) Unit := do
  let serial := (← get).size
  modify (·.push { serial, parent, name := t.name, branchLabel := label, state := t.state,
                   node := t })
  for h : i in [0:t.children.size] do
    let c := t.children[i]
    rowsAux (some serial) (branchLabel t i c) c

/-- The rows, in depth-first order: row `n` is the node of serial `n`. -/
def rows (t : Tree) : Array Row := (rowsAux none none t |>.run #[]).2

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
  let head ← match t with
    | .opened _ => do
      let s ← t.ppSequent
      pure (head ++ .nest (ind + 4) (m!"\n" ++ s))
    | _ => pure head
  let mut out := #[head]
  match t.children with
  | #[c] => out := out ++ (← displayAux c ind)
  | cs =>
    for h : i in [0:cs.size] do
      let c := cs[i]
      let l := (branchLabel t i c).getD s!"#{i + 1}"
      out := out.push m!"{pad}  [{l}]"
      out := out ++ (← displayAux c (ind + 4))
  return out

/-- The tree, displayed, and its summary. -/
def display (t : Tree) : MetaM MessageData := do
  let (ls, _) ← (displayAux t 0).run 0
  return MessageData.joinSep (ls.toList ++ [t.summary]) "\n"

end Tree


/-- `.r`: a constructor named against the expected type, as a walk names a
taclet. -/
def dotIdent (n : Lean.Name) : Lean.Term :=
  ⟨mkNode ``Lean.Parser.Term.dotIdent #[mkAtom ".", mkIdent n]⟩

/-- The constant `n` as the scope spells it (`update` under `open Proves`). -/
def short (n : Lean.Name) : MetaM Ident := return mkIdent (← unresolveNameGlobal n)

/-- The constant `n` as `Proves.n` when the scope reads it so, as a walk's
`apply Proves.fmlValid` is written; else as the scope spells it. -/
def qualified (n : Lean.Name) : MetaM Ident := do
  let q := Lean.Name.mkSimple n.getPrefix.getString! ++ Lean.Name.mkSimple n.getString!
  if (← resolveGlobalName q).any (·.1 == n) then return mkIdent q
  short n


/-- Run `tacs` on the goal `g`, errors as errors; the goals left. -/
def runOn (g : MVarId) (tacs : Array (TSyntax `tactic)) : TacticM (List MVarId) := do
  setGoals [g]
  for t in tacs do Term.withoutErrToSorry (evalTactic t)
  getUnsolvedGoals


/-- A tactic's lines. -/
def tacLines (t : TSyntax `tactic) : MetaM (Array String) := do
  return ((toString (← PrettyPrinter.ppTactic t)).splitOn "\n").toArray

/-- The walk the tree is, its lines indented relative to the first: one
`apply` per rule, a `case` per goal of a node with several (a `·` where the
goals have no distinct names), and `sorry` for an open leaf. -/
partial def Tree.script (t : Tree) : MetaM (Array String) := do
  match t with
  | .opened _ => return #[r"sorry"]
  | .solved _ tacs => return (← tacs.mapM tacLines).flatten
  | .rule _ _ tacs _ children =>
    let head := (← tacs.mapM tacLines).flatten
    match children with
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


/-- `t`'s lines. -/
def termLines (t : Lean.Term) : MetaM (Array String) := do
  return ((toString (← PrettyPrinter.ppTerm t)).splitOn "\n").toArray

end ProofTree

end Solidity
