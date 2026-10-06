import Solidity.Calculus.ProofTree
import Solidity.Tools.Common

/-!
# `#proof_tree`, `#proof_node`, `#proof_tree_json`: solkey's proof tree

```
#proof_tree dl!{ a == 1 → ⟨ uint x = a; require(x == 1); ⟩ x == 1 }
#proof_node 7 dl!{ a == 1 → ⟨ uint x = a; require(x == 1); ⟩ x == 1 }
#proof_tree_json dl!{ a == 1 → ⟨ uint x = a; require(x == 1); ⟩ x == 1 }
```

The three requests solkey's web prover answers about a proof
(`WebProver`'s `tree`, `node` and the summary that comes with them), on the
tree `ProofTree.ofFormula` grows for `⊢ φ` (`Calculus/ProofTree.lean`):

* `#proof_tree φ` — the tree as solkey's GUI lays it out, one line
  `serial: rule` per node under KeY's name, a sub-branch per goal of a split
  labelled as solkey labels it (`"Holds"`, `"if se1 true"`, …;
  `ProofTree.branchLabels`), an open leaf with its sequent; and the summary:
  closed or not, open goals, nodes, branches.
* `#proof_node n φ` — node `n`: its sequent `dl{ Γ ⟹ φ }`, its rule, its
  state, the branch it starts, its parent and its children, and the tactics
  that applied its rule (or closed it).
* `#proof_tree_json φ` — the tree in the web prover's shape (`Tree.toJson`):
  rows `[serial, parent, name, branchLabel, state]`, the sequents by serial,
  `closed`, `openGoalCount` and `stats`.

`φ` is a closed formula of a named contract (`elabFormula`).  The tree is
the one `sol_derive?` suggests as a walk: each node an elaborated `apply`,
each leaf closed by `refine close ?_; sol_symex; sol_close` where that
closes it.
-/

namespace Solidity.Tools

open Lean Elab Command Term Meta ProofTree

/-- The tree of `⊢ φ` for the command `cmd`. -/
def proofTreeOf (cmd : String) (t : Lean.Term) : TermElabM Tree := do
  let (φ, C, _) ← elabFormula cmd t
  ofFormula C φ

/-- `#proof_tree φ`: the proof tree of `⊢ φ`, solkey's view of it. -/
elab "#proof_tree " t:term : command => liftTermElabM do
  logInfo (← (← proofTreeOf "#proof_tree" t).display)

/-- `#proof_node n φ`: the node of serial number `n` of `⊢ φ`'s proof tree. -/
elab "#proof_node " n:num t:term : command => liftTermElabM do
  let tree ← proofTreeOf "#proof_node" t
  let rows := tree.rows
  let some r := rows[n.getNat]?
    | throwError "#proof_node: no node {n.getNat}; the tree has {rows.size} (0 to {rows.size - 1})"
  let children := (rows.filter (·.parent == some r.serial)).map (·.serial)
  let tacs ← match r.node.act with
    | .rule _ ts _ | .closed ts => ts.mapM fun s => return m!"{s}"
    | .opened => pure #[]
  let field (k : String) (v : MessageData) : MessageData := m!"{k}: {v}"
  logInfo <| MessageData.joinSep [
    field "node" m!"{r.serial}",
    m!"sequent:" ++ .nest 2 m!"\n{← r.node.ppSequent}",
    field "rule" m!"{r.name}",
    field "state" m!"{r.state}",
    field "branch" m!"{r.branchLabel.getD "-"}",
    field "parent" m!"{(r.parent.map toString).getD "-"}",
    field "children" m!"{children.toList}",
    field "tactics" (MessageData.joinSep tacs.toList "; ")] "\n"

/-- `#proof_tree_json φ`: the proof tree of `⊢ φ` as solkey's web prover
hands it out. -/
elab "#proof_tree_json " t:term : command => liftTermElabM do
  logInfo (← (← proofTreeOf "#proof_tree_json" t).toJson).pretty

end Solidity.Tools
