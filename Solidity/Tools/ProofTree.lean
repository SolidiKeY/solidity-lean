import Solidity.Calculus.ProofTree
import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.Surface
import Solidity.Tools.Common

/-!
# `#proof_tree`, `#proof_node`, `#proof_tree_json`: solkey's proof tree

```
#proof_tree cdl!{ a == 1 → ⟨ uint x = a; require(x == 1); ⟩ x == 1 }
#proof_node 7 cdl!{ a == 1 → ⟨ uint x = a; require(x == 1); ⟩ x == 1 }
#proof_tree_json cdl!{ a == 1 → ⟨ uint x = a; require(x == 1); ⟩ x == 1 }
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

`φ` is a closed scoped formula of a named contract at the empty context
(`elabCoreFormula?`).  The tree is the one
`sol_derive?` suggests as a walk: each node an elaborated `apply`, each leaf
closed where the scoped closer closes it.
-/

namespace Solidity.Tools

open Lean Elab Command Term Meta

/-- `#proof_tree φ`: the proof tree of `⊢ φ`, solkey's view of it. -/
syntax "#proof_tree " term : command

/-- `#proof_node n φ`: the node of serial number `n` of `⊢ φ`'s proof tree. -/
syntax "#proof_node " num term : command

/-- `#proof_tree_json φ`: the proof tree of `⊢ φ` as solkey's web prover
hands it out. -/
syntax "#proof_tree_json " term : command

/-! ## The formula a command reads -/

/-- A closed scoped formula of a named contract: the formula, and the
contract's name quoted; none for `dl!{ … }` read without the switch, or any
other term. -/
def elabCoreFormula? (t : Lean.Term) : TermElabM (Option (Lean.Expr × Lean.Expr)) := do
  -- `dl!{ … }`, `dl[C]{ … }` without the switch (`open scoped
  -- Solidity.Scoped`) read as the closer's formulas, which have no tree:
  -- left unread, so that the command says so (`notScoped`)
  if let some (.atom _ v) := t.raw.getHead? then
    if v.startsWith "dl" && !(← surfaceOn) then return none
  let φ ← try elabTerm t none catch _ => return none
  synthesizeSyntheticMVarsNoPostponing
  let φ ← instantiateMVars φ
  let ty ← whnf (← inferType φ)
  unless ty.isAppOfArity ``Fml 2 do return none
  let some n := (← whnfR ty.appFn!.appArg!).constName? | return none
  if φ.hasFVar || φ.hasMVar then throwError "the formula is not closed{indentExpr φ}"
  return some (φ, mkApp2 (mkConst ``Lean.mkConst) (toExpr n)
    (mkApp (mkConst ``List.nil [0]) (mkConst ``Lean.Level)))

/-- What a command says of a term that is not a closed scoped formula. -/
def notScoped {α : Type} (cmd : String) : MetaM α :=
  throwError "{cmd}: not a closed scoped formula `Fml C Γ` (`cdl!\{ … }`, or `dl!\{ … }` \
    under `open scoped Solidity.Scoped`)"

/-! ## The proof tree -/

/-- The tree of `⊢ φ` for a scoped `φ`, or none for any other term. -/
def coreProofTree? (t : Lean.Term) : TermElabM (Option ProofTree.Tree) := do
  let some (φ, _) ← elabCoreFormula? t | return none
  let ty ← whnf (← inferType φ)
  unless ← isDefEq (ty.getArg! 1) (ctxE []) do
    throwError "#proof_tree: the formula is not closed at the empty context"
  return some (← ProofTree.ofFormula ty.appFn!.appArg! φ)

/-- What `#proof_node n φ` shows of the node `n` of `tree`, as
`Tools/ProofTree.lean` shows it. -/
def proofNodeMsg (cmd : String) (tree : ProofTree.Tree) (n : Nat) : MetaM MessageData := do
  let rows := tree.rows
  let some r := rows[n]?
    | throwError "{cmd}: no node {n}; the tree has {rows.size} (0 to {rows.size - 1})"
  let children := (rows.filter (·.parent == some r.serial)).map (·.serial)
  let tacs ← match r.node.act with
    | .rule _ ts _ | .closed ts => ts.mapM fun s => return m!"{s}"
    | .opened => pure #[]
  let field (k : String) (v : MessageData) : MessageData := m!"{k}: {v}"
  return MessageData.joinSep [
    field "node" m!"{r.serial}",
    m!"sequent:" ++ .nest 2 m!"\n{← r.node.ppSequent}",
    field "rule" m!"{r.name}",
    field "state" m!"{r.state}",
    field "branch" m!"{r.branchLabel.getD "-"}",
    field "parent" m!"{(r.parent.map toString).getD "-"}",
    field "children" m!"{children.toList}",
    field "tactics" (MessageData.joinSep tacs.toList "; ")] "\n"

/-- `#proof_tree φ`. -/
@[command_elab Solidity.Tools.«command#proof_tree_»]
def elabProofTreeCore : CommandElab := fun stx => liftTermElabM do
  let some tree ← coreProofTree? ⟨stx[1]⟩ | notScoped "#proof_tree"
  logInfo (← tree.display)

/-- `#proof_node n φ`. -/
@[command_elab Solidity.Tools.«command#proof_node__»]
def elabProofNodeCore : CommandElab := fun stx => liftTermElabM do
  let some tree ← coreProofTree? ⟨stx[2]⟩ | notScoped "#proof_node"
  logInfo (← proofNodeMsg "#proof_node" tree (stx[1].isNatLit?.getD 0))

/-- `#proof_tree_json φ`. -/
@[command_elab Solidity.Tools.«command#proof_tree_json_»]
def elabProofTreeJsonCore : CommandElab := fun stx => liftTermElabM do
  let some tree ← coreProofTree? ⟨stx[1]⟩ | notScoped "#proof_tree_json"
  logInfo (← tree.toJson).pretty

end Solidity.Tools
