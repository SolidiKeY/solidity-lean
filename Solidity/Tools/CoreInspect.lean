import Solidity.Tools.Inspect
import Solidity.Tools.ProofTree
import Solidity.Calculus.Core.Delab
import Solidity.Calculus.Core.Quote
import Solidity.Calculus.Core.ProofTree
import Solidity.Calculus.Core.Surface

/-!
# `#wp`, `#step` and the proof tree on scoped formulas

`Tools/Inspect.lean`'s `#wp φ` and `#step φ`, for a formula `φ : Core.Fml C Γ`
(`cdl!{ … }`, `Calculus/Core/Notation.lean`): the scoped strategy
(`Core.symex`, `Core.Fml.step`) runs as compiled code, its result is quoted
(`Core.Fml.quote`) and printed by `Core.Delab`'s printer, as today's are.
`#wp` also prints the reduction of the result's erasure (`Core.Fml.erase`)
when it is in `sol_decide`'s fragment, and `#step` the rule the scoped strategy
fires, by name (`ruleAtC?`, `Core.ruleOf?`).

`#proof_tree φ`, `#proof_node n φ` and `#proof_tree_json φ`
(`Tools/ProofTree.lean`) on a scoped formula show the tree of `⊢ φ` that
`Core.ProofTree.ofFormula` grows (`Calculus/Core/ProofTree.lean`), in the
same layout.

Each command is a second elaborator of today's syntax: it takes a scoped
formula and leaves any other term to today's.
-/

namespace Solidity.Tools

open Lean Elab Command Term Meta
open Semantics Decide

variable {C : Contract}

/-- What `#wp` shows of a scoped `φ`: the formula the scoped strategy leaves,
quoted, and the reduction of its erasure when it is in the fragment. -/
def wpQuotedC [FreshNames] (c : Lean.Expr) {Γ : Core.Ctx} (φ : Core.Fml C Γ) :
    Lean.Expr × Option String :=
  let ψ := Core.symex 200 φ
  let ψ' := ψ.erase []
  (ψ.quote c, if ψ'.inL Sym.empty then some (LFml.fmt ψ'.reduce) else none)

/-- What `#step` shows of a scoped `φ`: the formula one step leaves, quoted. -/
def stepQuotedC (c : Lean.Expr) {Γ : Core.Ctx} (φ : Core.Fml C Γ) : Option Lean.Expr :=
  φ.step.map (·.quote c)

/-- A closed scoped formula of a named contract: the formula, and the
contract's name quoted. -/
def elabCoreFormula? (t : Lean.Term) : TermElabM (Option (Lean.Expr × Lean.Expr)) := do
  -- today's notation (`dl!{ … }`, `dl[C]{ … }`) is today's elaborator's,
  -- left unread so that it is not elaborated twice, unless the switch
  -- (`open scoped Solidity.Core.Surface`) makes it scoped
  if let some (.atom _ v) := t.raw.getHead? then
    if v.startsWith "dl" && !(← Core.surfaceOn) then return none
  let φ ← try elabTerm t none catch _ => return none
  synthesizeSyntheticMVarsNoPostponing
  let φ ← instantiateMVars φ
  let ty ← whnf (← inferType φ)
  unless ty.isAppOfArity ``Core.Fml 2 do return none
  let some n := (← whnfR ty.appFn!.appArg!).constName? | return none
  if φ.hasFVar || φ.hasMVar then throwError "the formula is not closed{indentExpr φ}"
  return some (φ, mkApp2 (mkConst ``Lean.mkConst) (toExpr n)
    (mkApp (mkConst ``List.nil [0]) (mkConst ``Lean.Level)))

/-- The rule one step fires on the scoped formula `φ`, by name: at the first
statement with a rule, looking through updates, a precondition, binders and
a conjunction's left goal first, as `Core.Fml.stepAt` looks (`ruleOf?`);
`emptyModality` where the first modality's program is done. -/
partial def ruleAtC? (φ : Lean.Expr) : MetaM (Option Lean.Name) := do
  let k ← mkAppM ``Core.Fml.fresh #[φ]
  let rec go (e : Lean.Expr) : MetaM (Option Lean.Name) := do
    let e ← whnf e
    let args := e.getAppArgs
    match e.getAppFn.constName? with
    | some ``Core.Fml.and =>
      match ← go args[2]! with
      | some n => return some n
      | none => go args[3]!
    | some ``Core.Fml.imp => go args[3]!
    | some ``Core.Fml.upd => go args[5]!
    | some ``Core.Fml.havoc => go args[2]!
    | some ``Core.Fml.all => go args[4]!
    | some ``Core.Fml.bind => go args[5]!
    | some ``Core.Fml.anon => go args[3]!
    | some ``Core.Fml.modal =>
      let P ← whnf args[5]!
      if P.isAppOf ``Core.Prog.nil then return some `emptyModality
      unless P.isAppOf ``Core.Prog.cons do return none
      let s := P.getArg! (P.getAppNumArgs - 2)
      let some (c, _) ← Core.ruleOf? k args[4]! s | return none
      return some (← Core.ProofTree.keyName c s)
    | _ => return none
  go φ

/-- `#wp φ` for a scoped formula. -/
@[command_elab Solidity.Tools.«command#wp_»]
def elabWpCore : CommandElab := fun stx => liftTermElabM do
  let some (φ, c) ← elabCoreFormula? ⟨stx[1]⟩ | throwUnsupportedSyntax
  let e ← mkAppM ``wpQuotedC #[c, φ]
  let (ψ, red) ← unsafe evalExpr (Lean.Expr × Option String) (← inferType e) e
  let tail := match red with
    | some r => m!"\nupdate-free:\n    {r}"
    | none => m!"\noutside `sol_decide`'s fragment (`Fml.inL`): no reduction"
  logInfo (m!"symbolic execution leaves:\n    {ψ}" ++ tail)

/-- `#step φ` for a scoped formula. -/
@[command_elab Solidity.Tools.«command#step_»]
def elabStepCore : CommandElab := fun stx => liftTermElabM do
  let some (φ, c) ← elabCoreFormula? ⟨stx[1]⟩ | throwUnsupportedSyntax
  let e ← mkAppM ``stepQuotedC #[c, φ]
  let ψ? ← unsafe evalExpr (Option Lean.Expr) (← inferType e) e
  match ψ? with
  | none => logInfo "no modality left: `close`"
  | some ψ =>
    let r := match ← ruleAtC? φ with
      | some n => toString n
      | none => "?"
    logInfo m!"  ~[{r}]~>\n    {ψ}"

/-! ## The proof tree -/

/-- The tree of `⊢ φ` for a scoped `φ`, or none for any other term. -/
def coreProofTree? (t : Lean.Term) : TermElabM (Option ProofTree.Tree) := do
  let some (φ, _) ← elabCoreFormula? t | return none
  let ty ← whnf (← inferType φ)
  unless ← isDefEq (ty.getArg! 1) (mkApp (mkConst ``List.nil [0]) (mkConst ``Core.LTy)) do
    throwError "#proof_tree: the formula is not closed at the empty context"
  return some (← Core.ProofTree.ofFormula ty.appFn!.appArg! φ)

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

/-- `#proof_tree φ` for a scoped formula. -/
@[command_elab Solidity.Tools.«command#proof_tree_»]
def elabProofTreeCore : CommandElab := fun stx => liftTermElabM do
  let some tree ← coreProofTree? ⟨stx[1]⟩ | throwUnsupportedSyntax
  logInfo (← tree.display)

/-- `#proof_node n φ` for a scoped formula. -/
@[command_elab Solidity.Tools.«command#proof_node__»]
def elabProofNodeCore : CommandElab := fun stx => liftTermElabM do
  let some tree ← coreProofTree? ⟨stx[2]⟩ | throwUnsupportedSyntax
  logInfo (← proofNodeMsg "#proof_node" tree (stx[1].isNatLit?.getD 0))

/-- `#proof_tree_json φ` for a scoped formula. -/
@[command_elab Solidity.Tools.«command#proof_tree_json_»]
def elabProofTreeJsonCore : CommandElab := fun stx => liftTermElabM do
  let some tree ← coreProofTree? ⟨stx[1]⟩ | throwUnsupportedSyntax
  logInfo (← tree.toJson).pretty

end Solidity.Tools
