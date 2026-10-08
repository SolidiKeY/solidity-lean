import Solidity.Calculus.Chains
import Solidity.Calculus.Decide
import Solidity.Calculus.ProofTree
import Solidity.Tools.ProofTree

/-!
# `#wp`, `#step` and the proof tree on today's formulas

`Tools/Inspect.lean`'s and `Tools/ProofTree.lean`'s commands are the scoped
calculus's.  This module adds a second elaborator to each, for today's
formula (`dl!{ … }`, `dl[C]{ … }`) read without the switch
(`open scoped Solidity.Core.Surface`): today's strategy (`symex`,
`Fml.step`) and today's proof tree (`ProofTree.ofFormula`,
`Calculus/ProofTree.lean`).  Declared after the scoped ones, each is tried
first and leaves every other term to them.  Two pins read today's formulas
so (`Examples/Tools.lean`'s `InspectToday`, `Examples/Tactics/CoreNotation`'s
last); W4 deletes this module with today's calculus.
-/

namespace Solidity.Tools

open Semantics Decide

open Lean Elab Command Term Meta

/-- Whether the command's formula is today's: `dl…{ … }` read without the
switch, which `elabCoreFormula?` leaves to this module. -/
def todayFormula (t : Lean.Term) : TermElabM Bool := do
  if ← Core.surfaceOn then return false
  match t.raw.getHead? with
  | some (.atom _ v) => return v.startsWith "dl"
  | _ => return false

variable {C : Contract}

/-- What `#wp` shows of `φ`: the formula symbolic execution leaves, quoted
against the contract `c`, and its reduction when it is in the fragment. -/
def wpQuoted [FreshNames] (c : Lean.Expr) (φ : Fml C) : Lean.Expr × Option String :=
  let ψ := symex 200 φ
  (ψ.quote c, if ψ.inL Sym.empty then some (LFml.fmt ψ.reduce) else none)

/-- What `#step` shows of `φ`: the formula one step leaves, quoted. -/
def stepQuoted (c : Lean.Expr) (φ : Fml C) : Option Lean.Expr :=
  φ.step.map (·.quote c)

/-- `#wp φ` for today's formula. -/
@[command_elab Solidity.Tools.«command#wp_»]
def elabWpToday : CommandElab := fun stx => liftTermElabM do
  unless ← todayFormula ⟨stx[1]⟩ do throwUnsupportedSyntax
  let (φ, _, c) ← elabFormula "#wp" ⟨stx[1]⟩
  let e ← mkAppM ``wpQuoted #[c, φ]
  let ty ← inferType e
  let (ψ, red) ← unsafe evalExpr (Lean.Expr × Option String) ty e
  let tail := match red with
    | some r => m!"\nupdate-free:\n    {r}"
    | none => m!"\noutside `sol_decide`'s fragment (`Fml.inL`): no reduction"
  logInfo (m!"symbolic execution leaves:\n    {ψ}" ++ tail)

/-- `#step φ` for today's formula. -/
@[command_elab Solidity.Tools.«command#step_»]
def elabStepToday : CommandElab := fun stx => liftTermElabM do
  unless ← todayFormula ⟨stx[1]⟩ do throwUnsupportedSyntax
  let (φ, _, c) ← elabFormula "#step" ⟨stx[1]⟩
  let e ← mkAppM ``stepQuoted #[c, φ]
  let ty ← inferType e
  match ← unsafe evalExpr (Option Lean.Expr) ty e with
  | none => logInfo "no modality left: `close`"
  | some ψ =>
    let r := match ← Chain.ruleOfLine φ with
      | some (_, n) => toString n
      | none => "?"
    logInfo m!"  ~[{r}]~>\n    {ψ}"

/-- The tree of `⊢ φ` for today's formula. -/
def proofTreeOf (cmd : String) (t : Lean.Term) : TermElabM ProofTree.Tree := do
  let (φ, C, _) ← elabFormula cmd t
  ProofTree.ofFormula C φ

/-- `#proof_tree φ` for today's formula. -/
@[command_elab Solidity.Tools.«command#proof_tree_»]
def elabProofTreeToday : CommandElab := fun stx => liftTermElabM do
  unless ← todayFormula ⟨stx[1]⟩ do throwUnsupportedSyntax
  logInfo (← (← proofTreeOf "#proof_tree" ⟨stx[1]⟩).display)

/-- `#proof_node n φ` for today's formula. -/
@[command_elab Solidity.Tools.«command#proof_node__»]
def elabProofNodeToday : CommandElab := fun stx => liftTermElabM do
  unless ← todayFormula ⟨stx[2]⟩ do throwUnsupportedSyntax
  let tree ← proofTreeOf "#proof_node" ⟨stx[2]⟩
  logInfo (← proofNodeMsg "#proof_node" tree (stx[1].isNatLit?.getD 0))

/-- `#proof_tree_json φ` for today's formula. -/
@[command_elab Solidity.Tools.«command#proof_tree_json_»]
def elabProofTreeJsonToday : CommandElab := fun stx => liftTermElabM do
  unless ← todayFormula ⟨stx[1]⟩ do throwUnsupportedSyntax
  logInfo (← (← proofTreeOf "#proof_tree_json" ⟨stx[1]⟩).toJson).pretty

end Solidity.Tools
