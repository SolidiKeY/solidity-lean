import Solidity.Calculus.DecideScoped
import Solidity.Calculus.Delab
import Solidity.Calculus.Quote
import Solidity.Calculus.ProofTree
import Solidity.Calculus.Surface
import Solidity.Tools.ProofTree
import Solidity.Tools.Taclet

/-!
# `#wp`, `#step`: looking inside the calculus

```
#wp cdl!{ [ alice.age = 42; uint x = alice.age; ] x == 42 }
#step cdl!{ [ alice.age = 42; uint x = alice.age; ] x == 42 }
```

* `#wp φ` runs the scoped strategy to the end (`symex 200`, what
  `sol_symex` does) and prints what is left, the first-order formula whose
  validity is `φ`'s.  When it is in `sol_decide`'s fragment it also prints
  its reduction (`Fml.reduceS`): the updates pushed in and every read of a
  write eliminated, a typed formula over the initial state alone, printed
  by `LFml.ppWith` in KeY's spelling (`find(storage, alice.age)`,
  `save(s, p, w)`, `delAt(s, p)`, `if(i = j) then a else b`, `=`, `∧`,
  `→`, `¬`, `∀ uint x; φ`).
* `#step φ` takes one step and names the rule the scoped strategy fires
  (`ruleAtC?`, `ruleOf?`), as a line of `#derivation`.

`φ` is a closed scoped formula of a named contract, `φ : Fml C Γ`
(`cdl!{ … }`, or `dl!{ … }` under `open scoped Solidity.Scoped`): the
strategy runs as compiled code (`unsafe evalExpr`), its result is quoted
(`Fml.quote`) against the contract's name and printed by `Delab`'s
printer (`elabCoreFormula?`, `Tools/ProofTree.lean`).

A file that inspects the calculus imports this module alone: it brings the
proof tree's commands (`#proof_tree`, `#proof_node`, `#proof_tree_json`,
`Tools/ProofTree.lean`) and `#taclet` (`Tools/Taclet.lean`) with it.
-/

namespace Solidity.Tools

open Semantics Decide

/-! ## The binders' names

The scoped reduction keys a local by the binder count where it is pushed
(`SymS.next`, the atom `LTm.var k`), which prints as `#k`; `#wp` prints it
by the name its binder gives, replaying the count as `Fml.toLS` makes it. -/

/-- The names an update declares, in the order it pushes them
(`Upd.replayS`). -/
def _root_.Solidity.Upd.declNames {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → List Var
  | _, .nil => []
  | _, .snoc U _ => U.declNames
  | _, .decl U x _ => U.declNames ++ [x]
  | _, .pop U _ => U.declNames
  | _, .drop U _ => U.declNames

/-- The name of each key the reduction of `φ` gives a local, from `k` on,
as `Fml.toLS` counts the locals it pushes. -/
def _root_.Solidity.Fml.keyNames : {Γ : Ctx} → Nat → Fml C Γ → List (Nat × Var)
  | _, k, .all x _ φ => (k, x) :: Fml.keyNames (k + 1) φ
  | _, k, .bind _ x _ φ => (k, x) :: Fml.keyNames (k + 1) φ
  | _, k, .upd _ U φ =>
    let ds := U.declNames
    (ds.zipIdx k).map (fun (x, i) => (i, x)) ++ Fml.keyNames (k + ds.length) φ
  | _, k, .not φ => Fml.keyNames k φ
  | _, k, .and φ ψ => Fml.keyNames k φ ++ Fml.keyNames k ψ
  | _, k, .imp φ ψ => Fml.keyNames k φ ++ Fml.keyNames k ψ
  | _, _, _ => []

/-- The fresh names, with the key `#k` printed by the name its binder gives
(`ks`) where that name is the only one. -/
def keyedNames [inst : FreshNames] (ks : List (Nat × Var)) : FreshNames where
  name b k :=
    if b == "#" then
      match (ks.filter (·.1 == k)).map (·.2) |>.eraseDups with
      | [x] => toString x
      | _ => inst.name b k
    else inst.name b k
  parse := inst.parse

/-! ## The commands -/

variable {C : Contract}

open Lean Elab Command Term Meta

/-- `#wp φ`: what symbolic execution leaves of `φ`, and, in `sol_decide`'s
fragment, its reduction to the initial state. -/
syntax "#wp " term : command

/-- `#step φ`: one step of the strategy on `φ`, and the rule it fires. -/
syntax "#step " term : command

/-- What `#wp` shows of a scoped `φ`: the formula the scoped strategy leaves,
quoted, and its reduction when it is in the fragment. -/
def wpQuotedC [FreshNames] (c : Lean.Expr) {Γ : Ctx} (φ : Fml C Γ) :
    Lean.Expr × Option String :=
  let ψ := symex 200 φ
  -- a modality left is outside the fragment
  (ψ.quote c, match Γ, ψ with
    | [], ψ =>
      if !ψ.active then
        let inst := keyedNames (ψ.keyNames 0)
        ψ.reduceS.map fun r => r.ppWith (inst.name "#") PrimTy.toStr
      else none
    | _, _ => none)

/-- What `#step` shows of a scoped `φ`: the formula one step leaves, quoted. -/
def stepQuotedC (c : Lean.Expr) {Γ : Ctx} (φ : Fml C Γ) : Option Lean.Expr :=
  φ.step.map (·.quote c)


/-- The rule one step fires on the scoped formula `φ`, by name: at the first
statement with a rule, looking through updates, a precondition, binders and
a conjunction's left goal first, as `Fml.stepAt` looks (`ruleOf?`);
`emptyModality` where the first modality's program is done. -/
partial def ruleAtC? (φ : Lean.Expr) : MetaM (Option Lean.Name) := do
  let k ← mkAppM ``Fml.fresh #[φ]
  let rec go (e : Lean.Expr) : MetaM (Option Lean.Name) := do
    let e ← whnf e
    let args := e.getAppArgs
    match e.getAppFn.constName? with
    | some ``Fml.and =>
      match ← go args[2]! with
      | some n => return some n
      | none => go args[3]!
    | some ``Fml.imp => go args[3]!
    | some ``Fml.upd => go args[5]!
    | some ``Fml.havoc => go args[2]!
    | some ``Fml.all => go args[4]!
    | some ``Fml.bind => go args[5]!
    | some ``Fml.anon => go args[3]!
    | some ``Fml.modal =>
      let P ← whnf args[5]!
      if P.isAppOf ``Prog.nil then return some `emptyModality
      unless P.isAppOf ``Prog.cons do return none
      let s := P.getArg! (P.getAppNumArgs - 2)
      let some (c, _) ← ruleOf? k args[4]! s | return none
      return some (← ProofTree.keyName c s)
    | _ => return none
  go φ

/-- `#wp φ`, including imported obligations declared without executable code. -/
@[command_elab Solidity.Tools.«command#wp_»]
def elabWpCore : CommandElab := fun stx => liftTermElabM do
  let some (φ, c) ← elabCoreFormula? ⟨stx[1]⟩ | notScoped "#wp"
  let φ ← Symex.evaluable φ
  let e ← mkAppM ``wpQuotedC #[c, φ]
  let (ψ, red) ← unsafe evalExpr (Lean.Expr × Option String) (← inferType e) e
  let tail := match red with
    | some r => m!"\nupdate-free:\n    {r}"
    | none => m!"\noutside `sol_decide`'s fragment (`Fml.reduceS`): no reduction"
  logInfo (m!"symbolic execution leaves:\n    {ψ}" ++ tail)

/-- `#step φ`, including imported obligations declared without executable code. -/
@[command_elab Solidity.Tools.«command#step_»]
def elabStepCore : CommandElab := fun stx => liftTermElabM do
  let some (φ, c) ← elabCoreFormula? ⟨stx[1]⟩ | notScoped "#step"
  let φ ← Symex.evaluable φ
  let e ← mkAppM ``stepQuotedC #[c, φ]
  let ψ? ← unsafe evalExpr (Option Lean.Expr) (← inferType e) e
  match ψ? with
  | none => logInfo "no modality left: `close`"
  | some ψ =>
    let r := match ← ruleAtC? φ with
      | some n => toString n
      | none => "?"
    logInfo m!"  ~[{r}]~>\n    {ψ}"

end Solidity.Tools
