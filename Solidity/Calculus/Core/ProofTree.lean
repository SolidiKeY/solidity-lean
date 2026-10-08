import Solidity.Calculus.ProofTree
import Solidity.Calculus.Core.Completeness
import Solidity.Calculus.Core.Delab

/-!
# The proof tree of a scoped goal

`Calculus/ProofTree.lean`'s tree, grown on a scoped goal `H ⊢ φ`
(`Core.Proves`, `Calculus/Core/Proves.lean`): the same nodes, rows, labels
and printers (`ProofTree.Tree`), the moves the scoped calculus makes.  At a
goal `⟨[ s; ..ω ]⟩ φ` the rule is the one `Stmt.step` fires, by name
(`ruleOf?`, `Calculus/Core/Completeness.lean`), applied as a walk writes it:
`apply update (Taclet.toStep .localValueAssign)`, the `Proves` constructor
of its premise's kind with the taclet's `toStep`.  Nothing is trusted: each
node is an elaborated `apply`.

What the scoped calculus adds is not a node:

* a scope's end (`}` of a block, the fresh locals of a rule) is a popping
  update that the next node's `updIntro` takes, and a declaration's hidden
  binder (`bindIntro`); both are folded into the node before them, as
  tactics of that node: KeY has no step there.

A leaf is closed by `closeTrue` (`true` behind a context of scope ends and
box updates), else as a walk ends: `Proves.close` takes the sequent, its
context in front, to its erasure (`Calculus/Core/CloseErase.lean`), which
today's `sol_symex; sol_close` closes (`closeTacs`), then by the tactics
`Config.closers` lists.  `Proves.close` takes a leaf behind updates of
either modality (`Fml.closableB`).

A rule of an operator family prints as KeY's taclet at its operator
(`RuleShapes.keyTacletAt`, at today's name of the constructor).
-/

namespace Solidity.Core

namespace Proves

variable {C : Contract} {R : RuleSet} {Γ₀ : Ctx}

/-- `impRight` (`intro`). -/
theorem impRight {Γ : Ctx} {H : Hyps C Γ₀ Γ} {a φ : Fml C Γ} (h : Proves C R Γ₀ (H.pre a) φ) :
    Proves C R Γ₀ H (.imp a φ) := .intro h

/-- `allRight` (`allIntro`). -/
theorem allRight {Γ : Ctx} {H : Hyps C Γ₀ Γ} {x : Var} {p : PrimTy} {φ : Fml C (.val p :: Γ)}
    (h : Proves C R Γ₀ (H.all x p) φ) : Proves C R Γ₀ H (.all x p φ) := .allIntro h

/-- `emptyModality` (`empty`). -/
theorem emptyModality {Γ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {κ : Frames C Γ Γ₂}
    {φ : Fml C Γ₂} (h : Proves C R Γ₀ H (κ.exit m φ)) : Proves C R Γ₀ H (.modal m .nil κ φ) :=
  .empty h

end Proves

namespace ProofTree

open Lean Meta Elab Tactic
open Solidity.ProofTree (Tree Act short dotIdent runOn)

/-- How the tree is grown: whether a leaf is closed by its erasure
(`closeTacs`), the tactics tried after it (each list a closing script), and
at most how many nodes. -/
structure Config where
  erased : Bool := true
  closers : Array (Array (TSyntax `tactic)) := #[]
  maxNodes : Nat := 10000

/-- `closeTrue`, the closer every tree tries first. -/
def closeTrueTacs : MetaM (Array (TSyntax `tactic)) := do
  return #[← `(tactic| exact $(← short ``Proves.closeTrue) rfl)]

/-- The tactics a leaf is closed by, as a walk ends: `Proves.close` at the
empty outer scope (a tree's goal is `[] ⊢ φ`), then today's closer on the
erasure. -/
def closeTacs : MetaM (Array (TSyntax `tactic)) := do
  return #[← `(tactic| refine $(← short ``Proves.close) [] $(mkIdent `rfl)
      $(← short ``List.nodup_nil) ?_),
    ← `(tactic| sol_symex), ← `(tactic| sol_close)]

/-- The `Proves` constructor of a premise kind. -/
def provesCtor (premise : Lean.Name) : Option Lean.Name :=
  [(``Premise.update, ``Proves.update), (``Premise.unfold, ``Proves.unfold),
   (``Premise.bind, ``Proves.bind), (``Premise.split, ``Proves.split),
   (``Premise.check, ``Proves.check), (``Premise.done, ``Proves.done),
   (``Premise.branches, ``Proves.branches), (``Premise.cases, ``Proves.cases),
   (``Premise.inv, ``Proves.inv), (``Premise.inline, ``Proves.inline)].lookup premise

/-- The operator a statement applies, its first `BinOp`, `UnOp` or `IncDec`
constructor: a constructor, not a function of the namespace (`BinOp.ret` in
a value's type, which an `if`'s branch carries). -/
def operatorOf? (env : Environment) (s : Expr) : Option Lean.Name :=
  (s.find? fun e => match e.constName? with
    | some n => (n.getPrefix == ``BinOp || n.getPrefix == ``UnOp || n.getPrefix == ``IncDec) &&
        env.isConstructor n
    | none => false).bind (·.constName?)

/-- The name a node prints for the scoped constructor `c` fired on `s`:
KeY's taclet at the operator, for a row of an operator family (by today's
name of the constructor); else `c`'s own. -/
def keyName (c : Lean.Name) (s : Expr) : MetaM Lean.Name := do
  let own := Chain.lastName c
  let today := (`Solidity.Taclet).append own
  if (RuleShapes.operatorOrder.lookup today).isNone then return own
  let s ← instantiateMVars s
  let some op := operatorOf? (← getEnv) s | return own
  match RuleShapes.keyTacletAt today op with
  | some t => return Lean.Name.mkSimple t.name
  | none => return own

/-- One way to take the step at a goal: the rule's name, the tactics, and how
its goals are taken apart. -/
structure Move where
  name : Lean.Name
  tacs : Array (TSyntax `tactic)
  /-- `Premise.branches`: the goal `∀ b ∈ bs, …` to take apart. -/
  branches : Bool := false
  /-- `Premise.cases`: the goals `∀ f ∈ fs, …` and `∀ U ∈ us, …`. -/
  cases : Bool := false
  /-- An `if`'s condition, for `ifElseSplit`'s labels. -/
  se : Option String := none

/-- An `if`'s condition, printed with the names of the context `H`
(`Delab.hypsParts`), as `ifElseSplit`'s labels name it: `se1` for a fresh
local. -/
def condOf? (C H s : Expr) : MetaM (Option String) := do
  try
    unless (← whnf s).isAppOf ``Stmt.ite do return none
    Delab.withTwins s false fun env => do
      let (_, _, ns) ← (Delab.hypsParts C H).run env
      let st ← whnf (← (Delab.tr ns s).run env)
      unless st.isAppOf ``Solidity.Stmt.ite do return none
      let c ← Solidity.ppExpr (st.getArg! 1)
      return some (toString (← PrettyPrinter.ppCategory `sol_expr c))
  catch _ => return none

/-- The goal `Core.Proves C R Γ₀ H φ`, its parts. -/
def goalParts? (ty : Expr) : Option (Expr × Expr × Expr) :=
  if ty.isAppOfArity ``Proves 6 then
    some (ty.getArg! 0, ty.getArg! 4, ty.getArg! 5)
  else none

/-- A move that adds no node: the hidden binder, and an update of scope ends
(`Upd.popsOnly`).  Applied after a rule, as part of its node. -/
def silentAt (g : MVarId) : MetaM (Option (TSyntax `tactic)) := g.withContext do
  let ty ← whnfR (← instantiateMVars (← g.getType))
  let some (_, _, φ) := goalParts? ty | return none
  let φ ← whnf φ
  match_expr φ with
  | Fml.bind _ _ _ _ _ _ => return some (← `(tactic| apply $(← short ``Proves.bindIntro)))
  | Fml.upd _ _ _ _ U _ =>
    let pops ← whnfD (← mkAppM ``Upd.popsOnly #[U])
    if pops.isConstOf ``Bool.true then
      return some (← `(tactic| apply $(← short ``Proves.updIntro)))
    return none
  | _ => return none

/-- The moves the strategy makes at the goal `H ⊢ φ`: none at a goal with no
rule, a leaf. -/
def movesAt (g : MVarId) : MetaM (Array Move) := g.withContext do
  let ty ← whnfR (← instantiateMVars (← g.getType))
  let some (C, H, φ0) := goalParts? ty | return #[]
  let φ ← whnf φ0
  match_expr φ with
  | Fml.imp _ _ _ _ =>
    return #[{ name := `impRight, tacs := #[← `(tactic| apply $(← short ``Proves.impRight))] }]
  | Fml.all _ _ _ _ _ =>
    return #[{ name := `allRight, tacs := #[← `(tactic| apply $(← short ``Proves.allRight))] }]
  | Fml.upd _ _ _ _ _ _ =>
    return #[{ name := `updIntro, tacs := #[← `(tactic| apply $(← short ``Proves.updIntro))] }]
  | Fml.bind _ _ _ _ _ _ =>
    return #[{ name := `bindIntro, tacs := #[← `(tactic| apply $(← short ``Proves.bindIntro))] }]
  | Fml.modal _ _ _ _ m P _ _ =>
    let P ← whnf P
    if P.isAppOf ``Prog.nil then
      return #[{ name := `emptyModality,
                 tacs := #[← `(tactic| apply $(← short ``Proves.emptyModality))] }]
    unless P.isAppOf ``Prog.cons do return #[]
    let s := P.getArg! (P.getAppNumArgs - 2)
    let k ← mkAppM ``Hyps.fresh #[H, φ0]
    let some (c, p) ← ruleOf? k m s | return #[]
    -- a premise built by a function (`Premise.expandCall`) is its constructor's
    -- (the call trees over `Callees`, `Examples/ProofTree.lean`)
    let some premise := (← whnf p).getAppFn.constName? | return #[]
    let some ctor := provesCtor premise | return #[]
    let toStep := if (`Solidity.Core.LeanTaclet).isPrefixOf c then ``LeanTaclet.toStep
      else ``Taclet.toStep
    let d ← `(($(← short toStep) $(dotIdent (Chain.lastName c))))
    let name ← keyName c s
    -- an `if`'s condition, as `ifElseSplit`'s labels name it
    let se ← if premise == ``Premise.split then condOf? C H s else pure none
    let ctorId ← short ctor
    let tac ← if premise == ``Premise.branches || premise == ``Premise.cases then
        `(tactic| apply $ctorId:ident $d:term rfl)
      else `(tactic| apply $ctorId:ident $d:term)
    return #[{ name, se, branches := premise == ``Premise.branches,
               cases := premise == ``Premise.cases, tacs := #[tac] }]
  | _ => return #[]

/-- After `apply branches r`: the goal `∀ b ∈ bs, …` taken apart, one goal
per outcome. -/
def splitBranches (g : MVarId) : TacticM (Array (TSyntax `tactic) × List MVarId) := do
  let names := #[``List.forall_mem_cons, ``List.not_mem_nil, ``false_implies, ``implies_true,
    ``and_true]
  let lemmas ← names.mapM fun n => do `(Lean.Parser.Tactic.simpLemma| $(← short n):ident)
  let simp ← `(tactic| simp only [$lemmas,*])
  let gs ← runOn g #[simp]
  let [g'] := gs | return (#[simp], gs)
  let rec count (e : Expr) (fuel : Nat) : Nat :=
    match fuel, e.app2? ``And with
    | f + 1, some (_, b) => count b f + 1
    | _, _ => 1
  let n := count (← whnfR (← instantiateMVars (← g'.getType))) 64
  if n < 2 then return (#[simp], gs)
  let holes ← (List.range n).toArray.mapM fun _ => `(term| ?_)
  let refine ← `(tactic| refine ⟨$holes,*⟩)
  return (#[simp, refine], ← runOn g' #[refine])

/-- `apply cases r` with its goals taken apart, the formulas first, then one
goal per update. -/
def applyCases (g : MVarId) (tacs : Array (TSyntax `tactic)) :
    TacticM (Array (TSyntax `tactic) × List MVarId) := do
  let names := #[``List.forall_mem_cons, ``List.not_mem_nil, ``false_implies, ``implies_true,
    ``and_true]
  let lemmas ← names.mapM fun n => do `(Lean.Parser.Tactic.simpLemma| $(← short n):ident)
  let some last := tacs.back? | return (tacs, ← runOn g tacs)
  let t ← `(tactic| $last <;> (try simp only [$lemmas,*]) <;> (try and_intros))
  let tacs := tacs.pop.push t
  return (tacs, ← runOn g tacs)

/-- The silent moves at a goal, as long as there is one: their tactics and the
goal left. -/
partial def silent (g : MVarId) : TacticM (Array (TSyntax `tactic) × MVarId) := do
  let some t ← silentAt g | return (#[], g)
  let s ← saveState
  try
    let [g'] ← runOn g #[t] | s.restore; return (#[], g)
    let (more, g'') ← silent g'
    return (#[t] ++ more, g'')
  catch _ => s.restore; return (#[], g)

/-- Grow the tree at the goal `g`, whose branch is labelled `label`. -/
partial def grow (cfg : Config) (fuel : IO.Ref Nat) (label : Option Lean.Name) (g : MVarId) :
    TacticM Tree := g.withContext do
  let n ← fuel.get
  if n == 0 then throwError "proof tree: more than {cfg.maxNodes} nodes"
  fuel.set (n - 1)
  let sequent ← instantiateMVars (← g.getType)
  for mv in ← movesAt g do
    let s ← saveState
    let applied ← try
        if mv.cases then some <$> applyCases g mv.tacs
        else
          let gs ← runOn g mv.tacs
          if mv.branches then
            match gs with
            | [g'] => (fun (more, gs) => some (mv.tacs ++ more, gs)) <$> splitBranches g'
            | _ => pure (some (mv.tacs, gs))
          else pure (some (mv.tacs, gs))
      catch _ => s.restore; pure none
    let some (tacs, gs) := applied | continue
    -- a single goal goes on through the silent moves, in this node
    let (tacs, gs) ← match gs with
      | [g'] => do let (more, g'') ← silent g'; pure (tacs ++ more, [g''])
      | _ => pure (tacs, gs)
    let labels ← if gs.length < 2 || mv.branches || mv.cases then pure (gs.map fun _ => none) else
      gs.mapM fun c => do
        let t ← c.getTag
        pure (match t with | .str _ l => some (Lean.Name.mkSimple l) | _ => none)
    let mut cs := #[]
    for (c, l) in gs.zip labels do
      -- a goal of several goes on through the silent moves first, in its own node
      let (pre, c') ← if gs.length < 2 then pure (#[], c) else silent c
      let t ← grow cfg fuel l c'
      cs := cs.push (if pre.isEmpty then t else prefixTacs pre t)
    return .node g sequent label (.rule mv.name tacs mv.se) cs
  -- a leaf
  let erased ← if cfg.erased then pure #[← closeTacs] else pure #[]
  for tacs in #[← closeTrueTacs] ++ erased ++ cfg.closers do
    let s ← saveState
    try
      if (← runOn g tacs).isEmpty then return .node g sequent label (.closed tacs) #[]
      s.restore
    catch _ => s.restore
  return .node g sequent label .opened #[]
where
  /-- The silent moves `pre` made at the top of the branch `t`: its first
  node's tactics, its goal the branch's own. -/
  prefixTacs (pre : Array (TSyntax `tactic)) (t : Tree) : Tree :=
    match t with
    | .node _ e l (.rule n ts se) cs => .node t.goal e l (.rule n (pre ++ ts) se) cs
    | .node _ e l (.closed ts) cs => .node t.goal e l (.closed (pre ++ ts)) cs
    | t => t

/-- The tree of the goal `g`; the goals it leaves open are its open leaves. -/
def build (g : MVarId) (cfg : Config := {}) : TacticM Tree := do
  let fuel ← IO.mkRef cfg.maxNodes
  -- the hidden binders of the formula's parameters are no node either
  let (pre, g') ← silent g
  let t ← grow cfg fuel none g'
  let t := if pre.isEmpty then t else grow.prefixTacs pre t
  setGoals t.openGoals.toList
  return t

/-- The tree of `⊢ φ`, `φ : Core.Fml C []`, on a goal of its own. -/
def ofFormula (C φ : Expr) (cfg : Config := {}) : TermElabM Tree := do
  let nil := mkApp (mkConst ``List.nil [0]) (mkConst ``LTy)
  let ty := mkAppN (mkConst ``Proves) #[C, mkConst ``RuleSet.all, nil, nil,
    mkApp2 (mkConst ``Hyps.nil) C nil, φ]
  let g ← mkFreshExprSyntheticOpaqueMVar ty
  let out ← IO.mkRef (default : Tree)
  discard <| Tactic.run g.mvarId! do out.set (← build g.mvarId! cfg)
  out.get

end ProofTree

end Solidity.Core
