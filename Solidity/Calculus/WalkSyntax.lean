import Solidity.Calculus.Derive
import Solidity.Calculus.Surface
import Solidity.Calculus.TacticSyntax

/-!
# The walk on a scoped goal

Under `open scoped Solidity.Scoped` a walk keeps solkey's text: one
`apply` per rule, the rule named as solkey names it (`apply update
.storageFieldWriteSave`, `apply unfold .localValueDeclInitDrop`, `apply
empty`, …), and a leaf is left by `sol_leaf` for the scoped closers
(`Calculus/ProofTree.lean`, `Calculus/ProvesDerive.lean`).  On a scoped goal (`Proves`) each line
is the scoped rule of the same kind, its premise the named taclet's
(`Taclet.step_eq`, `LeanTaclet.toStep`).

Where the scoped calculus takes a step today's names otherwise:

* `apply cases r` and `apply branches r` leave the same goals as today's
  (`∀ f ∈ fs, …`, `∀ U ∈ us, …`, `∀ b ∈ bs, …`), the silent steps left to
  the lines after them;
* `apply unfold r` is `Proves.unfold`, `bind` (a declaration with an
  initializer: the local joins the context, `localValueDeclInitDrop`) or
  `inline` (a call's frame dropped under its returns), whichever `r`'s premise is;
  `apply unfoldStep` (a read into a hole, whose line `apply` cannot match,
  so the line names no rule) is the strategy's premise by `rfl`;
* the steps KeY does not show are taken before and after each rule,
  silently (`core_silent`): a scope's end (an update that only pops) and a hidden
  binder join the context;
* `apply invBox r` (`apply invLean r` under the diamond) is the scoped
  `inv`, its goals `init`, `thn` and `els` (solkey's two goals under the
  box, no third); `apply updIntro` takes an update into the context;
* `apply empty` (`emptyModality`) is a step only where a modality is left
  with no statement: a rule that leaves none goes on into the rest or past
  the frames (Gate G0, condition 6), so after a last statement it does
  nothing, and before a statement it is refused (`core_skip`); so is
  `apply allIntro` on a parameter `Proves.valid` already bound;
* `apply Proves.valid` binds the formula's parameters (`∀`, `cdl!`) with
  `allRight` at once, as today's walk leaves them free (`core_params`); an
  explicit `∀ uint x;` (`cdl!` marks it, decision 28) is left to its own
  `apply allRight`;
* a leaf is left by `sol_leaf` (`Proves.closeValid`), the leaf step the
  walks and the tree write.

Each reading is a `scoped macro_rules` of the namespace `Solidity.Scoped`,
tried before Lean's `apply`.
-/

namespace Solidity

open Lean Elab Tactic Meta

/-- The update only pops (a scope's end), decided on the term. -/
def Walk.popsOnly (U : Expr) : MetaM Bool := do
  let b ← whnfD (← mkAppM ``Upd.popsOnly #[U])
  return b.isConstOf ``Bool.true

/-- `core_silent`: on a scoped goal, the steps KeY does not show: a scope's
end (an update that only pops) and a hidden binder join the context; before
any rule, so do the formula's parameters (`allRight`: today's walk reads
them free).  It fails on a goal that is not a scoped sequent. -/
syntax (name := coreSilent) "core_silent" : tactic

/-- The context holds the formula's parameters only (`∀` and hidden
binders over nothing): no rule has fired yet. -/
partial def Walk.paramsOnly (H : Expr) : MetaM Bool := do
  let H ← whnf H
  if H.isAppOf ``Hyps.nil then return true
  if H.isAppOf ``Hyps.all || H.isAppOf ``Hyps.bind then
    let args := H.getAppArgs
    -- `all H x p` and `bind H m x t`: `H` follows the contract and the scopes
    return ← Walk.paramsOnly args[3]!
  return false

/-- One silent step on the goal `g`: the goals it leaves, `none` where there
is none to take. -/
def Walk.silentStep (g : MVarId) : MetaM (Option (List MVarId)) := do
  let ty ← g.getType
  unless ty.isAppOf ``Proves do return none
  let φ ← whnf (← instantiateMVars ty.appArg!)
  let H := ty.appFn!.appArg!
  let step : Option Lean.Name ←
    if φ.isAppOf ``Fml.bind then pure (some ``Proves.bindIntro)
    else if φ.isAppOf ``Fml.all && !Fml.isExplicitAll φ && (← Walk.paramsOnly H) then
      pure (some ``Proves.allIntro)
    else if φ.isAppOf ``Fml.upd then
      let args := φ.getAppArgs
      if ← Walk.popsOnly args[args.size - 2]! then pure (some ``Proves.updIntro) else pure none
    else pure none
  let some c := step | return none
  return some (← g.apply (← mkConstWithFreshMVarLevels c))

@[tactic coreSilent]
def evalCoreSilent : Tactic := fun _ => do
  if let some g := (← getUnsolvedGoals).head? then
    unless (← instantiateMVars (← g.getType)).isAppOf ``Proves do
      throwError "core_silent: not a scoped sequent"
  for _ in [0:256] do
    let some g := (← getUnsolvedGoals).head? | return
    let some gs ← Walk.silentStep g | return
    replaceMainGoal gs

/-- `core_params`: on a scoped goal, the formula's parameters into the
context (`allIntro`, `bindIntro`), up to an explicit `∀` (`cdl!`'s mark,
decision 28), whose line the walk writes (`apply allRight`). -/
syntax (name := coreParams) "core_params" : tactic

@[tactic coreParams]
def evalCoreParams : Tactic := fun _ => do
  for _ in [0:256] do
    let some g := (← getUnsolvedGoals).head? | return
    let ty ← instantiateMVars (← g.getType)
    unless ty.isAppOf ``Proves do return
    let φ ← whnf ty.appArg!
    let c ← if φ.isAppOf ``Fml.bind then pure ``Proves.bindIntro
      else if φ.isAppOf ``Fml.all && !Fml.isExplicitAll φ then pure ``Proves.allIntro
      else return
    replaceMainGoal (← g.apply (← mkConstWithFreshMVarLevels c))

/-- `core_skip empty`, `core_skip allIntro`: the line where the scoped
strategy already took its step, after the silent steps: `empty` where no
modality is left at the head (a rule that leaves no statement went past the
frames), `allIntro` where the context holds the parameters only and no `∀`
is left (`Proves.valid` and `core_silent` bound them).  It fails anywhere
else, so the line is checked: `apply empty` before a statement is refused. -/
syntax (name := coreSkip) "core_skip " ident : tactic

@[tactic coreSkip]
def evalCoreSkip : Tactic := fun stx => do
  evalTactic (← `(tactic| core_silent))
  let some g := (← getUnsolvedGoals).head? | throwError "no goals"
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOf ``Proves do throwError "core_skip: not a scoped sequent"
  let φ ← whnf ty.appArg!
  let H := ty.appFn!.appArg!
  -- the macros below write the kind under their own scopes
  match stx[1].getId.eraseMacroScopes with
  | `empty =>
    if φ.isAppOf ``Fml.modal then
      throwError "apply empty: a modality is left, with a statement to run"
  | `allIntro =>
    unless (← Walk.paramsOnly H) && !φ.isAppOf ``Fml.all do
      throwError "apply allIntro: no quantifier at the head"
  | _ => throwUnsupportedSyntax

/-- `core_tag a b …`: name the first goals `a`, `b`, …, for `case` (a rule's
goals named as its premises are, today's names). -/
syntax (name := coreTag) "core_tag" (ppSpace ident)+ : tactic

@[tactic coreTag]
def evalCoreTag : Tactic := fun stx => do
  let names := stx[1].getArgs.map (·.getId)
  let gs ← getUnsolvedGoals
  for g in gs, n in names do g.setTag n

/-- `core_rule c r`: the scoped rule `c` (`Proves.update`, …) by the
taclet `r`, solkey's or Lean's, then the silent steps on each goal it leaves.
The taclet is elaborated last (`by exact`), so that its side conditions are
decided once its schema variables are read off the goal; `core_rule2` for a rule with KeY's two
goals, `thn` and `els`. -/
syntax (name := coreRule) "core_rule " ident ppSpace term:max : tactic
@[inherit_doc coreRule]
syntax (name := coreRule2) "core_rule2 " ident ppSpace term:max : tactic

/-- Seed the loop mode from the named rule's find, then check its whole type. -/
syntax (name := coreWhileUnwind) "core_while_unwind" : tactic

@[tactic coreWhileUnwind]
def evalCoreWhileUnwind : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let goal ← instantiateMVars (← g.getType)
  let_expr Taclet _ _ _ _ _ s _ := goal | throwUnsupportedSyntax
  let ctor := mkConst ``Taclet.whileUnwind
  let (xs, _, ty) ← forallMetaTelescope (← inferType ctor)
  let_expr Taclet _ _ _ _ _ f _ := ty | throwUnsupportedSyntax
  unless ← matchFind f (← whnfD s) [] do throwError "whileUnwind: find does not match"
  unless ← isDefEq ty goal do throwError "whileUnwind: premise does not match"
  g.assign (mkAppN ctor xs)
  replaceMainGoal []

macro_rules
  | `(tactic| core_rule $c .whileUnwind) =>
    `(tactic| core_silent;
      (refine $c (by exact Solidity.Taclet.step_eq (by core_while_unwind)) ?_) <;> core_silent)
  | `(tactic| core_rule $c $r) =>
    `(tactic| core_silent; first
      | (refine $c (by exact Solidity.Taclet.step_eq $r) ?_) <;> core_silent
      | (refine $c (by exact Solidity.LeanTaclet.toStep $r) ?_) <;> core_silent)
  | `(tactic| core_rule2 $c $r) =>
    `(tactic| core_silent; first
      | ((refine $c (by exact Solidity.Taclet.step_eq $r) ?_ ?_; core_tag thn els)
          <;> core_silent)
      | ((refine $c (by exact Solidity.LeanTaclet.toStep $r) ?_ ?_; core_tag thn els)
          <;> core_silent))

/-- `core_inv d`: the scoped invariant rule by the premise `d`, its goals
`init`, `thn` and `els`. -/
syntax (name := coreInv) "core_inv " term:max : tactic

macro_rules
  | `(tactic| core_inv $d) =>
    `(tactic| (refine Solidity.Proves.inv (by exact $d) ?_ ?_ ?_; core_tag init thn els)
      <;> core_silent)

namespace Scoped

scoped macro_rules
  | `(tactic| apply update $r:term) =>
    `(tactic| first
      | core_rule Solidity.Proves.update $r
      | core_rule Solidity.Proves.updates $r)
  | `(tactic| apply unfold $r:term) =>
    `(tactic| first
      | core_rule Solidity.Proves.unfold $r
      | core_rule Solidity.Proves.bind $r
      | core_rule Solidity.Proves.inline $r)
  | `(tactic| apply unfoldLean $r:term) =>
    `(tactic| first
      | core_rule Solidity.Proves.unfold $r
      | core_rule Solidity.Proves.bind $r
      | core_rule Solidity.Proves.inline $r)
  | `(tactic| apply doneLean $r:term) =>
    `(tactic| first
      | core_rule Solidity.Proves.done $r)
  | `(tactic| apply checkLean $r:term) =>
    `(tactic| first
      | core_rule2 Solidity.Proves.check $r)
  | `(tactic| apply unfoldStep) =>
    `(tactic| first
      | (core_silent; apply Solidity.Proves.unfold rfl) <;> core_silent
      | (core_silent; apply Solidity.Proves.bind rfl) <;> core_silent
      | (core_silent; apply Solidity.Proves.inline rfl) <;> core_silent)
  | `(tactic| apply split $r:term) =>
    `(tactic| first
      | core_rule2 Solidity.Proves.split $r
      | core_rule2 Solidity.Proves.guardedUpdates $r)
  | `(tactic| apply splitBox $r:term) =>
    `(tactic| first
      | core_rule2 Solidity.Proves.split $r
      | core_rule2 Solidity.Proves.guardedUpdates $r)
  | `(tactic| apply done $r:term) =>
    `(tactic| first
      | core_rule Solidity.Proves.done $r)
  | `(tactic| apply Proves.check $r:term) =>
    `(tactic| first
      | core_rule2 Solidity.Proves.check $r)
  | `(tactic| apply cases $r:term) =>
    `(tactic| first
      | (core_silent; refine Solidity.Proves.cases (by exact Solidity.Taclet.step_eq $r) rfl ?_ ?_)
      | (core_silent; refine Solidity.Proves.cases (by exact Solidity.LeanTaclet.toStep $r) rfl ?_ ?_))
  | `(tactic| apply branches $r:term) =>
    `(tactic| first
      | (core_silent; refine Solidity.Proves.branches (by exact Solidity.Taclet.step_eq $r) rfl ?_)
      | (core_silent; refine Solidity.Proves.branches (by exact Solidity.LeanTaclet.toStep $r) rfl ?_))
  | `(tactic| apply invBox $r:term) =>
    `(tactic| first
      | (core_silent; core_inv (Solidity.Taclet.step_eq $r))
      | (core_silent; core_inv (Solidity.LeanTaclet.toStep $r)))
  | `(tactic| apply invLean $r:term) =>
    `(tactic| first
      | (core_silent; core_inv (Solidity.Taclet.step_eq $r))
      | (core_silent; core_inv (Solidity.LeanTaclet.toStep $r)))
  | `(tactic| apply updIntro) =>
    `(tactic| first
      | (core_silent; apply Solidity.Proves.updIntro) <;> core_silent)
  | `(tactic| apply impRight) =>
    `(tactic| first
      | (core_silent; apply Solidity.Proves.intro) <;> core_silent)
  | `(tactic| apply allRight) =>
    `(tactic| first
      | (core_silent; apply Solidity.Proves.allIntro) <;> core_silent)
  | `(tactic| apply emptyModality) =>
    `(tactic| first
      | (core_silent; apply Solidity.Proves.empty) <;> core_silent
      | core_skip empty)
  | `(tactic| apply empty) =>
    `(tactic| first
      | (core_silent; apply Solidity.Proves.empty) <;> core_silent
      | core_skip empty)
  | `(tactic| apply intro) =>
    `(tactic| first
      | (core_silent; apply Solidity.Proves.intro) <;> core_silent)
  | `(tactic| apply allIntro) =>
    `(tactic| first
      | (core_silent; apply Solidity.Proves.allIntro) <;> core_silent
      | core_skip allIntro)
  | `(tactic| apply Proves.valid) =>
    `(tactic| first
      | (refine Solidity.Proves.valid (R := RuleSet.all) ?_; core_params))

end Scoped

end Solidity
