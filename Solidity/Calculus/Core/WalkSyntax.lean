import Solidity.Calculus.Core.Derive
import Solidity.Calculus.Core.Surface
import Solidity.Calculus.Symex

/-!
# Today's walk on a scoped goal

Under `open scoped Solidity.Core.Surface` a walk keeps today's text: one
`apply` per rule, the rule named as solkey names it (`apply update
.storageFieldWriteSave`, `apply unfold .localValueDeclInitDrop`, `apply
empty`, `refine close ?_`, …).  On a scoped goal (`Core.Proves`) each line
is the scoped rule of the same kind, its premise the named taclet's
(`Taclet.step_eq`, `LeanTaclet.toStep`); on today's goal it is today's.

Where the scoped calculus takes a step today's names otherwise:

* `apply unfold r` is `Core.Proves.unfold`, `bind` (a declaration with an
  initializer: the local joins the context, `localValueDeclInitDrop`) or
  `inline` (a call's frame dropped under its returns), whichever `r`'s premise is;
  `apply unfoldRule (Stmt.step _ _ _).rule` (a read into a hole, whose line
  `apply` cannot match) is the strategy's premise by `rfl`;
* the steps KeY does not show are taken after each rule, silently
  (`core_silent`): a scope's end (an update that only pops) and a hidden
  binder join the context;
* `apply empty` (`emptyModality`) is a step only where a modality is left
  with no statement: a rule that leaves none goes on into the rest or past
  the frames (Gate G0, condition 6), so after a last statement it does
  nothing;
* `apply Proves.valid` binds the formula's parameters (`∀`, `cdl!`) with
  `allRight` at once, as today's walk leaves them free.

Each reading is a `scoped macro_rules` of the namespace `Solidity.Core.Surface`,
tried before today's `apply`.
-/

namespace Solidity.Core

open Lean Elab Tactic Meta

/-- The update only pops (a scope's end), decided on the term. -/
def Walk.popsOnly (U : Expr) : MetaM Bool := do
  let b ← whnfD (← mkAppM ``Upd.popsOnly #[U])
  return b.isConstOf ``Bool.true

/-- `core_silent`: on a scoped goal, the steps KeY does not show: a scope's
end (an update that only pops) and a hidden binder join the context. -/
syntax (name := coreSilent) "core_silent" : tactic

/-- One silent step on the goal `g`: the goals it leaves, `none` where there
is none to take. -/
def Walk.silentStep (g : MVarId) : MetaM (Option (List MVarId)) := do
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOf ``Core.Proves do return none
  let φ ← whnf ty.appArg!
  let step : Option Lean.Name ←
    if φ.isAppOf ``Fml.bind then pure (some ``Proves.bindIntro)
    else if φ.isAppOf ``Fml.upd then
      let args := φ.getAppArgs
      if ← Walk.popsOnly args[args.size - 2]! then pure (some ``Proves.updIntro) else pure none
    else pure none
  let some c := step | return none
  return some (← g.apply (← mkConstWithFreshMVarLevels c))

@[tactic coreSilent]
def evalCoreSilent : Tactic := fun _ => do
  for _ in [0:256] do
    let some g := (← getUnsolvedGoals).head? | return
    let some gs ← Walk.silentStep g | return
    replaceMainGoal gs

/-- `core_rule c r`: the scoped rule `c` (`Core.Proves.update`, …) by the
taclet `r`, solkey's or Lean's, then the silent steps on each goal it leaves.
The taclet is elaborated last (`by exact`), so that its side conditions are
decided once its schema variables are read off the goal; `core_rule2` for a rule with KeY's two
goals, `thn` and `els`. -/
syntax (name := coreRule) "core_rule " ident ppSpace term:max : tactic
@[inherit_doc coreRule]
syntax (name := coreRule2) "core_rule2 " ident ppSpace term:max : tactic

macro_rules
  | `(tactic| core_rule $c $r) =>
    `(tactic| first
      | (refine $c (by exact Solidity.Core.Taclet.step_eq $r) ?_) <;> core_silent
      | (refine $c (by exact Solidity.Core.LeanTaclet.toStep $r) ?_) <;> core_silent)
  | `(tactic| core_rule2 $c $r) => do
    -- the goals named as the rule's premises are, unhygienically, for `case`
    let thn := mkIdent `thn
    let els := mkIdent `els
    `(tactic| first
      | (refine $c (by exact Solidity.Core.Taclet.step_eq $r) ?$thn ?$els) <;> core_silent
      | (refine $c (by exact Solidity.Core.LeanTaclet.toStep $r) ?$thn ?$els) <;> core_silent)

namespace Surface

scoped macro_rules
  | `(tactic| apply update $r:term) =>
    `(tactic| first
      | apply _root_.Solidity.Proves.update $r
      | core_rule Solidity.Core.Proves.update $r)
  | `(tactic| apply unfold $r:term) =>
    `(tactic| first
      | apply _root_.Solidity.Proves.unfold $r
      | core_rule Solidity.Core.Proves.unfold $r
      | core_rule Solidity.Core.Proves.bind $r
      | core_rule Solidity.Core.Proves.inline $r)
  | `(tactic| apply unfoldRule $r:term) =>
    `(tactic| first
      | apply _root_.Solidity.Proves.unfoldRule $r
      | (apply Solidity.Core.Proves.unfold rfl) <;> core_silent
      | (apply Solidity.Core.Proves.bind rfl) <;> core_silent
      | (apply Solidity.Core.Proves.inline rfl) <;> core_silent)
  | `(tactic| apply split $r:term) =>
    `(tactic| first
      | apply _root_.Solidity.Proves.split $r
      | core_rule2 Solidity.Core.Proves.split $r)
  | `(tactic| apply splitBox $r:term) =>
    `(tactic| first
      | apply _root_.Solidity.Proves.splitBox $r
      | core_rule2 Solidity.Core.Proves.split $r)
  | `(tactic| apply done $r:term) =>
    `(tactic| first
      | apply _root_.Solidity.Proves.done $r
      | core_rule Solidity.Core.Proves.done $r)
  | `(tactic| apply Proves.check $r:term) =>
    `(tactic| first
      | apply _root_.Solidity.Proves.check $r
      | core_rule2 Solidity.Core.Proves.check $r)
  | `(tactic| apply empty) =>
    `(tactic| first
      | apply _root_.Solidity.Proves.empty
      | (apply Solidity.Core.Proves.empty) <;> core_silent
      | core_silent)
  | `(tactic| apply intro) =>
    `(tactic| first
      | apply _root_.Solidity.Proves.intro
      | (apply Solidity.Core.Proves.intro) <;> core_silent)
  | `(tactic| apply allIntro) =>
    `(tactic| first
      | apply _root_.Solidity.Proves.allIntro
      | (apply Solidity.Core.Proves.allIntro) <;> core_silent)
  | `(tactic| apply Proves.valid) =>
    `(tactic| first
      | apply _root_.Solidity.Proves.valid
      | (refine Solidity.Core.Proves.valid (R := RuleSet.all) ?_; repeat (first | refine Solidity.Core.Proves.allIntro ?_ | refine Solidity.Core.Proves.bindIntro ?_)))
  | `(tactic| refine close ?_) =>
    `(tactic| first
      | refine _root_.Solidity.Proves.close ?_
      | refine Solidity.Core.Proves.close [] rfl List.nodup_nil ?_)

end Surface

end Solidity.Core
