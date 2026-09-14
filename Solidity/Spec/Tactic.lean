import Solidity.EvalBattery
import Solidity.Spec.Assertion

/-!
# `sol_spec`: discharging SolSpec obligations

`sol_wp` (`Wp/Verifier.lean`) proves a judgment from *one concrete
store*: every value in the state is a literal, so the interpreter
reduces to a verdict and the postcondition to a ground Boolean. A
specification is not like that — `@custom:requires`/`@custom:ensures`
quantify over every state satisfying the precondition, so the front-end
builds the initial state out of *Lean variables* (`SVal.int balSender`
for a `uint256 balSender`) and the obligation is universally quantified
over them.

That one change is what `sol_spec` has to absorb, and it is smaller than
it looks. The *shape* of the state stays concrete — root names, struct
fields, statement forms, types are all literals — so
`sol_eval_battery` still reduces `execStmt` all the way down; only the
leaves stay symbolic. Two consequences:

* a statement whose effect is a pure state update (`balSender -= amount`)
  reduces to a state literal with an open arithmetic term in it, and the
  step is peeled exactly as `sol_wp` peels it, through the total
  `vc_stmt_eval` rewrite;
* a statement that *branches* on a symbolic value (`require(amount <=
  balSender)`, `if (…)`) reduces to an `ite`/`match` the interpreter
  cannot settle. There `sol_spec` does what `sol_wp` never had to:
  `split`, and carry both branches forward. The branch conditions become
  hypotheses, which is exactly what the arithmetic finisher needs.

The residual goals are then linear arithmetic over `Int` (`omega`),
decidable ground facts (`decide`), or hypotheses (`assumption`). The
finisher is deliberately run under `try`: a goal `sol_spec` cannot close
is *left open*, so Lean reports "unsolved goals" with the real proof
state rather than an opaque tactic failure — which is what the VS Code
extension surfaces on the offending `@custom:` line.

Escape hatch: a clause tagged `@custom:tactic <tac>` in the source is
emitted with `<tac>` in place of `sol_spec`, so a specification that
outruns the automation can still be proved by hand.
-/

namespace Solidity
namespace Spec

open Lean Semantics

set_option maxHeartbeats 4000000

/-! ## The evaluation battery

`sol_eval_battery` (from `EvalBattery.lean`) normalizes interpreter
terms; assertions add one more layer — the `Spec` readers and the
range/quantifier wrappers. `sol_spec_battery` is the two together, and
it is what both the step and the finisher call. -/

/-- The `Spec`-side simp set: assertion readers, the specification
connectives, and enough of the interpreter to settle a *read*.

Two things about it are deliberate.

It runs `at *`, not just on the goal. Hypotheses carry specifications
too: the range hypotheses arrive as `inRange 0 255 x`, which `omega`
cannot use until it is `0 ≤ x ∧ x ≤ 255`, and a `solspec!{…}` precondition
arrives as `Spec.valInt s0 …  ≤ Spec.valInt s0 …`, which is a stalled
interpreter call until the read is reduced. Leaving either folded is the
difference between an obligation that closes and one that does not.

It therefore repeats the *read* half of `sol_eval_battery` — which is a
`simp` call on the goal, with no location to point elsewhere. The
duplication buys the `at *`; the write half (`execStmt`, `execAssign`,
the copy helpers) stays in `sol_eval_battery`, which the driver runs on
the goal, because only the goal ever contains a statement. -/
macro "sol_spec_unfold" : tactic =>
  `(tactic|
    simp only [Spec.totalVC, Spec.partialVC, Spec.Obligation,
               Spec.RevertObligation, Spec.modifiesOnly, Spec.frameEntries,
               Spec.svalAt, Spec.intAt, Spec.boolAt, Spec.lenAt,
               Spec.isIntAt, Spec.localInt, Spec.localBool, Spec.netAt,
               Spec.valInt, Spec.valBool,
               Spec.inRange, Spec.forallIn, Spec.existsIn,
               -- Reading a state: the interpreter's evaluation path.
               Semantics.evalValue, Semantics.evalInt, Semantics.readM,
               Semantics.resolveS, Semantics.resolveMBase,
               Semantics.resolveLoc,
               Semantics.State.findStorage, Semantics.State.getEnv,
               Semantics.State.getNet, Semantics.State.getObj,
               Semantics.SVal.find, Semantics.lookupBy,
               Semantics.SVal.asValue, Semantics.MVal.asValue,
               Semantics.Value.asInt, Semantics.Value.asBool,
               Semantics.applyBinOp, Semantics.applyUnOp,
               bind, Except.bind, pure, Except.pure,
               -- The smart constructors a specification path expands to.
               SoliditySyntax.rootExpr, SoliditySyntax.varExpr,
               SoliditySyntax.fieldExpr, SoliditySyntax.indexExpr,
               SoliditySyntax.intLitExpr, SoliditySyntax.globalExpr,
               SoliditySyntax.aliasExpr, SoliditySyntax.aliasKind,
               SoliditySyntax.fieldFor, SoliditySyntax.fieldForName,
               SoliditySyntax.fieldTy, SoliditySyntax.originFor,
               SoliditySyntax.storageOriginFor,
               SoliditySyntax.localStorageTyFor, SoliditySyntax.declTy,
               SoliditySyntax.typedVarTy, SoliditySyntax.indexElemTy,
               SoliditySyntax.binopExpr, SoliditySyntax.unopExpr,
               SoliditySyntax.ternaryExpr,
               StandardExample.stackUint, StandardExample.stackBool,
               StandardExample.memoryPerson, StandardExample.personTy,
               StandardExample.accountTy, StandardExample.tokenTy,
               StandardExample.personRef, StandardExample.accountRef,
               StandardExample.tokenRef, StandardExample.accountField,
               StandardExample.tokenField, StandardExample.ageField,
               StandardExample.balanceField, StandardExample.valueField,
               WrappedExpr.kind, WrappedExpr.ty,
               Typed.WrappedExpr.kind, Typed.WrappedExpr.ty,
               Ty.isPrimitive, Ty.indexElemTy,
               Field.name, Field.primitive, Field.identity,
               BinOp.retTy, UnOp.retTy] at *)

/-- Interpreter normalization plus assertion unfolding. Both halves are
`try`ed: on a goal that is already fully symbolic (`0 ≤ balSender - amount`,
say) neither has anything to do, and a `simp` that makes no progress is a
failure, not a no-op.

The battery runs `at *` for the same reason `sol_spec_unfold` does: a
`solspec!` precondition lands in the context as a stalled `evalValue`,
and `omega` cannot see an arithmetic fact through a `match`. -/
macro "sol_spec_battery" : tactic =>
  `(tactic| (try sol_spec_unfold; try sol_eval_battery at *))

/-- The shape `checkArith` leaves in a branch hypothesis: a guarded
success. `split` on the enclosing verdict match records the scrutinee
as `(if C then .ok a else .error e) = .ok v` (or `= .error e'`), and
until the `if` is resolved `omega` sees nothing. These two rewrite the
equation into the guard proposition it encodes. -/
theorem ite_ok_eq_ok_iff {c : Prop} [Decidable c] {α : Type}
    {a v : α} {e : Semantics.Halt} :
    ((if c then (Except.ok a : Semantics.Res α) else .error e) = .ok v)
      ↔ c ∧ a = v := by
  split <;> simp_all

theorem ite_ok_eq_error_iff {c : Prop} [Decidable c] {α : Type}
    {a : α} {e e' : Semantics.Halt} :
    ((if c then (Except.ok a : Semantics.Res α) else .error e)
        = .error e') ↔ ¬ c ∧ e = e' := by
  split <;> simp_all

/-- Turn the Boolean residue the interpreter leaves behind into the
propositions `omega` reasons about, over the goal *and* the branch
hypotheses `split` introduced.

The `injEq` lemmas are the load-bearing ones. A `split` on a guard
leaves `Value.bool (decide (a ≤ b)) = Value.bool true`, and until the
constructor is peeled off, `decide_eq_true_eq` has nothing to match and
`omega` sees an opaque equation between two `Value`s rather than the
arithmetic fact it needs. The `ite_ok_*` pair does the same for the
checked-arithmetic guards `checkArith` leaves in branch hypotheses. -/
macro "sol_spec_decide" : tactic =>
  `(tactic|
    try simp only [Semantics.PrimVal.bool.injEq, Semantics.PrimVal.int.injEq,
                   Spec.ite_ok_eq_ok_iff, Spec.ite_ok_eq_error_iff,
                   decide_eq_true_eq, decide_eq_false_iff_not,
                   Bool.not_eq_true, Bool.and_eq_true, Bool.or_eq_true,
                   ne_eq] at *)

/-! ## Peeling one annotated step -/

/-- Reduce `vcNext`/`revertsNext` on the verdict just computed.

Order matters, and not in the obvious direction. When the verdict is a
`match` on a value the interpreter could not settle — `require` on a
symbolic guard — `split` turns it into one constructor verdict per
branch, and *then* `simp only [vcNext]` reduces each. Doing the `simp`
first instead is actively wrong: with no equation to apply it
delta-unfolds `vcNext` into a raw matcher on `Res State`, and `split`
then splits *that*, generalizing the concrete state into an opaque
variable the interpreter can no longer evaluate at.

So: `split` first, falling back to the plain reduction when the verdict
is already a constructor and there is nothing to split. -/
macro "sol_spec_reduce" : tactic =>
  `(tactic|
    (first
      | (split <;> (try simp only [Spec.vcNext, Spec.revertsNext]))
      | (try simp only [Spec.vcNext, Spec.revertsNext])))

/-- One step of the driver: peel an annotated statement through the
total `vc_stmt_eval` rewrite (verdict computed by `sol_exec_eval`, as in
`sol_wp`), or consume a ghost `assert`/`assume`, or open the
postcondition's structure (`∧` splits into goals, `→`/`∀` introduces).
Fails when none applies, which is how the `repeat` driver terminates. -/
macro "sol_spec_step" : tactic =>
  `(tactic|
    ((first
        | rw [Spec.vc_stmt_eval (by sol_exec_eval)]
        | rw [Spec.revertsVC_stmt_eval (by sol_exec_eval)]
        | rw [Spec.vc_assert]
        | rw [Spec.vc_assume]
        | rw [Spec.revertsVC_assert]
        | rw [Spec.revertsVC_assume]
        | rw [Spec.vc_nil]
        | apply And.intro
        | intro _);
     sol_spec_reduce))

/-- Close a leaf goal: normalize the assertion readers against the final
state literal, turn Boolean residue into propositions, then try the
cheap closers in increasing order of cost. `omega` is the workhorse —
after normalization a Solidity postcondition is linear integer
arithmetic over the symbolic inputs. -/
macro "sol_spec_finish" : tactic =>
  `(tactic|
    (try intros;
     sol_spec_battery;
     sol_spec_decide;
     -- The checked-arithmetic guards arrive as conjunctions carrying a
     -- `Value.int … = v` capture of the checked result; split them and
     -- substitute so the readers below reduce over the actual value.
     try (repeat cases ‹_ ∧ _›);
     try subst_vars;
     first
       | rfl
       | trivial
       | assumption
       | omega
       | decide
       -- `done` matters: a `simp_all` that makes progress without
       -- closing must fall through to the arithmetic pass, not count
       -- as success and strand the goal.
       | (simp_all; done)
       | (try simp_all; omega)))

/-! ## The driver -/

/-- Symbolically execute to exhaustion, then attempt every leaf.

The opening `simp only` is not optional: `totalVC`/`partialVC` are
abbreviations and `Obligation` a definition, and `rw` matches through
neither — with the goal still stated in those terms, `vc_stmt_eval` finds
no `vc` to rewrite and *not one step fires*. Unfolding them first is what
turns the goal into the `vc` the driver knows how to peel.

The finisher runs under `try` so an unclosable goal survives as an
"unsolved goals" error carrying the real proof state. -/
macro "sol_spec_run" : tactic =>
  `(tactic|
    (try simp only [Spec.totalVC, Spec.partialVC, Spec.Obligation,
                    Spec.RevertObligation];
     repeat (any_goals sol_spec_step);
     all_goals (try sol_spec_finish)))

/--
`sol_spec` proves a SolSpec obligation — a `Spec.totalVC` /
`Spec.partialVC` / `Spec.revertsVC` goal — by symbolic execution of the
annotated body followed by arithmetic.

`sol_spec [s₀, body]` first unfolds the named definitions; the front-end
always passes the generated state and body definitions, so the
interpreter sees literals.
-/
syntax (name := solSpec) "sol_spec" (" [" term,* "]")? : tactic

macro_rules
  | `(tactic| sol_spec) => `(tactic| sol_spec_run)
  | `(tactic| sol_spec [$ts,*]) => do
      -- `simp only [...]` takes `simpLemma`s, not bare terms; rebuild
      -- each element at that kind before splicing.
      let lemmas <- ts.getElems.mapM fun t =>
        `(Lean.Parser.Tactic.simpLemma| $t:term)
      `(tactic| (simp only [$lemmas,*]; sol_spec_run))

end Spec
end Solidity
