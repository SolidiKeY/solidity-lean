import Solidity.Calculus.SurfaceNotation
import Solidity.Calculus.TacticSyntax
import Solidity.Calculus.CloseLemmas
import Solidity.Calculus.CloseNonlin
import Solidity.Calculus.CloseAll

/-!
# Closing the first-order goal: `sol_close`

`sol_symex` leaves `{U₁} … {Uₙ} φ` with no modality in it.  Its updates are
not rewritten away, as mini-solkey's `Ch14_Updates` does: a term here *is* a
reading of the typed state (`Tm.eval`), so applying an update in an
arbitrary state `σ` is computing it, and what remains is a statement about
what the storage, memory and locals read on a `σ` nobody knows.
`sol_close` proves that statement with contextual `simp` passes over the
`close_rw_s` set, then `omega` or `grind` for the arithmetic.

This module declares the tactic syntax; every step's elaborator is
`Calculus/CloseScoped.lean`'s, on a scoped leaf (`Close.scopedGoal`), the
scoped formula read with `close_rw_s`, its parameters at their types.  The
untyped elaborators and their `close_rw` set went at W10.5.1
(`docs/intrinsic.md`): no leaf is untyped since W9.5a.

**Weakest preconditions.**  `Modality.wp m x P` is `P` of what `x` returns,
or `m.onHalt` when it halts.  Pushed through the binds of the evaluators
(`Modality.wp_bind`), it turns the goal into a nest of `∀ τ, x = .ok τ → …`
(the box) or `∃ τ, x = .ok τ ∧ …` (the diamond).  A `split` on the
unfolded `match`es does not get there: it splits the outermost one only,
and leaves the evaluator's inner matches in hypotheses.

What does not close, and why:

* a write under the diamond at a path with an index: the index check may
  revert, and the leaf does not say it does not.  At a path with no index
  (`⟨ alice.age = 1; ⟩ true`) the write does not halt and closes as under
  the box (`Calculus/CloseFrame.lean`);
* two symbolic keys the formula does not tell apart: there is no case
  split on `k = j`, so `[ balances[k] = 5; balances[j] = 6; ] balances[k] == 5`
  stays open (it is false at `k = j`);
* two memory objects: nothing says that two allocations are different
  objects, since `⊨ᶠ` includes states whose heap already holds an object at
  `nextId`;
* a read of an array a push wrote, the array known only by its shape:
  `[ uint n = values.length; values.push(42); ] values.length == n + 1`
  stays open, since `Calculus/CloseFrame.lean` has no clause for a push
  (the length it leaves, the slot it writes, the frame beside it), so the
  typed `Storage.push` is not read further
  (`Examples/Tactics/CallOperands.lean` pins it open, and writes its push rows as
  chains for this);
* a default read out of a fresh memory object (`Person memory m;
  uint x = m.age;`): the default of a struct type (`SVal.dflt`) is
  fuelled by the type's rank, which `simp` does not unfold.
-/

namespace Solidity

/-! ## The tactic -/

namespace Close

open Lean Elab Tactic Meta in
/-- Whether the main goal is a scoped leaf's: it or its context reads a
typed state (`Solidity.State`, `Fml.Valid`, `holds`), or what the scoped closer
leaves of one past an update (`CloseS.Landed`, `CloseS.LandedAll`: a
premise `Nonempty (Landed …)` once the rest reads no landed state).  `Calculus/CloseScoped.lean`'s steps run on such a goal only,
reading it with `close_rw_s`. -/
def scopedGoal : TacticM Bool := withMainContext do
  let names : List Lean.Name :=
    [`Solidity.State, `Solidity.Fml.Valid, `Solidity.holds, `Solidity.CloseS.Landed,
     `Solidity.CloseS.LandedAll]
  let hit (e : Expr) : Bool := (e.find? fun x => x.isConst && names.contains x.constName!).isSome
  if hit (← instantiateMVars (← getMainTarget)) then return true
  for d in ← getLCtx do
    if !d.isImplementationDetail && hit (← instantiateMVars d.type) then return true
  return false

end Close

/-- The first pass of `sol_close`: evaluate, and name every write with what
is known of it. -/
syntax "sol_close_eval" : tactic

/-- The second: each premise in scope for what follows it, so that the facts
about a write rewrite the reads after it.  Nothing is named bare yet: a
result a later fact decides (the array a push lands on) is decided first. -/
syntax "sol_close_facts" : tactic

/-- The third: what is left is named bare, under the box. -/
syntax "sol_close_reads" : tactic

/-- `sol_close_reads` on the goal and every hypothesis. -/
syntax "sol_close_reads_all" : tactic

/-- An equation left as Theory values (`Tm.denote`) that reads a storage
alias local (`Tm.pvP`, which no `Tm.agreeB` admits: an unset alias reads
`dangling`): each side read in the Theory at the path the alias holds
(`CloseS.denote_len`, `CloseS.denote_pvP`), so an `ensures` the frame below
gave closes the frame's own.  Fails where no such equation is left. -/
syntax "sol_close_denote" : tactic

/-- `sol_close_unwrap` with no equation strengthened: an equation that reads
a storage alias stays a Theory equation (`Fml.Valid.of_evalEqsTh`). -/
syntax "sol_close_unwrap_th" : tactic

/-- Fails unless an equation of the leaf reads a storage alias (`Tm.pvP`):
an `ensures` of a returned alias, assumed or owed. -/
syntax "sol_close_alias_guard" : tactic

/-- `sol_close` on a leaf whose equations read a storage alias
(`sol_close_alias_guard`): read in the Theory (`sol_close_unwrap_th`), the
alias at the path it holds (`sol_close_denote`).  Fails where it does not
close the leaf. -/
syntax "sol_close_alias" : tactic

/-- A value read back, `∃ a, t = a.val ∧ φ a` with `t` a literal: the
witness `t`, in range by `decide`.  Fails on any other goal. -/
syntax "sol_close_witness" : tactic

/-- Expose typed ranges and existential read witnesses before the final arithmetic pass. -/
syntax (name := tacticSol_close_enrich) "sol_close_enrich" : tactic

/-- `sol_close`'s first step: a scoped leaf (`Fml.Valid ψ`) read as `holds`
in every typed state (`Calculus/CloseScoped.lean`); any other goal is
left as it is. -/
syntax "sol_close_unwrap" : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| sol_close_unwrap) => pure ()

/-- Open landed-state binders after the scoped closer has simplified their reads.
The implementation is registered in `CloseScoped`, where the lemma exists. -/
syntax "sol_close_landed" : tactic

/-- Instantiate quantified premises after opening the leaf's later binders.
The implementation is registered by `CloseScoped`. -/
syntax "sol_close_quantified" : tactic

/-- `sol_skip_after n tac`: `tac` with `n` thousand heartbeats of its own;
past them, or where it fails, nothing is done.  A saturation that grows
past its budget is skipped: what it would add is often not needed. -/
syntax "sol_skip_after " num tacticSeq : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| sol_skip_after $n $tac) => do
    let saved ← saveState
    -- never past what the declaration's own limit has left (`Budget.within`)
    let ok ← tryCatchRuntimeEx (Budget.within n.getNat do
        Term.withoutErrToSorry <| withoutRecover <| evalTactic tac
        pure true) (fun _ => pure false)
    unless ok do saved.restore

/-- `sol_within n tac`: `tac` with `n` thousand heartbeats of its own,
never past what the declaration's limit has left (`Budget.within`); past
them, or where `tac` fails, it fails with the goal as it was, so a `first`
goes on to its next alternative. -/
syntax "sol_within " num tacticSeq : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| sol_within $n $tac) => do
    let r ← Budget.bounded n.getNat
      (Term.withoutErrToSorry <| withoutRecover <| evalTactic tac)
    if r.isNone then throwError "sol_within: failed, or past {n.getNat}000 heartbeats"

/-- An `Option` read a leaf asks of as `∃ a, t = some a ∧ φ a` (a length, a
lookup), in the goal or a premise: each such `t` generalized over both and
split, its `none` contradicting the premise that reads it, its `some a`
taking each `∃` to its `φ a` (`exists_eq_left'`): a premise's witness is then
the goal's.  At most 8 reads; fails where there is none. -/
syntax "sol_close_some_cases" : tactic

namespace Close

open Lean Meta in
/-- The `t` of each `∃ a, t = some a ∧ _` in `e`, at most `64` of them, over
at most `20000` nodes (a leaf's terms are shared, not walked twice per
occurrence). -/
partial def someReads (e : Expr) : StateM (Array Expr × Nat) Unit := do
  let (acc, n) ← get
  if n == 0 || acc.size ≥ 64 then return
  set (acc, n - 1)
  if e.isAppOfArity ``Exists 2 then
    if let .lam _ _ b _ := e.appArg! then
      if b.isAppOfArity ``And 2 then
        let eq := b.appFn!.appArg!
        if eq.isAppOfArity ``Eq 3 && (eq.getArg! 2).isAppOfArity ``Option.some 2 &&
            (eq.getArg! 2).appArg! == .bvar 0 && !(eq.getArg! 1).hasLooseBVars then
          let t := eq.getArg! 1
          modify fun (acc, n) => (if acc.contains t then acc else acc.push t, n)
  match e with
  | .app f a => someReads f; someReads a
  | .lam _ t b _ | .forallE _ t b _ => someReads t; someReads b
  | .letE _ t v b _ => someReads t; someReads v; someReads b
  | .mdata _ b | .proj _ _ b => someReads b
  | _ => pure ()

end Close

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| sol_close_some_cases) => do
    let g ← getMainGoal
    let ts ← g.withContext do
      let mut st : Array Expr × Nat := (#[], 20000)
      st := ((Close.someReads (← instantiateMVars (← g.getType))).run st).2
      for d in ← getLCtx do
        unless d.isImplementationDetail do
          st := ((Close.someReads (← instantiateMVars d.type)).run st).2
      pure st.1
    if ts.isEmpty then throwError "sol_close_some_cases: no read `∃ a, t = some a ∧ _`"
    let mut goals := [g]
    for t in ts.toList.take 8 do
      let mut next := []
      for g in goals do
        let gs ← g.withContext do
          -- the premises that read `t`, reverted, so that it is generalized in them too
          let mut hs : Array FVarId := #[]
          for d in ← getLCtx do
            if !d.isImplementationDetail && ((← instantiateMVars d.type).find? (· == t)).isSome then
              hs := hs.push d.fvarId
          -- with what depends on them: `revert` says how many went back
          let (rs, g₁) ← g.revert hs
          let ty ← instantiateMVars (← g₁.getType)
          unless (ty.find? (· == t)).isSome do return [(← g₁.introNP rs.size).2]
          let (fs, g₂) ← g₁.generalize #[{ expr := t, xName? := `L }]
          let some L := fs[0]? | return [g]
          let cs ← g₂.cases L
          cs.toList.mapM fun c => do
            let (_, c') ← c.mvarId.introNP rs.size
            pure c'
        next := next ++ gs
      goals := next
    setGoals goals
    evalTactic (← `(tactic| all_goals (try simp only [Option.some.injEq, exists_eq_left',
      reduceCtorEq, false_and, and_false, exists_false, false_implies, implies_true,
      true_and, and_true] at *)))

/-- `sol_close`'s write facts and reads (`sol_close_facts`,
`sol_close_reads`).  On a leaf past a `{havoc}` (`State.havoc`: a loop's
exit or preservation under its invariant), where the frame of the prefix's
writes saturates over the havocked states, each is skipped past a budget of
its own (`sol_skip_after`): what the leaf needs is then the invariant and
the guard.  Elsewhere they run as they always have. -/
syntax "sol_close_saturate" : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| sol_close_saturate) => do
    let havoc ← withMainContext do
      let t ← instantiateMVars (← getMainTarget)
      pure (t.find? (·.isConstOf `Solidity.State.havoc)).isSome
    if havoc then
      evalTactic (← `(tactic| sol_skip_after 10000 sol_close_facts))
      evalTactic (← `(tactic| all_goals sol_skip_after 10000 sol_close_reads))
    else
      evalTactic (← `(tactic| try sol_close_facts))
      evalTactic (← `(tactic| all_goals try sol_close_reads))

open Lean Elab Tactic Meta in
/-- Fails unless the leaf has a joined update: an update (`Fml.upd`) whose
value is conditional (`Op3.ite`, `Upd.ifJoin`, a joined `if`'s), not a
conditional of the post alone (a specification's ternary).  The guard of
`sol_close`'s join alternative, so a leaf with none is not evaluated twice. -/
elab "sol_close_has_ite" : tactic => withMainContext do
  let joined (x : Expr) : Bool :=
    x.isAppOfArity `Solidity.Fml.upd 6 &&
      ((x.getArg! 4).find? fun y =>
        y.isConstOf `Solidity.Op3.ite || y.isConstOf `Solidity.Upd.ifJoin).isSome
  let hit (e : Expr) : Bool := (e.find? joined).isSome
  if hit (← instantiateMVars (← getMainTarget)) then return
  for d in ← getLCtx do
    if !d.isImplementationDetail && hit (← instantiateMVars d.type) then return
  throwError "sol_close_has_ite: no joined update"

/-- A leaf whose updates' values are conditional (`bif c then a else b`, what
a joined `if`'s `{x := c ? e₁ : e₂}` reads, `ifElseJoin`), each value
`∃ a, X = some a ∧ P a` read as a fresh `a` and its defining fact `X = some a`
(KeY's join with the conditional in the antecedent): `X` returns (by cases on
its conditions, `omega` refuting the case that halts), and `P a` follows
from the facts, which `omega` reads as disjunctions.  Fails unless the goal
reads a conditional value. -/
syntax "sol_close_join" : tactic

/-- A leaf of many joined values (`CloseJ.stepsMin` conditional terms or
more), read one binder and one update at a time, the rest of the formula
held opaque, each value named once with its defining fact and the interval
its cases give; `omega` reads the intervals, and only where they do not
suffice the defining facts (`sol_close_finish`).  Within a budget of its
own (`CloseJ.budget`); fails, leaving the leaf as it was, where it does not
close it. -/
syntax "sol_close_join_steps" : tactic

/-- Fails on a leaf of more than `CloseJ.wholeMax` joined updates: the guard
of `sol_close`'s alternatives that evaluate a leaf whole, which on such a
leaf run past the heartbeats rather than fail. -/
syntax "sol_close_few_joins" : tactic

/-- `sol_close`'s last pass, on goals with no state left: the arithmetic
(`omega`, `grind`), with the witnesses' ranges, an `Option` read split once,
and products. -/
macro "sol_close_finish" : tactic => `(tactic|
  -- `Int.tmod_lt_of_pos`, `Int.lt_tmod_of_pos`: solkey's `smod_lessPositiveDenom`,
  -- `smod_NumPos` and `smod_NumNeg`, a remainder within a positive divisor;
  -- `Int.tmod_nonneg`, `Close.tmod_nonpos`: `smod_geZero`, its sign the
  -- dividend's; `Int.mul_tmod_left`: `smodMultiple`;
  -- `Close.uintBitwise_and_self`: its `binaryAndIdentity`, at an `int256`;
  -- `Int.tdiv_eq_ediv_of_nonneg`: solkey's `sdiv_axiom`, a quotient of a
  -- nonnegative dividend is `div` (`div_axiom`: grind's own)
  all_goals first
    | omega
    | grind [Close.lookupBy_uint_congr, Int.tmod_lt_of_pos, Int.lt_tmod_of_pos,
        Int.tmod_nonneg, Close.tmod_nonpos, Int.mul_tmod_left, Int.mul_tmod_right,
        Int.tdiv_eq_ediv_of_nonneg, Close.uintBitwise_and_self]
    | (sol_close_enrich
       all_goals (repeat' (first | intro _ | apply And.intro))
       all_goals first
         | omega
         | grind [Close.lookupBy_uint_congr, Int.tmod_lt_of_pos, Int.lt_tmod_of_pos,
             Int.tmod_nonneg, Close.tmod_nonpos, Int.mul_tmod_left, Int.mul_tmod_right,
             Int.tdiv_eq_ediv_of_nonneg, Close.uintBitwise_and_self])
    -- an `Option` read whose witness a premise gives and the goal asks
    -- again (`∃ a, len = some a ∧ _`), split once for both
    | (sol_close_some_cases
       all_goals (repeat' (first | intro _ | apply And.intro))
       -- the witnesses' ranges (`sol_close_enrich`)
       all_goals (try sol_close_enrich)
       all_goals (repeat' (first | intro _ | apply And.intro))
       all_goals first
         | omega
         | grind [Close.lookupBy_uint_congr, Int.tmod_lt_of_pos, Int.lt_tmod_of_pos,
             Int.tmod_nonneg, Close.tmod_nonpos, Int.mul_tmod_left, Int.mul_tmod_right,
             Int.tdiv_eq_ediv_of_nonneg, Close.uintBitwise_and_self])
    -- Last, where a product remains: bounded literal/symbolic bound
    -- products, sign-guarded monotonicity and factor/difference squares.
    | (sol_close_nonlin
       grind [Int.tmod_lt_of_pos, Int.lt_tmod_of_pos, Int.tmod_nonneg, Close.tmod_nonpos,
         Int.tdiv_eq_ediv_of_nonneg]))

/-- `sol_close`: prove a formula with no modality left in an arbitrary state
(`Calculus/Close.lean`; a scoped leaf by `Calculus/CloseScoped.lean`'s
steps of the same names).  Run `sol_symex` first; with no goal left it does
nothing. -/
macro "sol_close" : tactic => `(tactic|
  all_goals first
  -- a leaf whose equations read a storage alias (an `ensures` of a returned
  -- alias): read in the Theory, the alias at the path it holds; else as below
  | sol_close_alias
  -- a leaf of many joined values: one update at a time, each value named
  -- once with its interval (`sol_close_join_steps`)
  | sol_close_join_steps
  -- a leaf whose values a joined `if` left conditional: each a fresh value
  -- and its facts (`sol_close_join`), within a budget of its own (its case
  -- splits bounded too, `joinMaxCases`), so past it the alternatives
  -- below are still tried
  |(sol_close_has_ite
    sol_close_few_joins
    sol_within 160000 (
    sol_close_unwrap
    intro σ
    sol_close_eval
    all_goals sol_close_saturate
    all_goals (try sol_close_landed)
    all_goals try (intros; sol_close_reads_all)
    all_goals try (subst_vars; sol_close_reads_all)
    all_goals (try intros)
    all_goals (try simp only [Close.exists_unit, Close.forall_unit, Close.exists_const_type,
      Close.forall_const_type] at *)
    all_goals (try sol_close_witness)
    all_goals (repeat' (first | intro _ | apply And.intro))
    -- a goal the evaluation left no conditional value in: as below
    all_goals first | sol_close_join | sol_close_finish))
  -- past `CloseJ.wholeMax` joined updates, none of the whole evaluations
  |(sol_close_few_joins
    sol_close_quantified)
  |(sol_close_few_joins
    sol_close_unwrap
    intro σ
    sol_close_eval
    all_goals sol_close_saturate
    -- the states an update lands on (`CloseS.LandedAll`), opened to binders
    all_goals (try sol_close_landed)
    all_goals try (intros; sol_close_reads_all)
    all_goals try (subst_vars; sol_close_reads_all)
    all_goals (try intros)
    -- a bounds check returns `()`: nothing is left to choose
    all_goals (try simp only [Close.exists_unit, Close.forall_unit, Close.exists_const_type,
      Close.forall_const_type] at *)
    -- a value read back (`∃ a, t = a.val ∧ φ a`): the witness is `t`, its
    -- bounds of a literal by `decide`
    all_goals (try sol_close_witness)
    -- a premise `Nonempty (Landed …)` where the rest no longer reads a landed
    -- state: every premise introduced, every conjunct its own goal
    all_goals (repeat' (first | intro _ | apply And.intro))
    all_goals sol_close_finish))

/-- `sol_close_mt`'s first pass: `sol_close_eval` with the storage
evaluators unfolded over a deployment's storage. -/
syntax "sol_close_mt_eval" : tactic

/-- `sol_close` from a deployment's storage, `{storage := mtSt ‖ …}` in
front (`CloseS.eval_mtSt`): the storage is then a list of the roots at their
defaults, and the storage evaluators are unfolded over it — solkey's
`selectOnEmptyStorage` and `saveOnEmptyStorage` (`structRules.key`), read off
that list, which is what lets a write under the diamond return.  An
arbitrary storage is left to the read-after-write facts.
A read at a free key of a mapping the deployment does not write, and a
member of a struct root, close since the typed empty storage
(`CloseS.find_init_append`; `Examples/Tactics/Constructors.lean`). -/
macro "sol_close_mt" : tactic => `(tactic|
  all_goals
   (sol_close_unwrap
    intro σ
    sol_close_mt_eval
    all_goals try sol_close_facts
    all_goals try sol_close_reads
    all_goals (try sol_close_landed)
    all_goals try (intros; sol_close_reads_all)
    all_goals (try intros)
    all_goals (repeat' (first | intro _ | apply And.intro))
    all_goals first | omega | grind [Close.lookupBy_uint_congr]))

end Solidity
