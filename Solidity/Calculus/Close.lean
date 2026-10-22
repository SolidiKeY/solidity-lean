import Solidity.Calculus.SurfaceNotation
import Solidity.Calculus.TacticSyntax
import Solidity.Calculus.CloseLemmas
import Solidity.Calculus.CloseNonlin

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

/-- `sol_close`: prove a formula with no modality left in an arbitrary state
(`Calculus/Close.lean`; a scoped leaf by `Calculus/CloseScoped.lean`'s
steps of the same names).  Run `sol_symex` first; with no goal left it does
nothing. -/
macro "sol_close" : tactic => `(tactic|
  all_goals first
  -- a leaf whose equations read a storage alias (an `ensures` of a returned
  -- alias): read in the Theory, the alias at the path it holds; else as below
  | sol_close_alias
  |(sol_close_unwrap
    intro σ
    sol_close_eval
    all_goals try sol_close_facts
    all_goals try sol_close_reads
    -- the states an update lands on (`CloseS.LandedAll`), opened to binders
    all_goals (try simp only [CloseS.landedAll_def])
    all_goals try (intros; sol_close_reads_all)
    all_goals try (subst_vars; sol_close_reads_all)
    all_goals (try intros)
    -- a bounds check returns `()`: nothing is left to choose
    all_goals (try simp only [Close.exists_unit, Close.forall_unit, exists_const, forall_const] at *)
    -- a value read back (`∃ a, t = a.val ∧ φ a`): the witness is `t`, its
    -- bounds of a literal by `decide`
    all_goals (try sol_close_witness)
    -- a premise `Nonempty (Landed …)` where the rest no longer reads a landed
    -- state: every premise introduced, every conjunct its own goal
    all_goals (repeat' (first | intro _ | apply And.intro))
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
      -- last, where nothing above closed and a product of two non-literal
      -- integers is left: solkey's `multiply_2_inEq0` of their atoms' bounds
      -- (`Calculus/CloseNonlin.lean`)
      | (sol_close_nonlin
         grind [Int.tmod_lt_of_pos, Int.lt_tmod_of_pos, Int.tmod_nonneg, Close.tmod_nonpos,
           Int.tdiv_eq_ediv_of_nonneg])))

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
    all_goals (try simp only [CloseS.landedAll_def])
    all_goals try (intros; sol_close_reads_all)
    all_goals (try intros)
    all_goals (repeat' (first | intro _ | apply And.intro))
    all_goals first | omega | grind [Close.lookupBy_uint_congr]))

end Solidity
