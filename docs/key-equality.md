# One equation, KeY's `=`

Internal formulas have one equation, `a = b` (`Fml.eq`), KeY's `=`: it compares
what the sides denote in the Theory (`Tm.denote`), total as KeY's terms
are.  There is no definedness test.  This records the change that removed
`defined(t)` and `Fml.eqD` (`defined(a) ∧ defined(b) ∧ a ≐ b`), and what
replaced each use.

Public `Spec` equations instead require successful evaluation of both
operands; see [correctness.md](correctness.md).

## What a formula says

- `a = b` holds where the sides denote the same Theory value.  It is
  reflexive even where a side halts: `0 - 1 == 0 - 1` is valid
  (`Examples/CheckedLinear.lean`, `closedFailure_valid`), and an equation of
  one halting side and one that returns is false.  `==` and `!=` in a
  formula, a spec's `==`, and a comparison `a < b` (`a < b = true`) are this
  equation (`!=` of two halting sides is false); `≐` is gone from the
  notation.
- `wt(s)` is a predicate (`Fml.wellFormed`), KeY's `wellFormed(heap)`: the
  storage `s` evaluates to passes the shape test (`Storage.wtB`).  An
  obligation is `wt(storage) → …` (`Fml.wt`, `Calculus/Problem.lean`).
- What may revert is evaluated by the program, as KeY's terms cannot halt:
  a condition is a captured local (`if`, `require`, `assert`, KeY's `se`), or
  read by an update, `{ b := cond } (b = FALSE)` (`loopExit`, the invariant
  rules), which lands where the condition returns.
- A spec's frame owes `find(storage, p) = find(old, p)` with no guard: a
  storage read is total in the Theory.  The layout premise of a `bool` word
  is `true`.

## The rules

`loopExit` reads its condition by an update under the diamond, so a
condition that halts is not false (`Premise.sound_loopExit`).  Not
`⟨[ assert(!cond); ]⟩`: an unfold premise must simulate the loop's run
(`TRes.Sim`), which a panic where the loop runs its body does not.

`whileInvariantDiamond` keeps solkey's text: `0 <= dec ∧ dec < variant` is
read in the Theory, and the bound is the Theory value of `dec`, which the
next head's update reads as the interpreter does (`Tm.denote_eval`); the
invariant under the variant's local reads as without it
(`Val.lower_denote_up`, `Calculus/TermWk.lean`).

The exact reductions (`Calculus/ProgramReduction.lean`) read `require`,
`assert` and `if` by an update (`capture`, `popped`) and stay exact.

## The closers

Where the Theory reads both sides as the interpreter does (`Tm.agreeB`,
`Calculus/TermAgree.lean`: locals, literals, operators, the ledger, reads
of `storage` or `old` at a root, a member or a mapping entry, a dynamic
array's length there, memory reads), an equation is the one of their typed
readings, a halt included (`holds_eq_of_agree`).

- `sol_decide` reads such an equation exactly at either polarity: `.eq`
  where a side returns (`Tm.totB`), the equation of two `Option`s otherwise
  (`LFml.optEq`).  Any other equation is its typed equation in a goal (which
  implies it) and "equal where both return" in an assumption (which it
  implies).  An assumption the reduction cannot read (an update, a
  modality, `{havoc}`, an anonymising update) is dropped rather than
  failing the leaf; a hidden binder there still does.
- `sol_close_unwrap` marks each equation the closer reads by value, once,
  at the meta level (`evalEqsE`, definitionally `Fml.evalEqs`): an agreeing
  one with the proof of its agreement (`Fml.eqT`, `Fml.eqA`,
  `CloseS.holds_eqT`, `holds_eqA`); one of locals, literals and values of
  the transaction stays as it is (`CloseS.holds_eq`, `denote_pvV`).  An
  equation it is to prove that does not agree is read by an update under
  the diamond, its body an equation of atoms marked with no proof
  (`Fml.eqCap`, `Fml.eqAtom`, `CloseS.holds_eqAtom`).  The leaf implies the formula (`Fml.evalEqs_sound`,
  `Calculus/EvalEqs.lean`); where a term's Booleans do not reduce (a free
  variable) the pass is skipped and the leaf read as it stands.

## Costs

`TestSuite/Derived15`'s `invariantVariantSkipsBreakIteration` needs
185 000–200 000 heartbeats of its 200 000, on master and here alike; the
unwrap pass is meta-level so as not to add to it.
