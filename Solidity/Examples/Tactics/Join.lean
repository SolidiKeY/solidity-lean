import Solidity.Tools.ProofTree
import Solidity.Tools.Counterexample
import Solidity.Calculus.Closers

/-!
# A join after a conditional (`ifElseJoin`)

`if (c) { x = x + 1; }` runs as one update, `{x := c ? x + 1 : x}`
(`LeanTaclet.ifElseJoin`, `Calculus/Arms.lean`'s `Upd.ifJoin?`): the rest of
the program is run once, not once per branch, so `n` such `if`s in sequence
make a tree of `5n + 3` nodes and one leaf, where `ifElseSplit` made
`2^n` leaves (`docs/automation.md`, M6).  The leaf reads each joined value as
a fresh one and its defining fact (`sol_close_join`,
`Calculus/CloseScoped.lean`); from two joined updates on, one update at a
time, each value's interval read off its cases (`sol_close_join_steps`), so
the leaf's cost grows about linearly in `n`.
-/

namespace Solidity.Examples.Tactics.Join

local instance : InContract := ⟨StandardExample⟩

open scoped Solidity.Scoped

/-! The family the M6 table measures, `n = 1, 2, 5`: one branch, the nodes
growing by five per `if`. -/

/--
info: 0: allRight
1: localValueDeclInitDrop
2: localValueAssign
3: ifElseUnfold
4: localValueDeclInitDrop
5: boolEqualityAssignment
6: ifElseJoin
7: Closed goal
closed: 0 open goal(s), 8 node(s), 1 branch(es)
-/
#guard_msgs in
#proof_tree dl!{ ⟨ uint x = 0; if (a == 1) { x = x + 1; }; ⟩ x <= 1 }

/--
info: 0: allRight
1: allRight
2: localValueDeclInitDrop
3: localValueAssign
4: ifElseUnfold
5: localValueDeclInitDrop
6: boolEqualityAssignment
7: ifElseJoin
8: ifElseUnfold
9: localValueDeclInitDrop
10: boolEqualityAssignment
11: ifElseJoin
12: Closed goal
closed: 0 open goal(s), 13 node(s), 1 branch(es)
-/
#guard_msgs in
#proof_tree dl!{ ⟨ uint x = 0; if (a == 1) { x = x + 1; }; if (b == 1) { x = x + 1; }; ⟩ x <= 2 }

/--
info: 0: allRight
1: allRight
2: allRight
3: allRight
4: allRight
5: localValueDeclInitDrop
6: localValueAssign
7: ifElseUnfold
8: localValueDeclInitDrop
9: boolEqualityAssignment
10: ifElseJoin
11: ifElseUnfold
12: localValueDeclInitDrop
13: boolEqualityAssignment
14: ifElseJoin
15: ifElseUnfold
16: localValueDeclInitDrop
17: boolEqualityAssignment
18: ifElseJoin
19: ifElseUnfold
20: localValueDeclInitDrop
21: boolEqualityAssignment
22: ifElseJoin
23: ifElseUnfold
24: localValueDeclInitDrop
25: boolEqualityAssignment
26: ifElseJoin
27: Closed goal
closed: 0 open goal(s), 28 node(s), 1 branch(es)
-/
#guard_msgs in
#proof_tree dl!{ ⟨ uint x = 0; if (a == 1) { x = x + 1; }; if (b == 1) { x = x + 1; }; if (c == 1) { x = x + 1; }; if (d == 1) { x = x + 1; }; if (e == 1) { x = x + 1; }; ⟩ x <= 5 }

/-! Each proved by the strategy (`sol_prove`); a leaf its kernel closer does
not close (`LFml.decideLift` lifts at most `liftConds` conditionals) is
closed by `sol_close`, as `sol_prove?` writes it: by
`sol_close_join_steps` from `n = 2`, within the default heartbeats up to
`n = 12`. -/

theorem joinFamily1 : ⊨ᶠ dl!{ ⟨ uint x = 0; if (a == 1) { x = x + 1; }; ⟩ x <= 1 } := by
  sol_prove

theorem joinFamily2 : ⊨ᶠ dl!{ ⟨ uint x = 0; if (a == 1) { x = x + 1; }; if (b == 1) { x = x + 1; }; ⟩ x <= 2 } := by
  sol_prove
  case leaf1 =>
    sol_leaf
    sol_close

theorem joinFamily3 : ⊨ᶠ dl!{ ⟨ uint x = 0; if (a == 1) { x = x + 1; }; if (b == 1) { x = x + 1; }; if (c == 1) { x = x + 1; }; ⟩ x <= 3 } := by
  sol_prove
  case leaf1 =>
    sol_leaf
    sol_close

theorem joinFamily4 : ⊨ᶠ dl!{ ⟨ uint x = 0; if (a == 1) { x = x + 1; }; if (b == 1) { x = x + 1; }; if (c == 1) { x = x + 1; }; if (d == 1) { x = x + 1; }; ⟩ x <= 4 } := by
  sol_prove
  case leaf1 =>
    sol_leaf
    sol_close

theorem joinFamily5 : ⊨ᶠ dl!{ ⟨ uint x = 0; if (a == 1) { x = x + 1; }; if (b == 1) { x = x + 1; }; if (c == 1) { x = x + 1; }; if (d == 1) { x = x + 1; }; if (e == 1) { x = x + 1; }; ⟩ x <= 5 } := by
  sol_prove
  case leaf1 =>
    sol_leaf
    sol_close

theorem joinFamily6 : ⊨ᶠ dl!{ ⟨ uint x = 0; if (a == 1) { x = x + 1; }; if (b == 1) { x = x + 1; }; if (c == 1) { x = x + 1; }; if (d == 1) { x = x + 1; }; if (e == 1) { x = x + 1; }; if (f == 1) { x = x + 1; }; ⟩ x <= 6 } := by
  sol_prove
  case leaf1 =>
    sol_leaf
    sol_close

theorem joinFamily7 : ⊨ᶠ dl!{ ⟨ uint x = 0; if (a == 1) { x = x + 1; }; if (b == 1) { x = x + 1; }; if (c == 1) { x = x + 1; }; if (d == 1) { x = x + 1; }; if (e == 1) { x = x + 1; }; if (f == 1) { x = x + 1; }; if (g == 1) { x = x + 1; }; ⟩ x <= 7 } := by
  sol_prove
  case leaf1 =>
    sol_leaf
    sol_close

theorem joinFamily8 : ⊨ᶠ dl!{ ⟨ uint x = 0; if (a == 1) { x = x + 1; }; if (b == 1) { x = x + 1; }; if (c == 1) { x = x + 1; }; if (d == 1) { x = x + 1; }; if (e == 1) { x = x + 1; }; if (f == 1) { x = x + 1; }; if (g == 1) { x = x + 1; }; if (h == 1) { x = x + 1; }; ⟩ x <= 8 } := by
  sol_prove
  case leaf1 =>
    sol_leaf
    sol_close

theorem joinFamily9 : ⊨ᶠ dl!{ ⟨ uint x = 0; if (a == 1) { x = x + 1; }; if (b == 1) { x = x + 1; }; if (c == 1) { x = x + 1; }; if (d == 1) { x = x + 1; }; if (e == 1) { x = x + 1; }; if (f == 1) { x = x + 1; }; if (g == 1) { x = x + 1; }; if (h == 1) { x = x + 1; }; if (i == 1) { x = x + 1; }; ⟩ x <= 9 } := by
  sol_prove
  case leaf1 =>
    sol_leaf
    sol_close

theorem joinFamily10 : ⊨ᶠ dl!{ ⟨ uint x = 0; if (a == 1) { x = x + 1; }; if (b == 1) { x = x + 1; }; if (c == 1) { x = x + 1; }; if (d == 1) { x = x + 1; }; if (e == 1) { x = x + 1; }; if (f == 1) { x = x + 1; }; if (g == 1) { x = x + 1; }; if (h == 1) { x = x + 1; }; if (i == 1) { x = x + 1; }; if (j == 1) { x = x + 1; }; ⟩ x <= 10 } := by
  sol_prove
  case leaf1 =>
    sol_leaf
    sol_close

theorem joinFamily11 : ⊨ᶠ dl!{ ⟨ uint x = 0; if (a == 1) { x = x + 1; }; if (b == 1) { x = x + 1; }; if (c == 1) { x = x + 1; }; if (d == 1) { x = x + 1; }; if (e == 1) { x = x + 1; }; if (f == 1) { x = x + 1; }; if (g == 1) { x = x + 1; }; if (h == 1) { x = x + 1; }; if (i == 1) { x = x + 1; }; if (j == 1) { x = x + 1; }; if (k == 1) { x = x + 1; }; ⟩ x <= 11 } := by
  sol_prove
  case leaf1 =>
    sol_leaf
    sol_close

theorem joinFamily12 : ⊨ᶠ dl!{ ⟨ uint x = 0; if (a == 1) { x = x + 1; }; if (b == 1) { x = x + 1; }; if (c == 1) { x = x + 1; }; if (d == 1) { x = x + 1; }; if (e == 1) { x = x + 1; }; if (f == 1) { x = x + 1; }; if (g == 1) { x = x + 1; }; if (h == 1) { x = x + 1; }; if (i == 1) { x = x + 1; }; if (j == 1) { x = x + 1; }; if (k == 1) { x = x + 1; }; if (l == 1) { x = x + 1; }; ⟩ x <= 12 } := by
  sol_prove
  case leaf1 =>
    sol_leaf
    sol_close

/-- Under the box, each joined value read as whatever it returns
(`CloseS.wp_box_optRes`). -/
example : ⊨ᶠ dl!{ [ uint x = 0; if (a == 1) { x = x + 1; }; if (b == 1) { x = x + 1; }; if (c == 1) { x = x + 1; }; if (d == 1) { x = x + 1; }; if (e == 1) { x = x + 1; }; if (f == 1) { x = x + 1; }; ] x <= 6 } := by
  sol_prove
  case leaf1 =>
    sol_leaf
    sol_close

/-- Offsets other than one: the interval of each joined value is its cases'. -/
example : ⊨ᶠ dl!{ ⟨ uint x = 0; if (a == 1) { x = x + 1; }; if (b == 1) { x = x + 2; }; if (c == 1) { x = x + 1; }; if (d == 1) { x = x + 2; }; if (e == 1) { x = x + 1; }; if (f == 1) { x = x + 2; }; if (g == 1) { x = x + 1; }; ⟩ x <= 10 } := by
  sol_prove
  case leaf1 =>
    sol_leaf
    sol_close

/-- An `if` with both branches assigning is joined too,
`{x := se1 ? 2 : 1}`; the closer splits the value back into its two cases
at the leaf (`sol_close_ite_split`, KeY's `ifthenelse_split`). -/
example : ⊨ᶠ dl!{ [ if (a == 1) { x = 2; } else { x = 1; }; ] x != 0 } := by
  sol_prove

/-! ## What does not hold

A false leaf after six joins (`x <= 5`, false where all six conditions
hold): `sol_close_join_steps` fails within its budget, and no evaluation
of the whole leaf is tried after it (`CloseJ.wholeMax`), so the closer
fails, at about the cost of a true leaf, rather than running past the
declaration's heartbeats.  (The hypothesis only closes the example once
the closer has failed.) -/
example (h : ⊨ᶠ dl!{ ⟨ uint x = 0; if (a == 1) { x = x + 1; }; if (b == 1) { x = x + 1; }; if (c == 1) { x = x + 1; }; if (d == 1) { x = x + 1; }; if (e == 1) { x = x + 1; }; if (f == 1) { x = x + 1; }; ⟩ x <= 5 }) :
    ⊨ᶠ dl!{ ⟨ uint x = 0; if (a == 1) { x = x + 1; }; if (b == 1) { x = x + 1; }; if (c == 1) { x = x + 1; }; if (d == 1) { x = x + 1; }; if (e == 1) { x = x + 1; }; if (f == 1) { x = x + 1; }; ⟩ x <= 5 } := by
  fail_if_success
    sol_prove
    case leaf1 =>
      sol_leaf
      sol_close
  exact h

/-- A joined branch that overflows under the diamond: `x + 1` does not
return at `a = 2^256 − 1`, `b = 1`: refuted by a counterexample, and the
leaf stays open (below). -/
theorem joinOverflowRefuted : ¬ (⊨ᶠ dl!{ ⟨ uint x = a; if (b == 1) { x = x + 1; }; ⟩ x >= a }) := by
  sol_refute

/--
info: 0: allRight
1: allRight
2: localValueDeclInitDrop
3: localValueAssign
4: ifElseUnfold
5: localValueDeclInitDrop
6: boolEqualityAssignment
7: ifElseJoin
8: OPEN GOAL
    dl{ ∀ uint b, ∀ uint a, { x := a }, { se1 := b == 1 }, { x := (se1 ? x + 1 : x) } ⟹ x >= a }
open: 1 open goal(s), 9 node(s), 1 branch(es)
-/
#guard_msgs in
#proof_tree dl!{ ⟨ uint x = a; if (b == 1) { x = x + 1; }; ⟩ x >= a }

end Solidity.Examples.Tactics.Join
