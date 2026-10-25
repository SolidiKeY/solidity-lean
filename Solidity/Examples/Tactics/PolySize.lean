import Solidity.Tools.ProofTree
import Solidity.Calculus.Closers

/-!
# Polynomial size: three families

The theorem `docs/automation.md` sets (M6, M8): symbolic execution takes a
number of steps, and produces formulas, of size polynomial in the program
and specification text.  Three families measure it, each pinned for small
`k` by `#proof_size` (below): the proof tree's nodes and branches (KeY's
goals), its open goals, and its largest leaf: the leaf's sequent as
`sol_leaf` reads it (`⊨ᶠ ψ`), in term nodes (`Fml.tmSize`, M5).

* **Sequential `if`s** that each write a local the next one reads, both
  branches assigning: `if (a == 1) { x = x + 1; } else { x = 0; }`, the
  `i`-th `else` setting `x` to the literal `i - 1`, `k` of them, then
  `x <= k`.
* **Loops with a literal bound** under their invariants:
  `for (uint i = 0; i < 10; i++) { s = s + 1; }`, `k` of them in
  sequence, each with its invariant, then `s == 10 * k`.
* **The two combined**: one such loop whose body is `k` sequential `if`s.

`docs/automation.md`, "M8 · Polynomial size", records the counts and
times for `k = 1 … 6`.
-/

namespace Solidity.Examples.Tactics.PolySize

local instance : InContract := ⟨StandardExample⟩

open scoped Solidity.Scoped

/-! ## The size of a proof tree -/

open Lean Elab Command Meta Tactic in
/-- A leaf's size: its sequent as `sol_leaf` reads it, `⊨ᶠ ψ`, and the
term nodes of `ψ` (`Fml.tmSize`, M5). -/
def leafSize (seq : Expr) : TermElabM Nat := do
  let g ← mkFreshExprSyntheticOpaqueMVar seq
  let gs ← Tactic.run g.mvarId! (evalTactic (← `(tactic| sol_leaf)))
  let [g'] := gs | throwError "#proof_size: `sol_leaf` left {gs.length} goals"
  let ty ← instantiateMVars (← g'.getType)
  unless ty.isAppOf ``Fml.Valid do throwError "#proof_size: `sol_leaf` left {ty}"
  unsafe evalExpr Nat (mkConst ``Nat) (← mkAppM ``Fml.tmSize #[ty.appArg!])

/-- The leaves of a proof tree, leftmost first. -/
partial def treeLeaves (t : ProofTree.Tree) : Array ProofTree.Tree :=
  if t.children.isEmpty then #[t] else t.children.foldl (· ++ treeLeaves ·) #[]

/-- `#proof_size φ`: `⊢ φ`'s proof tree (`#proof_tree`) measured, its nodes,
its branches, its open goals, and its largest leaf in term nodes. -/
syntax "#proof_size " term : command

open Lean Elab Command Meta in
@[command_elab Solidity.Examples.Tactics.PolySize.«command#proof_size_»]
def elabProofSize : CommandElab := fun stx => liftTermElabM do
  let some tree ← Tools.coreProofTree? ⟨stx[1]⟩ | Tools.notScoped "#proof_size"
  let mut big := 0
  for l in treeLeaves tree do
    big := max big (← leafSize (← instantiateMVars l.sequent))
  logInfo m!"{tree.rows.size} node(s), {tree.leaves} branch(es), \
    {tree.openGoals.size} open, largest leaf {big} term node(s)"

/-! ## Sequential `if`s, both branches assigning

`ifElseSplit` copies the rest of the program into both goals: `2^k`
branches, `7 · 2^k + k − 4` nodes. -/

/-- info: 11 node(s), 2 branch(es), 0 open, largest leaf 27 term node(s) -/
#guard_msgs in
#proof_size dl!{ ⟨ uint x = 0; if (a == 1) { x = x + 1; } else { x = 0; }; ⟩ x <= 1 }

/-- info: 26 node(s), 4 branch(es), 0 open, largest leaf 45 term node(s) -/
#guard_msgs in
#proof_size dl!{ ⟨ uint x = 0; if (a == 1) { x = x + 1; } else { x = 0; };
  if (b == 1) { x = x + 1; } else { x = 1; }; ⟩ x <= 2 }

/-- info: 55 node(s), 8 branch(es), 0 open, largest leaf 63 term node(s) -/
#guard_msgs in
#proof_size dl!{ ⟨ uint x = 0; if (a == 1) { x = x + 1; } else { x = 0; };
  if (b == 1) { x = x + 1; } else { x = 1; }; if (c == 1) { x = x + 1; } else { x = 2; }; ⟩ x <= 3 }

/-! ## Loops with a literal bound, by their invariants

The invariant rule runs the body once, whatever the bound: a loop is a
constant number of nodes. -/

/-- info: 10 node(s), 3 branch(es), 0 open, largest leaf 49 term node(s) -/
#guard_msgs in
#proof_size dl!{ [ uint s = 0;
  /// @custom:key invariant i <= 10 && s == i
  for (uint i = 0; i < 10; i++) { s = s + 1; }; ] s == 10 }

/-- info: 17 node(s), 5 branch(es), 0 open, largest leaf 78 term node(s) -/
#guard_msgs in
#proof_size dl!{ [ uint s = 0;
  /// @custom:key invariant i <= 10 && s == i
  for (uint i = 0; i < 10; i++) { s = s + 1; };
  /// @custom:key invariant i <= 10 && s == 10 + i
  for (uint i = 0; i < 10; i++) { s = s + 1; }; ] s == 20 }

/-! ## Both: a loop whose body is sequential `if`s -/

/-- info: 18 node(s), 4 branch(es), 0 open, largest leaf 66 term node(s) -/
#guard_msgs in
#proof_size dl!{ [ uint s = 0;
  /// @custom:key invariant i <= 10 && s <= 1 * i
  for (uint i = 0; i < 10; i++) { if (a == 1) { s = s + 1; } else { s = 0; } }; ] s <= 10 }

end Solidity.Examples.Tactics.PolySize
