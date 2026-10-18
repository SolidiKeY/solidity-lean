import Solidity.Tools.Inspect
import Solidity.Calculus.Notation

/-!
# The proof tree of a scoped goal, pinned

`Calculus/ProofTree.lean`'s tree of `⊢ φ` for a scoped `φ`
(`cdl!{ … }`), printed by `#proof_tree`, `#proof_node` and
`#proof_tree_json` as today's are (`Examples/ProofTree.lean`).  Where the
trees differ from today's:

* a parameter is bound by `∀` (`cdl!`), so the tree starts with `allRight`;
* a rule that leaves no statement goes on into the rest of the program, or
  past the frames to the postcondition, in one step (`Fml.modalK`, Gate G0's
  condition 6), so there is no `emptyModality` after it;
* a leaf is closed by `closeTrue`, else by `sol_leaf` and the scoped
  `sol_close`, behind a diamond update too.
-/

namespace Solidity.Examples.Tactics.ProofTree

open Solidity

local instance : InContract := ⟨StandardExample⟩

/-! `ifElseSplit`'s labels name the condition at the node; a split has
KeY's two goals under either modality. -/

/--
info: 0: allRight
1: allRight
2: ifElseUnfold
3: localValueDeclInitDrop
4: boolEqualityAssignment
5: ifElseSplit
  [if se1 true]
    6: localValueAssign
    7: Closed goal
  [if se1 false]
    8: localValueAssign
    9: Closed goal
closed: 0 open goal(s), 10 node(s), 2 branch(es)
-/
#guard_msgs in
#proof_tree cdl!{ [ if (a == 1) { x = 2; } else { x = 1; }; ] true }

/-! A comparison before an `if`, or in its branch, prints as KeY's taclet at
its operator (`lessEqualAssignment`), not as the family's
`binopAssignment`: the operator is the statement's first `BinOp`
constructor, not `BinOp.ret` in the branches' value types (a regression
pin). -/

/--
info: 0: allRight
1: allRight
2: allRight
3: ifElseUnfold
4: localValueDeclInitDrop
5: lessEqualAssignment
6: ifElseSplit
  [if se1 true]
    7: localValueAssign
    8: Closed goal
  [if se1 false]
    9: localValueAssign
    10: Closed goal
closed: 0 open goal(s), 11 node(s), 2 branch(es)
-/
#guard_msgs in
#proof_tree cdl!{ [ if (a <= b) { x = 1; } else { x = 2; }; ] true }

/--
info: 0: allRight
1: allRight
2: ifElseUnfold
3: localValueDeclInitDrop
4: boolEqualityAssignment
5: ifElseSplit
  [if se1 true]
    6: localValueDeclInitDrop
    7: lessEqualAssignment
    8: Closed goal
  [if se1 false]
    9: localValueAssign
    10: Closed goal
closed: 0 open goal(s), 11 node(s), 2 branch(es)
-/
#guard_msgs in
#proof_tree cdl!{ [ if (a == 1) { bool c = x <= 1; } else { x = 2; }; ] true }

/--
info: node: 1
sequent:
  dl{ ∀ uint x ⟹ [ if (true) {x = 2;} else {x = 1;}; ] ¬x = 0 }
rule: ifElseSplit
state: inner
branch: -
parent: 0
children: [2, 4]
tactics: apply Proves.split (Taclet.toStep .ifElseSplit)
-/
#guard_msgs in
#proof_node 1 cdl!{ [ if (true) { x = 2; } else { x = 1; }; ] x != 0 }

/-! A `try` has a goal for each way the call may end, a `send` for each
outcome, labelled as their rules label them. -/

/--
info: 0: allRight
1: tryCallNoCallbackBox
  [call succeeded]
    2: allRight
    3: localValueAssign
    4: Closed goal
  [Error caught]
    5: localValueAssign
    6: Closed goal
  [Panic caught]
    7: localValueAssign
    8: Closed goal
  [other failure caught]
    9: localValueAssign
    10: Closed goal
closed: 0 open goal(s), 11 node(s), 4 branch(es)
-/
#guard_msgs in
#proof_tree cdl!{ [ try I(7).get() returns (uint v) { x = v; } catch { x = 0; }; ] true }

/--
info: 0: allRight
1: sendNoCallbackBox
  [send succeeded]
    2: Closed goal
  [send failed]
    3: Closed goal
closed: 0 open goal(s), 4 node(s), 2 branch(es)
-/
#guard_msgs in
#proof_tree cdl!{ [ ok = to.send(5); ] true }

/-! The hidden binder of `ok`, which the program assigns without declaring,
is no node. -/

/--
info: 0: localValueDeclInitDrop
1: localValueAssign
2: sendNoCallbackDiamond
  [non-negative amount]
    3: Closed goal
  [send succeeded]
    4: Closed goal
  [send failed]
    5: Closed goal
closed: 0 open goal(s), 6 node(s), 3 branch(es)
-/
#guard_msgs in
#proof_tree cdl!{ ⟨ uint to = 9; ok = to.send(5); ⟩ true }

/--
info: {"stats": {"nodes": 6, "branches": 2},
 "sequents":
 ["dl{ ⟹ ∀ uint x; [ if (true) {x = 2;} else {x = 1;}; ] true }",
  "dl{ ∀ uint x ⟹ [ if (true) {x = 2;} else {x = 1;}; ] true }",
  "dl{ ∀ uint x, true = true ⟹ [ x = 2; } ] true }",
  "dl{ ∀ uint x, true = true, { x := 2 } ⟹ true }",
  "dl{ ∀ uint x, true = false ⟹ [ x = 1; } ] true }",
  "dl{ ∀ uint x, true = false, { x := 1 } ⟹ true }"],
 "openGoalCount": 0,
 "nodes":
 [[0, -1, "allRight", null, "inner"],
  [1, 0, "ifElseSplit", null, "inner"],
  [2, 1, "localValueAssign", "if true true", "inner"],
  [3, 2, "Closed goal", null, "closed"],
  [4, 1, "localValueAssign", "if true false", "inner"],
  [5, 4, "Closed goal", null, "closed"]],
 "closed": true}
-/
#guard_msgs in
#proof_tree_json cdl!{ [ if (true) { x = 2; } else { x = 1; }; ] true }

/-! A leaf with a formula left closes as a walk ends: `sol_leaf` and the
scoped `sol_close`. -/

/--
info: 0: allRight
1: ifElseSplit
  [if true true]
    2: localValueAssign
    3: Closed goal
  [if true false]
    4: localValueAssign
    5: Closed goal
closed: 0 open goal(s), 6 node(s), 2 branch(es)
-/
#guard_msgs in
#proof_tree cdl!{ [ if (true) { x = 2; } else { x = 1; }; ] x != 0 }

/--
info: node: 3
sequent:
  dl{ ∀ uint x, true = true, { x := 2 } ⟹ ¬x = 0 }
rule: Closed goal
state: closed
branch: -
parent: 2
children: []
tactics: sol_leaf; sol_close
-/
#guard_msgs in
#proof_node 3 cdl!{ [ if (true) { x = 2; } else { x = 1; }; ] x != 0 }

/-! `#step` names the rule as the tree does: KeY's taclet at the operator. -/

/--
info:   ~[additionAssignment]~>
    dl{ ∀ uint a; ∀ uint y; { y := a + 1 } true }
-/
#guard_msgs in
#step cdl!{ [ y = a + 1; ] true }

/-! A tree is of a goal at the empty context: a formula over locals is
refused, not grown on an ill-typed goal. -/

/-- error: #proof_tree: the formula is not closed at the empty context -/
#guard_msgs in
#proof_tree (Fml.tt : Fml StandardExample [.val .uint])

end Solidity.Examples.Tactics.ProofTree
