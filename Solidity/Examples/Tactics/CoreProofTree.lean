import Solidity.Tools.CoreInspect
import Solidity.Calculus.Core.Notation

/-!
# The proof tree of a scoped goal, pinned

`Calculus/Core/ProofTree.lean`'s tree of `⊢ φ` for a scoped `φ`
(`cdl!{ … }`), printed by `#proof_tree`, `#proof_node` and
`#proof_tree_json` as today's are (`Examples/ProofTree.lean`).  Where the
trees differ from today's:

* a parameter is bound by `∀` (`cdl!`), so the tree starts with `allRight`;
* a rule that leaves no statement goes on into the rest of the program, or
  past the frames to the postcondition, in one step (`Fml.modalK`, Gate G0's
  condition 6), so there is no `emptyModality` after it;
* a leaf is closed by `closeTrue` alone until a closer of scoped leaves is
  given (`Config.closers`).
-/

namespace Solidity.Examples.Tactics.CoreProofTree

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

/--
info: node: 1
sequent:
  dl{ ∀ uint x ⟹ [ if (true) {x = 2;} else {x = 1;}; ] ¬x = 0 }
rule: ifElseSplit
state: inner
branch: -
parent: 0
children: [2, 4]
tactics: apply Core.Proves.split (Core.Taclet.toStep .ifElseSplit)
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
    3: OPEN GOAL
        dl{ { to := 9 } ⟹ 0 <= 5 }
  [send succeeded]
    4: OPEN GOAL
        dl{ { to := 9 }, { net := if(to = this) then net else store(net, at(to), net(to) - 5) ‖ ok := true } ⟹ true }
  [send failed]
    5: OPEN GOAL
        dl{ { to := 9 }, { ok := false } ⟹ true }
open: 3 open goal(s), 6 node(s), 3 branch(es)
-/
#guard_msgs in
#proof_tree cdl!{ ⟨ uint to = 9; ok = to.send(5); ⟩ true }

/--
info: {"stats": {"nodes": 6, "branches": 2},
 "sequents":
 ["dl{ ⟹ ∀ uint x; [ if (true) {x = 2;} else {x = 1;}; ] true }",
  "dl{ ∀ uint x ⟹ [ if (true) {x = 2;} else {x = 1;}; ] true }",
  "dl{ ∀ uint x, true ≐ true ⟹ [ x = 2; } ] true }",
  "dl{ ∀ uint x, true ≐ true, { x := 2 } ⟹ true }",
  "dl{ ∀ uint x, true ≐ false ⟹ [ x = 1; } ] true }",
  "dl{ ∀ uint x, true ≐ false, { x := 1 } ⟹ true }"],
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

/-! `#step` names the rule as the tree does: KeY's taclet at the operator. -/

/--
info:   ~[additionAssignment]~>
    dl{ ∀ uint a; ∀ uint y; { y := a + 1 } true }
-/
#guard_msgs in
#step cdl!{ [ y = a + 1; ] true }

end Solidity.Examples.Tactics.CoreProofTree
