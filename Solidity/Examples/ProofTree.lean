import Solidity.Tools.ProofTree

/-!
# The proof tree, pinned

solkey's view of a proof, a tree of sequents (`Calculus/ProofTree.lean`), and
the tactics that write a proof out, as `#guard_msgs` tests:

* `#proof_tree`, `#proof_node` and `#proof_tree_json` (`Tools/ProofTree.lean`)
  print the tree of `⊢ φ` as solkey's GUI and web prover do;
* `sol_derive?` suggests the `apply` walk the tree is, `sol_chain?` the
  `calc` a derivation `φ ~*> ψ` is.

If the strategy picks another rule, or a printer changes, these fail.
-/

namespace Solidity.Examples.ProofTree

open Proves

local instance : InContract := ⟨StandardExample⟩

/-! ## The tree

`a == 1 → ⟨ uint x = a; require(x == 1); ⟩ x == 1`: a run of steps, one
flat branch, then `requireSimple`'s three goals, each a sub-branch labelled
with its case name. -/

/--
info: 0: impRight
1: localValueDeclInitDrop
2: localValueAssign
3: requireConditionCapture
4: localValueDeclInitDrop
5: binopAssignment
6: requireSimple
  [thn]
    7: emptyModality
    8: Closed goal
  [els]
    9: revertDiamond
    10: Closed goal
  [cov]
    11: Closed goal
closed: 0 open goal(s), 12 node(s), 3 branch(es)
-/
#guard_msgs in
#proof_tree dl!{ a == 1 → ⟨ uint x = a; require(x == 1); ⟩ x == 1 }

/-! A write under the diamond is not valid (`alice` may be missing): the leaf
stays open, and shows its sequent. -/
/--
info: 0: storageFieldWriteSave
1: emptyModality
2: OPEN GOAL
    dl{ { storage := save(storage, alice.age, 1) } ⟹ true }
open: 1 open goal(s), 3 node(s), 1 branch(es)
-/
#guard_msgs in
#proof_tree dl!{ ⟨ alice.age = 1; ⟩ true }

/-! ## A node, and the tree as data

`#proof_node n φ` is solkey's `node` request; `#proof_tree_json φ` its `tree`
request, the rows `[serial, parent, name, branchLabel, state]`. -/

/--
info: node: 1
sequent:
  dl{ true ≐ true ⟹ [ x = 2; ] ¬x = 0 }
rule: localValueAssign
state: inner
branch: thn
parent: 0
children: [2]
tactics: apply update .localValueAssign
-/
#guard_msgs in
#proof_node 1 dl!{ [ if (true) { x = 2; } else { x = 1; }; ] x != 0 }

/--
info: {"stats": {"nodes": 8, "branches": 3},
 "sequents":
 ["dl{ ⟹ [ if (true) {x = 2;} else {x = 1;}; ] ¬x = 0 }",
  "dl{ true ≐ true ⟹ [ x = 2; ] ¬x = 0 }",
  "dl{ true ≐ true, { x := 2 } ⟹ [ ] ¬x = 0 }",
  "dl{ true ≐ true, { x := 2 } ⟹ ¬x = 0 }",
  "dl{ true ≐ false ⟹ [ x = 1; ] ¬x = 0 }",
  "dl{ true ≐ false, { x := 1 } ⟹ [ ] ¬x = 0 }",
  "dl{ true ≐ false, { x := 1 } ⟹ ¬x = 0 }",
  "dl{ ⟹ true }"],
 "openGoalCount": 0,
 "nodes":
 [[0, -1, "ifElseSplit", null, "inner"],
  [1, 0, "localValueAssign", "thn", "inner"],
  [2, 1, "emptyModality", null, "inner"],
  [3, 2, "Closed goal", null, "closed"],
  [4, 0, "localValueAssign", "els", "inner"],
  [5, 4, "emptyModality", null, "inner"],
  [6, 5, "Closed goal", null, "closed"],
  [7, 0, "Closed goal", "cov", "closed"]],
 "closed": true}
-/
#guard_msgs in
#proof_tree_json dl!{ [ if (true) { x = 2; } else { x = 1; }; ] x != 0 }

/-! ## `sol_derive?`: the walk

The suggestion is the walk `ApplySteps.guardedCopy` writes by hand. -/

/--
info: Try this:
  apply intro
    apply unfold .localValueDeclInitDrop
    apply update .localValueAssign
    apply unfold .requireConditionCapture
    apply unfold .localValueDeclInitDrop
    apply update .binopAssignment
    apply split .requireSimple
    case thn =>
      apply empty
      refine close ?_
      sol_symex
      sol_close
    case els =>
      apply done .revertDiamond
      refine close ?_
      sol_symex
      sol_close
    case cov =>
      refine close ?_
      sol_symex
      sol_close
-/
#guard_msgs in
/-- `a == 1 → ⟨ uint x = a; require(x == 1); ⟩ x == 1`. -/
theorem guardedCopy : ⊢ dl!{ a == 1 → ⟨ uint x = a; require(x == 1); ⟩ x == 1 } := by
  sol_derive?

/--
info: Try this:
  apply Proves.valid
    apply update .storageFieldWriteSave
    apply unfold .transfer_unfold_rightSndArgument
    apply unfold .localValueDeclInitDrop
    apply update .binopAssignment
    apply update .transferNoCallbackBox
    apply unfold .localValueDeclInitDrop
    apply update .storageFieldReadFind
    apply empty
    refine close ?_
    sol_symex
    sol_close
-/
#guard_msgs in
/-- `alice.age = 1; to.transfer(x + 2); uint y = alice.age;`: on `⊨ φ` the
walk starts with `apply Proves.valid`; the payment, once its amount is
captured, is one update (`transferNoCallbackBox`). -/
theorem transferFrameStorage :
    ⊨ dl!{ [ alice.age = 1; to.transfer(x + 2); uint y = alice.age; ] y == 1 } := by
  sol_derive?

/-! ## `sol_chain?`: the `calc`

A derivation `φ ~*> ψ` written out, every line and every rule. -/

/--
info: Try this:
  exact calc dl!{ [ alice.age = v; x = 1; ] find(storage, alice.age) = v }
      _ ~[storageFieldWriteSave]~> dl!{ { storage := save(storage, alice.age, v) } [ x = 1; ] find(storage, alice.age) = v } := rfl
      _ ~[localValueAssign]~> dl!{ { storage := save(storage, alice.age, v) } { x := 1 } [ ] find(storage, alice.age) = v } := rfl
      _ ~[emptyModality]~> dl![.box]{ { storage := save(storage, alice.age, v) } { x := 1 } find(storage, alice.age) = v } := rfl
-/
#guard_msgs in
example : dl!{ [ alice.age = v; x = 1; ] alice.age == v }
    ~*> dl![.box]{ { storage := save(storage, alice.age, v) } { x := 1 } alice.age == v } := by
  sol_chain?

section
variable (m : Modality) (φ : Post StandardExample)

/-! At a modality `m` and a postcondition `φ`, each step is `by sol_chain`. -/
/--
info: Try this:
  exact calc dl![m]{ ⟨[ alice.age = v; ]⟩ φ }
      _ ~[storageFieldWriteSave]~> dl![m]{ { storage := save(storage, alice.age, v) } ⟨[ ]⟩ φ } := by sol_chain
      _ ~[emptyModality]~> dl![m]{ { storage := save(storage, alice.age, v) } φ } := by sol_chain
-/
#guard_msgs in
example : dl![m]{ ⟨[ alice.age = v; ]⟩ φ } ~*> dl![m]{ { storage := save(storage, alice.age, v) } φ } := by
  sol_chain?

end

end Solidity.Examples.ProofTree
