import Solidity.Tools.ProofTree
import Solidity.Calculus.ChainGen
import Solidity.Calculus.Derive

/-!
# The proof tree, pinned

solkey's view of a proof, a tree of sequents (`Calculus/ProofTree.lean`), and
the tactics that write a proof out, as `#guard_msgs` tests:

* `#proof_tree`, `#proof_node` and `#proof_tree_json` (`Tools/ProofTree.lean`)
  print the tree of `⊢ φ` as solkey's GUI and web prover do;
* `sol_derive?` suggests the `apply` walk the tree is, `sol_chain?` the
  `calc` a derivation `φ ~*> ψ` is;
* `sol_prove?` suggests `sol_prove` (`Calculus/Derive.lean`), the same walk
  as one kernel evaluation, and a tactic per leaf its closer leaves.

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

/-! ## `sol_prove?`: the walk in one evaluation

A write read back: the leaf closes by its terms (`LFml.syn`) inside the
residue, and the replay is `sol_prove` alone. -/

/--
info: Try this:
  sol_prove
-/
#guard_msgs in
example : ⊢ dl!{ [ alice.age = v; uint y = alice.age; ] y == v } := by
  sol_prove?

/-! `guardedCopy`'s three leaves do not close by their terms alone
(`LFml.syn`): each is left, a `case` of its own, and closed by `sol_decide`'s
next step. -/

/--
info: Try this:
  sol_prove
    case leaf1 =>
      refine Proves.close ?_
      sol_symex
      refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
      sol_reduce
      sol_decide_cons
    case leaf2 =>
      refine Proves.close ?_
      sol_symex
      refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
      sol_reduce
      sol_decide_cons
    case leaf3 =>
      refine Proves.close ?_
      sol_symex
      refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
      sol_reduce
      sol_decide_cons
-/
#guard_msgs in
example : ⊢ dl!{ a == 1 → ⟨ uint x = a; require(x == 1); ⟩ x == 1 } := by
  sol_prove?

/-! ## A failed `assert`

`assertSimple` checks its condition: two goals, `thn` (the run goes on) and
`els`, that the condition holds (a panic does not satisfy the box, so this
goal has nothing to close but the condition).  The tree, the walk
(`Proves.check`) and `sol_prove`'s residue each go through it once. -/

/--
info: 0: impRight
1: localValueDeclInitDrop
2: localValueAssign
3: assertConditionCapture
4: localValueDeclInitDrop
5: binopAssignment
6: assertSimple
  [thn]
    7: emptyModality
    8: Closed goal
  [els]
    9: Closed goal
closed: 0 open goal(s), 10 node(s), 2 branch(es)
-/
#guard_msgs in
#proof_tree dl!{ a == 1 → [ uint x = a; assert(x == 1); ] x == 1 }

/--
info: Try this:
  apply intro
    apply unfold .localValueDeclInitDrop
    apply update .localValueAssign
    apply unfold .assertConditionCapture
    apply unfold .localValueDeclInitDrop
    apply update .binopAssignment
    apply Proves.check .assertSimple
    case thn =>
      apply empty
      refine close ?_
      sol_symex
      sol_close
    case els =>
      refine close ?_
      sol_symex
      sol_close
-/
#guard_msgs in
example : ⊢ dl!{ a == 1 → [ uint x = a; assert(x == 1); ] x == 1 } := by
  sol_derive?

/--
info: Try this:
  sol_prove
    refine Proves.close ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons
-/
#guard_msgs in
example : ⊢ dl!{ a == 1 → [ uint x = a; assert(x == 1); ] x == 1 } := by
  sol_prove?

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

/-! ## `#chain`, `sol_rws`: past the program

`#chain φ` goes on where `sol_chain?` on `~*>` stops: after the program, one
rewrite a link until the line is last, written as one chain term to paste.
The strategy's steps are grouped as the paper prints them
(`ChainGen.groupSteps`): a rule with the `emptyModality` after it, and a
declaration with the binding or read it leaves, are one `~*>`. -/

section
variable (m : Modality) (φ : Post StandardExample)

/--
info: theorem chain :
    dl![m]{ ⟨[ alice.age = v; x = 1; ]⟩ φ }
    ~[storageFieldWriteSave]~> dl![m]{ { storage := save(storage, alice.age, v) } ⟨[ x = 1; ]⟩ φ }
    ~*> dl![m]{ { storage := save(storage, alice.age, v) } { x := 1 } φ }
    ~[sequentialToParallel]~> dl![m]{ { storage := save(storage, alice.age, v) ‖ x := 1 } φ } := by
  sol_chain
-/
#guard_msgs in
#chain dl![m]{ ⟨[ alice.age = v; x = 1; ]⟩ φ }

-- A concrete starting state in front of the program: the declaration and
-- its read are one `~*>`, and the read resolves to the literal.
/--
info: theorem chain :
    dl![m]{ { storage := save(storage, alice.age, 42) } ⟨[ uint x = alice.age; ]⟩ φ }
    ~*> dl![m]{ { storage := save(storage, alice.age, 42) } { x := find(storage, alice.age) } φ }
    ~[sequentialToParallel]~> dl![m]{ { storage := save(storage, alice.age, 42) ‖ x := find(save(storage, alice.age, 42), alice.age) } φ }
    ~[findOnSave]~> dl![m]{ { storage := save(storage, alice.age, 42) ‖ x := 42 } φ } := by
  sol_chain
-/
#guard_msgs in
#chain dl![m]{ { storage := save(storage, alice.age, 42) } ⟨[ uint x = alice.age; ]⟩ φ }

/-- The program by the strategy, then the merge and the read of the fresh
`Person` in one link. -/
example :
    dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
            ⟨[ v = carol.account.balance; ]⟩ φ }
    ~~> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) ‖
          mv1 := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖ v := 0 } φ } :=
  calc dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
               ⟨[ v = carol.account.balance; ]⟩ φ }
    _ ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          { mv1 := read(memory, carol.account) } { v := read(memory, mv1.balance) } φ } := by sol_chain
    _ ~~> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) ‖
          mv1 := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖ v := 0 } φ } := by
      sol_rws [sequentialToParallel, readAddEqual]

/--
info: Try this:
  sol_rws [sequentialToParallel]
-/
#guard_msgs in
example : dl![m]{ { storage := save(storage, alice.age, v) } { x := 1 } φ }
    ~~> dl![m]{ { storage := save(storage, alice.age, v) ‖ x := 1 } φ } := by
  sol_rws?

/-! `sol_chain?` on `~~>` at any length: one rewrite, one step, none. -/
#guard_msgs (drop info) in
example : dl![m]{ { storage := save(storage, alice.age, v) } { x := 1 } φ }
    ~~> dl![m]{ { storage := save(storage, alice.age, v) ‖ x := 1 } φ } := by
  sol_chain?

#guard_msgs (drop info) in
example : dl![m]{ { x := 1 } ⟨[ ]⟩ φ } ~~> dl![m]{ { x := 1 } φ } := by
  sol_chain?

#guard_msgs (drop info) in
example : dl![m]{ { x := 1 } φ } ~~> dl![m]{ { x := 1 } φ } := by
  sol_chain?

end

end Solidity.Examples.ProofTree
