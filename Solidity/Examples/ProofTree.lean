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

A write read back: the leaf closes by the closer (`LFml.close`) inside the
residue, and the replay is `sol_prove` alone. -/

/--
info: Try this:
  sol_prove
-/
#guard_msgs in
example : ⊢ dl!{ [ alice.age = v; uint y = alice.age; ] y == v } := by
  sol_prove?

/-! `guardedCopy` closes inside the residue too: its premise `a == 1`
gives `a` the value `1` (KeY's `applyEq`), and `x == 1` folds to `true`. -/

/--
info: Try this:
  sol_prove
-/
#guard_msgs in
example : ⊢ dl!{ a == 1 → ⟨ uint x = a; require(x == 1); ⟩ x == 1 } := by
  sol_prove?

/-! Intervals: a premise `x <= 100` bounds the `uint` local `x`, so the
diamond's `x + 1` stays in range; under the box, `require(x >= 1 && …)`
keeps `x - 1` in range and decides `y < 100`. -/

/--
info: Try this:
  sol_prove
-/
#guard_msgs in
example : ⊢ dl!{ ∀ uint x; x <= 100 → ⟨ uint y = x + 1; ⟩ y == x + 1 } := by
  sol_prove?

/--
info: Try this:
  sol_prove
-/
#guard_msgs in
example : ⊢ dl!{ ∀ uint x; [ require(x >= 1 && x <= 100); uint y = x - 1; ] y < 100 } := by
  sol_prove?

/-! Two writes at keys the premises do not separate: the leaf is left, and
closed by `sol_decide`'s next step, which splits on `k == j`. -/

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
example : ⊢ dl!{ [ balances[k] = 5; balances[j] = 5; ] balances[k] == 5 } := by
  sol_prove?

/-! A parallel update: `r = ++x;` leaves `{ x := x + 1 ‖ r := x + 1 }`,
which the closer reads only once `Fml.seqUpd` has split it. -/

/--
info: Try this:
  sol_prove
-/
#guard_msgs in
example : ⊢ dl!{ ⟨ uint x = 5; uint r = ++x; ⟩ r == 6 && x == 6 } := by
  sol_prove?

/-! A replay must fit one declaration's `maxHeartbeats` (`Derive.replayFits`,
which `#solkey_derive?` reports as pending and `sol_prove?` warns of).  A
statement's own elaboration needs more than a limit low enough to refuse a
small replay, so the test is pinned on its own, at a limit of 1000 raw
heartbeats. -/

/-- info: [false, true, true] -/
#guard_msgs in
#eval show Lean.CoreM (List Bool) from do
  let at_ (max hb : Nat) : Lean.CoreM Bool :=
    withTheReader Lean.Core.Context ({ · with maxHeartbeats := max }) (Derive.replayFits hb)
  return [← at_ 1000 2000, ← at_ 1000 1000, ← at_ 0 2000]

/-! Memory: `Person memory carol;` leaves the pair
`{ carol := freshId(addM(memory)) ‖ memory := addM(memory) }`, which
`Fml.seqUpd` keeps whole (`Derive.memAlloc?`); `alice = carol;` copies the
memory object into storage as its view.  Both leaves close inside the
residue. -/

/--
info: Try this:
  sol_prove
-/
#guard_msgs in
example : ⊢ dl!{ [ Person memory carol; carol.age = 5; uint x = carol.age; ] x == 5 } := by
  sol_prove?

/--
info: Try this:
  sol_prove
-/
#guard_msgs in
example : ⊢ dl!{ [ Person memory carol; carol.age = 42; alice = carol; carol.age = 43;
                   uint x = alice.age; ] x == 42 } := by
  sol_prove?

/-! Arrays and copies (`LStor.arr`, `LStor.copy`): a push, a `pop` after
it and a copy close inside the residue; under `wt(storage)` the diamond of
a push and a `pop` returns (a length is at least `0`, `Facts.lo`), and so
does a write below the slot a `push()` of a struct takes, through an index
or through the alias it returns (`Derive.pushAlias?`, `Facts.slotTy`). -/

/--
info: Try this:
  sol_prove
-/
#guard_msgs in
example : ⊢ dl!{ [ values.push(3); uint n = values.length; ] n > 0 } := by
  sol_prove?

/--
info: Try this:
  sol_prove
-/
#guard_msgs in
example : ⊢ dl!{ [ uint n = values.length; values.push(3); values.pop(); uint m = values.length; ]
    m == n } := by
  sol_prove?

/--
info: Try this:
  sol_prove
-/
#guard_msgs in
example : ⊢ dl!{ [ alice = bob; uint x = bob.age; ] alice.age == x } := by
  sol_prove?

/-- `wt(storage)`, the premise of a diamond obligation (`Fml.wt`). -/
def wtStd : Fml StandardExample := .defined (.wt StandardExample.vars .storage)

/--
info: Try this:
  sol_prove
-/
#guard_msgs in
example : ⊢ .imp wtStd dl!{ ⟨ values.push(3); values.pop(); ⟩ true } := by
  sol_prove?

/--
info: Try this:
  sol_prove
-/
#guard_msgs in
example : ⊢ .imp wtStd dl!{ ⟨ persons.push(); persons[0].age = 1; ⟩ true } := by
  sol_prove?

/--
info: Try this:
  sol_prove
-/
#guard_msgs in
example : ⊢ .imp wtStd dl!{ ⟨ Person storage p = persons.push(); p.age = 1; ⟩ true } := by
  sol_prove?

/-! The reduction's compiled code reads a pushed array's old length and
value only where the read needs them (`CaseTree.toTermLazy`).  Run
strictly, the work doubled with each push (twelve onto one array: 23 ms;
twelve onto each of two, interleaved: 106 s), and `sol_prove?`'s size test
(`Derive.leafFits`) builds the reduction before it counts it.  Here the leaf
is within `closeSize` and its reduction past `elimSize`: refused in
milliseconds. -/

/-- Twenty-two pushes onto one array. -/
def pushes22 : Fml StandardExample :=
  dl!{ [
    values.push(0); values.push(1); values.push(2); values.push(3); values.push(4);
    values.push(5); values.push(6); values.push(7); values.push(8); values.push(9);
    values.push(10); values.push(11); values.push(12); values.push(13); values.push(14);
    values.push(15); values.push(16); values.push(17); values.push(18); values.push(19);
    values.push(20); values.push(21); ]
    values.length > 0 }

#guard (Derive.residue Derive.budget Derive.synClose Derive.budget [] pushes22).map
  (fun (ls, _) => ls.map fun (l : List (Hyp StandardExample) × Fml StandardExample) =>
    (((Hyp.wrap (Derive.dropWt l.1) l.2).seqUpd.toL Decide.Sym.empty).fits
      Derive.closeSize).isSome && !Derive.leafFits l.1 l.2) == some [true]

/-! The size bound (`Derive.closeSize`): a storage written from its own
read doubles the leaf with each write.  Four `total += 1;` close inside the
residue; six leave one leaf past the bound, which neither the closer nor
`sol_prove?`'s reducing steps attempt (`Derive.leafFits`). -/

/-- Four writes of `total` from its own read. -/
def writes4 : Fml StandardExample :=
  dl!{ [ total = 0; total += 1; total += 1; total += 1; total += 1; ] total == 4 }

/-- Six writes of `total` from its own read. -/
def writes6 : Fml StandardExample :=
  dl!{ [ total = 0; total += 1; total += 1; total += 1; total += 1; total += 1;
    total += 1; ] total == 6 }

#guard Derive.proves [] writes4
#guard (Derive.residue Derive.budget Derive.synClose Derive.budget [] writes6).map
  (fun (ls, _) => ls.map fun (l : List (Hyp StandardExample) × Fml StandardExample) =>
    Derive.leafFits l.1 l.2) == some [false]

/-! The reduction is bounded apart (`Derive.elimSize`): a read below a
`delete` carries the read before it twice, so ten deletes make a leaf of
330 nodes, within `closeSize`, whose reduction has 79587. -/

/-- Ten deletes of `wallet`, then a read of its mapping member. -/
def deletes10 : Fml StandardExample :=
  dl!{ [ delete wallet; delete wallet; delete wallet; delete wallet; delete wallet;
    delete wallet; delete wallet; delete wallet; delete wallet; delete wallet; ]
    wallet.stash[owner] == 0 }

#guard (Derive.residue Derive.budget Derive.synClose Derive.budget [] deletes10).map
  (fun (ls, _) => ls.map fun (l : List (Hyp StandardExample) × Fml StandardExample) =>
    (((Hyp.wrap (Derive.dropWt l.1) l.2).seqUpd.toL Decide.Sym.empty).fits
      Derive.closeSize).isSome && !Derive.leafFits l.1 l.2) == some [true]

/-! A power is folded only up to the exponent `256` (`Decide.powBig`):
`Int.pow` recurses once per unit of it, heeding no heartbeats. -/

#guard match Decide.foldBin .pow .uint (.lit (.int 2)) (.lit (.int 1000000000)) with
  | .binop .. => true
  | _ => false
#guard match Decide.foldBin .pow .uint (.lit (.int 2)) (.lit (.int 255)) with
  | .lit (.int v) => v == 2 ^ 255
  | _ => false

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
The strategy's steps are grouped as the worked examples print them
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
