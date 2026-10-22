import Solidity.Tools.ProofTree
import Solidity.Tools.Inspect
import Solidity.Calculus.Derive
import Solidity.Calculus.Closers
import Solidity.Calculus.ProvesDerive
import Solidity.Tools.CompleteVerification

/-!
# The proof tree, pinned

solkey's view of a proof, a tree of sequents (`Calculus/ProofTree.lean`), and
the tactics that write a proof out, as `#guard_msgs` tests:

* `#proof_tree`, `#proof_node` and `#proof_tree_json` (`Tools/ProofTree.lean`)
  print the tree of `⊢ φ` as solkey's GUI and web prover do;
* `sol_derive?` suggests the `apply` walk the tree is;
* `sol_prove?` suggests `sol_prove` (`Calculus/ProvesDerive.lean`), the same walk
  as one kernel evaluation, and a tactic per leaf its closer leaves.

If the strategy picks another rule, or a printer changes, these fail.

The sections `Scoped` read the scoped calculus (`open scoped
Solidity.Scoped`, `docs/intrinsic.md`, W3): a tree of `⊢ φ` over
`Proves` (`Calculus/ProofTree.lean`), a walk of its rules
(`Calculus/Derive.lean`) written in today's walk text, which the
scope's macros read (`Calculus/WalkSyntax.lean`; the steps KeY does
not show, a scope's end, a hidden binder and the parameters' `∀`, are not
written).  There a parameter is bound by `∀`, so a tree starts with
`allRight`; a rule that leaves no statement goes on into the
rest of the program, so no `emptyModality` follows it; a split has KeY's two
goals under either modality, its branch's `}` printed; under `sol_prove` a
leaf closes on its scoped form (`Calculus/LeafDerive.lean`,
`Proves.closeHolds`), behind diamond updates too (an update's reading asks
only of the typed states it may end in), and one it leaves by `sol_leaf`
and a closer.  `sol_prove?` is the scoped one (`Calculus/Closers.lean`).
The chains the tactics write (`sol_chain?`, `#chain`, `sol_rws?`) are
pinned in `Examples/Tactics/Chains.lean`.

A node's tactics (`#proof_node`) are the ones it elaborated,
`apply Proves.update (Taclet.toStep .localValueAssign); apply
Proves.updIntro`, where master printed the walk text `apply update
.localValueAssign`: the scoped node applies the `Proves` constructor with
the taclet's `toStep` and folds the silent moves after it in
(`Calculus/ProofTree.lean`).
-/

namespace Solidity.Examples.ProofTree


local instance : InContract := ⟨StandardExample⟩

section Scoped
open scoped Scoped

/-! ## The tree

`a == 1 → ⟨ uint x = a; require(x == 1); ⟩ x == 1`: the parameter's `∀`,
a run of steps, one flat branch, then `requireSimple`'s goals, each a
sub-branch labelled as solkey labels it ("Holds", "Reverts").  `x == 1` is
`binopAssignment` at `==`, which prints as KeY's `boolEqualityAssignment`.
The leaves sit behind the diamond's updates, which `sol_leaf` takes. -/

/--
info: 0: allRight
1: impRight
2: localValueDeclInitDrop
3: localValueAssign
4: requireConditionCapture
5: localValueDeclInitDrop
6: boolEqualityAssignment
7: requireSimple
  [Holds]
    8: Closed goal
  [Reverts]
    9: revertDiamond
    10: Closed goal
closed: 0 open goal(s), 11 node(s), 2 branch(es)
-/
#guard_msgs in
#proof_tree dl!{ a == 1 → ⟨ uint x = a; require(x == 1); ⟩ x == 1 }

/-! A write under the diamond is valid over typed states: a typed storage
has every member, so a write along a path through no array slot returns
(`CloseS.wp_diamond_write_total`), and the leaf closes. -/
/--
info: 0: storageFieldWriteSave
1: Closed goal
closed: 0 open goal(s), 2 node(s), 1 branch(es)
-/
#guard_msgs in
#proof_tree dl!{ ⟨ alice.age = 1; ⟩ true }

/-! ## A node, and the tree as data

`#proof_node n φ` is solkey's `node` request; `#proof_tree_json φ` its `tree`
request, the rows `[serial, parent, name, branchLabel, state]`. -/

/--
info: node: 2
sequent:
  dl{ ∀ uint x, true = true ⟹ [ x = 2; } ] ¬x = 0 }
rule: localValueAssign
state: inner
branch: if true true
parent: 1
children: [3]
tactics: apply Proves.update (Taclet.toStep .localValueAssign); apply Proves.updIntro
-/
#guard_msgs in
#proof_node 2 dl!{ [ if (true) { x = 2; } else { x = 1; }; ] x != 0 }

/--
info: {"stats": {"nodes": 6, "branches": 2},
 "sequents":
 ["dl{ ⟹ ∀ uint x; [ if (true) {x = 2;} else {x = 1;}; ] ¬x = 0 }",
  "dl{ ∀ uint x ⟹ [ if (true) {x = 2;} else {x = 1;}; ] ¬x = 0 }",
  "dl{ ∀ uint x, true = true ⟹ [ x = 2; } ] ¬x = 0 }",
  "dl{ ∀ uint x, true = true, { x := 2 } ⟹ ¬x = 0 }",
  "dl{ ∀ uint x, true = false ⟹ [ x = 1; } ] ¬x = 0 }",
  "dl{ ∀ uint x, true = false, { x := 1 } ⟹ ¬x = 0 }"],
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
#proof_tree_json dl!{ [ if (true) { x = 2; } else { x = 1; }; ] x != 0 }

/-! The labels are the ones the rules write (`"if s#se true": …`, dropped by
the macro), `Taclet.branchLabels`; this reads `Calculus/Rules.lean` and fails
where the two disagree.  A label names what its schema variable stands for
at the node, as KeY's `NodeInfo.setBranchLabel` does: `if true true` above,
the condition's fresh local below. -/

/-- The strings between double quotes in `s`. -/
def quoted (s : String) : List String := go (s.splitOn "\"")
where
  go : List String → List String
    | _ :: q :: rest => q :: go rest
    | _ => []

#guard_msgs in
#eval show IO Unit from do
  let src ← IO.FS.readFile "Solidity/Calculus/Rules.lean"
  for (r, ls) in Taclet.branchLabels do
    let some rest := (src.splitOn s!"  | {r} ")[1]? | throw (IO.userError s!"no rule {r}")
    -- the rule's text: up to the next constructor, docstring, comment or blank line
    let body := ["\n  |", "\n  /-", "\n  --", "\n\n"].foldl (fun b sep => (b.splitOn sep)[0]!) rest
    let written := quoted body
    unless written == ls do
      throw (IO.userError s!"{r} writes the labels {written}, Taclet.branchLabels {ls}")

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
#proof_tree dl!{ [ if (a == 1) { x = 2; } else { x = 1; }; ] true }

/-! A `try` has a goal for each way the call may end, labelled as
`tryCallNoCallbackBox` labels them. -/

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
#proof_tree dl!{ [ try I(7).get() returns (uint v) { x = v; } catch { x = 0; }; ] true }

/-! A send has a goal for each outcome, labelled as `sendNoCallbackBox`
labels them; under the diamond the amount's sign is owed first
(`sendNoCallbackDiamond`). -/

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
#proof_tree dl!{ [ ok = to.send(5); ] true }

/-! A send's walk takes the rule's goals apart on its `apply` line, so a
replayed walk touches only them. -/

/--
info: Try this:
  apply Proves.fmlValid
    apply cases .sendNoCallbackBox <;>
        (try simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]) <;>
      (try and_intros)
    · sol_leaf
      sol_close
    · sol_leaf
      sol_close
-/
#guard_msgs in
example : ⊨ᶠ dl!{ [ ok = to.send(5); ] true } := by
  sol_derive?

/-! The box walk replayed beside another open goal, which it leaves alone,
in the scoped calculus's own constructors: the parameter's `∀` is
`allRight`, the hidden binder of `ok`, which the program assigns without
declaring, `bindIntro`. -/

example : (⊨ᶠ dl!{ [ ok = to.send(5); ] true }) ∧ (1 = 1 ∧ 2 = 2) := by
  refine ⟨?_, ?_⟩
  refine Proves.fmlValid (R := RuleSet.all) ?_
  refine Proves.allRight ?_
  refine Proves.bindIntro ?_
  apply Proves.cases (Taclet.step_eq .sendNoCallbackBox) rfl <;>
      (try simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]) <;>
    (try and_intros)
  · exact Proves.closeTrue rfl
  · exact Proves.closeTrue rfl
  exact ⟨rfl, rfl⟩

/-! Under the diamond the leaves sit behind the diamond's updates, which
`sol_leaf` takes: here `to := 9`, `ok := true`,
`ok := false`. -/

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
#proof_tree dl!{ ⟨ uint to = 9; ok = to.send(5); ⟩ true }

/--
info: Try this:
  apply Proves.fmlValid
    apply unfold .localValueDeclInitDrop
    apply update .localValueAssign
    apply cases .sendNoCallbackDiamond <;>
        (try simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]) <;>
      (try and_intros)
    · sol_leaf
      sol_close
    · sol_leaf
      sol_close
    · sol_leaf
      sol_close
-/
#guard_msgs in
example : ⊨ᶠ dl!{ ⟨ uint to = 9; ok = to.send(5); ⟩ true } := by
  sol_derive?

/-! The same two by the reflective driver (`Derive.residue`, its
`Premise.cases` arm). -/

/--
info: Try this:
  sol_prove (steps := 128)
-/
#guard_msgs in
example : ⊢ dl!{ [ ok = to.send(5); ] true } := by
  sol_prove?

/--
info: Try this:
  sol_prove (steps := 128)
    sol_leaf
    sol_close
-/
#guard_msgs in
example : ⊢ dl!{ ⟨ uint to = 9; ok = to.send(5); ⟩ true } := by
  sol_prove?

/-! A split has KeY's two goals (`Proves.split`): no `cov`. -/

/--
info: 0: allRight
1: impRight
2: localValueDeclInitDrop
3: localValueAssign
4: requireConditionCapture
5: localValueDeclInitDrop
6: boolEqualityAssignment
7: requireSimple
  [Holds]
    8: Closed goal
  [Reverts]
    9: revertBox
    10: Closed goal
closed: 0 open goal(s), 11 node(s), 2 branch(es)
-/
#guard_msgs in
#proof_tree dl!{ a == 1 → [ uint x = a; require(x == 1); ] x == 1 }

/--
info: Try this:
  apply splitBox .ifElseSplit
    case thn =>
      apply update .localValueAssign
      sol_leaf
      sol_close
    case els =>
      apply update .localValueAssign
      sol_leaf
      sol_close
-/
#guard_msgs in
example : ⊢ dl!{ [ if (true) { x = 2; } else { x = 1; }; ] x != 0 } := by
  sol_derive?

/-- The suggestion replayed: today's walk text, which the scope's macros
read (`Calculus/WalkSyntax.lean`). -/
example : ⊢ dl!{ [ if (true) { x = 2; } else { x = 1; }; ] x != 0 } := by
  apply splitBox .ifElseSplit
  case thn =>
    apply update .localValueAssign
    sol_leaf
    sol_close
  case els =>
    apply update .localValueAssign
    sol_leaf
    sol_close

/-! ## `sol_derive?`: the walk

The suggestion is the walk `ApplySteps.guardedCopy` writes by hand, today's
text with no `cov` goal; each leaf closes behind the diamond's updates
(`Fml.closableB`). -/

/--
info: Try this:
  apply impRight
    apply unfold .localValueDeclInitDrop
    apply update .localValueAssign
    apply unfold .requireConditionCapture
    apply unfold .localValueDeclInitDrop
    apply update .binopAssignment
    apply split .requireSimple
    case thn =>
      sol_leaf
      sol_close
    case els =>
      apply done .revertDiamond
      sol_leaf
      sol_close
-/
#guard_msgs in
/-- `a == 1 → ⟨ uint x = a; require(x == 1); ⟩ x == 1`. -/
theorem guardedCopy : ⊢ dl!{ a == 1 → ⟨ uint x = a; require(x == 1); ⟩ x == 1 } := by
  sol_derive?

/--
info: Try this:
  apply Proves.fmlValid
    apply update .storageFieldWriteSave
    apply unfold .transfer_unfold_rightSndArgument
    apply unfold .localValueDeclInitDrop
    apply update .binopAssignment
    apply update .transferNoCallbackBox
    apply unfold .localValueDeclInitDrop
    apply update .storageFieldReadFind
    sol_leaf
    sol_close
-/
#guard_msgs in
/-- `alice.age = 1; to.transfer(x + 2); uint y = alice.age;`: on `⊨ᶠ φ` the
walk starts with `apply Proves.fmlValid`; the payment, once its amount is
captured, is one update (`transferNoCallbackBox`). -/
theorem transferFrameStorage :
    ⊨ᶠ dl!{ [ alice.age = 1; to.transfer(x + 2); uint y = alice.age; ] y == 1 } := by
  sol_derive?

/-! ## `sol_prove?`: the walk in one evaluation

A write read back: the leaf closes by the closer (`LFml.close`) inside the
residue, and the replay retains its selected step budget. -/

/-- error: sol_prove: steps must be between 1 and 20000 -/
#guard_msgs in
example : ⊢ dl!{ ⟨ ⟩ true } := by
  sol_prove (steps := 0)

/-- error: sol_prove: steps must be between 1 and 20000 -/
#guard_msgs in
example : ⊢ dl!{ ⟨ ⟩ true } := by
  sol_prove (steps := 20001)

/--
info: Try this:
  sol_prove (steps := 128)
-/
#guard_msgs in
example : ⊢ dl!{ [ alice.age = v; uint y = alice.age; ] y == v } := by
  sol_prove?

/-! `guardedCopy` closes inside the residue too: its premise `a == 1`
gives `a` the value `1` (KeY's `applyEq`), and `x == 1` folds to `true`. -/

/--
info: Try this:
  sol_prove (steps := 128)
-/
#guard_msgs in
example : ⊢ dl!{ a == 1 → ⟨ uint x = a; require(x == 1); ⟩ x == 1 } := by
  sol_prove?

/-! Two writes at keys the premises do not separate: the closer splits on
`k == j` inside the residue. -/

/--
info: Try this:
  sol_prove (steps := 128)
-/
#guard_msgs in
example : ⊢ dl!{ [ balances[k] = 5; balances[j] = 5; ] balances[k] == 5 } := by
  sol_prove?

/-! A parallel update: `r = ++x;` leaves `{ x := x + 1 ‖ r := x + 1 }`,
which the scoped closer reads with both elements in the state before it
(`ElemS.parOk`, `RelU.par`). -/

/--
info: Try this:
  sol_prove (steps := 128)
-/
#guard_msgs in
example : ⊢ dl!{ ⟨ uint x = 5; uint r = ++x; ⟩ r == 6 && x == 6 } := by
  sol_prove?

/-! A split whose condition is ground under its updates keeps only the
branch it takes (`Hyps.groundS`, `Seq.refuteS`): the `revert()` branches are closed by
`Proves.closeFalse`, not run (two steps fewer in each).  The second reads `y` through twelve updates
`y := y * y`, each position listed once (`Upd.groundStepS`), not `2¹²` times. -/

/--
info: Try this:
  sol_prove (steps := 128)
-/
#guard_msgs in
example : ⊢ dl!{ ⟨ int v = -3; int r = 0; if (v < 0) { r = 1; } else { revert(); }; ⟩ r == 1 } := by
  sol_prove?

/--
info: Try this:
  sol_prove (steps := 128)
-/
#guard_msgs in
example : ⊢ dl!{ [ uint y = 1; y = y * y; y = y * y; y = y * y; y = y * y; y = y * y;
    y = y * y; y = y * y; y = y * y; y = y * y; y = y * y; y = y * y; y = y * y;
    if (y > 0) { y = 1; } else { revert(); }; ] y == 1 } := by
  sol_prove?

/-! Memory: `Person memory carol;` leaves the pair
`{ carol := freshId(addM(memory)) ‖ memory := addM(memory) }`, which the
scoped closer reads as one allocation (`pairLS`); `alice = carol;` copies the
memory object into storage as its view.  Both leaves close inside the
residue. -/

/--
info: Try this:
  sol_prove (steps := 128)
-/
#guard_msgs in
example : ⊢ dl!{ [ Person memory carol; carol.age = 5; uint x = carol.age; ] x == 5 } := by
  sol_prove?

/--
info: Try this:
  sol_prove (steps := 128)
-/
#guard_msgs in
example : ⊢ dl!{ [ Person memory carol; carol.age = 42; alice = carol; carol.age = 43;
                   uint x = alice.age; ] x == 42 } := by
  sol_prove?

/-! Arrays and copies (`pushRd`, `popRd`, `ovRS`): a push, a `pop` after
it and a copy close inside the residue; under `wt(storage)` the diamond of
a push and a `pop` returns (a length is at least `0`, `Facts.range`), and so
does a write below the slot a `push()` of a struct takes, through an
index. -/

/--
info: Try this:
  sol_prove (steps := 128)
-/
#guard_msgs in
example : ⊢ dl!{ [ values.push(3); uint n = values.length; ] n > 0 } := by
  sol_prove?

/--
info: Try this:
  sol_prove (steps := 128)
-/
#guard_msgs in
example : ⊢ dl!{ [ uint n = values.length; values.push(3); values.pop(); uint m = values.length; ]
    m == n } := by
  sol_prove?

/--
info: Try this:
  sol_prove (steps := 128)
-/
#guard_msgs in
example : ⊢ dl!{ [ alice = bob; uint x = bob.age; ] alice.age == x } := by
  sol_prove?

/-- `wt(storage)`, the premise of a diamond obligation (`Fml.wt`).  A push
at a full array (`Storage.full`) is out of gas, in the run and in the
update the walk leaves (`Upd.exh`), which both modalities accept. -/
def wtStd : Fml StandardExample [] := Fml.wt StandardExample

/--
info: Try this:
  sol_prove (steps := 128)
-/
#guard_msgs in
example : ⊢ .imp wtStd dl!{ ⟨ values.push(3); values.pop(); ⟩ true } := by
  sol_prove?

/--
info: Try this:
  sol_prove (steps := 128)
-/
#guard_msgs in
example : ⊢ .imp wtStd dl!{ ⟨ persons.push(); persons[0].age = 1; ⟩ true } := by
  sol_prove?

/- Through the alias a `push()` returns (`Person storage p = persons.push();
p.age = 1;`), the parallel binding's definedness is retained. The scoped
reader accepts resource exhaustion at a full array for this two-element
update as it does for a single storage push. -/

/-- The write through a `push()`'s alias, under the diamond. -/
def pushAlias : Fml StandardExample [] :=
  .imp wtStd dl!{ ⟨ Person storage p = persons.push(); p.age = 1; ⟩ true }

#guard (Seq.residue .all .nil pushAlias).map List.isEmpty == some true

/--
info: Try this:
  sol_prove (steps := 128)
-/
#guard_msgs in
example : ⊢ pushAlias := by
  sol_prove?

/-! The length past a push, read back under the diamond: the push's room is
the premise of what follows it (`roomM`), which bounds the length (W9.8.5). -/
/--
info: Try this:
  sol_prove (steps := 128)
-/
#guard_msgs in
example : ⊢ .imp wtStd dl!{ ⟨ persons.push(); uint n = persons.length - 1; ⟩ true } := by
  sol_prove?

/-! Intervals: a premise `x <= 100` bounds the `uint` local `x`, so the
diamond's `x + 1` stays in range; under the box, `require(x >= 1 && …)`
keeps `x - 1` in range and decides `y < 100`.  The explicit `∀` keeps `x`'s
range at the leaf: `cdl!` marks it, so it is not a parameter, and only the
parameters' `∀`s are bound as parameters (decision 28; the scoped closer
reads each at its type). -/

/--
info: Try this:
  sol_prove (steps := 128)
-/
#guard_msgs in
example : ⊢ dl!{ ∀ uint x; x <= 100 → ⟨ uint y = x + 1; ⟩ y == x + 1 } := by
  sol_prove?

/--
info: Try this:
  sol_prove (steps := 128)
-/
#guard_msgs in
example : ⊢ dl!{ ∀ uint x; [ require(x >= 1 && x <= 100); uint y = x - 1; ] y < 100 } := by
  sol_prove?

/-! After a walk's prefix the parameters are the context's: `apply intro`
binds `x`'s `∀` and takes the premise, and `sol_prove` counts the
parameters from the context's outermost entry down to the first
precondition (`Seq.paramCount`): one. -/

/-- info: some (1) -/
#guard_msgs in
example : ⊢ dl!{ x <= 100 → ⟨ uint y = x + 1; ⟩ y == x + 1 } := by
  apply intro
  run_tac do
    let ty ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    Lean.logInfo m!"{← Seq.paramCount ty.appFn!.appArg! (← Symex.evaluable ty.appArg!)}"
  sol_prove (steps := 128)

end Scoped

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

section Scoped
open scoped Scoped

/-! Each push stacks a storage update a later read is taken through, and
the elimination reads each through the ones below it.  `sol_prove?`'s size
test (`Seq.leafFitsOn`) counts the stack before the elimination
(`Seq.stackSize`): here the leaf is within `closeSize` and its stack of
twenty-two past the bound, refused in milliseconds.  The leaves are the `⊢`
walk's (`Seq.residue`), read as the closer reads them (`Hyps.wrap`,
`Fml.toLS`). -/

/-- The walk's leaves of `φ`, each read as the closer reads it: within
`closeSize`, its storage stack, and whether `leafFitsOn` takes it. -/
def leafStats (φ : Fml StandardExample []) : Option (List (Bool × Nat × Bool)) :=
  (Seq.residue .all .nil φ).map fun ls => ls.map fun (l : Seq.SLeaf StandardExample) =>
    match (l.2.1.wrap l.2.2).toLS true Decide.SymS.init with
    | some x => ((x.fits Seq.closeSize).isSome, x.stDepth, Seq.leafFitsOn (l.2.1.wrap l.2.2))
    | none => (false, 0, false)

/-- Twenty-two pushes onto one array. -/
def pushes22 : Fml StandardExample [] :=
  dl!{ [
    values.push(0); values.push(1); values.push(2); values.push(3); values.push(4);
    values.push(5); values.push(6); values.push(7); values.push(8); values.push(9);
    values.push(10); values.push(11); values.push(12); values.push(13); values.push(14);
    values.push(15); values.push(16); values.push(17); values.push(18); values.push(19);
    values.push(20); values.push(21); ]
    values.length > 0 }

#guard leafStats pushes22 == some [(true, 22, false)]

/-! A storage written from its own read: the literals fold where the
terms are built, so four and six `total += 1;` both close inside the
residue. -/

/-- Four writes of `total` from its own read. -/
def writes4 : Fml StandardExample [] :=
  dl!{ [ total = 0; total += 1; total += 1; total += 1; total += 1; ] total == 4 }

/-- Six writes of `total` from its own read. -/
def writes6 : Fml StandardExample [] :=
  dl!{ [ total = 0; total += 1; total += 1; total += 1; total += 1; total += 1;
    total += 1; ] total == 6 }

#guard (Seq.residue .all .nil writes4).map List.isEmpty == some true
#guard (Seq.residue .all .nil writes6).map List.isEmpty == some true

/-! Ten deletes stack ten storage updates, within `stackSize`: the leaf is
taken (`Seq.leafFitsOn`). -/

/-- Ten deletes of `wallet`, then a read of its mapping member. -/
def deletes10 : Fml StandardExample [] :=
  dl!{ [ delete wallet; delete wallet; delete wallet; delete wallet; delete wallet;
    delete wallet; delete wallet; delete wallet; delete wallet; delete wallet; ]
    wallet.stash[owner] == 0 }

#guard leafStats deletes10 == some [(true, 10, true)]

end Scoped

/-! A power is folded only up to the exponent `256` (`Decide.expBig`):
`Int.pow` recurses once per unit of it, heeding no heartbeats. -/

#guard match Decide.fold2 (C := StandardExample) (.binop .pow rfl)
    (.lit (p := .uint) (PrimTy.uint.ofLit 2 rfl)) (.lit (PrimTy.uint.ofLit 1000000000 rfl)) with
  | .app2 .. => true
  | _ => false
#guard match Decide.fold2 (C := StandardExample) (.binop .pow rfl)
    (.lit (p := .uint) (PrimTy.uint.ofLit 2 rfl)) (.lit (PrimTy.uint.ofLit 255 rfl)) with
  | .app0 (.lit v) => decide ((v : PrimTy.uint.Denote).1 = 2 ^ 255)
  | _ => false

section Scoped
open scoped Scoped

/-! ## A failed `assert`

`assertSimple` checks its condition: two goals, `thn` (the run goes on) and
`els`, that the condition holds (a panic does not satisfy the box, so this
goal has nothing to close but the condition).  The tree, the walk
(`Proves.check`) and `sol_prove`'s residue each go through it once. -/

/--
info: 0: allRight
1: impRight
2: localValueDeclInitDrop
3: localValueAssign
4: assertConditionCapture
5: localValueDeclInitDrop
6: boolEqualityAssignment
7: assertSimple
  [Holds]
    8: Closed goal
  [Violated]
    9: Closed goal
closed: 0 open goal(s), 10 node(s), 2 branch(es)
-/
#guard_msgs in
#proof_tree dl!{ a == 1 → [ uint x = a; assert(x == 1); ] x == 1 }

/--
info: Try this:
  apply impRight
    apply unfold .localValueDeclInitDrop
    apply update .localValueAssign
    apply unfold .assertConditionCapture
    apply unfold .localValueDeclInitDrop
    apply update .binopAssignment
    apply Proves.check .assertSimple
    case thn =>
      sol_leaf
      sol_close
    case els =>
      sol_leaf
      sol_close
-/
#guard_msgs in
example : ⊢ dl!{ a == 1 → [ uint x = a; assert(x == 1); ] x == 1 } := by
  sol_derive?

/--
info: Try this:
  sol_prove (steps := 128)
-/
#guard_msgs in
example : ⊢ dl!{ a == 1 → [ uint x = a; assert(x == 1); ] x == 1 } := by
  sol_prove?

/-! ## Calls

A call in a body is KeY's `InternalCall`, inlined by `internalCallExpand`;
a tuple assignment's call returns to its targets, a `FunctionBodyStatement`
inlined by `functionBodyExpand`, the targets assigned after it.  The call
is a node (the premise its function builds whnf'd to its constructor,
`Calculus/ProofTree.lean`), and the callee's body, a block, ends by
`blockEmpty`. -/

/-- Two functions, of one return and of two. -/
def Callees : Contract := contract!{
  uint total;
  function inc(uint x) returns (uint) { return x + 1; }
  function pair(uint x) returns (uint lo, uint hi) { return (x, x + 1); }
}

/--
info: 0: valueDeclSkip
1: internalCallExpand
2: localValueDeclInitDrop
3: localValueAssign
4: valueDeclSkip
5: blockEmpty
6: additionAssignment
7: localValueAssign
8: Closed goal
closed: 0 open goal(s), 9 node(s), 1 branch(es)
-/
#guard_msgs in
#proof_tree dl[Callees]{ ⟨ uint y = inc(1); ⟩ y == 2 }

/--
info: 0: valueDeclSkip
1: valueDeclSkip
2: functionBodyExpand
3: localValueDeclInitDrop
4: localValueAssign
5: valueDeclSkip
6: valueDeclSkip
7: blockEmpty
8: localValueAssign
9: additionAssignment
10: localValueAssign
11: localValueAssign
12: Closed goal
closed: 0 open goal(s), 13 node(s), 1 branch(es)
-/
#guard_msgs in
#proof_tree dl[Callees]{ ⟨ (uint a, uint b) = pair(1); ⟩ b == 2 }

/-! The same under the box. -/

/--
info: 0: valueDeclSkip
1: internalCallExpand
2: localValueDeclInitDrop
3: localValueAssign
4: valueDeclSkip
5: blockEmpty
6: additionAssignment
7: localValueAssign
8: Closed goal
closed: 0 open goal(s), 9 node(s), 1 branch(es)
-/
#guard_msgs in
#proof_tree dl[Callees]{ [ uint y = inc(1); ] y == 2 }

/--
info: 0: valueDeclSkip
1: valueDeclSkip
2: functionBodyExpand
3: localValueDeclInitDrop
4: localValueAssign
5: valueDeclSkip
6: valueDeclSkip
7: blockEmpty
8: localValueAssign
9: additionAssignment
10: localValueAssign
11: localValueAssign
12: Closed goal
closed: 0 open goal(s), 13 node(s), 1 branch(es)
-/
#guard_msgs in
#proof_tree dl[Callees]{ [ (uint a, uint b) = pair(1); ] b == 2 }

/-! ## Loops (`Examples/Tactics/Loops.lean`)

`whileUnwind` is `unfold`, `loopExit` is `checkLean`; under the box the
invariant rule is `invBox` (`Proves.inv`), solkey's two goals past
`init`. -/

/--
info: Try this:
  apply unfold .localValueDeclInitDrop
    apply update .localValueAssign
    apply unfold .whileUnwind
    apply unfold .ifElseUnfold
    apply unfold .localValueDeclInitDrop
    apply update .binopAssignment
    apply split .ifElseSplit
    case thn =>
      apply unfold .blockEmpty
      apply update .localIncrement
      apply checkLean .loopExit
      case thn =>
        sol_leaf
        sol_close
      case els =>
        apply updIntro
        sol_leaf
        sol_close
    case els =>
      sol_leaf
      sol_close
-/
#guard_msgs in
example : ⊢ dl!{ ⟨ uint i = 0;
    /// @custom:key unwind 1
    while (i < 1) { i++; }; ⟩ i == 1 } := by
  sol_derive?

/--
info: Try this:
  apply unfold .requireConditionCapture
    apply unfold .localValueDeclInitDrop
    apply update .binopAssignment
    apply splitBox .requireSimple
    case thn =>
      apply unfold .localValueDeclInitDrop
      apply update .localValueAssign
      apply invBox .whileInvariantBox
      case init =>
        sol_leaf
        sol_close
      case thn =>
        apply update .binopAssignment
        sol_leaf
        sol_close
      case els =>
        sol_leaf
        sol_close
    case els =>
      apply done .revertBox
      sol_leaf
      sol_close
-/
#guard_msgs in
example : ⊢ dl!{ [ require(n >= 0); uint i = 0;
    /// @custom:key invariant i <= n
    while (i < n) { i = i + 1; }; ] i == n } := by
  sol_derive?

end Scoped

namespace PushSourceNames

/-- A root with the upstream capture prefix must survive printed replay. -/
def contract : Contract := contract!{
  uint source9; uint[] values; uint[][] matrix;
}

local instance : InContract := ⟨contract⟩
open scoped Solidity.Scoped

/--
info: Try this:
  refine Proves.unfold rfl ?_ -- storagePushValue_unfold_rightFstPrimitiveArgument
    apply unfold .localValueDeclInitDrop
    refine Proves.unfold rfl ?_ -- storageIndexRead_unfold_rightFst
    apply unfold .storageLocalDeclInitDrop
    apply update .storageIndexReadArrayBindLocalRoot
    apply update .storageIndexReadArrayFind
    apply update .storagePushValueSave
    sol_leaf
    sol_close
-/
#guard_msgs in
example : ⊢ dl!{ [ values.push(matrix[0][0]); ] true } := by
  sol_derive?

end PushSourceNames

namespace MemoryPushNative

local instance : InContract := ⟨StandardExample⟩
open scoped Solidity.Scoped

/--
info: Try this:
  apply unfold .memoryLocalDeclInitDrop
    apply update .memoryArrayFreshAlloc
    apply update .storagePushMemoryCopySource
    sol_leaf
    sol_close
-/
#guard_msgs in
example : ⊢ dl!{ [ uint[] memory row = new uint[](1); matrix.push(row); ] true } := by
  sol_derive?

end MemoryPushNative

namespace ExactDecision

local instance : InContract := ⟨StandardExample⟩
open scoped Solidity.Scoped

/--
info: Try this:
  exact
    Decide.InputReduction.valid_of_decide
      ((DeclarationReduction.certified Fml.tt DeclarationFacts.valid_true).input?.get
        (id (Eq.refl true)))
      (id (Eq.refl true))
-/
#guard_msgs in
example : Fml.Valid (dl!{ true } : Fml StandardExample []) := by sol_exact?

/-- Replay the offered certificate without tactic search. -/
example : Fml.Valid (dl!{ true } : Fml StandardExample []) := by
  exact
    Decide.InputReduction.valid_of_decide
      ((DeclarationReduction.certified Fml.tt DeclarationFacts.valid_true).input?.get
        (id (Eq.refl true)))
      (id (Eq.refl true))

end ExactDecision

end Solidity.Examples.ProofTree
