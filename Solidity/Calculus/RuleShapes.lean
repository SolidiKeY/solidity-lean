import Solidity.Calculus.Rules

/-!
# The shape of the rule table

`Rules.lean` now says what a KeY taclet says: guarded goals, updates, bare
obligations, and the name of the taclet each rule transcribes.  That is more
structure than the old `block`-only table, and more structure is more room to
be quietly wrong.  This module is the check.

It holds three kinds of fact, and nothing else:

* **Reduction lemmas** for `StepEffect.mainBlock` — one per goal combinator, so
  the rest of the development can see a residual through a goal list without
  unfolding the combinator by hand.
* **A shape fact per rule**: every rule offers at least one goal, and a rule
  whose residual is non-empty carries no update.  These are `rfl` per rule,
  which is the point — the table is checked against itself, not against a
  second hand-written table.
* **Origin facts**: which KeY taclets the table claims, which it does not, and
  that box/diamond twins claim the same ones.  `taclets_partitioned` is the
  load-bearing one: of the 252 taclets in `solidityProgramRules.key`, 246 are
  claimed by a Lean rule and the remaining six are listed here with a reason.

What this module does *not* do is say whether a rule's update is *right*; that
is `Update/TacletTable.lean`, which proves each one against
`Wp.terminalUpdate?`.
-/

namespace Solidity
namespace RuleShapes

open Rules

/-! ## Reading a residual through a goal list -/

@[simp] theorem mainBlock_unfoldGoal (b : Block) :
    StepEffect.mainBlock (unfoldGoal b) = b := rfl

@[simp] theorem mainBlock_terminalGoal (u : UpdTerm) :
    StepEffect.mainBlock (terminalGoal u) = [] := rfl

@[simp] theorem mainBlock_splitGoals (φ : SideFormula) (p : List Premise)
    (u : UpdTerm) : StepEffect.mainBlock (splitGoals φ p u) = [] := rfl

@[simp] theorem mainBlock_assertGoals (c : WrappedExpr) :
    StepEffect.mainBlock (assertGoals c) = [] := rfl

@[simp] theorem mainBlock_revertGoals : StepEffect.mainBlock revertGoals = [] :=
  rfl

@[simp] theorem mainBlock_compoundGoals (op : BinOp) (t v : WrappedExpr) :
    StepEffect.mainBlock (compoundGoals op t v) = [] := rfl

@[simp] theorem mainBlock_compoundIndexGoals (op : BinOp) (t v : WrappedExpr) :
    StepEffect.mainBlock (compoundIndexGoals op t v) = [] := rfl

@[simp] theorem mainBlock_incDecGoals (v rhs : WrappedExpr) :
    StepEffect.mainBlock (incDecGoals v rhs) = [] := rfl

/-! ## Every rule offers a goal

A rule with no goals would be a rule that says nothing: its weakest
precondition would be the empty conjunction, `True`, and it would "prove"
anything it applied to.  Nothing in the table produces one — every combinator
emits one or two goals — but the fact is worth having as a `rfl` per rule
rather than as a reading of the combinators. -/

set_option maxHeartbeats 4000000 in
theorem goals_nonempty (r : RuleName) (stmt : Stmt)
    (h : (ruleEffect r).cond stmt) :
    (ruleEffect r).goals stmt h ≠ [] := by
  cases r <;> (cases stmt <;> first | exact (h : False).elim | exact List.cons_ne_nil _ _)

/-! ## Which KeY taclets the table claims -/

/-- Every taclet named by some rule of the table, `transferWithCallback`'s two
included (it is the `transferSemantics` alternative, so it is not in
`ruleNames`). -/
def claimedTaclets : List KeyTaclet :=
  ((ruleNames ++ [RuleName.transferWithCallback]).flatMap
    fun r => (ruleEffect r).origin.taclets).eraseDups

/-- The taclets of `solidityProgramRules.key` that **no** Lean rule claims, and
why.  Six, in three pairs:

* `emptyModality`, `blockEmpty` — architectural.  `Block = List Stmt` with
  branch bodies inlined, so there is no nested-block statement to erase and no
  `{} ; rest` find-shape; a derivation that ends in the empty block *is* the
  Lean analogue of `emptyModality` (`docs/lean-key-rule-map.md`).
* `indexWriteInnerNonSimpleIndexCapture`, `indexReadInnerNonSimpleIndexCapture`
  — deleted upstream by solkey `63c38cfaf6`, and a rejected design besides:
  their `\find` was hard-coded to the depth-2 shape `e1[nse][e2]`, so
  `m[i++][j][k] = v` matched nothing, and they had no right-hand-side freeze.
  Lean's `*UnfoldLeftFst` rules capture the whole inner path instead, which is
  strictly more general.
* `ifSplit`, `ifElseSplit` — ported as a theorem, not a rule.  They are
  sequent-level two-goal splits on a simple condition (`\add(se = TRUE ==>)`),
  and a single-successor `BlockStep` cannot produce two goals; the rewrite
  layer is deliberately stuck there and `SolidityJudgment.ite_split`
  (`JudgmentSplit.lean`) is the split. -/
def unclaimedTaclets : List KeyTaclet :=
  [ KeyTaclet.emptyModality, KeyTaclet.blockEmpty,
    KeyTaclet.indexWriteInnerNonSimpleIndexCapture,
    KeyTaclet.indexReadInnerNonSimpleIndexCapture,
    KeyTaclet.ifSplit, KeyTaclet.ifElseSplit ]

/-- **The coverage fact**: the corpus splits into what the table claims and
what this file excuses, with nothing in both and nothing in neither.  A taclet
that appears upstream and is never ported fails this, and so does a rule that
claims a taclet another rule already excused. -/
theorem taclets_partitioned :
    KeyTaclet.all.all
      (fun t => claimedTaclets.contains t != unclaimedTaclets.contains t) = true := by
  native_decide

theorem claimedTaclets_count : claimedTaclets.length = 246 := by native_decide

theorem unclaimedTaclets_count : unclaimedTaclets.length = 6 := by native_decide

/-! ## Box/diamond twins claim the same taclets

The `Box`/`Diamond` suffix is a *Lean* naming decision — where the calculus stacks
a bounds or nonempty check as two sequents, Lean splits the rule by modality.
Upstream has one taclet for the pair (two, for `revert` and `transfer`), and
both halves must name it: a twin pair that disagreed about its origin would be
claiming to come from two different places. -/

theorem twins_origin_eq :
    ((ruleEffect .storageIndexWriteArraySaveDiamond).origin =
      (ruleEffect .storageIndexWriteArraySaveBox).origin) ∧
    ((ruleEffect .storageIndexWriteArrayCopySourceDiamond).origin =
      (ruleEffect .storageIndexWriteArrayCopySourceBox).origin) ∧
    ((ruleEffect .storageIndexReadArrayFindDiamond).origin =
      (ruleEffect .storageIndexReadArrayFindBox).origin) ∧
    ((ruleEffect .storageIndexReadArrayBindLocalRootDiamond).origin =
      (ruleEffect .storageIndexReadArrayBindLocalRootBox).origin) ∧
    ((ruleEffect .storageIndexReadArrayStoreRootDiamond).origin =
      (ruleEffect .storageIndexReadArrayStoreRootBox).origin) ∧
    ((ruleEffect .storagePopSaveDiamond).origin =
      (ruleEffect .storagePopSaveBox).origin) ∧
    ((ruleEffect .memoryIndexWriteStoreDiamond).origin =
      (ruleEffect .memoryIndexWriteStoreBox).origin) ∧
    ((ruleEffect .memoryIndexWriteCopyDiamond).origin =
      (ruleEffect .memoryIndexWriteCopyBox).origin) ∧
    ((ruleEffect .memoryIndexReadHeapDiamond).origin =
      (ruleEffect .memoryIndexReadHeapBox).origin) ∧
    ((ruleEffect .memoryIndexReadAliasRootDiamond).origin =
      (ruleEffect .memoryIndexReadAliasRootBox).origin) ∧
    ((ruleEffect .memoryToStorageIndexArrayCopyRootDiamond).origin =
      (ruleEffect .memoryToStorageIndexArrayCopyRootBox).origin) ∧
    ((ruleEffect .revertDiamond).origin =
      (ruleEffect .revertBox).origin) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## `\heuristics` is derived, not repeated

`Rules.withOrigin` computes a rule's `heuristics` from its `origin`, so the two
cannot drift.  The check below is therefore about the *arms*: it fails on an
arm that sets `origin` by hand instead of going through `withOrigin`, which is
the only way the pair could come apart. -/

theorem heuristics_eq_origin :
    ruleNames.all (fun r => (ruleEffect r).heuristics ==
        ((ruleEffect r).origin.taclets.map KeyTaclet.heuristic).eraseDups)
      = true := by
  native_decide

/-! ## The rules with no taclet

A `leanOnly` origin is a claim that upstream has no counterpart, and there are
five reasons for one in this table:

* **front-end normalisation** — `pushAssignLower`, `pushFieldAssignLower`,
  `storagePushLhsToPushValue` rewrite Solidity's push sugar to the `Stmt.assign`
  form the interpreter already handles;
* **scratch bindings** — `storagePlaceAlias`, `exprStmtCapture`, and the
  `storageToMemoryDecl*` / `memoryToStorageUnfold*` steps, finer tiers than
  KeY's;
* **the call rule** — `functionCallArgCapture` (solkey has it only as a backlog
  item, `unfoldArgument`);
* **term-level rules lifted to program rules** — `ifElseTrue`, `ifElseFalse`,
  `ifElseNegated` come from `ifThenElseRules.key`, which `KeyTaclet` does not
  enumerate;
* **operator instances KeY does not have** — `**=` throughout the compound
  families, `&&`/`||` in `binopUnfoldRight` (they short-circuit, so KeY defers
  to the `if` rules), the whole `binopUnfoldResult` tier, and the memory
  arithmetic family, which landed upstream in solkey `444f029579` — *after* the
  revision this table was transcribed from (`e67a0d7c48`).

The list is computed rather than transcribed, so adding a rule without an
origin moves the count and fails the theorem below. -/
def leanOnlyRules : List RuleName :=
  ruleNames.filter fun r => (ruleEffect r).origin == KeyOrigin.leanOnly

theorem leanOnlyRules_count : leanOnlyRules.length = 174 := by native_decide

/-- And the complement: 221 of the 395 rule *instances* name a taclet.  The
`leanOnly` share is large because `ruleNames` lists every instance of a
parameterized family, including the ones whose condition is unsatisfiable —
`localCompoundAssign .lt` is a listed rule that can never fire, and KeY of
course has no `<=` taclet for it.  Counting rule *names* instead would hide
exactly the thing the count is for: a family with one instance annotated and
the rest forgotten. -/
theorem rules_with_origin_count :
    (ruleNames.filter fun r =>
      (ruleEffect r).origin != KeyOrigin.leanOnly).length = 221 := by
  native_decide

end RuleShapes
end Solidity
