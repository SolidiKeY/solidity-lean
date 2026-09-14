# Plan: Mirroring the solkey Solidity-in-KeY Calculus

## Implementation status (2026-07-05)

- **Phase 0 — done**: `docs/lean-key-rule-map.md` (tracking checklist).
- **Phase 1 — done**: `BinOp`/`UnOp`/`IncDec`; `WrappedExpr` gained
  `intLit`, `mkBinop`, `mkUnop`, `mkIncDec` (replacing `mkAnd`); `Stmt`
  gained `compoundAssign`, `ite`, `assertStmt`, `transfer`; measures,
  classifiers and the `sexpr!`/`sstmt!` macros extended. Comparisons are
  parenthesized-only (`(a < b)`) so the closing `>` of the modality syntax
  is unambiguous; `--` cannot be a Lean token (comment), decrements are
  built with `SoliditySyntax.incDecExpr`.
- **Phases 2–5 — done**: value/operator families (parameterized rule
  names `binopUnfoldLeft op` etc., one KeY taclet per instance;
  KeY-absent combinations carry unsatisfiable guards), storage compound
  assignments and inc/dec, `revert`/`assert`/`ite` (per D3(b)) and
  `transfer`. `candidate`/`applicable_eq_candidate` and the meta-theorems
  extended in lockstep; build green.
- **Phase 6 — interpreter and symbolic bridge delivered**: `Semantics.lean` is
  an executable state layer (storage tree, identity-indexed heap, `net`
  ledger, local bindings) giving meaning to
  `sol!{ < stmts > (post) }` / `sol!{ [ stmts ] (post) }` judgments via
  `SolidityJudgment.Holds`; the KeY taclet tests are ported as
  `native_decide`-verified examples in `Examples/Taclets/`.
  `RuleSoundness.lean` proves every nonterminal unfold rule symbolically and
  `RewriteSoundness.lean` supplies generic multi-step lifting. The
  parallel-update algebra (`updateRules.key`) is resolved as semantic
  `State` lemmas (`SemanticsProperties.lean`, "State-update algebra"
  section) plus the proof-level split `SolidityJudgment.ite_split`
  (`JudgmentSplit.lean`) — see the "Update algebra" section of the rule
  map. The state-carrying bridge for terminal rules is `Wp/TerminalUpdate.lean` +
  `Wp/TerminalRules.lean` (`terminal_step_sound`; `ConfigStep.exec` is
  stated on the rule's update).
- **Phase 7 — maintained continuously**; large rule lists forced
  `decide`-based membership proofs instead of `simp [ruleNames]`.
- **Parity pass (2026-08-28)**: all previously `open`/`verify` rows in
  `docs/lean-key-rule-map.md` resolved. Added: `require` statement +
  `requireConditionCapture`/`requireSimple`; short-circuit
  `logicalAnd/OrShortCircuitRhs` (the `binopUnfoldRight` short-circuit
  hole is closed); the `*ValueRhsCapture` trio
  (`storageRootWrite`/`fieldWrite`/`indexWriteValueRhsCapture`,
  RHS-before-LHS evaluation order, conditional soundness via
  `valueRhsCaptureAssign_sound`); `memoryStorageCopy`/
  `memoryStorageCopyUnfold` split out of the previously over-broad
  `memoryRootAlias`. Correspondence lock-ins and the
  `testStorageEvaluationOrder` port live in `RuleValidation.lean`
  (`RuleCorrespondence` section); the interpreter's target-first vs
  KeY's RHS-first divergence on interfering assignments is documented
  in the rule map's evaluation-order note. Semantics extensions:
  `functionBodyExpand` (function table `SoliditySyntax.funDef`,
  `expandCall`, fuel-bounded `inlineBlock`,
  `SolidityJudgment.checkInlined`; plus the Lean-only
  `functionCallArgCapture`) and `transferWithCallback`
  (`CallbackSemantics.lean`: relational `ExecC`/`HoldsC`,
  `holdsC_transfer_split`, `holds_of_holdsC`; rule set
  `ruleNamesWithCallback` mirrors KeY's `transferSemantics`
  choice). Logic layer: `JudgmentSplit.lean` (`ite_split` and
  corollaries) and the state-update algebra in
  `SemanticsProperties.lean`.

Goal: extend the Lean package `Solidity` so it models the same
Solidity calculus that `~/projects/solkey` implements in KeY
(`keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/`),
reusing the rewriting infrastructure already in place.

## 1. What already exists and can be reused

### Lean side (`Solidity/`)

| File | Reusable infrastructure |
| --- | --- |
| `AST.lean` | `Kind`/`Ty`/`RefTy`, untyped `WrappedExpr`/`PlaceExpr`, `Stmt`/`Block`, typed AST, `sexpr!`/`sstmt!`/`solbox!` macros, expression measures |
| `Rules.lean` | `RuleName`, `StepEffect` (`mode`/`cond`/`block`), `StepCase`, capture/alias helpers (`captureValue`, `captureStoragePath`, `captureIndex`, fresh-name conventions `pv`/`idx`/`sp`/`mv`), effect builders (`assignEffect`, `deleteEffect`, `pushEffect`, ...), and `ruleNames` |
| `Completeness.lean` | `RuleStep`, `FirstStepCase`, `step_of_ruleApplies` (definitional) and its converse `ruleApplies_of_ruleStep`; the completeness theorem proper is `RuleStep.complete_of_wellTyped` in `Coverage.lean` |
| `Uniqueness.lean` | total dispatch `candidate` + `applicable_eq_candidate`, mutual-exclusion theorem |
| `MultiStep.lean` | `BlockStep`, `NamedBlockStep`, `⇝` / `⇝⁺` / `⇝*` / `⇝[.rule]`, transitivity instances |
| `Termination.lean` | termination-certificate interface: any decreasing natural-number block measure yields well-founded rewriting |
| `Examples/`, `Counterexamples/` | per-rule concrete derivations mirroring `keyext.solidity.examples` |

The generated `ruleNames` cover the storage/memory program-rule families
of `solidityProgramRules.key`: root/field/index read & write (array and
mapping), push/pop (incl. push-lvalue forms), delete, storage/memory local
declarations, memory allocation and aliasing, storage↔memory copies, plus the
box/diamond bounds-splitting variants. Explicit `revertBox` and
`revertDiamond` rules consume `Stmt.revert`; legacy fallback names are not
members of the generated calculus.

### KeY side (solkey) — rule inventory to mirror

`solidityProgramRules.key` (205 taclets) plus supporting files:

1. Modality/sequent rules: `emptyModality`, `revertBox`, `revertDiamond`.
2. Storage/memory copy semantics (~90 taclets) — **already modeled in Lean**
   (naming differs, e.g. `storageFieldWrite_unfold_leftFst` ↔
   `storageFieldWriteUnfoldLeftFst`).
3. Value-variable declarations: `localValueDeclInitDrop`, `valueDeclSkip`.
4. Storage compound assignments: `+=`, `-=`, `*=`, `/=`, `%=` on
   root/field/index, each with `_unfold_leftFst` variants; `/=` and `%=`
   revert on zero divisor.
5. Increment/decrement: pre/post `++`/`--` on storage root, field, index and
   on locals; statement form and assignment form (`result = ++x`);
   `_unfold_leftFst` variants for complex paths.
6. Binary operators on values: `+`, `-`, `*`, `**`, `/`, `%` — each a
   3-step family (capture left, capture right, terminal assignment); `/`, `%`
   with zero-divisor revert branch.
7. Comparisons & booleans: `<`, `>`, `<=`, `>=`, bool `==`/`!=`, `&&`, `||`,
   `!`, unary minus — capture-lhs/capture-rhs/assignment families.
8. Capture ordering rules: `storageIndexWriteNonSimpleRhsCapture`,
   `*NonSimpleIndexCapture`, `assertConditionCapture`, RHS-before-index
   evaluation order.
9. `assert`: `assertSimple` splits into "Holds" (continue, condition added to
   antecedent) and "Violated" (prove `pv = TRUE`).
10. If-then-else: `ifthenelse_true/false/negated` (+ `_for` loop variants) in
    `ifThenElseRules.key`.
11. Payments: `transfer_unfold_leftFstReceiver`,
    `transfer_unfold_rightSndArgument`, `transferNoCallback` over the `net`
    ledger (`netHeader.key`).
12. State-level theories (LDTs), *not* program rewriting:
    `structRules.key` (`find`/`save`/`select`/`store` on `Struct`),
    `memoryRules.key` (`add`/`read`/`write`/defaults), `listRules.key`,
    `structMemoryRules.key` (lazy-copy reads), `updateRules.key`,
    plus arithmetic support (`intSimplificationRules.key`, `intDiv.key`).

## 2. Architectural decisions (settle before coding)

**D1 — Stay in the block-rewriting model.** The Lean formalization rewrites
`SolidityBlock`s; KeY taclets additionally emit updates (`{storage := ...}`)
and split sequent branches. Families 3–8 are pure program rewriting and drop
into the existing `StepEffect` shape unchanged. Keep them single-branch.

**D2 — Encode revert-guarded branches inside the program.** KeY handles
zero-divisor and array-bounds checks as a formula split inside
`\replacewith`. In the rewriting model, mirror the existing box/diamond
duplication already used for `storageIndexRead/Write` bounds: give `/`, `%`,
`/=`, `%=` box and diamond rule variants whose conditions mention the guard,
or (preferred, simpler) add `Stmt.ite` and rewrite
`x = a / b` ⇒ `if (b == 0) revert(); else x = a / b'` in one step, letting
the existing revert/fallback machinery finish. Pick one strategy and use it
for all guarded rules; document it in the rule comments.

**D3 — Branching effects for `assert` and `if`.** `assertSimple` and
`ifthenelse_*` genuinely split. Options:
  - (a) extend `StepEffect.block` to `List Block` (branches) — clean, but
    ripples through `RuleStep`, `BlockStep`, completeness, uniqueness,
    termination;
  - (b) keep single-branch by making `if` a *condition-directed* rewrite:
    two mutually exclusive rules `ifElseTrue`/`ifElseFalse` firing on literal
    conditions (`bool true`/`bool false`), preceded by
    `ifElseUnfold` for non-simple conditions — exactly the
    capture-then-dispatch discipline the rule set already uses. `assert`
    becomes `assertConditionCapture` + `assertTrue`/`assertFalseRevert`.
  Recommendation: (b). It preserves every existing meta-theorem statement and
  matches how the rules are phrased. Revisit (a) only if faithful
  sequent-level splits turn out to be needed.

**D4 — State semantics is a separate, later layer.** The KeY LDTs
(family 12) give meaning to `save`/`find`/`store` etc.; Lean currently never
interprets them. Model them as new self-contained files
(`Storage.lean`, `Memory.lean`, `Net.lean`, `Update.lean`) with a soundness
bridge, *after* the syntactic families are done. This is the largest work
item and independent of families 3–11.

**D5 — Naming.** Keep the established convention: KeY snake/underscore names
map to camelCase `RuleName`s (`storageRootAddAssign` stays as is,
`lessThanCaptureLhs` etc.). One `RuleName` per KeY taclet unless a Lean-side
condition legitimately merges box/diamond variants.

## 3. Phases

Each phase ends with: `lake build` green from the project root; `stepCases`,
`candidate`/`applicable_eq_candidate` (Uniqueness), coverage (Completeness),
and `stmtMeasure` (Termination) updated; at least one example per new rule
family under `Examples/`; new modules imported from
`Solidity.lean`. Use the Lean MCP for diagnostics; run
`/verification` after each phase for overlap/completeness/termination checks.

### Phase 0 — Inventory and mapping table
- Produce `docs/lean-key-rule-map.md`: every `solidityProgramRules.key`
  taclet → existing `RuleName` | planned `RuleName` | out-of-scope, with the
  phase that introduces it. This is the tracking checklist for all later
  phases and will surface naming drift in the ~90 already-covered rules.
- No Lean changes.

### Phase 1 — AST extensions
- `WrappedExpr`/typed `Expr`: replace the ad-hoc `and` with a general
  `binop : BinOp -> ...` (`add, sub, mul, pow, div, mod, lt, gt, le, ge,
  eqB, neB, and, or`) plus `not`, `neg`, and pre/post `inc`/`dec` place
  expressions. Keep `and` as a `@[match_pattern]` abbrev for compatibility.
- `Stmt`: add `compoundAssign (op) (lhs) (rhs)`, `ite (cond) (thn) (els)`
  (blocks), `assert`/`require (cond)`, `transfer (recipient) (amount)`,
  `incDec` statement form. (`stackDecl` already exists for value decls.)
- Extend the expression/statement measures in `AST.lean` for every new
  constructor (needed by Phase 7 termination updates).
- Extend `sexpr!`/`sstmt!` macros for the new syntax (`a + b`, `x += e`,
  `++x`, `if`, `assert`, `a.transfer(v)`).
- Update `simple`/`complex`/`assignable` classifiers so capture conditions
  can be expressed exactly as in KeY (`SimpleExpression` vs
  `NonSimpleExpression` schema variables).

### Phase 2 — Value/local expression rules (KeY families 3, 6, 7)
- `localValueDeclInitDrop`, `valueDeclSkip`.
- Binary-operator families: for each of `+ - * ** / %` and each comparison /
  boolean op: capture-lhs, capture-rhs, terminal-assignment rules, mirroring
  the KeY 3-step discipline; `logicalNotCapture/Assignment`,
  `unaryMinusCapture/Assignment`, `boolEquality*`/`boolInequality*`.
- Zero-divisor guards per decision D2.
- Reuse `captureValue`; add a generic `binopCapture` helper instead of ~40
  hand-rolled effects.

### Phase 3 — Storage compound assignment and inc/dec (families 4, 5)
- `storageRoot{Add,Sub,Mul,Div,Mod}Assign`, field/index variants and their
  `_unfold_leftFst` rules.
- Pre/post increment/decrement: root/field/index/local, statement and
  assignment forms, `_unfold_leftFst` variants.
- These reuse `fieldWriteResolveBlock`/`indexWriteResolveBlock`; most rules
  are "desugar into already-covered read + op + write" rewrites, which keeps
  completeness/termination arguments local.

### Phase 4 — Control flow, assert, evaluation-order captures (families 8–10)
- `ifElseUnfold`, `ifElseTrue`, `ifElseFalse` per decision D3(b); decide
  whether `_for` (loop) variants are in scope — if loops are outside the
  fragment, record them as out-of-scope in the Phase 0 table.
- `assertConditionCapture`, `assertTrue`, `assertFalseRevert`.
- Explicit `revertBox`/`revertDiamond` and `emptyModality` analogues if they
  are worth naming. Uncovered statements remain uncovered; do not
  restore statement-deleting fallbacks.
- RHS-before-index capture-order rules
  (`storageIndexWriteNonSimpleRhsCapture` etc.) — verify the existing
  `storageIndexWriteUnfoldLeftSndIndex`/`UnfoldLeftFst` conditions reproduce
  KeY's evaluation order (`a[++i] = ++i`), and add the missing RHS-capture
  rules if not.

### Phase 5 — Payments (family 11)
- `Stmt.transfer` rules: `transferUnfoldLeftFstReceiver`,
  `transferUnfoldRightSndArgument`, `transferNoCallback` (terminal: consumes
  the statement; its ledger effect becomes real in Phase 6).

### Phase 6 — State layer and updates (family 12; largest, independent)
- `Storage.lean`: `Struct` as the list/tree model of `structRules.key` with
  `find`, `save`, `select`, `store`, `push`, `pop`, `findLength`,
  `saveLength`, `default`, and the simplification lemmas
  (`selectOnStore`, `findDefinitionCons`, ... as `@[simp]`/`@[grind]`).
- `Memory.lean`: identity-indexed memory with `add`, `read`, `readR`,
  `write`, `delete`, `erase`; lazy copies `copySt`/`copyMem`
  (`structMemoryRules.key`), per `docs/copyStMem.md`.
- `Net.lean`: the per-address ledger of `netHeader.key`.
- `Update.lean`: parallel updates over `(storage, memory, net, locals)` with
  the composition/substitution laws of `updateRules.key`
  (see `docs/storage.md` and `docs/memory.md` in solkey).
- **Done** (`Wp/TerminalUpdate.lean`, `Wp/Terminal/Update*.lean`,
  `Wp/TerminalRules.lean`): each *terminal* rule has a state update
  `terminalUpdate?` written in state vocabulary, a theorem
  `<rule>_update : execStmt s stmt = terminalUpdate r stmt s` under the
  rule's guard, and the state-carrying step relation `ConfigStep.exec`
  (StepSoundness.lean) is stated on the update — the Lean analogue of
  "taclet ⇒ update" in KeY. Capture/unfold rules are state-neutral by
  `RuleSoundness`.
- Skip KeY's generic arithmetic files (`intSimplificationRules.key`,
  `intDiv.key`, `firstOrderRules.key`, `propRule.key`): Lean's `Int`,
  `omega`, and `grind` already provide this layer.

### Phase 7 — Meta-theory and examples (runs inside every phase, listed for emphasis)
- `Rules.lean`: extend `ruleNames` (or a new `extendedRuleNames` list if the
  canonical rule table should stay frozen).
- `Uniqueness.lean`: extend `candidate` and `applicable_eq_candidate`; a
  failing build here is the overlap detector — budget time, this file grows
  the fastest (currently 1805 lines; consider splitting per rule family).
- `Coverage.lean`: extend `ResidueShape` and `RuleStep.complete_of_wellTyped`
  when a residue family gains a rule.
- `Termination.lean`: instantiate `RewriteTerminationCertificate` by proving
  that each capture/unfold strictly decreases a concrete block measure; the
  binop capture chains likely need a per-expression operator count.
- `Examples/`: port representative tests from
  `keyext.solidity.examples/taclets` (`addition-simple`, `addition-both-storage`,
  `division-simple`, `logical-and-simple`, `less-than-simple`, ...) and
  `mainFeatures` (`testStorageEvaluationOrder`, assert tests) as end-to-end
  `⇝*` derivations, mirroring the style of
  `Examples/Derivations/Walkthroughs.lean` (the `sol_derivation` command).

## 4. Suggested order and effort

| Phase | Depends on | Relative size |
| --- | --- | --- |
| 0 mapping table | — | S |
| 1 AST | 0 | M |
| 2 value/operator rules | 1 | L (many rules, but templated) |
| 3 compound assign, inc/dec | 1–2 | L |
| 4 ite/assert/order | 1–2 | M |
| 5 transfer | 1 | S |
| 6 state layer | none (parallel) / bridge needs 2–5 | XL |
| 7 meta-theory | continuous | grows with 2–5 |

Phases 2–5 keep the current architecture untouched and get the rule set to
parity with `solidityProgramRules.key`. Phase 6 is what makes the Lean
artifact an *implementation of the semantics* rather than of the rewrite
system alone — schedule it after parity, or in parallel if soundness claims
are needed early.

## 5. Risks

- **Uniqueness blow-up**: every new family multiplies dispatch cases; keep
  conditions syntactically disjoint (the capture discipline guarantees this
  if `simple`/`complex` classifiers are exact) and split `Uniqueness.lean`
  by family before it becomes unbuildable.
- **Termination measure**: operator-capture chains terminate only if the
  measure counts operators inside expressions; get the measure right in
  Phase 1, not retroactively.
- **Evaluation order**: KeY's RHS-before-index rules encode Solidity's
  evaluation order; port the order, not just the rules — add
  `testStorageEvaluationOrder` as an example to lock it in.
- **Semantic drift vs. solkey**: the mapping table (Phase 0) is the single
  source of truth; every Lean rule should cite its KeY taclet name in a doc
  comment.
