# Porting mini-solkey's typed kernel into solidity-lean

mini-solkey (`~/projects/side-projects/lean/mini-solkey`) started
(2026-09-23) as a readable copy of the storage part of this package. Twenty
commits later it has guarantees this package does not: the syntax is typed,
so no well-formedness predicate is needed; the rules are one inductive
judgement; the calculus is complete with no residue, makes progress and
terminates; and there is a sequent calculus, derivation chains, update
simplification, a decision procedure and both modalities. This file is the
plan for carrying those ideas here at full scale, and the tracker of how far
the port has got (**Progress**, at the end).

mini-solkey itself does not change. It stays the reference: every step below
names the mini-solkey declaration to copy the shape from (its chapters,
`Ch02_Elab` … `Ch15_Decide`, are files of its `MiniSolKey/`).

Numbers about solidity-lean are from its commit `c1b681a`.

## 0. Ground rules

These are the rules mini-solkey was built under (its `AGENTS.md` and
`.claude/rules/`). They carry over:

- **Types, not predicates.** A statement no rule can run is a typing problem.
  Change the syntax so it cannot be written; never add a `wf`/`wellTyped`
  hypothesis. ("Use dependent types instead of well formed"; "more correct by
  construction, less wellfoundness".)
- **One judgement, one rule, one constructor.** Rules are constructors of an
  inductive relation, PLFA style, and proofs are `apply` walks.
- **Paper notation everywhere.** Statements, goals and taclets are written and
  printed in `dl{ … }`; if the notation cannot say something, extend it.
- **Tactics do not trust themselves.** Whatever a tactic computes goes back
  through `replaceTargetDefEq`, so the kernel re-checks it.
- **Every theorem has a docstring with a small Solidity example**, and headline
  theorems are followed by a checked `example`.

And solidity-lean's own constraints stay:

- Lean `v4.24.0`, no `[[require]]`.
- `side-projects/lean/solkey` imports `Solidity.Calculus.Rules` and
  `Solidity.Calculus.KeyTaclets` and names `RuleName`, `ruleEffect`,
  `StepEffect` and specific constructors in its correspondence proofs. Either
  keep those names working, or migrate `lean/solkey` in the same commit.
- The default build is about 24 CPU-minutes. Every phase below keeps it green.

## 1. What mini-solkey has, and where solidity-lean stands

| mini-solkey | solidity-lean today | Gap to close |
|---|---|---|
| `Ty := uint \| ref RefTy`, `RefTy` mutual, `Ty.casesOn3`, `match_pattern` aliases (`Ch02_Elab`) | `Ty := prim \| ref`, `RefTy := struct \| array \| mapping` (`AST.lean`). The split is there already | only the eliminator and the aliases |
| `Contract`, `Contract.fieldType`, `InContract` class (`Ch02_Elab`) | no contract: one global `structDef : Name → List (Name × Ty)` (`AST.lean:121`) | index everything by a contract |
| `Expr C T`, `Place C T`, `Lhs C T`, `SExpr`, `SPath C T`, `OpLhs C`, `Stmt C`: a field access carries `C.fieldType s f = some T` (`Ch02_Elab`) | `Typed.WrappedExpr`, which carries its type as data; `PlaceExpr` carries an `assignable` proof; `Semantics.stmtWt` (`Typing/Soundness.lean:2452`) is a type checker over it. The indexed `Typed.Expr : Kind → Ty → Type` exists but only examples use it | a typed statement layer the rules run on |
| `inductive Taclet C k : Modality → Stmt C → Premise C → Prop`, one constructor per rule, each type written `dl{ ⟨[ s; ]⟩ ⇝ p }` (`Ch06_Taclets`) | `sol_rule` commands assembled into `RuleName` + `ruleEffect : RuleName → StepEffect` (`Calculus/Rules.lean`, about 160 declarations); `RuleStep`/`BlockStep` are defined over the table | a rule judgement |
| typed shapes (`EClass`/`LClass : Kind → Type`, `PClass`), `RuleName.accepts`, `rules_disjoint`/`rules_complete` by `decide +kernel` with no hypothesis | `UniquenessAux.candidate` (`Uniqueness.lean:575`), `RuleSetDisciplined` | uniqueness and coverage as one `decide` |
| `Stmt.step : (s : Stmt C) → Step k m s`, total; each arm proves `accepts` and `smaller` | nothing total; the first applicable rule in list order (`FirstStepCase`) | a total dispatcher |
| `Stmt.complete`, no hypothesis, no residue (`Ch11`) | `coverage_residue` and `RuleStep.complete_of_wellTyped` (`Coverage.lean`) assume `stmtWt` and `¬ ResidueShape`, with 26 residue shapes | completeness with no residue |
| `Premise := update \| unfold \| split \| done`; `ifElseSplit` and `requireSimple` are rules with two premises | the `if` is outside the step relation (`SolidityJudgment.ite_split`, `JudgmentSplit.lean`) | `split` as a premise |
| `Fml.progress`, `Fml.active_iff_step` (`Ch11`) | `Progress.not_progress`: refuted, because a symbolic `if` has no single-residual step | progress, over the premise-level relation |
| `Fml.measure = 2 ^ weight · (…)`, `Fml.step_wellFounded`, `symex_normalizes` (`Ch12`) | `Termination.lean` is an interface with no measure; `BlockStep.wellFounded` is `sorry` (`Progress.lean:113`) | a concrete measure |
| `Modality := diamond \| box`, `Modality.after`, `revertBox`/`revertDiamond`, `Fml.diamond_iff_box` | `SolidityModality := box \| diamond \| both`; `Res := Except Halt` with `revert \| stuck` | decide what `both` and `stuck` become |
| `inductive Proves : List (Hyp C) → Fml C → Prop` (`intro`, `update`, `unfold`, `split`, `done`, `empty`, `close`) and `Proves.sound` | `Update/Step.lean` `CalculusHolds`, explicitly not proved to imply `SolidityJudgment.Holds` | a sound sequent calculus |
| frame lemma `holds_agree`; freshness by index; `FreshNames` class | `ResultsAgree` over `aliasNames` with a `stmtUsesVar … = false` hypothesis per rule | freshness checked, not assumed |
| chains `~[r]~>`, `~>`, `~*>`, `Fml.Via`, `calc`, `sol_chain`, uniqueness of the evidence (`Ch13`) | `sol_derivation`, `⇝[r]`, `⇝*`, at the block layer; `Paper/Control.lean` says the `if` has no chain | chains that go through a split |
| `inductive UpdRule` (`sequentialToParallel`, `simplifyUpdate`, `elimSelfUpdate`, `applySkip`, `applyOnRigid`), each an iff (`Ch14`) | `Update.lean` `Par.seq_single`, `upd_merge`, `Frontier.Equiv` | one iff lemma per KeY update taclet |
| `Term.elimReads`, `LPath.cmp`, `LFml.valid_iff`, `Fml.valid_iff_reduce`, `sol_decide` (`Ch15`) | simp sets (`rule_simp`, `theory_rw`) | a decision procedure |
| `delAt s p = save s p (clear (find s p))`; `clear` keeps mapping entries; `LedgerDelete.mappingSurvivesStructDelete` | `delNode` drops `at` members (`Theory/Storage.lean:381`) | a semantics fix, checked against solc |
| `dl{}`, `dl_schema{}`, `dl[C]{}`, delaborators, `pp.mini.dl` (mini-solkey's `Notation`) | `RuleSyntax`, `SequentSyntax` (`seq!{}`), `SequentPP`, which mini-solkey's notation started from | contract resolution; one notation |
| closed goals evaluated by `evalExpr` + hand quoters (`Prog.quote`, `Fml.quote`), kernel re-check | 502 `native_decide` | a kernel-checked fast path |

## 2. Strategy: a typed kernel beside the untyped AST, then cut over

An in-place rewrite is not realistic: solidity-lean is 85k lines,
`Calculus/RuleSoundness.lean` alone is 11.9k, and `lean/solkey` depends on the
untyped API. The plan is to build the typed calculus next to the old one,
connect the two by erasure, and move consumers over one at a time.

```
  Stmt (untyped, today)  ◀──erase──  Stmt C (typed, new)
        │                                  │
   stmtWt, ruleEffect                 Taclet, Stmt.step, Proves
        │                                  │
   RuleSoundness *_sound  ──reused──▶ Taclet.sound
```

- **A new directory**, `Solidity/Kernel/` (the name is a proposal): `Contract`,
  `Expr C K T` (contract, data location, type), the simple sorts, `Stmt C`.
- **Erasure**, `erase : Stmt C → Stmt`, and the theorem that the typed terms are
  exactly the well-typed ones:
  `elab_complete : stmtWt Γ L s = some Γ' → ∃ t, elab s = .ok t ∧ erase t = s`,
  with `elab_sound` in the other direction. This is what retires `stmtWt` as a
  hypothesis: a theorem over `Stmt C` needs none.
- **The old table stays, as the erased view.** For every `Taclet` constructor,
  a bridge theorem says its erasure is `ruleEffect` of the `RuleName` of the
  same name. The existing `*_sound` proofs then give `Taclet.sound` through
  erasure, and `lean/solkey` keeps building until phase 7.

## 3. Phases

Each phase ends with: `lake build` green, the `sorry` count not higher than
before, `#print axioms` on the new headline theorems showing only `propext`,
`Classical.choice` and `Quot.sound`, and the docs updated.

### Phase 1: types and the contract

- `Ty.casesOn3`-style `@[cases_eliminator]` and `@[match_pattern, reducible]`
  aliases (`Ty.struct`, `Ty.mapping`, `Ty.array`), as in `Ch02_Elab`.
- `structure Contract`, `Contract.fieldType`, `class InContract` with a
  low-priority default and `local instance` overrides. Port the contracts that
  `structDef` hard-codes into named `Contract` constants (they must be named:
  see §4, the fast path).
- `structDef` becomes a function of the contract. Keep a compatibility
  definition for the untyped layer until phase 7.

### Phase 2: typed syntax, elaboration, erasure

- `Expr`, `Place`, `Lhs`, and the simple sorts for every KeY schema-variable
  sort the rules use: `se`, `sp`, `mv`, `nmp`, `ie`, `lsv`, `gsp`, … (today
  `RuleSyntax.schemaVar` reads them off the name, as mini-solkey's
  `Notation.headAt` does). Over all of storage, memory and stack, arrays,
  `push`/`pop`, and calls.
- Walk the 26 constructors of `Coverage.ResidueShape` one by one. Each either
  becomes **unrepresentable** (mini-solkey's move: the operands of `+=` and
  `if` are simple sorts, and "capture into locals first" is the elaborator's
  job, not the calculus's), or **gets a rule**. A symbolic `if` gets
  `ifElseSplit` as a `split` premise (phase 3). Record the decision for each in
  the file.
- `elab`, `erase`, `elab_complete`, `elab_sound`; quoters for every new
  constructor (`Stmt.quote`, …).

### Phase 3: the taclet judgement

- `Premise C := update U | unfold P | split c P Q | done b`, and
  `Premise.Correct` (`Ch06_Taclets`).
- `inductive Taclet C k m : Stmt C → Premise C → Prop`, one constructor per
  `RuleName`, its type written in the notation. Port by family, in the order
  of the `RuleSoundness` ledger: storage first (mini-solkey's 39 rules map one
  to one), then memory, the cross-domain copies, arithmetic, control, calls.
- `Taclet.sound`, per constructor, from the existing `*_sound` theorem through
  erasure (`ResultsAgree` ↔ `Run.agree`). The ledger today reads "80 unfold
  rules: 26 clean, 50 open, 4 missing, 2 sorry"; this phase does not have to
  close the open rows, but it must not hide them: a constructor with no
  soundness proof stays listed.
- Typed shapes and `RuleName.accepts`; `rules_disjoint` and `rules_complete` by
  `decide +kernel` over `Shape.all`. mini-solkey's typed shapes went from 139
  to 72; expect the same effect here, and expect it to matter (§4).

### Phase 4: `Stmt.step`, completeness, progress

- The total dispatcher, arms carrying `accepts_tac` and `smaller_tac`. At
  about 175 rules against mini-solkey's 39, split it by family
  (`Stmt.stepStorage`, …) and dispatch on the statement's head first.
- `Stmt.complete` with no hypothesis (`Ch11_Completeness`).
- `Fml.progress` and `Fml.active_iff_step`, over the formula layer, where a
  split is a step. `Progress.not_progress` stays true of `BlockStep` and should
  stay in the tree, with a docstring saying the new theorem is about a
  different relation and why that relation is the right one.

### Phase 5: termination

- `Stmt.weight`, `Prog.weight` (`Ch06_Taclets`), extended for copies, arrays and
  calls. Calls are inlined, so the weight needs the call table to be acyclic;
  state that as a property of the contract, checked by `decide`, not as a
  hypothesis on every theorem.
- The measure `2 ^ weight · (…)`: the exponent is needed because a split copies
  the rest of the program into both goals.
- `Fml.step_wellFounded`, `symex_normalizes`, and `BlockStep.wellFounded` from
  them through `RewriteTerminationCertificate`, closing the `sorry` at
  `Progress.lean:113`.

### Phase 6: the logic layer

- `Fml C` with `modal m P φ`, `Modality.after` over `Res`. Two decisions:
  whether `SolidityModality.both` survives or becomes the `⟨[ … ]⟩` schematic
  form over `m : Modality`, and whether `Halt.stuck` can be made
  unrepresentable by the typed syntax (it should be, for a well-typed program).
- The frame lemma `holds_agree` and freshness by index (`Var.fresh base k`,
  `k = maxIdx φ.vars + 1`). That removes the per-rule `stmtUsesVar` hypotheses.
- `inductive Proves` and `Proves.sound : Γ ⊢ φ → ⊨ Hyp.wrap Γ φ`. This is the
  theorem `CalculusHolds` lacks today.
- `FreshNames`.

### Phase 7: cut over

- `RuleName` and `ruleEffect` are generated from the `Taclet` constructors, or
  proved equal to them. Decide the naming question (§5) first.
- `lean/solkey`: `Decode` targets a `Taclet` premise instead of a `StepEffect`;
  the five `Corresp/*` agreement theorems are restated; `CLAUDE.md`'s coupling
  note is updated. One commit on each side.
- Retire `Coverage.ResidueShape`, `UniquenessAux.candidate`, and the `stmtWt`
  hypotheses. Update `docs/module-map.md`, `docs/calculus-parity.md` and
  `docs/lean-key-rule-map.md`.

### Phase 8: the rest, in any order after phase 6

- **Chains** (`Ch13_Chains`): `OneStep`, `Steps`, `StepBy`, `Via`, `calc`
  instances, `sol_chain`, uniqueness. With `split` a premise, the `if` gets a
  chain, which `Paper/Control.lean` says it cannot have today.
- **Update simplification** (`Ch14_Updates`): one `UpdRule` constructor per KeY
  update taclet, each proved as an iff, mapped onto `Update/`'s
  `Par`/`Frontier` machinery.
- **Decision procedure** (`Ch15_Decide`): read-over-write elimination with the
  four-way path comparison, then `omega`. The riskiest item: arrays (lengths,
  `push`/`pop`) and memory need their own path relations, and every step must
  stay an equivalence or the completeness claim is lost.
- **`delAt` keeps mapping entries**: check against solc, then change
  `delNode`, and port `mappingSurvivesStructDelete`.
- **One notation**: `dl{}` and `seq!{}`/`sol!{}` merged, with `dl[C]{}` resolving
  names against a contract and the `pp` option to switch it off.
- **`native_decide` on closed formulas** replaced by the `evalExpr` + quote +
  `replaceTargetDefEq` path, where it applies.

## 4. Sharp edges already hit in mini-solkey

- **`Meta.reduce` through indexed families is about 100× slower.** mini-solkey
  evaluates closed goals with `evalExpr` and quotes them back with hand-written
  quoters; the kernel re-checks. This only works for a contract that is a
  named constant, and every new syntax constructor needs an arm in every
  quoter.
- **`deriving ToExpr` fails on constructors with proof fields.** Quote the
  contract as its constant and proofs as `Eq.refl`.
- **A big overlapping `match` is unusable in proofs**: `simp` and `whnf` time
  out. That is why `Stmt.step` is a total dispatcher.
- **An inner `match` does not refine an index.** Dispatcher arms need
  top-level patterns, and `if h : …` rather than `if …` so the branch fact
  reaches the proof obligations.
- **`cases` on the indexed syntax** fails with "dependent elimination failed"
  unless the index is generalised first.
- **Notation**: the concrete `dl{}` needs `priority := high` over the schematic
  one; the chain macro builds applications with `Syntax.mkApp` (in a quotation
  `$a $b` reads `$b` as an arrow); `dl_fml`/`dl_term` need category
  parenthesizers, or `dl{ a = b } ~> ψ` prints with parentheses.
- **Shape blow-up.** Storage × memory × stack × arrays multiplies the shapes.
  The `Kind`-indexed classes (`EClass`, `LClass`, `PClass`) are what kept
  mini-solkey's `decide` small; `decide +kernel` over thousands of shapes may
  still be slow, so measure before committing to one `Shape.all`.
- **Broken builds hidden by pipes.** A commit was once pushed while the build
  was red because `lake build | tail` hid the failure. Check the exit code.

## 5. Open questions

- **Rule names.** *Decided (2026-09-25):* `Taclet` constructors carry
  solkey's taclet names, the `KeyTaclet` constructors of
  `Calculus/KeyTaclets.lean` (`storageFieldWrite_unfold_leftFst`), as
  mini-solkey does. A Lean-only rule with no taclet keeps its `RuleName`.
  `RuleName` itself stays camelCase until phase 7, since `lean/solkey`'s
  proofs pin it.
- **`both`**: keep `SolidityModality.both`, or only `Modality` plus the
  schematic `⟨[ … ]⟩`?
- **`native_decide`**: forbidden in mini-solkey. Ban it in solidity-lean too,
  or only in the new `Kernel/`?
- **The deliberate differences** listed in the README ("Where this differs
  from the paper and from solkey, on purpose") are **not** to be ported:
  paths built on the right, the `findOnSave` shortcuts, unbounded words,
  `keccak` as a constructor, locals in memory. Confirm none of them is wanted.

## 6. Checklist for porting one rule

mini-solkey's `.claude/rules/rule-table.md`, plus solidity-lean's own steps:

1. A `RuleName` constructor.
2. A row in `RuleName.accepts`. If `rules_disjoint` fails, it overlaps an old
   row; if `rules_complete` fails, a shape has no rule.
3. A `Taclet` constructor, in the notation, and its case of `Taclet.sound`.
4. An arm in `Stmt.step`. If `smaller_tac` fails, fix the rule or the measure;
   do not add a hypothesis.
5. The bridge theorem to `ruleEffect` (until phase 7).
6. The `SoundnessLedger` pin, `docs/lean-key-rule-map.md`, and a rebuild of
   `lean/solkey`.

## Progress

Each line is ticked in the commit that makes it true. A phase is done when
`lake build Solidity` is green, `rg -n 'sorry|native_decide|^axiom'
Solidity/Kernel` prints nothing, and `lean_verify` on its headline theorems
lists only the standard three axioms.

- [x] Phase 0: this tracker, `.claude/rules/kernel.md`, the index rows.
- [x] Phase 1: `Ty` eliminator, `Contract`, `InContract`, named contracts
  (`Kernel/Contract.lean`).
- [ ] Phase 2: typed syntax, erasure, elaboration, quoters.
  - [x] storage and stack values: `Kernel/Syntax.lean`, `Erase.lean`
    (`Prog.erase_wt`), `Elab.lean` (`ksol[C]{}`), `Print.lean`
  - [x] memory (M1–M3 below; `delete` excepted)  - [x] arrays, `push`/`pop` (`Stmt.push`, `Stmt.pop`; `sp.push()` as a
    place is still open)  - [x] compound assignment
    (`Stmt.opAssign` on an `OpLoc`)  - [x] `++`/`--` (`Stmt.incDec`,
    `Stmt.assignIncDec`; `ksol` parses `++` only, `--` being a Lean comment)  - [x] ternary
    (`Val.ternary`, lazy as `evalValue`)  - [x] `transfer`  - [ ] calls
  - [ ] `decode : Stmt → Option (Stmt C Γ Γ')` with `decode (erase t) = some t`,
    for the corpus and to retire `stmtWt` hypotheses
  - [ ] the 26 `ResidueShape` verdicts (table below)
  - memory, the plan (the old table's 56 memory rules, in three commits):
    - [x] **M1** `MPath` (`var x` a memory local, `loc`) / `MLoc` (`field`, `index` on a `uint`)
      beside `SPath`/`Loc` in the mutual block, `Val.readMem`; `declMem R x (init : Option
      (MRhs R))` with `MRhs := alias (p : MPath) | copy (p : SPath) hm` (none allocates),
      `rebindMem x (r : MRhs R)`, `assignMem (l : MLoc T) (r : MSrc T)` with
      `MSrc := val v | ref p` (a memory reference, by identity); the reads, writes,
      declarations, aliases and their unfolds: 23 taclets, `MHole` for the reads'
      unfolds, frames `MLoc.write_agree`, `allocDefault_agree`
    - [x] **M2** the cross-domain rules
      - [x] `MRhs.copy` (memory from storage, `copyStToM`): `storageToMemoryDeclCopyRoot`,
        `…CopyField`, `storageToMemoryDeclUnfoldRightFst` (the whole path captured, so an
        entry copies too, which the old table cannot), `memoryStorageCopy`, `…CopyUnfold`
      - [x] storage from memory, its own statement `Stmt.assignFromMem l p` (not a `Src`,
        so `push` of a memory value stays unrepresentable): `memoryToStorageStoreRoot`,
        `…FieldCopyRoot`, `…FieldCopyField`, `…IndexMappingCopyRoot`, `…IndexArrayCopyRoot`,
        the receiver unfolds and the index capture; the source is any memory path
        (`memoryToStorageUnfoldRightFstSource` would capture it, the verdict below)
      - memory `delete`: not a kernel statement while `stmtWt` rejects it ("v1: storage
        deletes only"); `Prog.erase_wt` has no hypothesis to excuse it
    - [x] **M3** `OpLoc.mfield`/`mindex`, `VHole.mem`: `memoryFieldOpAssign`,
      `memoryIndexArrayOpAssign`, the two `…OpAssignUnfoldLeftFst`, the six `…Increment…`,
      `ternaryToIfMemory`; through the interpreter's own `readLoc`/`writeLoc` (`opMem`, `bumpMem`)
- [ ] Phase 3: `Taclet`, `Taclet.sound`, `rules_disjoint`/`rules_complete`.
  - [x] storage, with the control rules on simple conditions
    (`Kernel/Taclet.lean`, `Kernel/Sound.lean`: 41 taclets, all sound)
  - [x] array elements (`Loc.index` over `IndexTy`; no bounds split, the
    update reverts as the statement does)
  - [x] `push`/`pop`: `storagePushValueSave`, `storagePushValueCopySource`,
    `storagePushLengthSave`, `storagePushValue_unfold_rightSndArgument` (a value or a
    path, one kind-neutral capture `Src.decl`), the three `…_unfold_leftFstReceiver`,
    `storagePopSave` (no emptiness split); `push()` needs `Ty.defaultOkS`
  - [ ] `lsv = sp.push()`, `sp.push() = v`, `sp.push().f = v`  - [ ] memory  - [ ] cross-domain
  - [x] operators into a local (`binopAssignment`, `binopUnfoldLeft/Right`,
    the two short-circuit rules, `unopAssignment`, `unopCapture`)
  - [x] compound assignment `op=`: `localOpAssign`, `storage{Root,Field}OpAssign`,
    `storageIndex{Mapping,Array}OpAssign`, the two `…OpAssignUnfoldLeftFst`,
    `compoundAssignValueRhsCapture`; update `Upd.opSave`, frame `OpLoc.store_agree`
  - [x] `++`/`--`: `localIncrement`, `storage{Root,Field,Index}Increment`, the two
    `…IncrementUnfoldLeftFst`, `localAssignIncrement`,
    `storage{Root,Field,Index}IncrementAssignment`; updates `Upd.bump`/`Upd.bumpBind`,
    frame `OpLoc.bump_agree`
  - [x] ternary: `ternaryToIf`, `ternaryToIfStorage` (a conditional source is lowered
    before any receiver unfold, as KeY's `isValueSource` requires), `ternaryCaptureCond`
    over a value hole `VHole`
  - [x] `transfer`: the two unfolds, `transferNoCallback` (KeY's default
    `transferSemantics`; `withCallback` is the alternative, not ported)
  - [ ] calls (`functionBodyExpand`, `functionCallArgCapture`)
  - [x] the bridge, names: `Taclet.rule`, `Taclet.origin`,
    `Taclet.origin_claimed` (`Kernel/Bridge.lean`); `Taclet` is a `Type`, so
    a derivation's constructor can be read back
  - [x] the bridge, run: `Prog.disagreements` (kernel `Stmt.step` against
    the old `candidate` on the erasure), pinned by `#guard` on a tour of every
    statement form: three disagreements, both verdicts below
  - [ ] the bridge, shapes: `(ruleEffect d.rule).cond s.erase`, and at the
    scratch names `se`/`sp`/`ie` the residual's erasure against `ruleEffect`
    (a sweep closes the terminal rules; the unfolds need `Hole.fill` erasure
    lemmas)
  - [ ] typed shapes, `rules_disjoint`/`rules_complete` (with `Stmt.step`, phase 4)
  - [ ] `dl{ … }` notation for taclets, premises and updates
- [ ] Phase 4: `Stmt.step`, `Stmt.complete`, `Fml.progress`.
  - [x] `Stmt.step` and `Stmt.complete` over the current syntax (`Kernel/Step.lean`)
  - [ ] disjointness (at most one rule per statement, up to scratch names)
  - [ ] `Fml.progress`, with the formula layer of phase 6
- [ ] Phase 5: the measure, `symex_normalizes`, `BlockStep.wellFounded`.
  - [x] sizes and `Taclet.smaller` (`Kernel/Measure.lean`): the measure of a goal
    is `Σ 5 ^ size`; an unfolding rule leaves at most four smaller statements,
    a split smaller branches
  - [x] the measure falls on goals: `Kont.weight`, and `Kont.vc_fuel` (past
    the weight, the executor's fuel changes nothing: `symex_normalizes`),
    `Kont.goals` (`Kernel/Symex.lean`)
  - [ ] `BlockStep.wellFounded` (the old layer's `Progress.lean` sorry), at cut-over
- [ ] Phase 6: `Fml C`, `Proves`, `Proves.sound`, `FreshNames`.
  - [x] `Post`, `Kont` (with `up`, so the rest of a program is never retyped),
    `Hyps`, `Proves`, `Proves.sound` (`Kernel/Logic.lean`)
  - [x] the symbolic executor (`Stmt.step` driving `Proves`), `Prog.correct`
    against `execBlock`, the `symex`/`symex_close` tactics, worked examples
    (`Kernel/Symex.lean`); a precondition is `Hyps.assume`
  - [ ] `FreshNames`
- [ ] Phase 7: cut over, `lean/solkey` migrated.
- [ ] Phase 8: chains, `UpdRule`, decision procedure, `delAt`, one notation.

### Decisions

| Question | Decision | Date |
|---|---|---|
| Rule names | solkey's taclet names (§5) | 2026-09-25 |
| `native_decide` | forbidden in `Solidity/Kernel/`; old files keep their count | 2026-09-25 |
| Struct bodies | stay the package-wide `Semantics.structDef`, which the interpreter reads; a `Contract` is its storage roots only, and `Contract.fieldType` reads the table. A per-contract table would let a contract disagree with what runs. Revisit in phase 7, if the interpreter is made contract-parametric | 2026-09-25 |
| Context index | a statement is `Stmt C Γ Γ'`, indexed by the local context `stmtWt` threads, and each name carries its `Γ` binding (a root, `lookupBy r Γ = none` too). That is what makes `Prog.erase_wt` hypothesis-free: without the index a typed term could use `x` at two types, and only a predicate could rule it out | 2026-09-25 |
| Declarations | a declaration introduces a fresh name (`isFresh`: neither a local nor a state variable), so contexts only grow and a name fresh at `Γ` occurs in no term typed at `Γ`. That is the freshness the untyped rules assume per rule (`stmtUsesVar … = false`); here it is typing | 2026-09-25 |
| Scratch names | a taclet takes its scratch names as parameters with freshness proofs; the elaborator and `Stmt.step` pick `se`, `sp`, `ie` first, so on a program that does not use them the residual erases to the rule table's own | 2026-09-25 |
| Conditions | `if`, `require` and `assert` test a `Simple` value; `ksol` captures any other condition into a fresh `bool` first (`ifElseUnfold`, `requireConditionCapture` are the elaborator's). A branch still may not declare, so a complex condition nested in a branch is an elaboration error | 2026-09-25 |
| `T storage x;` | not a kernel statement: solc ≥ 0.5 rejects an uninitialised storage pointer (`storageLocalDeclSkip` has no kernel counterpart) | 2026-09-25 |
| Semantics | kernel terms get a structural denotation, proved to be the interpreter's (`Prog.run_eq`); taclets are proved sound over it, not through the untyped `*_sound` theorems, whose scratch names are fixed strings | 2026-09-25 |
| Array bounds | no `inBounds` split: `SVal.find`/`SVal.save` revert out of range, so the kernel's update fails as the statement does. A failing update is read like a revert by the modalities | 2026-09-25 |
| Typed states | not needed: `Premise.Correct` is over every state. The short-circuit rules re-apply the operator to the value they read (`v = nse; v = v && true;`), so a non-boolean read is stuck in the premise as in the original. `Kernel.Typed` and `Val.eval_bool` stay for later use | 2026-09-25 |
| Operator families | a rule over an operator is one constructor (`binopAssignment op`), as in `Calculus/Rules.lean`; solkey's taclet is per operator | 2026-09-25 |
| Continuations | an unfolding rule's residual binds scratch names fresh at the statement's context; to retype the rest of the program past them, the names must also avoid what the rest declares. The formula-level step picks them avoiding both, and `Prog` weakens along an extension that names its new bindings | 2026-09-25 |
| Goals | a goal is `H ⊢ k`: hypotheses (path conditions and updates, a predicate transformer) and a continuation (`⟨P⟩ k`, `up h k`, a postcondition). An unfolding rule's premise is `⟨P⟩ up ⟨ω⟩ k`; the frame lemmas make that sound, and the scratch names need not avoid what `ω` declares. A diamond split also owes the condition's definedness (`c || !c`), and a closed box owes `H ⊢ true`: an update that fails under a diamond hypothesis is false | 2026-09-25 |
| `Taclet` in `Type` | a derivation is data: `Taclet.rule`/`Taclet.origin` read its constructor. In `Prop` they could not, and proof irrelevance would identify two rules deriving the same premise. `Stmt.complete` is `∃ pr, Nonempty (Taclet …)` | 2026-09-25 |
| State-variable operand | `x = total + 1;` captures `total` (`binopUnfoldLeft`), as KeY's `addition_unfold_left` does: a state variable is a `Path[storage,simple,primitive]`, not a `SimpleExpression` (literal or program variable). The old table's `s` admits it and fires `binopAssignment`; the kernel follows KeY | 2026-09-26 |
| Storage declaration, unbindable path | `Person storage r = persons[x + 1];` captures the index first (`Hole.decl`). KeY's `storageLocalDeclInitDrop` drops any initializer to an assignment, and so does the old table; the kernel has no `T storage x;` to drop to, so it fuses the drop with the rebind and needs the path bindable | 2026-09-26 |
| Compound target | `OpLoc`: a local, a state variable, a member, or an entry at a *simple* index. The old table is stuck on `values[i + 1] += 1;` and solkey has no taclet for it; `ksol` captures the index into `ie` first, as it does a condition. The update `Upd.opSave` reads the source first, as `execStmt` does, so the terminal rules are exact; no `?=` freeze in the unfolds, a kernel value having no effects | 2026-09-26 |
| `y = nsp.f++;` | the assignment form takes a target whose receiver is simple (`OpLoc.recvSimple`): neither solkey nor the old table has an unfold for it. `ksol` captures the receiver into a scratch `sp`, which the old table would bind by its Lean-only `storagePlaceAlias` and the kernel binds, as KeY does, by `storageLocalDeclInitDrop` (the bridge tour's fourth disagreement) | 2026-09-26 |
| Memory reference from a member | `mp.account = mq.account;` is `memoryFieldWriteCopy` from any *bindable* source. The old table (and solkey's `memoryFieldRead_unfold_rightSndResult`) first captures the member into a scratch `T memory se = mq.account;`, which requires the slot to hold a reference; the interpreter copies a reference slot as it is, so over every state the capture is not correct. The two `…_rightSndResult` memory rules are not kernel rules (the bridge tour's memory disagreements) | 2026-09-26 |
| Modalities | the kernel's box is partial correctness (it holds unless the run ends normally in a bad state) and its diamond needs a normal end; neither tells a revert from a stuck run. An unfolding rule then owes its statement the same *successful* outcome (`SameOk`), which the order-changing rules (`*StorageRef_unfold_leftFst`, `*NonSimpleIndexCapture`) meet without the side conditions the untyped `*_sound` theorems carry. `SolidityJudgment.Holds` differs on stuck runs ("a stuck execution validates nothing"); the phase-7 bridge must say so | 2026-09-25 |
| Unknown names | an error: parameters are declared locals. mini-solkey reads an unknown name as a `uint` parameter | 2026-09-25 |
| Ported contracts | one named constant per interpreter store, `initStorage_*` checks roots, order and defaults against the store by `simp` | 2026-09-25 |

### `ResidueShape` verdicts

One row per constructor of `Coverage.ResidueShape`, filled in phase 2:
*unrepresentable* (the typed syntax cannot write it, and why) or *rule* (the
`Taclet` constructor that runs it).

| Shape | Verdict |
|---|---|
| `iteSymbolicCond` | *rule*: `ifElseSplit`, a `split` premise (phase 3), on a `Simple` condition; a complex one is captured by `ksol` |
| `incDecStmt` | storage and stack *unrepresentable*: `Stmt.incDec` takes an `OpLoc` (a local, a state variable, a member, an entry at a simple index; `ksol` captures a complex index). Memory targets open |
| `assignMemFieldFromStorage` | open |
| `assignMemIndexFromStorage` | open |
| `assignStackRefUnfoldTarget` | *unrepresentable*: a stack local has a primitive type (`Val.local`) |
| `assignPushPlaceLhsNonStorage` | *unrepresentable* once push places exist: as `deletePushPlaceNonStorage` |
| `assignStorageLocalRootFromStack` | *unrepresentable*: an alias has a reference type, a stack local a primitive one |
| `assignMemoryRootFromStack` | open |
| `assignStackVarFromMemory` | open |
| `assignStackPlace` | *unrepresentable*: a member or index access has its base's location, and a stack local has no members |
| `assignPushRhsNonStorage` | *unrepresentable* once push places exist: as `deletePushPlaceNonStorage` |
| `assignPushRhsNonLocalLhs` | open |
| `assignOperatorRhsBadLhs` | storage slice *unrepresentable* (local root: reference type; stack place: none); memory root and push place open |
| `assignOperatorRhsRefTyped` | *unrepresentable*: an operator is applied at a primitive type (`Val.binop`) |
| `assignIncDecBadTarget` | storage and stack *unrepresentable*: `Stmt.assignIncDec` writes a stack local, from an `OpLoc` with a simple receiver (`ksol` captures another). Memory targets open |
| `assignTernaryBadLhs` | *unrepresentable*: a conditional is a `Val`, and a value is written only to a local or a storage `Loc` (`VHole`) |
| `assignCallRhs` | open |
| `assignStackPlaceRhs` | *unrepresentable*: as `assignStackPlace` |
| `compoundAssignPow` | *unrepresentable*: `Stmt.opAssign` carries `op.hasCompoundAssign`, which `**` fails (solkey has no `powAssign` taclet) |
| `compoundAssignBadTarget` | storage and stack *unrepresentable*: an `OpLoc` target. Memory targets open |
| `memoryDeclBadInit` | open |
| `deleteStorageLocalRoot` | *unrepresentable*: `delete` takes a `Loc`, never an alias |
| `deletePushPlaceNonStorage` | *unrepresentable* once push places exist: they will be over a storage `SPath` |
| `pushNonStorageTarget` | *unrepresentable*: `Stmt.push` takes a storage `SPath` (solc has no `push` on a memory array) |
| `pushMemoryValue` | open |
| `popNonStorageTarget` | *unrepresentable*: as `pushNonStorageTarget` |
