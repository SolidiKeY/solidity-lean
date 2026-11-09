# Audit: proof coverage gaps (2026-11-06)

Read-only audit, batch `audit-20261106`, lane `proof-coverage`, base
`c0228e0e774f29e365933e409bf747cb0d4ca089`. No Lean, proof, doc or config
file outside `docs/audits/` was changed. Paths are repository-relative.

## 1. Verdict

The trusted core is clean. `Solidity/` contains no real `sorry`, no axiom
and no `native_decide` (§2). `Stmt.sound` has no premises
(`Solidity/Calculus/StmtSound.lean:48`).

What the project proves, though, is almost entirely about its own
**intrinsic** model: `Stmt.run`, and an abstract machine with symbolic
storage slots. The links from that model outward are partial or missing.

- **Source to model.** The elaborator's lowering (`lowerLoops`,
  `uncheckStmts`) has no correctness theorem. Source↔model agreement exists
  for hand-written shapes (`Lowering/G19`, `Source/Agreement`) but not for
  what the elaborator emits.
- **Model to bytes.** The public end-to-end statement (`PublicCorrectness`)
  is inhabited only by toys.
- **Model to solc.** No row of the feature manifest is backed by a theorem
  relating it to solc. 12 of the 13 `present` rows are tested only or true
  by definition.

The headline compiler theorem, in all three of its forms, is satisfied by a
compiler that always reverts on any program that pays. The repository's own
docs call that disjunct a stale weakening that no proof reaches, and the
non-vacuity suite never exercises it.

The best-paying next efforts:
1. Delete that disjunct.
2. Put the existing headline witnesses into CI.
3. Make the manifest cite theorems.
4. Connect `lowerLoops` to the G19 shapes that are already proved.
5. Port the Source semantics' panic codes into the intrinsic model.

## 2. Method

All numbers below were produced on this base. The scripts are in
`docs/audits/proof-coverage-tools/`.

| Measurement | Command / tool | Result |
|---|---|---|
| Lean files (excluding `.lake`, `vendor`) | `find . -name '*.lean' …` | 7,592 files, ~1.16 M lines |
| Trust scan | `grep -P` for `sorry`, `^\s*axiom`, `native_decide`, `ofReduceBool`, `@[extern`, `opaque` | **`sorry`**: 28 hits in 14 files. All are strings or docs (proof-search output `r"sorry"`, e.g. `Calculus/Derive.lean:136`), except `Bridge/vendor/CaseStudies/Velvet/Syntax.lean:324`. **`axiom`**: 2 hits, a docstring and `Bridge/vendor/Loom/SMT.lean:215` (`axiom trust_smt : ∀ p, p`). **`native_decide`**: 0 uses in `Solidity/` (6 hits, all comments). **`@[extern]`**: only in `Bridge/vendor/EvmYul/FFI` |
| Is `trust_smt` reachable from the Bridge? | Import-closure walk from `Loom.MonadAlgebras.WP.Tactic`, the Bridge's only Loom import (`Bridge/SolidityBridge/Loom.lean:2`) | 27 modules; `Loom.SMT` is not among them |
| Theorem census | `python3 -I docs/audits/proof-coverage-tools/theorem_census.py` (2.1 s) | 73,013 theorem/lemma/example declarations. 34,936 are closed (no binders before `:`); 22,428 are ground facts about fixed values. By area: `Solidity/Yul` 20,271 (68 % closed), `Solidity/Backend` 15,006 (45 %), `Solidity/Calculus` 6,206 (5 %). 44 conclude `True` (§5) |
| Trust-gate headline set | `TrustAudit.lean` `headlines` list | 1,365 names (1,355 unique). 707 are under `Evm.Memory`; 705 contain `Examples` |
| Manifest | `python3` over `docs/solidity-features.json` | 212 rows. `current`: partial 160, notApplicable 37, present 13, missing 2. `scope`: model 152, exclude 30, abstract 23, upstream 7. 456 evidence paths, 0 missing |
| Claims inventory | 13 `present` rows plus 12 high-traffic `partial` rows, each traced to its backing declarations | Table in F8 |
| Statement quality | 43 theorems: all 21 in `Solidity/Theorems.lean`, plus 11 chosen per area, plus 11 drawn with `random.seed(20261106)` from the 637 `TrustAudit` headlines that are neither examples nor controls (list in `proof-coverage-tools/statement-sample.txt`) | 37 fine; 3 V3 (a disjunct satisfied by a trivial implementation); 2 V2 (premise equivalent to the conclusion, both disclosed or by design); 1 V5 (instance is a toy only); 0 V1 or V4 |
| Compiled fragment | Compared `Evm/Compile.lean:274-320` (`inFrag`) with `Syntax/Scoped.lean:405-514` (`Stmt`) | 36 constructors; `inFrag` returns `none` for 17 of them unconditionally |
| Exclusion corpus frequency | `find tests vendor -name '*.sol'` (396 files), then `grep -E -c` per pattern | Table in F6 |
| CI reach of the witnesses | `grep h28` in `lakefile.toml` and `.github/workflows/*` | 0 hits. The suite has its own `tests/h28-sol/non-vacuity/runtime/lakefile.toml` and runner |

Three read-only investigators ran the inventory, statement-quality and
residue sweeps. Every claim of theirs used here was re-read at the cited
line. A separate read-only skeptic then tried to refute each finding (§7).

## 3. Top 10 findings

Evidence is measured. Payoff and effort are the author's estimates, in hours
of proof work.

| Rank | Finding | Evidence | Est. payoff | Effort | Risk |
|---|---|---|---|---|---|
| 1 | The headline compiler theorem is satisfied by an always-reverting compiler on every paying program. No proof needs that disjunct, and no witness exercises it | `Theorems.lean:269`; `Evm/Correct.lean:1089`; `Evm/Compiler.lean:552` (`Agrees`). `.refused` is only ever re-wrapped (`Correct.lean:79,95,111,168,504,583,922,933,937`, `Evm/Stmt.lean:123`). `transfer_sim` maps a refusal to `.inr` (`Evm/Stmt.lean:892-`). The h28 witnesses close the pays branch by `cases hp` (`…/NonVacuityH28/Families.lean:86-98`) | Removes the obligation-5 always-revert loophole from 3 public statements | 8–20 h | Low |
| 2 | The public source-to-bytecode theorem is inhabited only by toys | `Roadmap/Contracts.lean:937`. In `Yul/Composition/CorrectnessPublic.lean:20-23`, 9 of 13 fields "pass through unchanged". Instances: `toy_publicCorrectness`, `publicCorrectness_of_faithful` (`Roadmap/Controls.lean:554`), `public_instance` (`CorrectnessPublicControls.lean:33`), all over `toySource`/`toyEvm` | Obligation 5: nothing above the abstract machine is end-to-end | Inventory: 1 day. Then large | High |
| 3 | The elaborator's lowering is unproved; source↔model agreement covers hand-written shapes only | `Syntax/Elab/Lower.lean:543` (`lowerLoops`, an `ElabM` def), cited by 0 theorems. G19 proves hand-built shapes (`Lowering/G19/AssignmentWhileBreak.lean:74` `correct`). `Source/Agreement/NormalStatement.lean:6-9` says "not inhabited here for any general … pair" | Every `present` row rests on this link (obligation 2) | 20–40 h to tie `lowerLoops` to G19 | High |
| 4 | The core compiler's machine builds in keccak injectivity, which the user decision forbids in the final theorem | `Evm/Machine.lean:165` (`Word.slot`), `:194-195` (`keccakMap`/`keccakArr`), `:223` (`Instr.loop`). 0 uses of `CollisionFree` in `Solidity/Evm`. `docs/compiler-verification.md`, "The machine" | Unblocks transfer of every compiler result to bytes | 40–80 h | Medium |
| 5 | The intrinsic model collapses panic and revert payloads, which the Source semantics already distinguishes | `Semantics/Run.lean:58-66` (`panic` carries no code) and `:90-92` (`ofOpt none = .revert`); `Semantics/Ops.lean:57-58`. Against: `Source/Observe.lean:145` (`PanicCode`), `Source/SemanticsExamples.lean:90,99`. `docs/solc-alignment.md`: "`⟨ revert("m"); ⟩ false ↯ []` is provable" | Removes provable formulas that are false of solc and observable via `try`/`catch` | 30–60 h | High |
| 6 | The compiled fragment refuses 17 of 36 statement forms, plus `keccak256`, `addmod`/`mulmod`, memory reads and `bool`/`int` mapping keys | `Evm/Compile.lean:312-319`, `:278`, `:127`, `:116`. Corpus: `try` 75 lines, `keccak256(` 14, `.send(` 8 | Each constructor widens `compiler_correct` | 10–30 h per constructor | Medium |
| 7 | The headline witnesses exist but no CI target builds them | `tests/h28-sol/non-vacuity` applies `Main.compiler_correct`/`_net`/`_checked` (`Families.lean:86,106,42`). 0 hits for `h28` in `lakefile.toml` and `.github/workflows/`. `docs/feature-work/h28-non-vacuity.md:112`: "`check.py --accept` intentionally fails" | A statement can weaken (as F1 did) without any build failing | 2–4 h | Low |
| 8 | The feature manifest cannot be traced to theorems: 9 of 13 `present` rows cite one file, 14 `partial` rows cite no Lean outside Examples/tests, and `present` admits class d | F8 table. `checkedArithmetic` cites only `docs/solc-alignment.md`, although `compile_correct` proves the checked guards | Makes F1–F7 auditable and exposes over- and under-claims | 6–10 h | Low |
| 9 | `DecisionTheorem` is open, `DecisionTheorem'` is total off the residue by definition, and the residue is never measured | `Calculus/Decision.lean:2018` (unproved `Prop`); `DecisionResidue.lean:273,293`; `Examples/Decision.lean:255` ("is not yet true"); `docs/automation.md:965` ("not enforced by the code") | A pinned residue census turns M7 progress into a number | 4–8 h | Low |
| 10 | The payment oracle is still quantified in the compiler theorem, and the formula-level no-callback special case is unproved | `docs/solidity-scope.md:90` (G00 Q2); `Calculus/Assumptions.lean:111`. Context-level special cases do exist: `Semantics/CtxEquiv/Basic.lean:256-262`, `Theory/Reachable/CallerModel.lean:279`. Corpus: `.transfer(` 41, `.call{value` 42, `.send(` 8 lines | Closes the remaining G00 Q2 item for formulas | 10–20 h | Medium |

## 4. Findings

### F1. An always-reverting compiler satisfies the headline compiler theorem on paying programs

`compiler_correct` (`Solidity/Theorems.lean:269`) is a disjunction of four
cases. Two of them let the machine revert when the program pays:

- third disjunct: `(Prog.pays P = true ∧ (⟦P⟧b, mc) ↯ₘ ∧ ∃ o, (P, σ) ⇓ o)`;
- fourth disjunct: allows `Prog.pays P = true ∧ (⟦P⟧b, mc) ↯ₘ` when the run
  diverges.

`Prog.pays` (`Evm/Compile.lean:253-268`) is true for any `transfer`,
including one inside a called body. For such a program, code that always
reverts satisfies the theorem: the third disjunct covers a source that ends,
the second a source that reverts, and the fourth a source that diverges. The
only exception is a source `panic`, which needs `Prog.asserts P = true`.

The same disjunct appears in:
- `Evm.compile_correct` (`Evm/Correct.lean:1089`);
- `Compilation.Agrees` (`Evm/Compiler.lean:552`), and therefore
  `compiler_checked` (`Theorems.lean:297`).

The exact theorem, `compile_exact` (`Correct.lean:1115`, with
`hpay : Prog.pays P = false`), does not appear in `Theorems.lean`.

`docs/compiler-verification.md` ("What is proved") says the disjunct is
unused: "No proof reaches that third case … `StmtOut.refused` is only
propagated from an inner `refused`, never originated … a stale weakening
(G04 R32, owned by G43)." The skeptic pass confirmed this. A refusal in
`transfer_sim` (`Evm/Stmt.lean:892-`) makes the typed run revert too and
yields `.inr`. Every `.refused` construction re-wraps an inner one
(`Correct.lean:79,95,111,168,504,583,922,933,937`; `Evm/Stmt.lean:123`).

The h28 non-vacuity suite never takes this branch. `Families.lean:86-98`
discharges it with `cases hp`, because `requireProgram` does not pay.

**First step.**
1. Delete the `StmtOut.refused` constructor; the build will list every
   match that needs an arm.
2. Close each such arm with `nomatch`.
3. Restate `compiler_correct`, `compile_correct` and `Agrees` with three
   disjuncts.
4. Add an h28 control that applies `compiler_correct` to
   `owner.transfer(30)` (`Evm/Examples.lean` `payOwner_run`).

### F2. The public end-to-end theorem has only toy instances

`PublicCorrectness` (`Roadmap/Contracts.lean:937`) states obligation 5. Its
negative controls are good: `not_publicCorrectness_*` in
`Roadmap/Controls.lean` reject the always-revert, erasing, sloppy and
hash-revert compilers.

It is inhabited only by toys:
- `toy_publicCorrectness`;
- `publicCorrectness_of_faithful` (`Roadmap/Controls.lean:554`);
- `public_instance` (`Yul/Composition/CorrectnessPublicControls.lean:33`).

All three are over `toySource`/`toyEvm`.

The generic producer, `Stages.publicCorrectness`
(`Yul/Composition/CorrectnessPublic.lean:68`), takes a `PublicBoundary`.
That structure's docstring says "9 of the 13 `PublicCorrectness` fields pass
through unchanged". The toy boundary fills those nine fields from
`toy_publicCorrectness` itself.

**First step.** For each of the nine pass-through fields, name the existing
real-pipeline lemma that would discharge it, or write "none". Commit the
table as a Controls file that `#check`s each candidate. Obligation 5 then
becomes a list of missing lemmas.

### F3. The elaborator's lowering is unproved

See the [lowering prior-art study](prior-art-lowering.md) for the comparison of actual-output association mechanisms and the existing bounded G19 proofs.

Every calculus and compiler theorem quantifies over intrinsic `Stmt`/`Prog`.
`Stmt` has no `break` (`Syntax/Scoped.lean:405-514`).

User syntax reaches that model through unverified meta-code:
- `lowerLoops` (`Syntax/Elab/Lower.lean:543`, an `ElabM` function, called at
  `:701` and from `Arms.lean:829,1522`) turns `break`, `continue` and `for`
  into flags and `while`.
- `uncheckStmts` (`:707-736`) rewrites `unchecked` blocks syntactically.

No theorem mentions either function.

Agreement between the independent `Source/` semantics and the model is
proved for hand-written target shapes. `Lowering/` has 662 files, including
36 under `Lowering/G19/` with kernel `correct` theorems for `while`,
`do`-`while` and `for` with `break`, `continue` and `return`. One example is
`G19/AssignmentWhileBreak.lean:74`, which relates
`Source.execS (.whileLoop … .brk)` to an intrinsic `Prog.run`.
`Source/Agreement` adds per-shape instances, and
`Source/Agreement/NormalStatement.lean:6-9` itself says "It is not inhabited
here for any general source/model program pair."

So the manifest's `breakStatement: present` rests on G19 shapes plus
printed-output `#guard_msgs` (`Examples/Tactics/Loops.lean:60-106`). Nothing
shows that the elaborator produces those shapes.

**First step.** Prove that `lowerLoops` output on the G19 source shapes
equals the targets G19 already verifies. One way is to evaluate `lowerLoops`
in a kernel-checkable pure fragment and prove the equation for the
`AssignmentWhileBreak` family. That reuses G19 rather than duplicating it.

### F4. The core compiler's machine builds in keccak injectivity

The machine's storage words are terms: `Word.slot` (`Evm/Machine.lean:165`).
It has:
- `keccakMap`/`keccakArr` instructions (`:194-195`);
- structured loops, `Instr.loop` (`:223`);
- relative jumps;
- addressed local cells.

`docs/compiler-verification.md` ("The machine") says slots as terms mean
keccak "never collides … This is global injectivity, which the user
decisions forbid in the final theorem". The approved premise is a per-run
collision bound (G04 R34). `CollisionFree` (`Hash/CollisionBound.lean`) has
0 uses in `Solidity/Evm`.

The calculus, by contrast, reads hashes as opaque atoms with no collision
resistance (`Calculus/Assumptions.lean:95`). The two halves of the project
therefore rest on different hash premises.

**First step.** Restate `save_repr`'s disjointness argument (`Occ`,
`Desc.unique`) over concrete words, under `CollisionFree` for the run's
preimages. According to the docs, it is the only use of injectivity.

### F5. The intrinsic model collapses panic and revert payloads

`THalt` (`Semantics/Run.lean:58-66`) has five constructors: `revert`,
`panic`, `diverge`, `exhausted` and `revertWith d`. `panic` carries no code.

Several failures end as a plain `.revert`:
- a failed checked operation: `TRes.ofOpt none = .error .revert`
  (`:90-92`);
- division and modulo by zero, which produce `none`
  (`Semantics/Ops.lean:57-58`);
- `pop` on an empty array.

So `Panic(0x11)`, `Panic(0x12)` and `Panic(0x31)` are all `.revert`.
Outside a self-call callee, `require(c, "m")` and `revert("m")` revert with
`[]`. `docs/solc-alignment.md` records that `⟨ revert("m"); ⟩ false ↯ []` is
provable and false of solc.

The difference is observable through `try`/`catch` and `revertData`. The
manifest requirements for `checkedArithmetic`, `assertBuiltin`, `arrayPop`
and `requireBuiltin` name these codes.

The independent Source semantics already gets this right:
- `Source/Observe.lean:145` defines `PanicCode` (`arithmetic` = 0x11,
  `divZero` = 0x12, `popEmpty` = 0x31) with `panicData`;
- `Source/SemanticsExamples.lean:90,99` shows overflow yielding
  `panicData .arithmetic` and division by zero yielding `.divZero`.

The defect is therefore confined to the intrinsic model and the calculus
built on it.

**First step.** Port `PanicCode`/`panicData` into `THalt`: have `TRes.ofOpt`'s
callers in `Ops.lean` produce `revertWith (panicData …)`. Find the
soundness arms to update with
`grep -l '\.error \.revert' Solidity/Calculus/Sound*`.

### F6. The compiled fragment covers 19 of 36 statement forms

`inFrag` (`Evm/Compile.lean:312-319`) returns `none` unconditionally for 17
constructors:

`assignLocalPush`, `send`, `declMem`, `rebindMem`, `assignFromMem`,
`assignMem`, `deleteMem`, `assignNew`, `tryCall`, `revertData`, `catchData`,
`pushOpAssign`, `pushIncDec`, `callReceiver`, `callReceiverPush`, `callRec`,
`assumeFalse` (the last is a calculus form, not Solidity).

It also refuses:
- `rebind … (.push ..)` (`:278`);
- the expressions `readMem`, `mlen`, `modular` (`addmod`/`mulmod`) and
  `hash` (`keccak256`) (`:127`);
- mappings keyed by `bool` or `int` (`:116`);
- loops whose body pushes, pays or shrinks (`:307-313`).

The memory path covers some of these separately:
- `Evm.Memory.compile_correct` (`Evm/MemoryCompile.lean:1257`);
- recursive dispatch (`Evm/MemoryRecursiveDispatch.lean:91`).

How often the refused syntax appears in the 396 `.sol` files:

| Pattern | Lines | Files |
|---|---|---|
| `try …` | 75 | 20 |
| `keccak256(` | 14 | 7 |
| `.send(` | 8 | 5 |
| `.transfer(` | 41 | 26 |
| `.call{value` | 42 | 17 |
| `msg.value` | 129 | 35 |

**First step.** Add `send`. The typed run and the `CALL` already agree on
refusal (`transfer_sim`), and `send` differs from `transfer` only in pushing
the flag.

### F7. The headline witnesses are not built by CI

The h28 non-vacuity suite (`tests/h28-sol/non-vacuity/lean/Solidity/Assurance/NonVacuityH28/`)
applies the headline compiler theorems:
- `Main.compiler_correct` (`Families.lean:86,156`, `Fragile.lean:32`,
  `Locals.lean:15`);
- `Main.compiler_net`, including on a paying program
  (`JointWorld.lean:32`);
- `Main.compiler_checked` (`CheckedObjects.lean:16`,
  `LoopContracts.lean:240`).

It also inhabits the allocating `AllocationInput.inr` branch
(`MemoryInputs.lean:59`, `CheckedObjects.lean:44`) and has negative controls.
Its pins are listed in `scripts/g07-axiom-pins.json`.

But the suite is built by its own runner and lakefile
(`tests/h28-sol/non-vacuity/runtime/lakefile.toml`, `run.py`).
`lakefile.toml` and `.github/workflows/*` contain no reference to it. Its
handoff says `check.py --accept` "intentionally fails until the remaining
whole-scope ledger … [is] complete" (`docs/feature-work/h28-non-vacuity.md:112`).

So a change to a headline statement can break or weaken its witnesses
without any CI failure. F1's loophole has no witness anywhere.

**First step.** Add the six NonVacuityH28 modules the handoff lists as
kernel-passing to a `lean_lib` in `lakefile.toml`, built by `lean.yml`.
Then add the paying-program control from F1.

### F8. Feature manifest claims vs evidence

Classes:
- **a**: kernel-proved, against the repo's own semantics;
- **b**: proved modulo named premises;
- **c**: tested only (`#guard`, fixtures, kernel `decide` on constants);
- **d**: true by definition or by table, with no theorem.

**The 13 `present` rows.** Tally: 1 a, 6 c, 6 d. None relates to solc.

| Row | Backing | Class |
|---|---|---|
| booleanLiterals | `Frontend/SolcJson/Body.lean:1618-1623`; `PrimTy.Denote .bool = Bool` | d |
| etherUnits | Manifest cites `Body.lean`; factors in `Syntax/Grammar.lean:416` `unitFactor?`; `Source/TypingExamples.lean:60` | c |
| timeUnits | Manifest cites `Body.lean`; factors in `Grammar.lean:416` | d |
| boolType | `Semantics.lean:23-24` (`Denote .bool = Bool`). Note: `bool` mapping keys become `uint` via `e ? 1 : 0` (`Body.lean:1143-1145`) | d |
| parentheses | `Grammar.lean:650` | d |
| ifStatement | `iteStep_sound` (`Calculus/SoundControl.lean:333`) → `Stmt.sound`; `compile_correct` | a (own semantics); b (fragment) |
| breakStatement | `lowerLoops`, G19 shapes, `#guard_msgs` (`Examples/Tactics/Loops.lean:60-106`) | c for the elaborator path (F3) |
| erc7201Builtin | `ERC7201.lean:32` `root_aligned`; constants by `decide +kernel` | c. No theorem that the runtime lowering (`Lower.lean:1673`) equals `ERC7201.root` |
| msgSender | `Semantics/State.lean:106` | d. The bound is `< 2^256`, not `< 2^160` |
| blockTimestamp | `State.lean:109` | d |
| typeName | `Body.lean:1101` (the solc AST name) | c. Only a `.sol` fixture |
| interfaceId | `Body.lean:1106-1115`; `Examples/Tactics/DeclarationMetadata.lean:23` | c. Selectors are read from solc's JSON, not computed |
| errorEventSelector | `Body.lean:1120-1126`; `DeclarationMetadata.lean:27,31` | c |

**The sampled `partial` rows:**
- `whileStatement`: `Stmt.sound_loop` (`Calculus/SoundLoops.lean:555`), class a.
- `push`/`pop`: `SoundStore.lean:504,566`, class a.
- `require`/`assert`: `SoundControl.lean:380,410`, class a.
- `tryStatement`, `externalTypedCalls`: class b, under the `TTx.ext` oracle
  and invariant `I`.
- `keccakBuiltin`: class c. `keccakBytes` (`Semantics/Heap.lean:473`) is
  backed by 5 `#guard` vectors (`Keccak.lean:111-120`); `Keccak.lean` has 0
  theorems.
- `emitStatement`: class c. Arguments are evaluated and the log is dropped
  (`Syntax/Raw.lean:192-197`).

**Traceability.** 9 of the 13 `present` rows cite exactly one file. These
14 `partial` rows cite no Lean outside Examples/tests: `checkedArithmetic`,
`uncheckedArithmetic`, `evaluationOrder`, `defaultInitialization`,
`referenceCopyRules`, `panicCodes`, `revertPayloads`, `rollback`,
`abiEntryValidation`, `constructorLifetime`, `nonpayableEntry`,
`staticCallRestriction`, `termination`, `worldAssumptions`.

`checkedArithmetic` cites only `docs/solc-alignment.md`, which under-claims:
`compile_correct` emits and proves solc's checked guards.
`docs/solidity-scope.md:65` defines `present` as "implementation evidence …
not a solc-equivalence theorem", so class d qualifies.

**First step.** Add a `theorems: [name]` field to each row, and a script that
`#check`s each name and flags `present` rows of class c or d.

### F9. The decision procedure's residue is unmeasured

`DecisionTheorem` (`Calculus/Decision.lean:2018`, "The open theorem") is an
unproved `Prop`. `Examples/Decision.lean:255` lists counterexamples.

`DecisionTheorem'` (`DecisionResidue.lean:293`) assumes `¬ φ.Residue`, and
`residue_iff_unknown` (`:273`) makes that equivalent to
`decideGoal φ ≠ .unknown`. Its totality is therefore definitional, which its
docstring states. Its real content is the soundness of each answer
(`decideGoal_sound`, `decideGoal_refutes`).

`docs/automation.md:965` says the shrink policy is "not enforced by the
code". No fixture counts `Fml.residue` leaves; the `Seq.residue` guards are a
different notion.

**First step.** Add a `#guard`-pinned count of residue leaves over the
existing TestSuite/Decision fixtures. `Fml.Residue` is decidable
(`DecisionResidue.lean:144`), so a route change that grows the residue then
fails the build.

### F10. The payment oracle remains in the compiler theorem; the formula-level no-callback case is unproved

G00 Q2 (`docs/solidity-scope.md:90`) did not approve the payment-acceptance
boolean. It also asked for the no-callback reading to be a proved special
case.

The context-level special case is already proved, so scope.md's "not yet
proved" is stale:
- `CtxRefines.noCallback` and `CtxEquiv.noCallback`
  (`Semantics/CtxEquiv/Basic.lean:256-262`);
- `exec_noCallback_iff_withCallback`
  (`Theory/Reachable/CallerModel.lean:279`).

Two things remain:
- `compile_correct` still quantifies over a fixed, history-free `accepts`
  oracle (compiler-verification.md, "The machine").
- The formula-level implication `⊨[I] φ → ⊨ₙ[I] φ` is unproved.
  `noCallback_iff` (`Theorems.lean:239`) needs `φ.callsBack false = false`,
  and `Assumptions.callback : Bool := false` (`Calculus/Assumptions.lean:111`)
  is the default reading.

**First step.** Prove `⊨[I] φ → ⊨ₙ[I] φ` by lifting
`CtxRefines.noCallback` through `ProvesC.valid`. Also update
`solidity-scope.md:90`.

## 5. Things that look bad but are fine

- **28 `sorry` hits.** They are string literals from proof-search tools
  (`r"sorry"` in `Calculus/Derive.lean`, `Closers.lean`, `TreeData.lean`),
  docstrings, or expected-error text. The one real `sorry` is in
  `Bridge/vendor/CaseStudies`, outside the trust closure.
- **`axiom trust_smt : ∀ p, p`** (`Bridge/vendor/Loom/SMT.lean:215`). It is
  not in the import closure of the Bridge's Loom import.
- **44 theorems or examples concluding `True`.** All are either negative
  controls, `fail_if_success have … ; trivial`
  (`Examples/Tactics/LexDiamond.lean:59`), or the closed-telescope witness
  `closed_input : True`
  (`tests/h62/item2/audit-calculus/JoinWalkWitnesses.lean:10`).
- **`Stmt.sound` has no premises** (`Calculus/StmtSound.lean:48`). This is
  genuine: each arm carries its own proof, and `rule_exists` inhabits
  `rule_sound`.
- **`DecisionTheorem'` assumes its totality.** This is disclosed
  (`DecisionResidue.lean:280-292`), and its real content is soundness. The
  gap is the missing measure (F9).
- **`lex_sound`** (`Frontend/Checked/Lexer.lean:711`) is translation
  validation. `lex` returns `ok` only after checking `Lexed` (`:688`), an
  independent specification. It is sound by design; completeness is not
  claimed.
- **`Prog.pays` counts `callRec` as paying** (`Evm/Compile.lean:260`). This
  does not widen F1, because `inFrag` refuses `callRec` (`:319`).
- **Three `Theorems.lean` headlines are unpinned:** `noCallback_soundness`,
  `noCallback_iff`, `cleanTail_holds`. There is no axiom or real `sorry` in
  `Solidity/`, and they reuse pinned proofs. Pinning them is cheap.
- **48 % of the 73k declarations are closed and 31 % are ground.** These are
  fixtures and controls, concentrated in Yul (13,822 closed) and Backend
  (6,821). That is expected, but declaration counts overstate general
  coverage.

## 6. Open questions for the user

None blocks this audit.

1. Should `present` require a theorem of class a or b, rather than
   implementation evidence (`docs/solidity-scope.md:65`)?
2. May a lane other than G43 remove F1's disjunct now, given that the docs
   say no proof reaches it?

## 7. Skeptic pass

A fresh read-only reviewer re-opened every citation in the first draft
(commit `f8f08205`) without using the Lean server, and tried to refute each
finding. Its verdicts, after the author re-checked its evidence, and what
this version changed:

| Draft finding | Verdict | Change |
|---|---|---|
| Compiler always-revert disjunct (now F1) | Survives | The draft said all "46 `refused` occurrences" were re-wraps; most are unrelated names (`transfer_refused` …). Now lists the actual `.refused` sites, adds `Evm/Stmt.lean:123`, and fixes `Agrees` to `:552` |
| Source to model "nothing proves" (now F3) | Downgraded | Missed the `Lowering/` tree: 662 files, with G19 kernel `correct` theorems for while/do/for with break/continue/return (e.g. `G19/AssignmentWhileBreak.lean:74`). Narrowed to "the elaborator's lowering is unproved"; the first step now reuses G19 |
| `PublicCorrectness` toy-only (now F2) | Survives | Added `publicCorrectness_of_faithful` (`Roadmap/Controls.lean:554`), also a toy |
| Symbolic machine (now F4) | Survives | None |
| Fragment coverage (now F6) | Survives | Added `rebind … .push` (`:278`) and memory-path recursion; noted `assumeFalse` is not Solidity |
| Panic codes (now F5) | Downgraded in scope | The Source semantics already has `PanicCode`/`panicData` (`Source/Observe.lean:145`). Narrowed to the intrinsic model; the first step is now a port |
| Callback/oracle (now F10, was rank 7) | Downgraded | Context-level special cases exist (`CtxEquiv/Basic.lean:256-262`, `CallerModel.lean:279`). Narrowed to the formula level and the `accepts` oracle; moved to rank 10. `callback` is at `:111`, not `:112` |
| Residue (now F9) | Survives | Quote fixed to "not enforced by the code" (`automation.md:965`); line fixed to `Examples/Decision.lean:255` |
| Manifest (now F8) | Survives; tallies confirmed (1 a / 6 c / 6 d) | Fixed `keccakBytes` to `Heap.lean:473` and the `#guard` count to 5; replaced the `AST.lean` citation for boolType |
| "15 of 43 lack a witness; compiler theorems never applied" (draft F10) | **Refuted** | `tests/h28-sol/non-vacuity` applies all three compiler theorems and inhabits `AllocationInput.inr`. The surviving, author-verified kernel is new F7: those witnesses are not built by CI (0 hits in `lakefile.toml` and workflows), and none covers a paying program. The draft's "15 of 43" figure is withdrawn |
