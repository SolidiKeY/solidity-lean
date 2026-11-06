# Audit: proof coverage gaps (2026-11-06)

Read-only audit, batch `audit-20261106`, lane `proof-coverage`, base
`c0228e0e774f29e365933e409bf747cb0d4ca089`. No Lean, proof, doc or config
file outside `docs/audits/` was changed. Paths are repository-relative.

## 1. Verdict

The kernel-checked core is clean: no `sorry`, no axiom and no `native_decide`
in `Solidity/` (§2). `Stmt.sound` has no premises
(`Solidity/Calculus/StmtSound.lean:48`). But almost everything the project
proves is about its own **intrinsic** model (`Stmt.run`, and an abstract
machine with symbolic storage slots). Nothing that is proved connects that
model to Solidity source text, to solc, or to EVM bytes:

- **Source to model (unverified).** The importer and elaborator lowering
  (`lowerLoops`, `uncheckStmts`, the `SolcJson` body importer) is meta-code
  with no correctness theorem. The independent `Source/` semantics meets the
  model only through per-shape agreement instances.
- **Model to bytes (toy only).** The one public end-to-end statement
  (`PublicCorrectness`) is inhabited only by toys.
- **The core compiler theorem is weak.** In the three statements of the
  headline compiler theorem, a compiler that always reverts satisfies the
  disjunct for any program that pays. The docs say no proof reaches that
  disjunct.

Of the 13 manifest rows marked `present`, none is backed by a general
theorem that relates the feature to solc. 12 are tested only or true by
definition; `ifStatement` is kernel-proved only against the repo's own
semantics.

The best-paying next efforts are cheap:
1. Delete the always-revert disjunct.
2. Write the missing witness controls.
3. Make the manifest point at theorems.

After those, verifying the loop/`break` lowering is the first real step
towards obligation 2.

## 2. Method

Every number below was produced on this base. The scripts are in
`docs/audits/proof-coverage-tools/`.

| Measurement | Command / tool | Result |
|---|---|---|
| Lean files (excluding `.lake`, `vendor`) | `find . -name '*.lean' …` | 7,592 files, ~1.16 M lines |
| Trust scan | `grep -P` over the file list for `sorry`, `^\s*axiom`, `native_decide`, `ofReduceBool`, `@[extern`, `opaque` | 28 `sorry` hits in 14 files, all in strings or docs (proof-search output `r"sorry"`, e.g. `Calculus/Derive.lean:136`) plus `Bridge/vendor/CaseStudies/Velvet/Syntax.lean:324`. 2 `axiom` hits: a docstring, and `Bridge/vendor/Loom/SMT.lean:215` `axiom trust_smt : ∀ p, p`. 0 `native_decide` uses in `Solidity/` (6 hits, all comments). `@[extern]` only in `Bridge/vendor/EvmYul/FFI` |
| Is `trust_smt` reachable from the Bridge? | import-closure walk from `Loom.MonadAlgebras.WP.Tactic` (the Bridge's only Loom import, `Bridge/SolidityBridge/Loom.lean:2`) | 27 modules, `Loom.SMT` not among them |
| Theorem census | `python3 -I docs/audits/proof-coverage-tools/theorem_census.py` (2.1 s) | 73,013 theorem/lemma/example declarations. 34,936 are closed (no binders before `:`), and 22,428 of those are ground facts about fixed values (no `∀∃→↔fun` in the conclusion). `Solidity/Yul`: 20,271 decls, 68 % closed. `Solidity/Backend`: 15,006 decls, 45 % closed. `Solidity/Calculus`: 6,206 decls, 5 % closed. 44 have a `True` conclusion (§5) |
| Trust-gate headline set | `TrustAudit.lean` `headlines` list (`grep -oP '^\s*``\K…'`) | 1,365 names (1,355 unique). 707 are under `Evm.Memory`, and 705 contain `Examples` |
| Manifest | `python3` over `docs/solidity-features.json` | 212 rows. `current`: partial 160, notApplicable 37, present 13, missing 2. `scope`: model 152, exclude 30, abstract 23, upstream 7. 456 evidence paths, 0 missing |
| Claims inventory | 13 `present` rows plus 12 high-traffic `partial` rows, each traced to its backing declarations | table in §4.F9 |
| Statement quality | 43 theorems. The fixed part: all 21 in `Solidity/Theorems.lean` plus 11 picked per area. The random part: 11 drawn with `random.seed(20261106)` from the 637 non-example, non-control `TrustAudit` headlines (list in `proof-coverage-tools/statement-sample.txt`) | 37 fine, 3 V3 (weak disjunct), 2 V2 (premise ≡ conclusion; both disclosed or by design), 1 V5 (toy-only instance), 0 V1/V4. 15 have no joint-satisfiability witness |
| Compiled fragment | read `Evm/Compile.lean:274-326` (`inFrag`) against `Syntax/Scoped.lean:405` (`Stmt`) | `Stmt` has 36 constructors, and `inFrag` returns `none` for 17 of them unconditionally |
| Exclusion corpus frequency | `find tests vendor -name '*.sol'` (396 files), then `grep -E -c` per pattern | table in §4.F7 |

Three read-only investigators did the inventory, statement-quality and
residue sweeps. Every claim they made that this report uses was re-read at
the cited line before inclusion. One sub-claim was refuted and dropped (§7).

## 3. Top 10 findings

Payoff and effort are the author's estimates, in hours of proof work. They
are judgements, not measurements; the evidence column is measured.

| Rank | Finding | Evidence | Est. payoff | Effort | Risk |
|---|---|---|---|---|---|
| 1 | The headline compiler theorem lets a compiler that always reverts satisfy it on every paying program, and docs say no proof uses that disjunct | `Theorems.lean:269`; `Evm/Correct.lean:1089`; `Evm/Compiler.lean:550` (`Agrees`); `docs/compiler-verification.md` "No proof reaches that third case"; 46 `refused` sites in `Solidity/Evm`, all of which propagate an inner `refused` | Removes the obligation-5 "always-revert" loophole from 3 public statements | 8–20 h | Low |
| 2 | No theorem links Solidity source to the intrinsic model: the lowering is unverified meta-code, and source/model agreement exists only per shape | `Syntax/Elab/Lower.lean:543` `lowerLoops` (an `ElabM` def, no theorem mentions it); `Source/Agreement/NormalStatement.lean:6-9` "not inhabited here for any general source/model program pair"; 212 theorems in `Source/Agreement/` (44 files) | All 13 `present` rows rest on this link; it is obligation 2 | 40 h for loops+`break`; 100s of hours in total | High |
| 3 | The public source-to-bytecode theorem is inhabited only by toys | `Roadmap/Contracts.lean:937` `PublicCorrectness`; `Yul/Composition/CorrectnessPublic.lean:24` (9 of 13 fields "pass through unchanged"); sole instance at `CorrectnessPublicControls.lean:21`, over `toySource`/`toyEvm` | Obligation 5; nothing above the abstract machine is end-to-end | 1 inventory day, then large | High |
| 4 | The core compiler targets a symbolic machine with storage-slot keccak injectivity built in, which the user decision forbids in the final theorem | `Evm/Machine.lean:165` `Word.slot`; `:194` `keccakMap`; `:223` `Instr.loop`; `docs/compiler-verification.md` "## The machine" | Unblocks every compiler result's transfer to bytes | 40–80 h | Medium |
| 5 | The compiled fragment refuses 17 of 36 statement forms, plus `keccak256`, `addmod`/`mulmod`, memory reads and `bool`/`int` mapping keys | `Evm/Compile.lean:312-319`, `:127`, `:116` | Each constructor added widens `compiler_correct`'s reach | 10–30 h per constructor | Medium |
| 6 | Halt codes collapse: overflow, division by zero and pop of an empty array are plain reverts, `THalt.panic` carries no code, and `require`/`revert("m")` revert with `[]` | `Semantics/Run.lean:58-66`, `:90-92`; `Semantics/Ops.lean:57-58`; `docs/solc-alignment.md` ("`⟨ revert("m"); ⟩ false ↯ []` is provable") | Removes provable formulas that are false of solc and are observable through `try`/`catch` | 30–60 h (semantics, then `Stmt.sound` arms) | High |
| 7 | Theorems still quantify over the unapproved payment-acceptance oracle, and the no-callback special case is unproved | `docs/solidity-scope.md:90` (G00 Q2); `Calculus/Assumptions.lean:112` `callback : Bool := false`; `compile_correct`'s `accepts` (compiler-verification.md "fixed, history-free oracle"); corpus: `.transfer(` 41, `.call{value` 42, `.send(` 8 lines | Unblocks the payable and external-call rows (3 rows, 91 corpus lines) | 20–40 h | Medium |
| 8 | `DecisionTheorem` is open, and `DecisionTheorem'` is total off the residue by definition; nothing measures or bounds the residue | `Calculus/Decision.lean:2018` (an unproved Prop); `DecisionResidue.lean:273,293`; `Examples/Decision.lean:252` "is not yet true"; `docs/automation.md` "nothing here enforces" shrinking | A residue census turns M7 progress into a number | 4–8 h for the census | Low |
| 9 | The manifest cannot be traced to theorems: 9 of the 13 `present` rows cite a single file, and 14 `partial` rows cite no Lean outside Examples/tests | §4.F9 table; `checkedArithmetic` cites only `docs/solc-alignment.md`, although `compile_correct` proves the checked guards | Makes items 1–8 auditable; shows over- and under-claims | 6–10 h (data plus a check script) | Low |
| 10 | 15 of 43 sampled theorems have no joint-satisfiability witness, and the headline compiler theorems are never applied anywhere | statement sample (§2); `compiler_correct`/`_net`/`_checked`/`Evm.compile_correct` have zero uses in Examples/Controls; the `Evm.Memory.compile_correct` witnesses use only `AllocationInput.inl` (cost 0) (`Evm/MemoryCompileExamples.lean:141,218`) | Catches vacuous statements like F1 before they ship | 1–2 h per witness | Low |

## 4. Findings

### F1. The headline compiler theorems allow an always-reverting compiler on paying programs

`compiler_correct` (`Solidity/Theorems.lean:269`) is a four-way disjunction.
Its third disjunct is:

```
(Prog.pays P = true ∧ (⟦P⟧b, mc) ↯ₘ ∧ ∃ o, (P, σ) ⇓ o)
```

Its fourth disjunct allows `Prog.pays P = true ∧ (⟦P⟧b, mc) ↯ₘ` when the
run diverges. So for any `P` with `Prog.pays P = true` (a `transfer`
anywhere, including inside a called body; `Evm/Compile.lean:253-268`), code
that always reverts satisfies the theorem:
- if the source ends, the third disjunct holds;
- if it reverts, the second does;
- if it diverges, the fourth does.

The only escape is a source `panic`, which needs `Prog.asserts P = true`.
The same disjunct appears in three more places:
- `Evm.compile_correct` (`Evm/Correct.lean:1089`);
- `Compilation.Agrees` (`Evm/Compiler.lean:550`);
- hence `compiler_checked` (`Theorems.lean:297`).

The exact version, `compile_exact` (`Correct.lean:1115`, hypothesis
`hpay : Prog.pays P = false`), is not on the main page.

`docs/compiler-verification.md` ("What is proved") states:

> No proof reaches that third case … `StmtOut.refused` is only propagated
> from an inner `refused`, never originated. The third case … [is] a stale
> weakening of the statement (G04 R32, owned by G43).

A grep agrees: all 46 `refused` occurrences in `Solidity/Evm/*.lean` are
docs or `exact .refused hp ⟨…⟩` re-wrappings of an inner result
(`Correct.lean:79,95,111,168,504,583,922-937`).

**First step.** Delete `StmtOut.refused` and let the build list every match
that needs an arm. If the docs are right, each such match is dead code;
replace it with `nomatch`. Then restate `compiler_correct` with three
disjuncts.

### F2. Nothing proves Solidity source corresponds to the intrinsic model

Every calculus and compiler theorem quantifies over intrinsic `Stmt`/`Prog`.
User-visible constructs are produced by unverified elaborator code:
- **`break`/`continue`.** `Stmt` has no `break` constructor (constructors at
  `Syntax/Scoped.lean:405-470`). `break`/`continue` are rewritten into flags
  by `lowerLoops` (`Syntax/Elab/Lower.lean:543`, an `ElabM` function).
  `for` is rewritten to `while` by the same code. No theorem mentions
  `lowerLoops`: grep finds it only in comments and the definition.
- **`unchecked`.** `unchecked` is a syntactic rewrite (`uncheckStmts`,
  `Lower.lean:707-736`).

The independent source semantics (`Solidity/Source/`, which has `break`,
`for` and `execS`) has type-preservation theorems
(`Source/Preservation/Fragment.lean:57` `progress_and_preservation`). Its
agreement with the model, though, is a named obligation. The obligation
file says so itself (`Source/Agreement/NormalStatement.lean:6-9`):

> This proposition names the real source and model computations. It is not
> inhabited here for any general source/model program pair.

The 212 theorems in `Source/Agreement/` (44 files) cover specific shapes
(bool slots, defaults, primitive slots).

Consequence: the manifest rates `breakStatement` `present` and `forStatement`
`partial`, yet their evidence is printed-output `#guard_msgs`
(`Examples/Tactics/Loops.lean:60-106`).

**First step.** State `NormalStmtObligation`
(`Source/Agreement/NormalStep.lean:14`) for the output of `lowerLoops` on `while (c) { …; break; … }`.
Prove it for the bodies already in the agreement fragment. That gives the
first verified lowering pass and a template for `for`/`continue`/`return`.

### F3. The public end-to-end theorem has only toy instances

`PublicCorrectness` (`Roadmap/Contracts.lean:937`) is the obligation-5
statement. Its controls are good: they refute the always-revert, erasing,
sloppy and hash-revert compilers (`Roadmap/Controls.lean`,
`not_publicCorrectness_*`).

It is inhabited only for toys:
- `toy_publicCorrectness` (`Roadmap/Controls.lean`);
- `public_instance` over `Stages toySource toyIntrinsic toyEvmLang toyEvm`
  (`Yul/Composition/CorrectnessPublicControls.lean:21,33`).

The generic producer `Stages.publicCorrectness`
(`Yul/Composition/CorrectnessPublic.lean:68`) takes a `PublicBoundary` whose
docstring (`:20-23`) says "9 of the 13 `PublicCorrectness` fields pass
through unchanged". The toy fills those nine from `toy_publicCorrectness`
itself (e.g. `hashes_source := by simpa only [compiler_eq] using
toy_publicCorrectness.hashes_source`).

The residue investigator's grep of `PublicCorrectness` and `PublicBoundary`
found no other instance.

**First step.** For each of the 9 pass-through fields:
1. Name the existing real-pipeline lemma that would discharge it, or
   record that none exists.
2. Commit that table as a Controls file that `#check`s each candidate.

That turns "obligation 5 is open" into a list of missing lemmas.

### F4. The core compiler's machine builds keccak injectivity in by construction

The machine's storage words are terms: `Word.slot` (`Evm/Machine.lean:165`).
The compiled code uses:
- `keccakMap`/`keccakArr` instructions (`:194-195`);
- structured loops, `Instr.loop` (`:223`);
- relative jumps;
- locals in addressed memory cells.

`docs/compiler-verification.md` ("The machine") says the slot terms make
"keccak never collides … This is global injectivity, which the user
decisions forbid in the final theorem". The approved premise is a per-run
collision bound (G04 R34).

The calculus, by contrast, reads hashes as opaque atoms with no collision
resistance (`Calculus/Assumptions.lean:95`). So the two halves of the
project rest on different hash premises.

**First step.** Restate `save_repr`'s disjointness argument
(`Occ`/`Desc.unique`, compiler-verification.md "The layout") over concrete
words, under `Hash/CollisionBound.lean`'s `CollisionFree` for the run's
preimages. It is the only place injectivity is used, per the docs.

### F5. The compiled fragment covers 19 of 36 statement forms

`inFrag` (`Evm/Compile.lean:274-320`) returns `none` unconditionally for
these 17 of `Stmt`'s 36 constructors:

`assignLocalPush`, `send`, `declMem`, `rebindMem`, `assignFromMem`,
`assignMem`, `deleteMem`, `assignNew`, `tryCall`, `revertData`, `catchData`,
`pushOpAssign`, `pushIncDec`, `callReceiver`, `callReceiverPush`, `callRec`,
`assumeFalse`.

It also refuses:
- the expressions `readMem`, `mlen`, `modular` (addmod/mulmod) and `hash`
  (keccak256), via `valIn` (`:127`);
- mappings keyed by `bool`/`int` (`locIn`, `:116`);
- loops whose body pushes, pays or shrinks (`:307-313`).

The memory path (`Evm.Memory.compile_correct`, `Evm/MemoryCompile.lean:1257`)
covers part of the memory constructors separately. Corpus frequency of what
stays out: `try …` 75 lines in 20 files, `keccak256(` 14 lines in 7 files,
`.send(` 8 lines in 5 files.

**First step.** `send`: the run and the `CALL` already agree on refusal
(`transfer_sim`, per compiler-verification.md). `send` differs from
`transfer` only in pushing the flag. Copy `transfer_sim` and its arm.

### F6. Panic and revert payloads are collapsed

- `THalt` (`Semantics/Run.lean:58-66`) has `revert`, `panic`, `diverge`,
  `exhausted` and `revertWith d`. `panic` carries no code.
- A failed checked operation is `TRes.ofOpt none = .error .revert`
  (`Run.lean:90-92`).
- Division and modulo by zero give `none` (`Semantics/Ops.lean:57-58`).
- Pop of an empty array gives `none`, hence a plain revert.

So `Panic(0x11)`, `(0x12)` and `(0x31)` are all `.revert`, and
`require(c, "m")`/`revert("m")` revert with `[]` outside a self-call callee.
`docs/solc-alignment.md` records that `⟨ revert("m"); ⟩ false ↯ []` is
provable and false of solc. The manifest requirements for `checkedArithmetic`,
`assertBuiltin`, `arrayPop` and `requireBuiltin` all name these codes.

This is observable from user code through `try`/`catch` and `revertData`.
Because `compile_correct` matches `.revert` with `.revert`, the compiler
proof cannot detect a wrong payload either.

**First step.** Make the halt carry its data: replace `revert` with
`revertWith` of the encoded `Panic(n)`/`Error(m)`. Find the affected
soundness arms with `grep -l 'THalt.revert\|.error .revert'
Solidity/Calculus/Sound*`. Start with `TRes.ofOpt`'s callers in `Ops.lean`.

### F7. Unapproved call premises are still in the theorems

G00 Q2 (`docs/solidity-scope.md:90`) did not approve `worldAssumptions` or
the payment-acceptance boolean, and required the no-callback reading to
become a *proved special case*. Today:
- **Default is the unproved case.** `Assumptions.callback : Bool := false`
  (`Calculus/Assumptions.lean:112`) is the default reading.
- **Only a partial bridge.** `noCallback_iff` (`Theorems.lean:239`) relates
  the two readings only under `φ.callsBack false = false`.
- **Oracle still quantified.** `compile_correct` quantifies over a fixed,
  history-free `accepts` oracle (compiler-verification.md, "The machine").

Corpus frequency of the affected syntax in 396 `.sol` files:

| Pattern | Lines | Files |
|---|---|---|
| `.transfer(` | 41 | 26 |
| `.call{value` | 42 | 17 |
| `.send(` | 8 | 5 |
| `msg.value` | 129 | 35 |
| `.balance` | 201 | 14 |

msg.value and the balance are approved quantified inputs, so they are not
blockers.

**First step.** Prove that the callback reading implies the no-callback one
(`⊨[I] φ → ⊨ₙ[I] φ`) for formulas whose `transfer`s target non-contract
accounts. That is the "proved special case" G00 Q2 asks for, and
`validC_false_iff` is the template.

### F8. The decision procedure's residue is unmeasured

`DecisionTheorem` (`Calculus/Decision.lean:2018`, "The open theorem") is an
unproved `Prop`; `Examples/Decision.lean:252` lists counterexamples.
`DecisionTheorem'` (`DecisionResidue.lean:293`) assumes `¬ φ.Residue`, and
`residue_iff_unknown` (`:273`) makes that premise equivalent to
`decideGoal φ ≠ .unknown`. Its totality part is definitional, and the
docstring says so. Its real content is `decideGoal_sound`/`_refutes`.

What is missing is a measure. `docs/automation.md` says the shrink policy is
"not enforced by the code", and no fixture counts residue leaves.

**First step.** Add a `#guard`-pinned count of `Fml.residue` over the leaves
the existing TestSuite/Decision fixtures produce. It is kernel-evaluable
(`instance : Decidable φ.Residue`, `:144`). A route change that grows the
residue then fails the build.

### F9. Feature manifest claims vs evidence

Classes: **(a)** kernel-proved against the repo's own semantics; **(b)**
proved modulo named premises; **(c)** tested only (`#guard`, fixtures,
`decide` on constants); **(d)** true by definition or table, no theorem.

**The 13 `present` rows**

| Row | Backing | Class |
|---|---|---|
| booleanLiterals | `Frontend/SolcJson/Body.lean:1618-1623`; `PrimTy.Denote .bool = Bool` | d |
| etherUnits | `Syntax/Grammar.lean:416` `unitFactor?`; `Source/TypingExamples.lean:60` | c |
| timeUnits | `Grammar.lean:416` | d |
| boolType | `AST.lean:155-166` | d (but `bool` mapping keys become `uint` via `e ? 1 : 0`, `Body.lean:1143-1145`) |
| parentheses | `Grammar.lean:650` | d |
| ifStatement | `iteStep_sound` (`Calculus/SoundControl.lean:333`) → `Stmt.sound`; `compile_correct` | a (own semantics) / b (fragment) |
| breakStatement | `lowerLoops` plus `#guard_msgs` (`Examples/Tactics/Loops.lean:60-106`) | c (see F2) |
| erc7201Builtin | `ERC7201.lean:32` `root_aligned`; constants by `decide +kernel` | c. No theorem that the runtime lowering (`Lower.lean:1673`) equals `ERC7201.root` |
| msgSender | `Semantics/State.lean:106` | d. The bound is `< 2^256`, not `< 2^160` |
| blockTimestamp | `State.lean:109` | d |
| typeName | `Body.lean:1101` (the solc AST name) | c. The `.sol` fixture only; no Lean fixture for `contractName()` |
| interfaceId | `Body.lean:1106-1115`; `Examples/Tactics/DeclarationMetadata.lean:23` | c. Selectors are read from solc's JSON, not computed |
| errorEventSelector | `Body.lean:1120-1126`; `DeclarationMetadata.lean:27,31` | c |

**The sampled `partial` rows**
- `whileStatement`: `Stmt.sound_loop` (`Calculus/SoundLoops.lean:555`), a.
- Push/pop: `pushStep_sound`/`popStep_sound` (`SoundStore.lean:504,566`), a.
- `require`/`assert`: `SoundControl.lean:380,410`, a.
- `tryStatement` and `externalTypedCalls`: b, under the `TTx.ext` oracle and
  the invariant `I`.
- `keccakBuiltin`: c. `keccakBytes` (`Semantics/Heap.lean:523`) is backed by
  three `#guard` vectors (`Keccak.lean:111-114`), and `Keccak.lean` has 0
  theorems.
- `emitStatement`: c. Arguments are evaluated and the log is dropped
  (`Syntax/Raw.lean:192-197`).

None of these relates to solc. Counting the 13 `present` rows: 1 kernel-proved
against the repo's own semantics, 6 tested only, 6 true by definition.

**Traceability.** 9 of the 13 `present` rows cite one file. These 14
`partial` rows cite no Lean outside Examples/tests:

`checkedArithmetic`, `uncheckedArithmetic`, `evaluationOrder`,
`defaultInitialization`, `referenceCopyRules`, `panicCodes`,
`revertPayloads`, `rollback`, `abiEntryValidation`, `constructorLifetime`,
`nonpayableEntry`, `staticCallRestriction`, `termination`, `worldAssumptions`.

`checkedArithmetic` cites only `docs/solc-alignment.md`. Yet `compile_correct`
emits and proves solc's checked guards (compiler-verification.md lists them),
so here the manifest under-claims.

**First step.** Add a `theorems: [name]` field per row. Add a script under
`scripts/` that checks each name with `lean_local_search`/`#check`, and
reports rows whose class is c or d while their `current` is `present`.

### F10. Joint-satisfiability witnesses are missing for headline theorems

H62/H69 (`docs/feature-work/h62-2-audit-roadmap.md:176`) requires a witness
inhabiting the hypotheses of each ordinary interface theorem. Of the 43
sampled theorems, 15 have none. Among them:
- `compiler_net`;
- `compiler_checked`;
- `solkey_soundness`, `solkey_step_taclet`, `solkey_eq_calculus`;
- `receiveRun_ok`;
- `cval_revert_of_cpart`;
- six `Evm.Memory` representation lemmas.

`compiler_correct` itself has only an indirect witness: `prog_sim` at
`Lowering/G19/AssignmentWhileResetControls.lean:46-48` meets the same
hypotheses, for a program that does not pay. None of `compiler_correct`,
`compiler_net`, `compiler_checked` or `Evm.compile_correct` is applied in
any Examples/Controls file. A witness on a *paying* program would have made
F1 visible.

Similarly, both `Evm.Memory.compile_correct` witnesses
(`MemoryCompileExamples.lean:141,218`) take `AllocationInput.inl` (cost 0),
so the allocating branch is never inhabited.

**First step.** Add a Controls file that applies `compiler_correct` from
`Sim.init` (`compile_storage`'s premises) to `owner.transfer(30)`
(`Evm/Examples.lean` `payOwner_run`). Then add one `AllocationInput.inr`
witness.

## 5. Things that look bad but are fine

- **28 `sorry` hits.** All are string literals produced by proof-search tools
  (`r"sorry"` in `Calculus/Derive.lean`, `Closers.lean`, `TreeData.lean`),
  docstrings, or expected-error text. The one real `sorry` is in
  `Bridge/vendor/CaseStudies`, outside the trust closure.
- **`axiom trust_smt : ∀ p, p`** (`Bridge/vendor/Loom/SMT.lean:215`). It is
  not in the import closure of the Bridge's only Loom import (27 modules
  walked).
- **44 theorems or examples concluding `True`.** All are negative controls of
  the form `fail_if_success have … ; trivial` (e.g.
  `Examples/Tactics/LexDiamond.lean:59`), or the closed-telescope witness
  `closed_input : True` (`tests/h62/item2/audit-calculus/JoinWalkWitnesses.lean:10`).
  The latter is legitimate for declarations with no hypotheses.
- **`Stmt.sound` with no premises** (`Calculus/StmtSound.lean:48`). This is
  genuine: the per-arm proofs carry it, and `rule_exists` inhabits
  `rule_sound`.
- **`DecisionTheorem'` assuming its conclusion's totality.** The docstring
  discloses it (`DecisionResidue.lean:280-292`), and the theorem's real
  content is the soundness of each answer. The gap is the missing measure
  (F8), not dishonesty.
- **`lex_sound`** (`Frontend/Checked/Lexer.lean:711`). This is translation
  validation: `lex` returns `ok` only after checking `Lexed` (`:688`), and
  `Lexed` is an independent specification (re-print, classification,
  maximal munch). It is sound by design, though it is not a proof that the
  scanner is complete.
- **`Prog.pays` counts `callRec` as paying** (`Evm/Compile.lean:260`). This
  does not widen F1, because `inFrag` refuses `callRec` (`:319`).
- **Three `Theorems.lean` headlines have no `#print axioms` pin**
  (`noCallback_soundness`, `noCallback_iff`, `cleanTail_holds`). The source
  scan shows no axioms or `sorry` in `Solidity/`, and they reuse pinned
  proofs (`ProvesC.valid`). Low risk, but cheap to pin.
- **48 % of the 73k declarations are closed and 31 % ground.** These are
  concrete facts, concentrated in Yul (13,822 closed) and Backend (6,821).
  That is the expected shape of controls and fixtures, not a quality defect.
  It does mean declaration counts overstate general proof coverage.

## 6. Open questions for the user

None of these blocks this audit. They are listed for prioritisation.

1. Should the manifest's `present` require a theorem (class a or b) rather
   than implementation evidence? The current definition
   (`docs/solidity-scope.md:65`) makes `present` compatible with class d.
2. Is removing the third disjunct of `compiler_correct` (F1) in scope for
   G43, or should another lane take it now, given the docs say no proof
   reaches it?

## 7. Skeptic pass

See the appended section below.
