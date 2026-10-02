# Validating the semantics and the rules against solc

Every theorem here is about `Stmt.run` and the rule table. This plan finds out
whether they say what solc-compiled code does: which checks to run, in what
order, and what each can show. Status: a plan. "What exists" lists what is
built; the lettered checks A to O are not built unless stated. Read "The chain
of trust" for what is unproved, "What solc's source shows" for the decisions it
forces, and "Order of work" for the sequence. `docs/solc-alignment.md` records
decisions taken and remaining deltas; `docs/compiler-verification.md` records
`compile_correct`.

Claims about solc were read in the 0.8.37 source (`solidity_0.8.37/` in the
local package cache; paths below are relative to it). The installed `solc` is
0.8.33 and SolidCore (below) pins 0.8.35, so any comparison pins one version.

## The chain of trust

```
Solidity source ──(1) sol{…} / contract!{…}──▶ Stmt C ──(2) Stmt.run──▶ State
      │                                           │
      └──(3) solc (legacy | via-IR) ──▶ EVM bytecode ──(4) EVM──▶ storage slots
```

Proved: the rules are sound for (2) (`Rule.sound`, `Proves.sound`,
`ProvesC.sound`); typed syntax cannot express what (2) cannot run (`not_stuck`,
`Stmt.run_wt`); the repository's compiler agrees with (2) (`compile_correct`).
Not proved, and not provable without a model of solc: that (1) reads a program
as solc does, and that (2) plus the layout equals (3) plus (4). **Every proof
reaches solc-compiled contracts only through that square.** A rule is wrong
about Solidity only through one of four links:

- **L1. `Stmt.run` is wrong** (`Semantics.lean`); the rule is sound against it.
- **L2. The elaborator misreads `sol{…}`** (`Syntax.lean`, `hoist`): evaluation
  order, what it captures, what it accepts.
- **L3. The rule is sound but too strong**: its premise asks for more than the
  program needs. `Stmt.complete` is coverage, not logical completeness. The
  `assert` rule was the known case; it now mirrors `require` and solc's revert
  (`Taclet.assertSimple`), so none is known.
- **L4. The trusted base leaks**: `sorry`, `native_decide`, `implemented_by`, or
  a side condition that proves too much.

"Correct" must name which solc: the two generators disagree, and solc's
`docs/bugs.json` lists 66 known miscompilations. A disagreement with an oracle
has four outcomes: the model is wrong; the pipelines disagree and the model
picked one; solc is wrong (a `bugs.json` row, or a new one); the program is
outside solc's language.

**What `compile_correct` checks.** It looks like a check of L1, but Lean checks
the proof against the definitions, not the definitions against the EVM. It pins
`Stmt.run` only as far as three trusted definitions are right: `Instr.step`
(the EVM), `compileStmt` (what solc emits), and `Sim` with the theorem's shape.
A machine written *from the interpreter* makes it hold by construction. That
was `transfer`'s case until `CALL` moved real balances (check C below): it
was `transferAt` re-spelled, a `net` field no EVM has beside the
interpreter's.

## What exists

- **A hand audit**, `docs/solc-alignment.md`.
- **The corpus**: 551 rows in `tests/solkey/expected.tsv` (224 proved, 67
  evaluated, 226 unsupported, 34 unported), checked by `scripts/check-corpus.sh`.
  73 come from solkey's `solc/*.sol`, hand ports of solc's `semanticTests` that
  solkey's `SolidityRuntimeExecutionTest` also runs on a Besu EVM. That is the
  only contact with solc: indirect, one state per function, asserts only.
- **`#difftest`** (`Tools/DiffTest.lean`): the interpreter against the
  repository's own compiler on random well-typed storages, from a start where
  `compile_correct`'s hypotheses hold. It tests those hypotheses and the
  generator, not solc. Its layout differs from solc's in two details: slots are
  terms (`Slot.root`/`hash`/`data`), and `bool` takes a whole slot where solc
  packs one byte (`libsolidity/ast/Types.h:720`).
- **Not built**: a trusted-base check, pinned solc facts (`Counterexamples/`
  refutes design decisions and cites no solc), a printer from `Stmt` to Solidity
  (`Calculus/RuleSyntax.lean` prints `sol{…}` notation only), any run of
  `solc --ir`/`--storage-layout`, any use of solc's test suites, `symex_complete`.

## What solc's source shows

**Operand order depends on the pipeline: one live disagreement.** Legacy
evaluates a binary operator's **right operand first**
(`libsolidity/codegen/ExpressionCompiler.cpp`, `visit(BinaryOperation)`); IR
the **left first** (`libsolidity/codegen/ir/IRGeneratorForStatements.cpp:868-869`).
`docs/ir-breaking-changes.rst:161-180`: `++a + a` at `a = 1` is `3` in legacy and
`4` via IR, neither guaranteed. The elaborator follows legacy (`captureExpr`), so
`x = i++ + i;` is proved about legacy and false under `--via-ir`. Options: (1) an
elaborator parameter `legacy | ir`, default legacy; (2) refuse an effect in an
operand whose order is observable, as `hoist` already does under `&&`/`||`, so a
proof holds for both; (3) keep legacy and record it. Only (2) holds however the
contract is compiled; take (1) if the corpus needs these programs.

**Where the pipelines agree, and the model with them** (elaboration table in
`solc-alignment.md`): assignment and `op=` do the right-hand side, then the target
(legacy `ExpressionCompiler.cpp:319,331`; IR `:436,455`); `x++` reads, modifies,
writes once (IR `:757-771`); base before index; call arguments left to right
(legacy `:710-712`); `&&`/`||` short-circuit (IR `:855-859`); constants are folded
(IR `:862-866`). Via IR, a modifier's parameters are re-initialised at each `_;`
(`docs/ir-breaking-changes.rst:106-157`; the fragment has one top-level `_;`, where
they agree) and `delete` of a storage struct zeroes padding too (`:77-104`; visible
only with packed types and a low-level read).

**Layout and panics.** `Evm/Repr.lean` is solc's layout
(`docs/internals/layout_in_storage.rst:21-28`) except for `bool` beside a packable
neighbour, so a slot-by-slot comparison is exact only for bool-free contracts;
D compares *decoded values* using `solc --storage-layout` instead. Panic codes
(`libsolutil/ErrorCodes.h:25-37`) collapse to `Halt.revert` in the model; a harness
records the code as an expected-cause tag, to catch a revert for the wrong reason.
`unchecked` selects `wrapping_*` over `checked_*` helpers
(`IRGeneratorForStatements.cpp:567-584`); `mod_…` checks a zero divisor in both.

**The IR is a composition of named helpers** from
`libsolidity/codegen/YulUtilFunctions.cpp` (`checked_add_<T>`, `array_pop_<T>`,
`copy_struct_to_storage_from_<F>_to_<T>` at `:3763`, `cleanup_storage_array_end_<T>`,
`panic_error_0x<nn>`), named by type identifiers (`Types.cpp:264-285`). `solc --ir`
lists every helper a contract instantiates: a coverage measure for E and the finite
lemma set for I.

**Open decisions in the model.**
- *Struct and array sources are not right-hand-side first* in solc (target
  resolved, then member-by-member copy); the interpreter is value-first
  (`solc-alignment.md`, "Known divergence").
- *`transfer` assumes the world pays.* `transferAt` books `net` and nothing
  else: no funds check, no refusing recipient. The machine has both (`bal`,
  `accepts`), and `compile_correct` states the difference as a third outcome,
  the machine reverting alone in code that pays, so the box carries over
  (`compile_box`) and the diamond does not: a payment has no rule under the
  diamond (`transferDiamond` closes it to `false`), since the EVM gives no
  termination the calculus could promise. Receivers are `uint`,
  not cut to 160 bits.
- *The callback reading belongs to `call{value:}`.* Under the 2300-gas stipend a
  callee cannot change storage, `net` or `selfBalance` (EIP-2200), so for `transfer`
  the right reading is no callback, the recipient free to revert.
  `Semantics/Callback.lean`'s havoc reads `a.call{value: v}("")`, which the syntax
  lacks.

## Deterministic checks

**A. The trusted base, in CI.** `#print axioms` on `Rule.sound`, `Proves.sound`,
`ProvesC.sound`, `symex_sound`, `compile_correct`; fail on anything beyond `propext`,
`Quot.sound`, `Classical.choice`, or on `sorry`, `native_decide`, `implemented_by` in
the closure (`Calculus/RuleShapes.lean:44` and `Typing/State.lean` use them; the
closure decides). A day; every other check assumes it (L4).

**B. solc facts, pinned.** One theorem per solc behaviour, closed by `decide` or
`#guard`, in `Solidity/Counterexamples/`, citing solc's file and line at the pinned
version: `a[i++] = i` writes `a[0] = 0`; `++a + a` at `a = 1` is `3` legacy and `4`
via IR; `pop` zeroes the slot it frees; `delete` keeps a mapping. Re-check the
citations when re-pinning.

**C. The machine and compiler against reality (L1 via `compile_correct`).**
- *Done:* `CALL` from the Yellow Paper: a world state (`bal : Nat → Nat`, the
  contract's address `self`) in place of `net`; a transfer to itself moves nothing;
  the callee's acceptance is a parameter (`accepts`) and the theorem quantifies over
  every one. The stipend is not modelled: a refusal stands for it.
- *Done:* `Sim` relates real quantities: `net(a) = bal₀ a - bal a` at every address
  but the contract's own, whose entry is pinned to `0` (`Sim.netSelf`), so a wrong
  `net` update fails the theorem, a payment to the contract itself that books
  something included; `compile_net` reads the ledger off a run.
- Every instruction against a real EVM (revm/evmone or Ethereum's
  `GeneralStateTests`): `#difftest` compares interpreter with machine, this compares
  machine with EVM.
- `compileStmt` against `solc --ir` statement by statement (compiled `transfer` as
  `send`, with an interpreter that did not revert, and the theorem would still hold).
  Name `Evm/Compile.lean`'s pieces after the helpers they mirror; where shapes cannot
  match are the documented deltas.

## Differential testing on an EVM

**D. The harness.** Lean generates a program `P`, prints it as a Solidity case
(`source`, `setUp`, `calls`), a Node harness compiles it with solc under legacy and
via-IR, with and without the optimizer, at pinned versions, runs it on an EVM, decodes
the storage by `--storage-layout`, and diffs with `Prog.run`. The Lean side, with no
dependency:
- a **printer** from `Stmt C` to Solidity (`Solidity.Tools.Emit`), its round trip
  `sol[C]{ print P } = P` checked by `#guard` per program (it prints elaborated
  programs, so a mismatch is the interpreter's fault);
- the **start state as a program**: `Build.rootsProg` (`Typing/Constructibility.lean`;
  `reachable_iff`: it builds every reachable storage) printed as `setUp()`, so no
  storage is encoded into slots and past-end slots come from push, pop and aliases;
- **`lake exe solcases`**, a `lean_exe` beside `solkeycheck` importing only `Syntax`,
  `Semantics` and `Tools/Show.lean`, so mutation runs (H) rebuild it without the
  proofs.

Per case and pipeline the harness reads the status and panic selector `0x4e487b71`
and every variable's storage (arrays to the larger of the old and new length,
mappings at the keys the case mentions). solkey's Besu `EvmContractRunner` is the
shortest path; evmone is what solc's tests use (`test/EVMHost.cpp`,
`test/Common.h:41-48`). Pin the EVM version: 0.8.37 defaults to Osaka
(`liblangutil/EVMVersion.h:174`). Verdicts: `agree`; `model` (differs from both
pipelines); `unspecified` (the pipelines differ; the case records which one the model
follows); `solc-bug` (matches a `bugs.json` row's `conditions` at the pinned
version); `rejected` (solc refuses the printed program: a printer or typing bug here).
They live in a TSV beside `expected.tsv` with a check script like `check-corpus.sh`,
so a changed verdict fails CI.

**E. Test inputs.** They compose:
- *Bounded enumeration*: one universe contract with every shape (`uint`/`int`/`bool`
  roots, dynamic and fixed arrays, a struct with a word, `bool`, mapping and array
  member, an array of it, a mapping to it, memory locals), every well-typed program up
  to a size bound, values from pools (`0`, `1`, `2`, `2^256-1`, `±2^255`, `-1`),
  reduced by symmetry, sized by `#eval`. The small-scope hypothesis; it would have
  found the operand-order issue mechanically.
- *Coverage targets*: every `Taclet`/`LeanTaclet` constructor under both modalities in
  at least *k* agreeing cases, a succeeding and a reverting one per guard (`Rule.eq_step`
  makes it a function of the program); every `.error .revert` site in `Semantics.lean`
  on both sides; the union of `solc --ir` helper names against the
  `YulUtilFunctions.cpp` families reachable from the fragment. Rule × helper exposes a
  rule tested through only one of several solc paths (storage-to-storage and
  memory-to-storage copies are one rule, two helper instantiations).
- *Path-directed inputs*: `sol_symex` leaves one goal per path; solving its path
  condition (`z3` on SMT-LIB, or `Tools/Counterexample.lean`'s witness search) gives one
  test per path, including the exact overflow boundary.
- *A source-level generator* for `hoist`/`captureExpr`, which the printer never tests:
  effects inside expressions (`a[i++] = i`, `m[k][k++] = …`, `xs[i++].push(i)`,
  `p.age += i++`), the same text to solc and `sol{…}`.

**F. solc's own suites and bugs.**
- `test/libsolidity/semanticTests/` (1697 files: a contract plus expected calls such
  as `// g() -> FAILURE, hex"4e487b71", 0x11`, run in solc's CI under legacy, IR and
  SSA-CFG). The expected values are the oracle, so no EVM: a translator from isoltest
  to `#run` plus `#guard`, what solkey did by hand for `solc/*.sol`. One agent per
  directory (`array` 228, `viaYul` 92, `various` 66, `operators` 63, `structs` 61,
  `storage` 44, …), recording why each file is out of the fragment, which measures its
  width.
- `test/libsolidity/syntaxTests/` (3535 files with expected errors): the oracle for the
  static side, what `sol{…}` must refuse (`Src.copy`'s `mapFree`, data locations,
  lvalues) and accept.
- `docs/bugs.json`: each fragment-relevant row (`DynamicArrayCleanup`,
  `StorageWriteRemovalBeforeConditionalTermination`,
  `FullInlinerNonExpressionSplitArgumentEvaluationOrder`, `SignedArrayStorageCopy`, …)
  is a regression case expecting the *fixed* behaviour; its `conditions` (`viaIR`,
  `optimizer`, `evmVersion`) name the configuration that must show the bug, which tests
  the harness too.

**G. Each rule against solc directly**, bypassing `Stmt.run`. For each
`Taclet`/`LeanTaclet` constructor (`#enum_ctors`, `Calculus/RuleShapes.lean`): a
canonical instance and start state; evaluate the rule's premise through the updates and
`Tm.denote` over `State.abs` (a different path from the interpreter); compile the
instance with solc and run it. Three independent computations, so a disagreement says
which is wrong. Runner: `solc --ir` with `test/tools/yulInterpreter/`, or evmone.

**H. Mutation testing.** A suite that always agrees may be too weak to disagree.
Mutate `Semantics.lean` one decision at a time (RHS after target, a `checkArith`
dropped, `pop` not clearing, `delete` resetting mappings, a push not reusing its slot,
an unbounded alias bind, `**` unchecked, `transfer` not debiting) and require the suite
to kill each. Mutate `Calculus/Rules.lean` too (drop a guard, swap a capture order): if
`Taclet.sound` still builds, the semantics does not constrain that detail (a freedom or
a hole in `Stmt.run`); if G misses it, G is too weak. A survivor is a decision no test
observes. Proofs do not build on a mutant, hence `solcases` must not import them.

## Translation validation through solc's Yul

**I.** For a program that matters (a benchmark, a published specification), *prove*
that solc's output agrees with `Stmt.run`, checking each output instead of trusting the
compiler (CompCert's approach to an untrusted pass).
1. A **Yul semantics in Lean** for what `--ir` emits. EVMYulLean (below) is one but
   pulls Mathlib, so the bridge lives in a sibling repository requiring both, as the
   `SolKey` reader does.
2. **One lemma per helper instantiation**, from the `--ir` helper list over E's
   universe contract. Done twice: `checked_add_t_int256` and siblings
   (`Evm/Signed.lean`), `checked_exp_unsigned` (`Evm/Exp.lean`). The rest is the same
   work per family.
3. **A structural match per program**: `fun_f_<id>` is `f`'s statements in order, each a
   composition of helper calls on fresh `expr_<n>` variables. A validator parses
   `solc --ir` (or `--ir-ast-json`), matches the body to the `Stmt`, discharges each call
   with its lemma, and emits a Lean proof that the Yul simulates `Prog.run P` under the
   layout.
4. **Trusted**: the Yul optimizer and Yul-to-EVM assembly. `--ir-optimized` is still Yul,
   but the match weakens into an equivalence proof. Legacy has no IR: D covers it alone.

By-product: `--ast-compact-json` as a second front end checks the elaborator's name
resolution against solc's (it would have caught the `sol!` name-typing gap in
`solc-alignment.md`).

## Checks an LLM does by reading the code

**The LLM proposes, the harness decides**: an agent hands in something checkable (a
witness program with solc's expected result, a table row a script checks), never a
verdict alone.

**J. A rule-to-solc map**, `docs/rule-solc-map.md` beside `docs/lean-key-rule-map.md`:
per constructor, the legacy function and line, the IR function and line with its
`YulUtilFunctions.cpp` helper, the `Stmt.run` clause, and witnesses (B facts, G cases).
One agent per rule family; `scripts/check-rule-solc-map.mjs`
checks that every constructor has a row and every cited witness
exists.

**K. Blind prediction, one checklist.** One agent sees only solc's source and the
snippet, never the Lean, and predicts the outcome; a second compares with the Lean.
That avoids anchoring; each disagreement becomes a B fact or a G case. All agents use
one checklist: evaluation order per pipeline; which checks fire (overflow, bounds, zero
divisor, empty `pop`); cleanup (`pop`, `delete`, past-the-end slots); reference or
copy, dangling references; memory or storage source; effects before a revert;
`bugs.json` rows at the pinned version.

**L. Adversaries.** Each mutant of H that nothing kills goes to an agent whose only job
is a program that tells it from the original. For each solc helper behind a statement
the model has an opinion on, an agent reads helper and Lean side by side and writes the
cases where they could differ (`copyStructToStorageFunction` against
`State.writeStorage`/`SVal.overlay`; `array_pop_<T>` against `storagePopSave`;
`cleanup_storage_array_end_<T>` against the past-end `shadow`). Dangling references and
past-end slots are the richest target, including the delta no test reads (`arr.push(v)`
of a struct over a recycled slot).

## Completeness and automation

Proved: every statement has exactly one rule (`Stmt.complete`, `Rule.eq_step`,
`Rule.premise_unique`); symbolic execution always steps and terminates
(`Fml.active_iff_step`, `symex_terminates`). Not proved: `⊨ φ ↔ ⊨ symex n φ`
(`symex_sound` is one direction). How much of Solidity the fragment covers is a
measurement (F, `docs/corpus-parity.md`), not a theorem.

**M. Symbolic execution is exact; premises as equivalences.** The rules are
equivalences in substance (`Modality.after_sameOk` is an `↔`; `UpdRule.sound` and
`Fml.simpUpds_holds` hold both ways). Missing: `Premise.Correct` as an equivalence and
`symex_complete : holds σ φ → holds σ (symex n φ)`. Then a loop-free formula is valid
exactly when its modality-free form is: relative completeness, so the calculus is never
why a proof fails, and L3 becomes a theorem. `SameOk` identifies `revert` with `stuck`,
so the converse needs "not stuck" (`not_stuck`, `Stmt.run_wt`). The callback calculus is
incomplete by design (havoc); loops (`docs/loops.md`) make completeness relative to
invariants.

**N. Reflective decision procedures.** A tactic cannot be proved complete; a function
`dec : LFml → Bool` with `dec ψ = true ↔ ∀ σ, ψ.holds σ` can, and `sol_decide`'s
reductions are already equivalences (`Fml.valid_iff_reduce`, `Fml.valid_iff_cons`; the
last step is `omega | grind`). Replace that step by fragment: key equalities and
reads-of-writes (congruence closure over symbolic keys; small; first), linear arithmetic
over bounded integers, then nonlinear, `**` and bitwise on 256-bit words (finite, so
decidable: `bv_decide` gives kernel-checked LRAT certificates, so stating the arithmetic
on `BitVec 256` makes automation complete up to SAT time). Quantifiers leave
decidability; test them (O).

**O. Testing the heuristic automation** (`sol_close`, `sol_spec`, `grind` glue).
- *Known-valid goals from runs*: state a generated program's exact final state as the
  postcondition; `#verify` must answer ✓, a perturbed conjunct ✗ with a certified
  witness. A "stuck" on a valid goal is a gap; count gaps in a TSV and fail CI when the
  count rises.
- *Two-sided agreement*: each generated goal is proved or refuted by `Fml.eval3`
  (`Tools/Counterexample.lean`); on a `sol_decide` failure, `z3` or `bv_decide` on the
  reduced formula tells an invalid goal from `omega` giving up.
- *Metamorphic tests*: a proof survives renaming locals, reordering independent
  statements, `x += a` as `x = x + a`, `unchecked` around a non-overflowing statement,
  and introducing an alias.
- *A budget*: heartbeats per goal, so a slowdown shows before a failure.

## Related Lean projects

All pull Mathlib (directly or through EVMYulLean), so none can be a `[[require]]` here:
use them as data, as external programs, or from a sibling repository.

- **SolidCore** (`paradigmxyz/solidity-lean`, read at `f22b110`, 2026-09-30): an
  executable semantics of Solidity 0.8.35 (legacy) whose observable results match solc
  bytecode on a real EVM through Foundry; about 1,188 `.sol` cases and a harness
  (`tests/forge-harness`), which is D working. Its `DIVERGENCE-LOG.md` (135 EVM-verified
  rows) is the fastest source of B facts: #187 (legacy evaluates the right operand
  first, `ExpressionCompiler.cpp:614-615`), #189/#190 (tuple components and siblings
  left to right), #177 (a storage reference to an element is bounds-checked once, so
  after `pop()` it reads the zeroed slot), #204 (`push()` only bumps the length, so a
  write through a dangling reference survives the re-grow: the recorded
  push-over-a-recycled-slot delta). D's printer should emit their case format; a sibling
  repository can run `Stmt.run` and their interpreter on the same programs with no EVM in
  the loop, and later prove a simulation, so `Taclet.sound` reaches a semantics tested
  against the EVM. Methods to copy: a pinning test per fix (99 witness modules), a classed
  divergence log, fault-injected detectors.
- **EVMYulLean** (`NethermindEth/EVMYulLean`): EVM and Yul at Cancun, 22,330 of 22,332
  conformance tests; I's Yul semantics and C's reference. Use Paradigm's fork
  (`danrobinson/EVMYulLean`), which carries corrections.
- **Clear** (`NethermindEth/Clear`): optimised Yul into Lean with verification-condition
  templates; its parser could be I's matcher. From 2024, tied to optimiser flags.
- **Solidus** (<https://www.paradigm.xyz/writing/solidus>): a verified compiler from
  SolidCore to EVM, so proofs tied to SolidCore reach Solidus output (not solc's). Its
  cost (about 1,700 agent-hours, $150k, humans on design and specification) is the
  reference for I.

## Order of work

Each step is useful alone and fans out to parallel agents.

1. **A**; **B** seeded with the open decisions; decide the operand order and fix
   `solc-alignment.md`; **C**'s `CALL` (done: real balances, `compile_correct`'s
   third outcome).
2. Triage SolidCore's divergence log against the fragment, one agent: each relevant row a
   B fact or a `Counterexamples/` entry.
3. **J** and **K**, one agent per rule family.
4. **D** emitting SolidCore's case format over E's universe contract, through their
   Foundry harness or solkey's Besu runner.
5. **F**, one agent per directory, then **G**.
6. Coverage reports (rule, halt cause, helper), **H**, **L**. After this "the semantics
   agrees with solc" and "the rules match Solidity" are measured claims: which programs,
   states and pipelines, and which mutants are killed.
7. **M**, then **N** (key equalities, then `bv_decide`), and **O** as automation grows.
8. **I** in a sibling repository: Yul semantics, helper lemmas per family, the per-program
   matcher for the benchmark contracts; and the Lean-to-Lean run with SolidCore. After
   this the claim is proved for the contracts that matter.
