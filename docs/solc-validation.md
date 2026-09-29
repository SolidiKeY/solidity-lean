# Validating the semantics against solc

How to find out whether `Stmt.run` does what solc-compiled code does, how to
generate the tests that say so, what reading solc's source buys over testing,
and which of the other properties (completeness, the automation always
closing) can be proved and which have to be tested. It is a plan: nothing in
it is built yet except what "Where we are" lists. `docs/solc-alignment.md`
records the decisions already taken; this document is how to check them and
find the ones not yet taken.

Everything about solc below was read in the 0.8.37 source tree (the tarball
in the local package cache, `solidity_0.8.37/`); paths into it are relative
to that root. The installed `solc` is 0.8.33.

## The chain of trust, and the one link that is not proved

```
Solidity source ──(1) sol{…} / contract!{…}──▶ Stmt C ──(2) Stmt.run──▶ State
      │                                           │
      └──(3) solc (legacy | via-IR) ──▶ EVM bytecode ──(4) EVM──▶ storage slots
```

Proved in the kernel: the calculus is sound for (2) (`Proves.sound`,
`ProvesC.sound`), the typed syntax cannot express what (2) cannot run
(`not_stuck`, `Stmt.run_wt`), and the repository's own compiler agrees with
(2) (`compile_correct`). Not proved, and not provable without a model of
solc: that (1) reads a program as solc reads it, and that (2) followed by the
layout equals (3) followed by (4). **Every proof in this repository is about
solc-compiled contracts only through that unproved square.** The rest of this
document is about closing it: by testing (sampling programs), and by
translation validation (proving it program by program).

"Correct with respect to solc" also has to name *which* solc. solc has two
code generators, they disagree (next section), the docs call the legacy
evaluation order unspecified, and `docs/bugs.json` lists 66 known
miscompilations with the versions and settings that trigger them. An oracle
disagreement therefore has four outcomes, not two: the model is wrong; the
two pipelines disagree (the behaviour is unspecified, and the model has
picked one); solc is wrong (a `bugs.json` row, or a new one); the program is
outside solc's language (solc rejects what the elaborator accepted).

## Where we are

- **A hand audit.** `docs/solc-alignment.md`: each place the interpreter
  follows solc over KeY, argued from solc's documentation and witnesses.
- **The corpus.** 551 obligations from solkey's `.sol` suites
  (`tests/solkey/expected.tsv`: 224 proved, 67 evaluated, 226 unsupported,
  34 unported), 73 of them from solkey's `solc/*.sol`, which are hand ports
  of solc's `semanticTests` with loops unrolled. solkey's
  `SolidityRuntimeExecutionTest` compiles those files with solc and runs them
  on an in-process Besu EVM, requiring no failing `assert`. So an assert the
  Lean corpus proves also held on a real EVM, at one state, for a
  hand-written program. That is the only contact with solc today, and it is
  indirect (through solkey's harness) and weak (one state per function,
  asserts only, no storage compared).
- **`#difftest`** (`Tools/DiffTest.lean`) compares the interpreter with the
  repository's *own* compiler (`Evm/Compile.lean`), which `compile_correct`
  already proves equal to it. It tests the theorem's hypotheses and the
  generator, not solc. Its layout is solc's in shape (consecutive slots,
  `keccak256(p)` array data, `keccak256(k ‖ p)` mapping entries) but not in
  two details. Slots are terms (`Slot.root`/`hash`/`data`), not keccak
  numbers. `bool` takes a whole slot, while solc packs it into one byte
  beside its neighbours (`BoolType::storageBytes() == 1`,
  `libsolidity/ast/Types.h:720`).
- **Nothing reads solc's own test suites**, runs `solc --ir` or
  `--storage-layout`, or prints a `Stmt` back as Solidity text. The
  delaborators in `Calculus/RuleSyntax.lean` print the `sol{…}` notation
  inside Lean, not a file solc can compile.

## What reading solc's source already shows

Read against the code generators, not the documentation, the model has one
live disagreement and several places where it is right for a reason no test
pins yet.

### The operand order of a binary operator depends on the pipeline

The legacy generator evaluates the **right operand first**
(`libsolidity/codegen/ExpressionCompiler.cpp`, `visit(BinaryOperation)`:
`acceptAndConvert(rightExpression…)` then `acceptAndConvert(leftExpression…)`;
it swaps only for a commutative operator with a literal on the right, which
cannot be observed). The IR generator evaluates the **left operand first**
(`libsolidity/codegen/ir/IRGeneratorForStatements.cpp:868-869`).
`docs/ir-breaking-changes.rst:161-180` gives the witness: `++a + a` at
`a = 1` is `3` in legacy and `4` via IR, and neither is guaranteed.

The elaborator follows legacy (`Syntax.lean`, `hoist`, the `.binop` case:
"solc evaluates the right operand first: `i++ + i` is `1 + 1`"). So
`x = i++ + i;` is proved about the legacy pipeline and is false for
`--via-ir`. There are three honest fixes:

1. make the order a parameter of the elaborator (`Pipeline := legacy | ir`,
   default legacy, which is solc's default) and state which one a proof
   assumes;
2. refuse an effect in an operand whose order is observable, as `hoist`
   already refuses one under `&&`/`||` or in a conditional's branch. Then a
   proof holds for both pipelines;
3. keep legacy and record it in `docs/solc-alignment.md`.

Option 2 matches what the elaborator already does elsewhere and is the only
one under which a proof holds whichever way the contract is compiled; 1 is
the one to take if the corpus needs these programs. Either way, the
`solc-alignment.md` table ("solc reads the right operand first") should say
"legacy".

### The orders that do agree, with the lines that make them agree

| Construct | Legacy (`ExpressionCompiler.cpp`) | IR (`IRGeneratorForStatements.cpp`) | Model |
|---|---|---|---|
| `lhs = rhs` | RHS (`:319`), then LHS (`:331`) | RHS (`:436`), then LHS (`:455`) | `execAssignNested`: RHS first |
| `lhs op= rhs` | RHS, then the lvalue read | RHS, then `readFromLValue` (`:466`), write (`:475`) | single resolution, RHS first |
| `x++` / `++x` | read, modify, write once | `:757-771`: read, `increment_…`, write | `.mkIncDec`: resolved once |
| `base[index]` | base (`~:2222`), then index (`~:2235`) | default traversal: base, then index (`AST_accept.h:958-967`) | the base captured before the index |
| call arguments | left to right, then the callee (`:710-712`) | left to right | `Arg.bindSeq` |
| `&&`, `\|\|` | short-circuit | short-circuit (`:855-859`) | short-circuit; no effect allowed on the right |

A constant subexpression is folded and never evaluated (IR `:862-866`), which
the model reproduces by having no effects in literals.

### Other pipeline differences, and whether the fragment can see them

From `docs/ir-breaking-changes.rst`:

- **Modifiers are functions via IR**: parameters and return variables are
  re-initialised at each `_;` (`:106-157`). The fragment allows `_;` once, at
  the top level of a modifier (`Syntax.lean`), and there the two agree.
  Admitting a second `_;`, or a `_;` inside a branch, would need a decision.
- **`delete` of a storage struct zeroes whole slots, padding included, via
  IR** (`:77-104`). This is invisible at the value level while every
  primitive is 256 bits wide. It becomes visible with packed `uintN`/`bool`
  and a low-level read, which the fragment does not have.
- **State-variable initialisation order under inheritance** (`:35-75`). There
  is no inheritance in the fragment.
- **`mulmod`/`addmod` arguments right to left in legacy** (`:184-227`). They
  are not in the fragment.

### The storage layout

`docs/internals/layout_in_storage.rst:21-28` gives the packing rules. The
model's layout (`Evm/Repr.lean`) is solc's for a contract with no `bool` next
to a packable neighbour, and differs otherwise. That matters to any
comparison made slot by slot, and it is why the harness below compares
*decoded values* rather than slots (`solc --storage-layout` gives the slot
and byte offset of every variable and member). Checking the model's own
layout against solc's slot by slot is a separate, smaller test. It is exact
for bool-free contracts, and teaching `ReprAt` to pack would close the gap.

### Panics are classified, the model collapses them

solc's codes are in `libsolutil/ErrorCodes.h:25-37`. The model maps them to
one `Halt.revert` (`docs/solc-alignment.md`, "Remaining deltas"). A harness
should still record the code, since it costs nothing and catches a revert for
the wrong reason (an overflow where the model thinks it reverts on bounds).
Carry an expected-cause tag alongside `Halt.revert` in the emitted case, not
in the semantics.

### `unchecked` and the helper families

`unchecked { … }` switches the IR generator's arithmetic mode
(`IRGeneratorForStatements.cpp:567-584`), which picks `wrapping_*` over
`checked_*` helpers for `+ - * **`, `++`/`--` and negation. `mod_…` checks
for a zero divisor in both modes, as the model's zero-divisor guard does. The
IR generator is a syntax-directed composition of named helpers from
`libsolidity/codegen/YulUtilFunctions.cpp`: `checked_add_<T>`,
`array_push_zero_<T>`, `array_pop_<T>`, `storage_set_to_zero_<T>`,
`copy_struct_to_storage_from_<F>_to_<T>` (`:3763`),
`copy_array_to_storage_from_<F>_to_<T>` (`:1967`),
`clear_storage_range_<T>`, `cleanup_storage_array_end_<T>`,
`mapping_index_access_<M>_of_<K>`, `panic_error_0x<nn>`, and so on. Each name
is a deterministic function of the type identifiers (`Types.cpp:264-285`;
struct ids embed the AST node id). `solc --ir` on a contract prints every
helper it instantiates. That list is what makes the two methods below
possible: a coverage measure for tests, and a finite set of lemmas for
translation validation.

## Method 1: differential testing against solc on an EVM

```
Lean: generate P : Prog C ──▶ case.json { source, setUp, calls, expected }
                                   │
          solc × {legacy, legacy -O, via-ir, via-ir -O} × {pinned versions}
                                   │   bytecode + storage layout
                                   ▼
                  EVM (Besu via solkey's runner; later evmone / revm)
                                   │   status, panic code, return data, raw slots
                                   ▼
               decode by --storage-layout ──▶ values ──▶ compare with Prog.run
```

**The Lean side** needs three pieces, all small, none a dependency:

- **A printer** from `Contract`/`Stmt C` to Solidity text. It should live in
  a new tools module (say `Solidity.Tools.Emit`), with the round trip
  `sol[C]{ print P } = P` checked by `#guard` on every generated program. It
  prints the *elaborated* program, whose effects are already captured into
  statements, so a mismatch there is the interpreter's fault. The elaborator
  gets its own generator (below).
- **The start state, as a program.** Do not encode storage into slots.
  `Build.rootsProg` (`Typing/Constructibility.lean`) is one checked program
  that builds any canonical, tight storage, and `reachable_iff` says that
  covers every storage a program can reach. So print it as a `setUp()`
  function and let both sides run it. That keeps layout bugs out of the start
  state, and it tests the builder too. Past-end slots (the `shadow` of
  `SVal.array`) are reached the same way the builder reaches them, by push,
  pop and aliases. Sequences of several calls come for free.
- **An exe that emits cases**, `lake exe solcases`, next to `solkeycheck`:
  a `lean_exe` target, not a `[[require]]`. Its imports should stop at
  `Syntax`, `Semantics` and `Tools/Show.lean`, so the mutation runs below
  can rebuild it without the proofs.

**The harness** lives outside the package, as `scripts/` does (Node), or in a
sibling repository like the `SolKey` reader. For each case it:

- compiles once per pipeline;
- deploys, runs `setUp()`, then the calls;
- reads the status and the panic selector `0x4e487b71` with its code;
- reads the storage of every variable in the layout: for arrays, up to the
  larger of the old and new length, so past-end slots are compared; for
  mappings, the keys the case mentions;
- decodes it into `SVal`'s shape, printed as `Tools/Show.lean` prints the
  model's final state;
- diffs.

solkey's `EvmContractRunner` (Besu) already compiles and deploys, so pointing
it at a directory of cases is the shortest path. evmone is what solc's own
`semanticTests` run on (`test/EVMHost.cpp`, pinned v0.22.0 in
`test/Common.h:41-48`), and it or revm is the fast path once volume matters.
Pin the EVM version: 0.8.37 defaults to Osaka (`liblangutil/EVMVersion.h:174`).

**Verdicts** are one per case and pipeline: `agree`; `model` (the model
differs from both pipelines); `unspecified` (the pipelines differ from each
other, and the case records which one the model follows); `solc-bug` (it
matches a `bugs.json` row's `conditions` for the pinned version);
`rejected` (solc does not compile the printed program: a printer or typing
bug on our side). Keep them in a TSV next to `tests/solkey/expected.tsv`,
with a check script like `check-corpus.sh`, so a verdict that changes fails
CI.

## Generating the tests

"All of them" is infinite. What can be exhaustive is a bounded space, a
coverage target, or a path set. The approaches compose; do them in this
order.

### Exhaustive, bounded enumeration

`Stmt C` is typed, so a type-directed enumerator produces only well-typed
programs, and every one is a claim that solc accepts it. Fix one "universe"
contract that has every shape the fragment has:

- `uint`, `int` and `bool` roots;
- a dynamic and a fixed-size `uint` array;
- a struct with a `uint`, a `bool`, a mapping and an array member;
- an array of that struct;
- a mapping to it;
- memory locals of the struct and array types.

Enumerate every program up to a size bound with values from pools: `0`, `1`,
`2`, `2^256-1`, `2^255`, `-2^255`, `-1`, and array lengths `0`, `1`, `2`.
Reduce by symmetry: canonical local names, and one operand order for
commutative operators without effects. Count the space with an `#eval`
before choosing the bound. Put many functions in one contract, since solc's
cost is per file and an EVM call is cheap.

This is the small-scope hypothesis: most semantic bugs show on small
programs and small states. It is the approach that would have found the
operand-order issue above mechanically.

### Coverage targets that are already well defined here

- **Rules.** `Rule.eq_step` (`Calculus/Uniqueness.lean`) says each statement
  fires exactly one rule, `Stmt.step`'s. Coverage by rule is a function of
  the program. Require every `Taclet`/`LeanTaclet` constructor, under both
  modalities, to appear in at least *k* agreeing cases. A reverting and a
  succeeding case are needed for every rule with a guard.
- **Halt causes.** Every place `Semantics.lean` returns `.error .revert` is
  one cause (overflow, bounds, empty `pop`, zero divisor, `assert`,
  `transfer` without funds). Each needs a case on both sides of it.
- **solc's helpers.** The union of helper names in `solc --ir` over the
  suite measures how much of solc's code generator the suite exercises. The
  target is every `YulUtilFunctions.cpp` family reachable from the fragment,
  at every instantiation shape: value, struct, array, nested, memory source,
  storage source. The cross product *rule × helper* shows a Lean rule tested
  against only one of the solc paths that implement it: storage-to-storage
  and memory-to-storage copies are one rule, `copy_struct_to_storage_from_…`
  instantiated twice. For finer coverage, build solc with `--coverage` and
  read `gcov` on `libsolidity/codegen/`.

### Path-directed inputs

For a program `P`, `sol_symex` leaves one goal per path. Its hypotheses are
the path condition: each guard of `checkArith`, each bounds check, each
branch. Solving each path condition gives one test per path, including the
exact overflow boundary. The solver can be `z3` (installed), exported from
the goal as SMT-LIB, or the witness search of `Tools/Counterexample.lean`,
whose pools and shrinker already exist. Enumeration picks the programs, and
this picks their inputs.

### Seeded from solc's own suites: oracles already written down

- **`test/libsolidity/semanticTests/`**: 1697 files, each a contract plus
  expected calls (`// f(uint256): 1 -> 2`,
  `// g() -> FAILURE, hex"4e487b71", 0x11`), run by solc's CI under legacy,
  IR and SSA-CFG (`test/libsolidity/SemanticTest.cpp:321-332`). The expected
  values are the oracle, so no EVM is needed. The relevant directories:

  | Directory | Files | Notes |
  |---|---|---|
  | `array` | 228 | `copying` 95, `pop` 16, `push` 14, `delete` 12 |
  | `viaYul` | 92 | |
  | `various` | 66 | |
  | `operators` | 63 | |
  | `structs` | 61 | |
  | `storage` | 44 | |
  | `cleanup` | 19 | |
  | `expressions` | 19 | |
  | `arithmetics` | 13 | |
  | `exponentiation` | 3 | |

  A translator from the isoltest format to `#run` plus `#guard` is exactly
  the work solkey did by hand for `solc/*.sol`. It suits agents: one per
  directory, unrolling loops as solkey did, and recording why each file is
  out of the fragment. That record measures the fragment's width against
  solc's own idea of what matters.
- **`test/libsolidity/syntaxTests/`**: 3535 files with the expected errors
  (`// TypeError 1234: (a-b): …`). These are the oracle for the static side:
  what `sol{…}` must refuse (`Src.copy`'s `mapFree`, data locations, lvalues)
  and what it must accept. The relevant directories are `dataLocations` (62),
  `array` (118), `structs` (53), `lvalues` (7), `unchecked` (7) and
  `operators` (86). It checks the claim "a statement no rule can run cannot
  be written" against solc's type checker.
- **`docs/bugs.json`**: each fragment-relevant row is a regression case whose
  expected result is the *fixed* behaviour. Relevant rows include
  `LostStorageArrayWriteOnSlotOverflow`, `DynamicArrayCleanup`,
  `StorageWriteRemovalBeforeConditionalTermination`,
  `FullInlinerNonExpressionSplitArgumentEvaluationOrder` and
  `SignedArrayStorageCopy`. Their `conditions` field (`viaIR`, `optimizer`,
  `evmVersion`) says which harness configuration must show the bug, which
  also tests the harness.

### The elaborator gets its own generator

The printer above prints elaborated programs, so it never tests `hoist` and
`captureExpr`. A second generator writes *source* Solidity with effects
inside expressions: `a[i++] = i`, `x = i++ + i`, `m[k][k++] = …`,
`xs[i++].push(i)`, `p.age += i++`. It feeds the same text to solc and to
`sol{…}`. This is where evaluation-order bugs live, and where the
operand-order issue would have shown.

### Measuring the suite: mutation testing

A suite that always agrees could be too weak to disagree. Mutate
`Semantics.lean` one decision at a time and require the differential suite to
fail on each mutant ("kill" it). The mutation classes:

- the RHS evaluated after the target;
- one `checkArith` dropped;
- `pop` no longer clearing;
- `delete` resetting mappings;
- a push that does not reuse its slot;
- an unbounded alias bind;
- `**` unchecked;
- `transfer` not debiting.

A surviving mutant is a semantic decision no test observes, which is where
the model can be wrong unnoticed. The proofs will not build on a mutant,
which is why the emitting exe must not import them. One agent per mutation
class runs this in parallel.

### Adversarial, source-directed cases

For each helper that implements a statement the model has an opinion on,
have an agent read the helper and the Lean code side by side and write the
cases where they could differ. Examples of pairs:

- `copyStructToStorageFunction` against `State.writeStorage`/`SVal.overlay`;
- `array_pop_<T>` against `storagePopSave`;
- `cleanup_storage_array_end_<T>` against the past-end `shadow`.

The dangling-reference and past-end-slot behaviour is the richest target: it
is where the model already departs from KeY, and where
`docs/solc-alignment.md` records a delta no test reads (`arr.push(v)` of a
struct over a recycled slot).

## Method 2: translation validation through solc's Yul

Testing samples programs. For a program you care about (a benchmark contract,
a specification you publish), you can instead **prove** that solc's output
for it agrees with `Stmt.run`, without verifying solc. This is CompCert's
approach to an untrusted pass: check each output, not the compiler.

1. **A Yul semantics in Lean** for the subset `--ir` emits: blocks,
   `let`/assignment, `if`/`switch`, functions, `sload`/`sstore`, memory,
   `keccak256`, the arithmetic builtins, `revert`. Nethermind's EVMYulLean is
   a Lean 4 EVM and Yul semantics tested against the Ethereum conformance
   suite. It pulls Mathlib, so the bridge lives in a sibling repository that
   requires both, as the `SolKey` reader does. This package stays
   dependency-free. solc's own `test/tools/yulInterpreter/` (map storage,
   real keccak) is a quick executable cross-check of that semantics.
2. **One lemma per helper instantiation.** Each helper solc emits for the
   fragment's types (a finite set at bounded nesting depth, enumerable from
   `--ir` over the universe contract) gets a theorem that it implements the
   model's operation through the layout relation. The repository has already
   done this twice, for `checked_add_t_int256` and siblings
   (`Evm/Signed.lean`) and for `checked_exp_unsigned` (`Evm/Exp.lean`). The
   rest is the same work repeated: suited to agents, one per family, the
   lemma statements generated from the helper's name and type.
3. **Per program, a structural match.** `IRGeneratorForStatements` is
   syntax-directed: `fun_f_<id>` is the statements of `f` in order, each a
   composition of helper calls on fresh `expr_<n>` variables. A validator
   parses `solc --ir` (or the experimental `--ir-ast-json`), matches the
   function body against the `Stmt` statement by statement, discharges each
   helper call with its lemma, and produces a Lean proof that the Yul
   simulates `Prog.run P` under the layout. That is a theorem about *this*
   solc's output for *this* program.
4. What stays trusted: the Yul optimizer and Yul-to-EVM assembly if you
   validate unoptimised `--ir`. `--ir-optimized` is still Yul, so the same
   validator applies, but the structural match weakens into a real
   equivalence proof. Legacy has no IR to read, so a legacy-compiled contract
   is covered by Method 1 only.

A cheaper step on the way: name the pieces of `Evm/Compile.lean` after the
helpers they mirror, as `uTail`/`sTail`/`expCode` already do in spirit, and
compare `compileProg P`'s shape with `solc --ir`'s for the same `P`. The
places where the shapes cannot match are the documented deltas (packing, the
operand order under IR).

Two by-products of reading solc's front end:

- **`--ast-compact-json` as a second front end.** Importing solc's typed AST
  into `Stmt C` checks the elaborator's name resolution and typing against
  solc's annotations. It would have caught the `sol!` name-typing gap in
  `docs/solc-alignment.md`: an `int` local read back is checked at `uint`.
- **The SMTChecker** (`libsolidity/formal/SMTEncoder.cpp`) models arrays and
  mappings as SMT arrays plus a length, with no slots and aliases havocked.
  It is a source-level second opinion on overflow and assert targets, not a
  storage oracle. It is low priority.

## Completeness and automation: what to prove, what to test

"Complete" means several different things here. Some are theorems already,
some can become theorems, and one can only be measured.

| Property | Status | Route |
|---|---|---|
| Every statement has a rule | proved: `Stmt.complete` (`Calculus/Completeness.lean`) | — |
| Exactly one rule per statement | proved: `Rule.eq_step`, `Rule.premise_unique` | — |
| Symbolic execution always steps, and terminates | proved: `Fml.active_iff_step`, `symex_terminates` | — |
| Symbolic execution loses no information: `⊨ φ ↔ ⊨ symex n φ` | **not proved**: `symex_sound` is one direction | provable, below |
| `sol_decide` decides its fragment | reductions proved exact (`Fml.valid_iff_reduce`, `Fml.valid_iff_cons`); the last step is `omega \| grind` | provable for a sub-fragment, below |
| `sol_close`, `sol_spec`, `grind` glue close what they should | unprovable as tactics | test, below |
| The fragment covers enough of Solidity | a measurement | `semanticTests` fraction; `docs/corpus-parity.md` |

### Symbolic execution is exact, and that can be a theorem

The rules are equivalences in substance: `Modality.after_sameOk`
(`Calculus/Logic.lean`) is an `↔`, and update simplification is already
stated both ways (`UpdRule.sound`, `Fml.simpUpds_holds`). What is missing is
`Premise.Correct` stated as an equivalence and `symex_complete :
holds σ φ → holds σ (symex n φ)`. With them, the validity of every loop-free
formula is exactly the validity of a modality-free one: relative
completeness, the property that says the calculus is never the reason a proof
fails.

Two things will stand in the way, and both are worth knowing about:

- `SameOk` identifies `revert` with `stuck`, so the converse needs "not
  stuck" as a hypothesis. `not_stuck` and `Stmt.run_wt` give it on
  well-typed states.
- `docs/solc-alignment.md` says the `assert` rule's obligation is strictly
  stronger than the program under the box modality. If so, that rule is a
  witness of incompleteness. Either weaken it to an equivalence or record it
  as the one exception in the theorem's statement.

The callback calculus (`ProvesC`) over-approximates by `havoc` and is
incomplete by design. Loops (`docs/loops.md`) will make completeness relative
to invariants, in Cook's and Harel's sense: provable when the needed
invariant is expressible.

### Automation that provably always closes

A tactic cannot be proved complete. A **reflective decision procedure** can:
a Lean function `dec : LFml → Bool` with `dec ψ = true ↔ ∀ σ, ψ.holds σ`,
run by `decide`. `sol_decide` is halfway there, because its reductions are
already equivalences. Replacing the final `omega | grind` with such a `dec`,
fragment by fragment, gives the theorem "on the fragment, `sol_decide`
succeeds exactly on valid goals":

- **Key equalities and reads-of-writes** (what the case trees split on):
  congruence closure over equalities of symbolic keys is decidable and small
  to verify. It is the first target.
- **Linear arithmetic over bounded integers**: decidable (Presburger on a
  finite domain). A verified procedure is heavy, but it is a closed,
  well-specified job.
- **Nonlinear, `**`, bitwise, shifts on 256-bit words**: decidable because
  finite, by bit-blasting. `bv_decide` is a complete procedure for
  quantifier-free bitvector goals, with kernel-checked LRAT certificates.
  Stating the arithmetic on `BitVec 256` makes the automation complete up to
  SAT time, and "always works" becomes "always works, given time".
- **Quantifiers** (`\forall` in specifications) leave decidability behind.
  There, test.

### Testing the automation that stays heuristic

- **Known-valid goals from runs.** Take generated programs, compute the exact
  final state concretely, and state it as the postcondition: `#verify` must
  answer ✓. Perturb one conjunct: it must answer ✗ with a certified witness.
  A "stuck" answer on a valid goal is an automation gap. Count gaps in a TSV
  and fail CI when the count rises.
- **Two-sided agreement.** For every generated goal, either the tactic
  proves it or `Fml.eval3` refutes it (`Tools/Counterexample.lean`). A goal
  on which neither answers is a gap to triage.
- **Separating the two failure causes of `sol_decide`.** On a goal in the
  fragment, a failure means the goal is invalid or `omega`/`grind` gave up.
  Export the reduced formula to SMT-LIB and ask `z3`, or try `bv_decide`, to
  tell which.
- **Metamorphic tests.** A proof should survive a change that preserves
  meaning:
  - renaming locals;
  - reordering independent statements;
  - rewriting `x += a` as `x = x + a`;
  - wrapping a statement that cannot overflow in `unchecked`;
  - introducing an alias.

  A verdict that changes is a bug in the automation or in a rule.
- **A budget.** In practice "closes" means "closes within the heartbeats".
  Record heartbeats per goal, so a regression in time shows before it turns
  into a failure.

## Order of work

Each step is useful on its own, and each fans out to parallel agents.

1. **Decide the operand order** (options above) and fix the
   `docs/solc-alignment.md` table. This takes a day and no infrastructure.
2. **The printer, its round trip, and `lake exe solcases`.** Reuse solkey's
   Besu runner for a first harness and run the enumerated universe contract
   under both pipelines.
3. **The `semanticTests` translator and the `syntaxTests` oracle**, with one
   agent per directory. Record the fragment-width numbers.
4. **Coverage reports** (rule, halt cause, solc helper) and **mutation
   runs**. Use the surviving mutants to steer the adversarial agents.
5. **`symex_complete`** and the resolution of the `assert` gap.
6. **Reflective `dec`** for key equalities, then the `bv_decide` route for
   word arithmetic.
7. **Translation validation** in a sibling repository: the Yul semantics,
   then helper lemmas (one agent per family), then the per-program matcher
   for the benchmark contracts.

After step 4, "the semantics agrees with solc" is a measured claim: which
programs, which states, which pipelines, and which mutants the suite kills.
After step 7 it is a proved one for the contracts that matter.
