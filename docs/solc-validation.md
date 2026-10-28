# Validating the semantics and the rules against solc

Every theorem here is about the typed run (`Prog.run`) and the rule table.
This document says how far that is checked against what solc-compiled code
does: what exists, and the checks still to build (lettered A to O; the
letters are kept so plans can cite them). `docs/solc-alignment.md` records
the decisions taken and the remaining deltas; `docs/compiler-verification.md`
records `compile_correct`. The pinned solc is 0.8.38 (`1835d247`, the
[upstream corpus](solidity-upstream-tests.md) and the
[feature inventory](solidity-feature-inventory.md)); older fixtures use 0.8.34.

## The chain of trust

```
Solidity source ──(1) sol{…} / solc_import──▶ Prog C ──(2) Prog.run──▶ State
      │                                           │
      └──(3) solc (legacy | via-IR) ──▶ EVM bytecode ──(4) EVM──▶ storage slots
```

Proved: the rules are sound for (2) (`Stmt.sound`, `Proves.sound`,
`ProvesC.sound_of`); the repository's compiler agrees with (2) on the
programs it compiles (`compile_correct` over `inFragP`, and the memory path;
`docs/compiler-verification.md`); no `try`, `send` or data reverts. (2) is never stuck: the typed run halts only by `THalt`
(`docs/intrinsic.md`). Not proved, and not provable without a model of solc:
that (1) reads a program as solc does, and that (2) plus the layout equals (3)
plus (4). **Every proof reaches solc-compiled contracts only through that
square.** A rule is wrong about Solidity only through one of four links:

- **L1. The typed run is wrong** (`Semantics/Run.lean`); the rule is sound
  against it.
- **L2. The elaborator misreads the source** (`hoist`, the solc import):
  evaluation order, captures, what it accepts.
- **L3. The rule is sound but too strong.** `Stmt.rule_exists` is coverage,
  not completeness.
- **L4. The trusted base leaks**: `sorry`, `native_decide`,
  `implemented_by`, or a side condition that proves too much.

"Correct" must name which solc: the two pipelines disagree, and solc's
`docs/bugs.json` lists known miscompilations. A disagreement with an oracle
has four outcomes: the model is wrong; the pipelines disagree and the model
picked one; solc is wrong; the program is outside solc's language.

`compile_correct` is not a check of L1 by itself: Lean checks the proof
against three trusted definitions (`Instr.step`, `Evm.compileStmt`, `Sim`). A
machine written *from the interpreter* makes it hold by construction; that is
why `CALL` moves real balances (`bal`, `accepts`) and `Sim` relates `net` to
them (`Sim.netSelf`, `compile_net`), so a wrong `net` update fails the
theorem.

## What exists

- **A hand audit**: `docs/solc-alignment.md`.
- **A. The trusted base**: `bash scripts/check-trust.sh` (source lint against
  `tests/trust-inventory.json`) and `TrustAudit.lean` (the headline theorems'
  transitive axioms: only `propext`, `Classical.choice`, `Quot.sound`); CI runs
  both ([assurance.md](assurance.md), M1).
- **The solkey corpus**: `tests/solkey/expected.tsv`, `scripts/check-corpus.sh`.
  Its `solc/*.sol` rows are solkey's hand ports of solc's `semanticTests`:
  indirect, one state per function, asserts only.
- **`#difftest`** (`Tools/DiffTest.lean`): the interpreter against the
  repository's own compiler on random well-typed storages. It tests
  `compile_correct`'s hypotheses and the generator, not solc.
- **F, in part: solc's own suites** ([solidity-upstream-tests.md](solidity-upstream-tests.md),
  `scripts/solidity-upstream.mjs`, results in `tests/upstream/results/`). The
  complete 0.8.38 `test/` tree is archived. `syntaxTests` diagnostics are
  compared with the pinned solc (a reference check: it does not test what
  `sol{}` or the import refuses). `semanticTests` scalar vectors are replayed
  on the typed interpreter through `solc_import`, in legacy and via-IR source
  modes; each fixture is working, broken (a frontend gap or a mismatch) or
  blocked (no adapter: gas, logs, revert data, aggregate/bytes ABI inputs,
  host behaviour). Two via-IR modifier mismatches are real deltas
  (`docs/solc-alignment.md`, "Remaining deltas").
- **D, in part: hand-written EVM vectors.** `scripts/check-abi-vectors.mjs`,
  `check-call-exception-vectors.mjs`, `check-transient-vectors.mjs`,
  `check-slice-copies.mjs`, `check-recursive-types.mjs` compile fixed
  programs with the SHA-pinned solc and run them on an externally supplied
  EthereumJS VM, legacy and via-IR, against expected results. Optional; no Lake
  dependency. Per-feature evidence, not a generated differential harness.
- **Operand order is decided**: legacy by default, `Contract.evalOrder :=
  .viaIR` for source order (`docs/options.md` O9).

## Still to build

**B. solc facts, pinned.** One theorem per solc behaviour, closed by `decide`
or `#guard`, in `Solidity/Counterexamples/`, citing solc's file and line at
the pin: `a[i++] = i` writes `a[0] = 0`; `++a + a` at `a = 1` is `3` legacy and
`4` via IR; `pop` zeroes the slot it frees; `delete` keeps a mapping.
SolidCore's divergence log (below) is the fastest source.

**C. The machine against a real EVM.** Every instruction of `Instr.step`
against revm/evmone or Ethereum's `GeneralStateTests`; `compileStmt` against
`solc --ir` statement by statement, `Evm/Compile.lean`'s pieces named after
the helpers they mirror. The stipend is not modelled (a refusal stands for
it).

**D. A generated differential harness (bounded increment implemented).**
`lake exe solcases` and `scripts/evm-reference/generated.mjs` now execute
160 intrinsically typed closed programs/start states against pinned solc and
EthereumJS in legacy/viaIR, optimizer off/on. Exact outputs, panic/revert
bytes and both declared roots after success/rollback are compared. Concrete
parser/printer and literal-arithmetic regressions are kernel checked. See
[implementation and evidence](feature-work/generated-differential.md) for
commands, scope, refusals and remaining D/E work. This does not establish
universal printer or solc correctness. The remaining full target follows.

Lean generates a program, prints it
as Solidity, a Node harness compiles it under legacy and via-IR, with and
without the optimizer, runs it on an EVM, decodes storage by
`--storage-layout`, and diffs with `Prog.runT`. Needs a printer from `Stmt C`
to Solidity with a `#guard`ed round trip (none exists: `Calculus/RuleSyntax.lean`
prints `sol{…}` only); the start state as a program (`Build.rootsProg`,
`Typing/Constructibility.lean`, printed as `setUp()`); a `lean_exe` importing
only `Syntax`, `Semantics` and `Tools/Show.lean`, so mutants (H) rebuild
without proofs. The harness records the panic selector `0x4e487b71` and its
code as an expected-cause tag. Verdicts `agree`, `model`, `unspecified`,
`solc-bug`, `rejected`, pinned in a TSV with a check script. `Evm/Repr.lean`
is solc's layout except `bool` beside a packable neighbour, so compare
decoded values, not slots.

**E. Test inputs.** Bounded enumeration over one universe contract with every
shape, values from pools (`0`, `1`, `2^256-1`, `±2^255`, `-1`); coverage
targets (every `Taclet`/`LeanTaclet` constructor under both modalities, a
succeeding and a reverting case per guard, the `solc --ir` helper names
reached); path-directed inputs from `sol_symex`'s path conditions; a source
generator for `hoist`/`captureExpr` (`a[i++] = i`, `m[k][k++] = …`,
`p.age += i++`).

**F, the rest.** Widen the runtime adapter past its blocked list; use
`syntaxTests` as the oracle for what the import must refuse and accept; turn
each fragment-relevant `bugs.json` row into a regression expecting the fixed
behaviour under its `conditions`.

**G. Each rule against solc directly.** Per constructor (`#enum_ctors`,
`Calculus/RuleShapes.lean`): a canonical instance, its premise evaluated
through the updates and `Tm.denote` (a path independent of the interpreter),
and the instance compiled and run: three computations, so a disagreement says
which is wrong.

**H. Mutation testing.** Mutate the typed run one decision at a time (RHS
after target, a range check dropped, `pop` not clearing, `delete` resetting
mappings, a push not reusing its slot, `**` unchecked, `transfer` not
debiting) and `Calculus/Rules.lean` (drop a guard, swap a capture order);
require the suite to kill each. A survivor is a decision no test observes.

**I. Translation validation through solc's Yul** (a sibling repository: a Yul
semantics such as EVMYulLean pulls Mathlib). One lemma per `--ir` helper
instantiation (done twice: `Evm/Signed.lean`, `Evm/Exp.lean`); a validator
matching `fun_f_<id>` to the `Stmt` and emitting a simulation proof. Trusted:
the Yul optimizer and assembly. Legacy has no IR; D covers it alone.

**J. A rule-to-solc map**, `docs/rule-solc-map.md` beside
`docs/lean-key-rule-map.md`: per constructor the legacy and IR code site, the
`YulUtilFunctions.cpp` helper, the `TRun.*` clause and witnesses, with a
script checking every constructor has a row.

**K. Blind prediction.** An agent sees only solc's source and a snippet and
predicts the outcome; another compares with the Lean. Each disagreement
becomes a B fact or a G case. Checklist: evaluation order per pipeline, which
checks fire, cleanup, reference or copy, dangling references, effects before a
revert, `bugs.json` rows.

**L. Adversaries.** For each surviving mutant, a program that tells it apart;
for each solc helper the model has an opinion on (`array_pop_<T>` against
`storagePopSave`, `cleanup_storage_array_end_<T>` against the past-end
shadow), the cases where they could differ. Dangling references and past-end
slots are the richest target.

**M. Symbolic execution is exact.** Proved: one rule per statement
(`Stmt.rule_exists`, `Rule.iff_step`, `Rule.premise_unique`) and
`symex_sound`. Missing: `Premise.Sound` as an equivalence and
`symex_complete : holds σ φ → holds σ (symex n φ)`, which would make L3 a
theorem for loop-free formulas. The callback calculus is incomplete by design
(havoc); loops make completeness relative to invariants.

**N. Reflective decision procedures.** `sol_decide`'s reduction is sound
(`Fml.Valid.of_reduceS`); replace its last `omega | grind` step by fragment:
key equalities and reads of writes, linear arithmetic, then 256-bit words on
`BitVec` with `bv_decide`.

**O. Testing the heuristic automation** (`sol_close`, `sol_spec`). Known-valid
goals from runs (`#verify` must answer ✓, a perturbed conjunct ✗); two-sided
agreement with `Fml.eval3` (`Tools/Counterexample.lean`); metamorphic tests
(renaming, reordering independent statements, `x += a` as `x = x + a`); a
heartbeat budget per goal.

## Related Lean projects

All pull Mathlib, so none can be a `[[require]]` here: use them as data, as
external programs, or from a sibling repository.

- **SolidCore** (`paradigmxyz/solidity-lean`): an executable semantics of
  Solidity (legacy) matched against solc bytecode on a real EVM through
  Foundry, about 1,188 cases. Its `DIVERGENCE-LOG.md` is a source of B facts
  (legacy right operand first; a storage reference bounds-checked once; a
  write through a dangling reference surviving `push()`).
- **EVMYulLean** (`NethermindEth/EVMYulLean`; Paradigm's fork carries
  corrections): EVM and Yul, I's semantics and C's reference.
- **Clear** (`NethermindEth/Clear`): optimised Yul into Lean; its parser
  could be I's matcher.
- **Solidus**: a verified compiler from SolidCore to EVM; its cost is the
  reference for I.

## Order of work

1. **B**, seeded from SolidCore's divergence log; **J** and **K** per rule
   family.
2. **F**'s rest: the runtime adapter's blocked families, `syntaxTests` as the
   import's oracle, `bugs.json`.
3. **D** with **E**'s universe contract, then **G**.
4. Coverage reports, **H**, **L**.
5. **M**, **N**, **O** as automation grows.
6. **C** against a real EVM; **I** in a sibling repository.
