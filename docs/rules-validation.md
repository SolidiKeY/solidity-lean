# Validating the rules against Solidity

How to find out whether `Calculus/Rules.lean` says what Solidity does. It is
a plan: nothing in it is built yet. `docs/solc-validation.md` is the plan for
the interpreter (differential testing, solc's own suites, translation
validation through Yul); this document narrows it to the rules, adds the
checks an LLM can do by reading the code, and records which Lean projects
online can help.

## Where a rule can be wrong

`Taclet.sound`, `LeanTaclet.sound` and `Rule.sound`
(`Calculus/RuleSoundness.lean`) prove every rule sound against `Stmt.run`.
So a rule is wrong about Solidity only through one of four links:

1. **`Stmt.run` is wrong** (`Semantics.lean`). The rule is then proved sound
   against the wrong semantics.
2. **The elaborator reads `sol{…}` differently from solc** (`Syntax.lean`,
   `hoist`): evaluation order, what it captures, what it accepts.
3. **The rule is sound but too strong.** Its premise asks for more than the
   program needs, so true things cannot be proved. The `assert` rule is the
   known case (`docs/solc-alignment.md`).
4. **The trusted base leaks**: a `sorry`, `native_decide`, `implemented_by`,
   or a `side_cond` that proves more than it should.

`Stmt.complete` (`Calculus/Completeness.lean`) is coverage, every statement
has a rule, not logical completeness: it says nothing about link 3.

Links 1 and 2 are the unproved square of `docs/solc-validation.md`. The
checks below cover all four.

## What the compiler theorem checks

`compile_correct` (`Evm/Correctness.lean`, `docs/compiler-verification.md`)
looks like a check of link 1: the interpreter and the compiled code both end
in `Sim`-related states, or both revert. Lean checks the proof against the
definitions, not the definitions against the EVM, so the theorem pins
`Stmt.run` down only as far as three trusted definitions are right:

| Trusted | Must match | If it does not |
|---|---|---|
| `Instr.step` (`Evm/Machine.lean`) | the EVM (Yellow Paper, conformance tests) | the theorem proves agreement with a fictional EVM |
| `compileStmt` (`Evm/Compile.lean`) | what solc emits | the theorem proves agreement with another language |
| `Sim` and the theorem's shape | what a proof should guarantee | a wrong behaviour `Sim` does not relate goes through |

With all three right, a wrong `Stmt.run` clause makes `compile_correct`
false, and so unprovable. A definition of the machine written *from the
interpreter* makes the theorem hold by construction, and so checks nothing.
`transfer` is the case in point: the machine's `CALL` is `transferAt`
re-spelled (the same funds guard, the same debit, a `net` field no EVM has, no
recipient), so its proof case matches `if` with `if`.

### K. The machine against a real EVM

- **`CALL` from the Yellow Paper**: a world state (`balances : Nat → Nat`, the
  contract's own address) in place of `net`; the value moves from the
  contract to the recipient, and a transfer to itself moves nothing; the
  callee is a parameter, and `compile_correct` quantifies over every callee
  (for all, never there exists, or an always-accepting callee hides the
  revert). With `transfer`'s 2300-gas stipend a callee cannot `SSTORE` or send
  value (EIP-2200), so accept-or-revert is all it can do; that is an
  assumption on the gas schedule, stated or modelled.
- **`Sim` relates real quantities**: `σ.selfBalance` to the machine's balance
  at its own address. `net` is a ghost the machine cannot hold, so a wrong
  `net` update passes the theorem; a separate lemma pins it (the sum of the
  changes to `net` is the change to `selfBalance`, on a run with no incoming
  funds).
- **Every instruction tested against a real EVM**: the same bytecode on
  `Machine` and on revm/evmone (or Ethereum's `GeneralStateTests`),
  compared. `Tools/DiffTest.lean` compares the interpreter with the machine;
  this compares the machine with the EVM. EVMYulLean would do it as a
  `[[require]]`, which this package cannot have.
- **`compileStmt` against solc**: each compiled statement beside what
  `solc --ir` emits for it (for `transfer`: the stipend, and the revert when
  `CALL` fails; compiled as `send`, with an interpreter that did not revert,
  the theorem would still hold).

## Deterministic checks

### A. The trusted base, in CI

A script that runs `#print axioms` on `Rule.sound`, `Proves.sound`,
`ProvesC.sound` and `symex_sound`, and fails on anything beyond `propext`,
`Quot.sound` and `Classical.choice`, or on `sorry`, `native_decide` or
`implemented_by` in their dependency closure. It is a day's work, and every
other check assumes it.

### B. solc facts, pinned

One theorem per known solc behaviour, closed by `decide` or `#guard`, each
citing solc's source (file and line at a pinned version) and a test that
shows it:

- `a[i++] = i` writes `a[0] = 0`;
- `++a + a` at `a = 1` is `3` under legacy and `4` under via-IR;
- `pop` zeroes the slot it frees;
- `delete` keeps a mapping.

They live in `Solidity/Counterexamples/`, beside the refutations that already
pin design decisions. A citation is re-checked when solc is re-pinned. The
divergence log of SolidCore (below) is the first source to mine for them.

### C. Each rule against solc directly

The check that bears on the rules most directly, and does not go through
`Stmt.run`:

- for each `Taclet` and `LeanTaclet` constructor, a canonical instance (the
  constructor list from `#enum_ctors`, `Calculus/RuleShapes.lean`, and the
  statement `Stmt.step` fires it on) and a concrete start state;
- evaluate the rule's premise on it: through the updates and `Term.denote`
  over `State.abs`, which is a different code path from the interpreter;
- compile the same instance with solc, run it, and compare the result or the
  revert.

That is three independent computations (the rule, the interpreter, solc), so
a disagreement says which of them is wrong. The coverage target is every
constructor, under both modalities, on a succeeding and a reverting state.
`Rule.eq_step` (`Calculus/Uniqueness.lean`) makes coverage a function of the
program. For the runner, `solc --ir` and solc's `yulInterpreter`, or evmone,
are lighter than Besu; SolidCore's Foundry harness (below) already exists.

### D. solc's `semanticTests` and `syntaxTests`

The translator `docs/solc-validation.md` describes. The expected outputs are
already written down, so no EVM is needed. It is the highest-value oracle
there is, and it splits well across agents, one per directory.
`syntaxTests` is the same for what `sol{…}` must refuse.

### E. Mutating the rules

Mutate `Calculus/Rules.lean` itself, not only `Semantics.lean`: drop a
guard, swap a capture order. Then:

- **does `Taclet.sound` still build?** If it does, the semantics does not
  constrain that detail. That is either a real freedom or a hole in
  `Stmt.run`, and either is worth knowing;
- **does the suite of C catch it?** If not, the suite is too weak there.

### F. Premises as equivalences

`Premise.Correct` stated as an `↔`, then `symex_complete`
(`docs/solc-validation.md`, "Symbolic execution is exact"). It catches link
3, rules that are sound but useless, and turns the `assert` gap into a
theorem or a recorded exception.

## Checks an LLM does by reading the code

The rule for all of them: **the LLM proposes, the harness decides.** An agent
never hands in a verdict alone. It hands in something checkable: a witness
program with solc's expected result (for B or C), or a row in a table a
script checks.

### G. A rule-to-solc map

`docs/rule-solc-map.md`, beside `docs/lean-key-rule-map.md`. One row per
constructor:

| Constructor | solc legacy | solc IR | `Stmt.run` clause | Witnesses |
|---|---|---|---|---|
| the `Taclet`/`LeanTaclet` name | `ExpressionCompiler.cpp` function and line | `IRGeneratorForStatements.cpp` function and line, and the `YulUtilFunctions.cpp` helper | the interpreter clause | the B facts and C cases |

Agents fill it, one per rule family. A `scripts/check-rule-solc-map.mjs`
checks that every constructor has a row and every
cited witness exists.

### H. Blind prediction

One agent sees only solc's source and the Solidity snippet, never the Lean,
and predicts the outcome. A second compares the prediction with the Lean.
This avoids anchoring: an agent that reads the Lean first tends to
rationalise it. Every disagreement becomes a B fact or a C case.

### I. One checklist for every rule

So that agents look at the same things every time:

- evaluation order, per pipeline;
- which checks fire: overflow, bounds, zero divisor, empty `pop`;
- cleanup: `pop`, `delete`, past-the-end slots;
- storage reference or copy, and dangling references;
- memory or storage source;
- effects before a revert;
- `docs/bugs.json` rows for the pinned version.

### J. Adversaries steered by mutants

Each mutant of E that nothing catches goes to an agent whose only job is to
write a program that tells the mutant from the original.

## Known gaps

- **Binary operand order.** The elaborator follows legacy (right operand
  first), which is wrong under via-IR. The simplest fix is to refuse an
  effect in an operand whose order is observable, so a proof holds for both
  pipelines (`docs/solc-validation.md`, option 2).
- **Struct and array sources are not right-hand-side first** in solc: it
  resolves the target before copying member by member, while the interpreter
  is value-first (`docs/solc-alignment.md`, "Known divergence").
- **`transfer` assumes its recipient.** `transferAt` succeeds whenever the
  funds cover the amount, and debits them whoever the recipient is. That is
  two unstated assumptions: the recipient never reverts (no `receive`, an
  explicit `revert`, more than 2300 gas), and it is never the contract itself
  (on the EVM that moves nothing and runs the contract's own `receive`).
  `address(this).transfer(v)` does not parse, but any `uint` holding the
  contract's address is a receiver, since the model has no address of its
  own. `Rule.sound` and `compile_correct` both hold, against the interpreter
  and a machine that share the assumptions; the diamond `transferNoCallback`
  then promises termination the EVM does not give. The receiver is also a
  `uint`, not an address below `2^160`. Two fixes: state the assumptions as
  hypotheses of `compile_correct` and the diamond rule, or give the
  interpreter a recipient oracle and a `this` address (the diamond rule then
  owes the recipient's acceptance, and solkey's rule changes with it). K
  exposes both cases either way.
- **The callback reading belongs to `call{value:}`**, not `transfer`: under
  the 2300-gas stipend a re-entrant callee cannot change storage, `net` or
  `selfBalance`, so for `transfer` the right reading is no callback, the
  recipient free to revert. `Semantics/Callback.lean`'s havoc is the reading
  of `a.call{value: v}("")`, which the syntax does not have.

## Lean projects online

Every one of them pulls Mathlib, directly or through EVMYulLean, so none can
be a `[[require]]` here. They are used as data copied in, as external
programs, or from a sibling repository that requires both packages, as the
`SolKey` reader does.

### SolidCore (`paradigmxyz/solidity-lean`)

<https://github.com/paradigmxyz/solidity-lean>, read at `f22b110`
(2026-09-30). An executable semantics of Solidity 0.8.35, legacy pipeline.
Its claim: on programs in scope, the observable result (return data, revert
and panic data, events, final storage) is byte-identical to solc-compiled
bytecode on a real EVM, through Foundry. Lean v4.28; requires EVMYulLean
(Paradigm's fork) and so Mathlib.

- **`DIVERGENCE-LOG.md`, 135 rows.** Each is a program with solc's
  behaviour, EVM-verified, classed `over-reject`, `over-accept`,
  `wrong-value` or `verified-correct`. Several are where this model is least
  sure of itself:
  - #187: legacy evaluates a binary operator's right operand first
    (`ExpressionCompiler.cpp:614-615`), which confirms the elaborator's
    choice for legacy;
  - #189, #190: tuple components and sibling expressions go left to right;
  - #177: solc bounds-checks a storage reference to an array element once,
    when the reference is made, and reads the raw slot afterwards. After a
    `pop()` the reference reads the zeroed slot rather than panicking;
  - #204: `push()` only bumps the length. A write through a dangling
    reference past the old length survives the re-grow
    (`p = arr[i]; arr.pop(); p.a = 5; arr.push();` then `arr[i].a` is 5).
    This is the "push over a recycled slot" delta that
    `docs/solc-alignment.md` records and no test reads.

  Triaging the rows against this fragment is the fastest source of B facts.
- **About 1,188 `.sol` cases and a Foundry harness** (`tests/forge-harness`,
  `scripts/compare_forge_solc_interpreter.sh`). Method 1 of
  `docs/solc-validation.md`, working. The planned printer should emit their
  case format, so their harness runs this model's programs.
- **A second executable oracle, with no EVM in the loop.** A sibling
  repository requiring both packages prints this model's programs, runs
  `Stmt.run` and SolidCore's interpreter, and compares final storage. Later,
  a simulation theorem between the two on this fragment: with it,
  `Taclet.sound` reaches a semantics that is tested against the EVM.
- **Their methods**: a pinning test with every fix (99 witness modules), a
  divergence log with classes and statuses, and an adjudicator whose
  detectors are tested by fault injection.
- **Versions to reconcile**: they pin solc 0.8.35. `docs/solc-validation.md`
  reads the 0.8.37 source and the installed solc is 0.8.33. Any comparison
  pins one.

### EVMYulLean (Nethermind)

<https://github.com/NethermindEth/EVMYulLean>. An executable EVM and Yul
model at the Cancun fork, passing 22,330 of 22,332 of Ethereum's conformance
tests. It is the Yul semantics Method 2 of `docs/solc-validation.md` needs.
Use Paradigm's fork, which carries corrections (SolidCore pins
`danrobinson/EVMYulLean`).

### Clear (Nethermind)

<https://github.com/NethermindEth/Clear>. Translates solc's optimised Yul into
Lean and generates verification-condition templates. Its parser and block
decomposition could be the "parse `solc --ir`, match statement by statement"
step of Method 2. From 2024, tied to specific optimiser flags.

### Solidus (Paradigm)

<https://www.paradigm.xyz/writing/solidus>. A verified compiler from
SolidCore to EVM bytecode. With this model tied to SolidCore on the
fragment, proofs made with the rules carry to Solidus-compiled bytecode
(not solc's). It also reports on the agent approach: most of the work by
LLM agents, over 1,700 hours and about $150k in API cost, with humans taking
the design and specification decisions.

### Less relevant

Verity (<https://github.com/lfglabs-dev/verity>: its own contract language
with a verified compiler to Yul), evmSmith (an AI writes EVM bytecode and
proves it safe) and EquiVM (<https://arxiv.org/abs/2607.26306>: refinement
proofs on deployed bytecode) do not model Solidity source, so none of them
checks a rule. The Yul formalization of <https://arxiv.org/abs/2507.19012> is
in ACL2.

## Order of work

1. **A**, and **B** with the known gaps as its first facts.
   **K**'s `CALL` with the `transfer` assumptions as hypotheses of
   `compile_correct`: a small change to `Evm/Machine.lean` and one proof
   case, and it turns the hidden assumptions into stated ones.
2. Triage SolidCore's divergence log against the fragment, one agent: each
   relevant row a B fact or a `Counterexamples/` entry, saying whether this
   model already matches.
3. **G** and **I**, with agents in parallel, one per rule family.
4. The printer of `docs/solc-validation.md`, emitting SolidCore's case
   format, run through their Foundry harness.
5. **D**, then **C**.
6. **E** and **J**.
7. **F**.
8. The sibling repository with SolidCore: the Lean-to-Lean differential run,
   then the simulation theorem if the runs keep agreeing.

After 5 and 6, "the rules match Solidity" is a measured claim: which rules,
which states, which pipelines, and which mutants the suite catches.
