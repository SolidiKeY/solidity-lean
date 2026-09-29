# Function specifications: design

Per-function `requires`/`ensures` with `\old` and `\forall`, the contract
invariant, and proof obligations that `sol_symex` + `sol_close` discharge
over symbolic parameters. The front end, the obligation and `sol_spec` are
built ("Decisions"); the plan below lists the rest. Read
`docs/kernel-port.md` ("Still open", "Decisions") first.

## What solkey does

Clauses are NatSpec lines above a function, or above the contract for
`invariant` (the solkey benchmark, `keyext.solidity.examples/benchmark/*.sol`):

```solidity
/// @custom:key requires count >= 1
/// @custom:key ensures count == \old(count) - 1                 // Counter.dec
/// @custom:key ensures \forall address a; a != receiver -> balances[a] == \old(balances[a])   // Coin.mint
/// @custom:key invariant \forall address a; pendingReturns[a] >= 0     // SimpleAuction
```

How solkey processes them:

- **Reading.** `speclang/natspec/KeyNatspec.java` reads the directives
  `box`, `skip`, `invariant`, `requires`, `ensures` and `assignable`
  (`assignable` is ignored, because bodies are inlined).
- **Parsing.** The expression language is `SolSpec.g4`, parsed by
  `SpecParser`. It is Solidity expressions plus `\old`, `\result`,
  `net(a)`, `->`, `<->`, and `\forall`/`\exists sort x; e`.
- **Translation.** `SpecCompiler` translates to `.key` text. A state
  variable becomes `find(storage, …)`. `\old(e)` reads `e` against the
  snapshot variables `old`/`oldNet`. `\old` is allowed in `ensures` only and
  cannot be nested. `\result` is the return variable.
- **The obligation** (`SolidityProblemSynthesizer.specifiedProblemText`) is
  always a **box**:

  ```
  msgValue ≥ 0 & requires & CInv(storage, net) ->
    {old := storage ‖ oldNet := net ‖ net := … + msgValue ‖ selfBalance := … + msgValue}
    \[{ result = f(args)@C; }\] (CInv(storage, net) & ensures)
  ```

  - The parameters are unconstrained program variables. `uint` is an
    unbounded `int`, so any bound on a parameter has to come from `requires`.
  - The invariant is assumed on entry and proved on exit. With
    `transferSemantics:withCallback` it is also proved at every `transfer`.
  - Constructors get no obligation, so nothing ever establishes the
    invariant at deployment.

Benchmark status per its README: 19 of 21 obligations close. `mint`/`burn`
of ERC20 stay open on internal calls. Every closed
proof was checked for vacuity.

## What the Lean side has today

- **Formulas.** `Fml` (`Update.lean`) has `tt`, `=`, `¬`, `∧`, `→`,
  `{U}`, both modalities and `{havoc}`. It has **no quantifier** and no
  pre-state reference. `Valid` is `∀ σ`.
- **Symbolic parameters exist already.** A name the formula does not
  declare is a free `uint` local (`Calculus/Notation.lean`, "parameter").
  `⊨` quantifies over every state, and so over every value of that local.
  `Examples/Decide.lean` decides goals over free keys `k`, `j` this way,
  and `Examples/Calls.lean` calls a function on a free argument
  (`callCapture`).
- **`sol_symex`** (`Calculus/Symex.lean`) runs any program with no loop and
  no callback to its end. There is no residue: one rule per statement
  (`Stmt.complete`), and it terminates (`symex_normalizes`). A call is
  inlined (`functionBodyExpand`).
- **`sol_decide`** (`Calculus/Decide.lean`, `Calculus/DecideComplete.lean`)
  handles the fragment `Fml.inL`: storage reads, writes and `delete`,
  `.length`, locals, operators and conditionals. Its reduction is an
  equivalence (`Fml.valid_iff_reduce`), and the reads are realizable
  (`Fml.valid_iff_cons`). It splits on each local (halted, `int`, `bool`),
  so **a free parameter is already handled**. It closes a goal when
  `omega`/`grind` close the reduced statement. It does not handle memory,
  storage copies, `push`/`pop` or `transfer`.
- **The contract invariant.** `Invariant C` (`Semantics/Callback.lean`) is
  a formula that must be *closed* (`fml.vars = []`) and contain no
  transfer. `ValidC` and
  `ProvesC` (`Calculus/Callback.lean`) use it for callbacks
  (`Examples/Callback.lean`).

So the procedure is in place. What is missing is the **front end** that
states the obligation, plus `\old`, `\forall`, range facts, and a
precondition that makes a diamond meaningful.

## Decisions (built 2026-09-28)

The clauses are translated to dynamic logic as solkey translates them, with
the same shapes: a clause is read against a storage term, `\old` reads the
storage variable `old`, `\forall` is a quantifier of the logic.

**1. A clause is data, kept as read, where solkey's NatSpec line stands.**
`SpecExpr` (`SpecSyntax.lean`) is `SolSpec.g4`; `contract!{ … }` reads
`requires e;`, `ensures e;`, `assignable l, …;` (or `assignable \nothing;`),
`skip;` above a function and `invariant e;` anywhere (`FunDecl.spec`,
`Contract.inv`); a function's `payable` attribute is kept
(`FunDecl.payable`).  Kept raw because a `Contract`
cannot hold an `Fml C`.

**2. The compiler is `SpecCompiler`'s** (`Calculus/Spec.lean`): a context
(`SpecCtx`) names the storage term, whether `\old`/`\result` mean
something, and the locals in scope.  A state variable is
`find(ctx.storage, p)`; `\old(e)` is `e` against `old`, and not nested;
`msg.sender`, `msg.value`, `block.timestamp`, `this.balance` are `Term.env`;
an enum member its position; `==` between conditions is `<->`; `\exists`
is `¬∀¬`.

**3. `old` is a storage variable**, KeY's `Struct old`: `STerm.pv`, bound
in the env (`Binding.store`) by the update `{old := storage}`
(`UpdElem.store`).  The update is in front only when an `ensures` reads
`\old`.  `find(old, p)` checks `p`'s indices against the current storage
and reads `old`: `sol_decide` cannot state that exactly and keeps `old`
outside its fragment; `sol_close` reads it semantically.

**4. `\forall` is `Fml.all x T φ`**, over `PrimTy.admits` (a `uint` in
`[0, 2^256)`).  `Fml.vars` keeps the bound name (a quantified invariant is
not `closed` yet).  `sol_close` reads it as a Lean `∀` over integers
(`Close.forall_admits_uint`), and `grind` instantiates it.

**5. The obligation is solkey's box** (`spec[C]{f}`):

```
R ∧ L ∧ M ∧ I ∧ requires →
  {old := storage ‖ oldNet := net ‖ book(msg.value)} [ T result = f(x₁, …, xₙ); ] (I ∧ ensures ∧ A)
```

`R` is each parameter's range and `L` the layout of the state the clauses
read (`layoutFmls`: each word of its declared type, at every key of a
mapping); solkey's reads are total and typed and need neither
(`docs/solkey-feedback.md`).  `M` is `msg.value >= 0` for a `payable`
function and `msg.value == 0` otherwise.  `I` is `Contract.inv`, assumed and
owed.  `specParts` returns the three parts apart: the premises every run
meets (`R`, `L`, `M`), the ones the specification states (`I`, `requires`),
and the conclusion.

The update is solkey's with three differences, none of which changes what
the formula means: `old := storage` is there when an `ensures` reads `\old`
or an `assignable` clause is given; `oldNet := net` only when an `\old(…)`
reads `net(a)` (solkey takes both with any `\old`); and `book(msg.value)`
(`UpdElem.book`, KeY's `net := storeSt(net, at(msgSender), … + msgValue) ‖
selfBalance := selfBalance + msgValue`) only for a `payable` function, since
`M` makes the other's `book(0)`.  Leaving them out is cheaper: symbolic
execution and `sol_close` pay for every element.

`net(a)` is `Term.net`, what the ledger holds for `a` (`State.getNet`), read
as a `uint` as `msg.value` is; under `\old` it is `Term.netOf oldNet a`, the
ledger snapshot `Binding.ledger` holds.  So `net(a) + msg.value` is
range-checked: `requires net(msg.sender) + msg.value >= 0;` says the sum is a
`uint`.

`A` is the frame of `assignable` (`assignableFml`): every word of the
contract's storage that no listed location covers is where it was,
`find(old, p) = find(old, p) → find(storage, p) = find(old, p)` (owed where
the word was there to begin with, since `⊨` also ranges over storages
without it), under `∀ k` at a mapping, with `¬ k = e` where `m[e]` is
listed and nothing below `m[*]` or a listed location itself.  An array owes
its length and every element below it.  A key is read in the pre-state,
against `old`.

**6. `sol_spec` proves one**: `sol_symex`, then `sol_close` with a word read
known to be a word (`Close.asValue_eq_ok`) and `grind`'s instantiation
bounded.  Splitting the obligation clause by clause was tried and costs
more: symbolic execution runs once per clause.  What closes is proved
beside each benchmark contract, which carries its clauses
(`Examples/Benchmark/Counter.lean`, `Examples/Benchmark/SimpleStorage.lean`,
`Examples/Benchmark/Mapping.lean`, `Examples/Benchmark/Coin.lean`), and in
`Examples/Specs.lean` (ERC20 over `msg.sender`, `Tally`); Coin's `send` and
ERC20's `transfer` (the debit and the credit to two keys that may be equal)
do not, as in the benchmark files.

**Still open.** The diamond (no revert) over reachable states (decision 6
of the earlier draft, `ValidR`); the invariant under callbacks (`ValidC`);
a quantified invariant as an `Invariant C`; `sol_decide` on `old`, `net`
and `book` (outside `Fml.inL`); the benchmarks' clauses over `net(a)`
(EtherWallet, Purchase, SimpleAuction), not yet tried.

## The corpus's concretized rows

`tests/solkey/expected.tsv` has **23** rows whose reason says
"concretized". For each, `scripts/solkey-port.mjs` (rule 2) replaced
`require(x == 5 && …)` on parameters with `uint x = 5;`. By rule 3, a
storage bound became pushes.

| Contract | # | Functions |
|---|---:|---|
| TestSuite | 14 | `additionStorageWrite`, `storagePushComplexReceiverNonsimpleArg`, `requireGuardBox`, `storageFieldWriteRhsCapture`, `storageIndexCopyValue`, `storageIndexDeleteNseIndex`, `storageIndexReadMappingStoreRoot`, `storageIndexReadNseIndex`, `storageIndexWriteNseChain`, `storageMatrixNseIndex`, `storageRootWriteRhsCapture`, `unaryMinusSimple`, `localArithmeticInRange`, `testCopyIntoMappingEntry` |
| SolcExpressions | 4 | `ternaryNestedOuterHigh`, `ternaryNestedOuterLow`, `ternaryNestedInnerHigh`, `ternaryNestedInnerLow` |
| SolcControlFlow | 5 | `ternarySelectsFirstMemorySource`, `ternaryIntoMemoryTarget`, `ifElseSelectsMemorySource`, `ternarySelectsValueByFlag`, `nestedIfElseSelectsBranch` |

Pinned verdicts: 17 `proved`, 3 `evaluated`, 3 `unsupported`. These pins
predate the syntax fixes, because the corpus has not been regenerated (see
"Still open" in `docs/kernel-port.md`).

**The symbolic form.** These are assert obligations, so the box would be
vacuous and the obligation stays a diamond:

```
⊨ D ∧ R ∧ pre → ⟨ body ⟩ true
```

- `pre` is the conjuncts that were dropped, bounds included
  (`1 < values.length` instead of the pushes).
- `R` gives the ranges.
- `D` is the **definedness** of each storage word the body reads or writes
  (`alice.age == alice.age`, `balances[i + 1] == balances[i + 1]`). An
  equation holds only when both sides are defined, and a write succeeds
  exactly where a read of the same path does (`save_ok_iff_find_ok`). This
  is decision 6 restricted to the paths in play, which the script can
  compute.
- Proved by `sol_symex; sol_decide`.

Of the 23 rows:

- **17 fall inside the fragment.** These are the 11 TestSuite storage and
  local rows (with the bounds as `pre`, `storageIndexCopyValue`,
  `storageIndexReadNseIndex` and `storageMatrixNseIndex` have no push left)
  and the 6 `ternary*`/`nestedIfElse*` rows, which touch locals only.
- **6 stay concretized:**
  - a real `push`: `storagePushComplexReceiverNonsimpleArg`;
  - a storage copy: `testCopyIntoMappingEntry`;
  - memory: `ifElseSelectsMemorySource`, `ternarySelectsFirstMemorySource`,
    `ternaryIntoMemoryTarget`;
  - an `int` elaboration failure: `unaryMinusSimple`.

## Plan

| Stage | Scope (files) | Risk |
|---|---|---|
| **S1 Symbolic corpus** | `scripts/solkey-port.mjs` (rules 2 and 3 emit `D ∧ R ∧ pre → ⟨…⟩ true` for the 17 rows), `Corpus/Basic.lean` (the obligation form beside `Diamond`), `tests/solkey/expected.tsv`, `docs/corpus-parity.md`. | Low. The risk is `sol_decide`'s heartbeats on longer bodies. Best done together with regenerating the corpus. |
| **S2 Specs and obligations** (built 2026-09-28, with S4's `Fml.all` and S5's `old`: see Decisions) | `Syntax.lean` (`FunSpec`, `Contract.inv`, the `contract!{}` clauses, `\old`/`\result` in `RawExpr`), `Calculus/Notation.lean` (`spec[C]{f}`: ranges, snapshot updates, the call, skolemizing positive `\forall`), `Semantics/Callback.lean` (`Invariant` from `Contract.inv`). Examples: a new module `Examples/Specs` with Counter, SimpleStorage, Mapping, NestedMapping, `Coin.mint` without `msg.sender`, the invariant at the initial store. | Medium. The elaborator is the only new trusted-looking part, and the kernel re-checks its output. |
| **S3 Benchmark port** | `scripts/solkey-port.mjs` reads `benchmark/*.sol`; `tests/solkey/expected.tsv` gets a status `specified`; `docs/corpus-parity.md`. Coin and ERC20 after wave 1's `msg.sender`/`msg.value`. | Low to medium. It depends on wave 1 (events, errors, `return`). |
| **S4 `Fml.all`** | `Update.lean`, `Calculus/Logic.lean`, `Calculus/Symex.lean`, `Calculus/Quote.lean`, `Calculus/Notation.lean`, `Calculus/Decide.lean`, `Calculus/DecideComplete.lean`, `Semantics/Callback.lean` (`Invariant.closed`). Unlocks SimpleAuction's invariant and the loops' quantified invariants (`docs/loops.md`, L5). | High. Completeness stops at `grind`'s instantiation. |
| **S5 Whole-storage `\old`** | `Update.lean` (a storage-valued snapshot term), the quoters, `Calculus/Decide.lean` (a second base storage that reduces to the initial one). Only if an `\old` under an unskolemizable quantifier turns up. | Medium to high. |
| **S6 Diamond specs** | `ValidR` over reachable states: `Typing/Constructibility.lean`, `Typing/Storage.lean` (the layout as constraints), `Calculus/DecideComplete.lean`. | High. |
| **S7 With callbacks** | Per-function `ValidC` with `ProvesC` (`Calculus/Callback.lean`). It needs a `ProvesC` strategy first, and a term over `net` for the ledger clauses. | Medium to high. |

S1 and S2 are independent and can run in parallel. S2's skolemization
covers every benchmark `\forall`, so S4 is needed only for invariants and
`requires`.
