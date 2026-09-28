# Function specifications: design

Per-function `requires`/`ensures` with `\old` and `\forall`, the contract
invariant, and proof obligations that `sol_symex` + `sol_decide` discharge
over symbolic parameters. This is a design and a plan; nothing here is built
yet. Read `docs/kernel-port.md` ("Still open", "Decisions") first.

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
  transfer. It cannot read the ledger, since no term does. `ValidC` and
  `ProvesC` (`Calculus/Callback.lean`) use it for callbacks
  (`Examples/Callback.lean`).

So the procedure is in place. What is missing is the **front end** that
states the obligation, plus `\old`, `\forall`, range facts, and a
precondition that makes a diamond meaningful.

## Decisions

**1. A spec is data in the `FunDecl`, raw, elaborated where it is used.**

- Shape: `FunDecl.spec : FunSpec` with
  `requires ensures : List RawExpr` and `skip : Bool`.
- Contract-level `invariant` clauses go in `Contract.inv : List RawExpr`.
- Why raw: a `Contract` cannot hold an `Fml C`, because `C` is `Fml`'s
  index. This is the same reason the body is kept as read (Decisions row
  "Where a callee's body lives").
- Syntax in `contract!{ }` (`Syntax.lean`): JML-style keywords between the
  header and the body, for example
  `function dec() requires count >= 1 ensures count == \old(count) - 1 { … }`,
  and `invariant e;` among the state variables.
- `scripts/solkey-port.mjs` translates `@custom:key` lines to this syntax.

**2. The obligation is a box validity, as solkey's.**

- `spec[C]{f}` (a new macro beside `dl[C]{}`, `Calculus/Notation.lean`)
  elaborates to:

  ```
  ⊨ R ∧ Î ∧ pre → {o₁ := ⌊e₁⌋} … {oₖ := ⌊eₖ⌋} [ res = f(x₁, …, xₙ); ] (Î ∧ post)
  ```

  - `x₁ … xₙ` are the parameters as free locals, under their declared
    names.
  - `res` stands for `\result`.
  - `Î` is the invariant, `pre`/`post` the conjoined clauses, lowered by
    the `dl` reader.
  - `R` gives each parameter's **range** (`0 <= x && x <= 2^256 - 1`,
    `b == b` for a `bool`). A free local ranges over every value,
    including a halt, and a checked operator on it halts outside its type's
    range.
- The call has simple arguments, so `functionBodyExpand` fires at once. The
  callee writes only its fresh copies of the parameters, so `post` reads
  the parameters' pre-state values. That is solc's value semantics, and
  `\old(x)` is simply `x`.
- **Why the box.** Under `⊨`, a diamond over a storage write is false in
  the states that lack the root (`Calculus/Close.lean`, first gap), so it
  needs a layout premise (decision 6). The box needs nothing and matches
  solkey.
- **The limit.** Lean's box accepts every halt (Decisions row
  "Modalities"). A failing `assert` inside a box-specified body therefore
  proves nothing, and "does not revert" is the diamond's job.

**3. `\old(e)` is a snapshot local, taken by an update in front of the modality.**

- Each occurrence gets a fresh local `oᵢ := ⌊eᵢ⌋`.
- This is exact: an update reads its right-hand side in the state it is
  applied in, which is the pre-state.
- It stays inside `sol_decide`'s fragment: one element per update, and a
  read of the starting storage (`LFml.initOnly`).
- It applies when `eᵢ`'s free names are parameters, state variables, or
  quantified variables that decision 4 skolemizes. That covers every
  benchmark clause except those over `net`.
- **Rejected for now:** solkey's whole-storage snapshot `old := storage`.
  `STerm` has no storage-valued variable, so it would take a new
  constructor, an arm in every quoter (the "Sharp edges" section of
  `docs/kernel-port.md`), and a second base storage in `Decide`. It is
  needed only for an `\old` under a quantifier that cannot be skolemized.
  That is stage S5.

**4. `\forall` is skolemized where it is positive, and a real quantifier where it is not.**

- **Positive position** (an `ensures` conjunct, or the right of `→`):
  `\forall address a; P` becomes a fresh free local `a` with its range
  guard, `range(a) → P`. This is sound and complete, because `⊨` already
  quantifies over `a`, and `a` is fresh, so no program writes it. Every
  `\forall` in the benchmark's `ensures` is of this kind (Coin, ERC20).
  No new constructor is needed.
- **Negative position** (`requires`, the invariant assumed on entry, under
  `¬`): this needs **`Fml.all (x : Var) (p : PrimTy) (φ)`**, with
  `holds σ (.all x p φ) ↔ ∀ v : p, holds (σ.setEnv x v) φ`. The
  consequences:
  - `Fml.vars` must exclude the bound variable, so `Invariant.closed`
    means "no *free* local";
  - `holds_frame`, the quoters and the `dl` reader each gain one case;
  - `Fml.stepAt` steps under the binder;
  - `Decide`'s reduction commutes with `∀` state by state, so
    `Fml.valid_iff_reduce` survives;
  - the closing step, however, has to instantiate a hypothesis `∀ v, …`:
    `omega` cannot, and `grind` does so heuristically. The procedure is
    therefore **not complete** above this line.
- `\exists` is `¬∀¬`.

**5. The contract invariant is assumed on entry and owed on exit.**

- `Î` in decision 2 is `Contract.inv`, elaborated to an `Invariant C`.
- Under callbacks the obligation is `ValidC I` of the same formula, proved
  with `ProvesC`. Two items in "Still open" of `docs/kernel-port.md` apply:
  `ProvesC` has no strategy, and a branch or a call around a transfer has
  no rule.
- Lean can also establish what solkey never does: the invariant at the
  initial store (`holds State.*Store Î`, decided by the kernel as the
  corpus is). That is a `docs/solkey-feedback.md` item.
- **Blocked:** an invariant or `ensures` over `net` (Purchase's invariant,
  EtherWallet's `ensures net(owner) == …`), because no term reads the
  ledger. `msg.sender` and `msg.value` (Coin, ERC20) wait for wave 1's
  environment values, which also supply solkey's booking of `msg.value`
  before the call.

**6. The diamond (no revert) comes later, as validity over reachable states.**

- `ValidR C φ` would mean true in every state whose storage is reachable
  for `C`, which `reachable_iff` (`Typing/Constructibility.lean`)
  characterises.
- `⊨ φ` implies `ValidR C φ`.
- Deciding it takes the layout's types as extra constraints in
  `DecideComplete`: a read at `alice.age` shows a word, and one at
  `balances` shows a mapping. Realizability would then have to produce a
  canonical and tight storage.

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
| **S2 Specs and obligations** | `Syntax.lean` (`FunSpec`, `Contract.inv`, the `contract!{}` clauses, `\old`/`\result` in `RawExpr`), `Calculus/Notation.lean` (`spec[C]{f}`: ranges, snapshot updates, the call, skolemizing positive `\forall`), `Semantics/Callback.lean` (`Invariant` from `Contract.inv`). Examples: a new module `Examples/Specs` with Counter, SimpleStorage, Mapping, NestedMapping, `Coin.mint` without `msg.sender`, the invariant at the initial store. | Medium. The elaborator is the only new trusted-looking part, and the kernel re-checks its output. |
| **S3 Benchmark port** | `scripts/solkey-port.mjs` reads `benchmark/*.sol`; `tests/solkey/expected.tsv` gets a status `specified`; `docs/corpus-parity.md`. Coin and ERC20 after wave 1's `msg.sender`/`msg.value`. | Low to medium. It depends on wave 1 (events, errors, `return`). |
| **S4 `Fml.all`** | `Update.lean`, `Calculus/Logic.lean`, `Calculus/Symex.lean`, `Calculus/Quote.lean`, `Calculus/Notation.lean`, `Calculus/Decide.lean`, `Calculus/DecideComplete.lean`, `Semantics/Callback.lean` (`Invariant.closed`). Unlocks SimpleAuction's invariant and the loops' quantified invariants (`docs/loops.md`, L5). | High. Completeness stops at `grind`'s instantiation. |
| **S5 Whole-storage `\old`** | `Update.lean` (a storage-valued snapshot term), the quoters, `Calculus/Decide.lean` (a second base storage that reduces to the initial one). Only if an `\old` under an unskolemizable quantifier turns up. | Medium to high. |
| **S6 Diamond specs** | `ValidR` over reachable states: `Typing/Constructibility.lean`, `Typing/Storage.lean` (the layout as constraints), `Calculus/DecideComplete.lean`. | High. |
| **S7 With callbacks** | Per-function `ValidC` with `ProvesC` (`Calculus/Callback.lean`). It needs a `ProvesC` strategy first, and a term over `net` for the ledger clauses. | Medium to high. |

S1 and S2 are independent and can run in parallel. S2's skolemization
covers every benchmark `\forall`, so S4 is needed only for invariants and
`requires`.
