# The stipend cost rule (decision G06 Q3)

Lane `lane-precompiles`, checkpoint 4. The module is
`Solidity/Stipend/Rule.lean`. It reads the scoped source AST
(`Solidity/Syntax/Scoped.lean`) and changes nothing in it.

## The decision

[solidity-scope.md, second round](../solidity-scope.md#second-round-2026-10-29),
G06 Q3: a compiler-independent source cost rule decides which
`receive`/fallback bodies fit the 2300-gas stipend of `transfer`/`send` to
an instance of the system.

- The source fails the payment for every other body.
- The compiler is proved to fit every admitted body, assuming cold
  (EIP-2929) access costs.
- For a body the rule rejects, the compiled payment must fail too
  (compiler-enforced).

G06 states the rule as `StipendRule Body` with `fits`, and the first half
of the compiler's duty as `StipendRule.Fitted`
([roadmap-g06-evm.md](roadmap-g06-evm.md), D22, B28).

## The rule

`Stipend.rule C : StipendRule (Body C)`. A `Body C` is a program from the
empty frame. `progCost` gives a body's cost, or `none` when the rule
rejects it outright:

| Admitted, with a cost (one unit per node and statement) | Rejected outright (`none`) |
|---|---|
| `declLocal`, `assignLocal` | any storage read or write (`assign`, `push`/`pop`, `delete`, `Val.read`, `Val.len`); `opAssign`/`incDec` even on locals (conservative) |
| `require`, `assert`, `revert`, `revertData` with literal parts | memory objects and reads (`declMem`, `assignMem`, `readMem`, `mlen`, …), `hash` |
| `ite` (condition plus the costlier branch), `block` | `transfer`, `send`, `tryCall`, `catchData` |
| internal `call` of a non-recursive function with no or one value return (arguments plus body) | `loop`, `callRec`, storage aliases (`rebind`, `declStorage`, storage/memory arguments), receiver calls, calls returning memory, an alias or a tuple |
| values over literals, locals and the environment keys, with `binop`, `unop`, `?:`, `addmod`/`mulmod` | `**` (`EXP` costs 50 gas per exponent byte) |

A body fits when `unit · cost + reserve ≤ 2300`. The model `osakaCold` has
`unit = 50` and `reserve = 300`, so a body fits when its cost is at most
40 units (`fits_iff`).

Why:

- **Storage.** Under cold costs one `SLOAD` is 2100 gas. EIP-2200's sentry
  makes every `SSTORE` fail at 2300 gas or less remaining, so a storing body
  can never succeed on Osaka with any compiler.
- **The environment keys** (`msg.sender`, `msg.value`, `block.timestamp`,
  `address(this)`, `address(this).balance`) are warm opcodes of 2–5 gas.
- **The constants** are generous per node: a checked addition with its
  overflow test is about 40 gas in solc's legacy output. The reserve covers
  the entry, the dispatch and the return.
- **They are definitional.** Changing them changes the source semantics, so
  G43 proves the compiler fits them; it does not retune them.

### Examples and non-examples (all proved)

- `empty_fits`: `receive() external payable {}` (cost 0).
- `requireValue_fits`: `require(msg.value != 0);` (cost 4).
- `requires_ten_fits` and `requires_eleven_not_fits`: ten copies of that
  `require` fit (40 units) and eleven do not (44 units). `requires_cost`
  gives their cost, `4·n`.
- `transfer_not_fits`: a body that pays.
- `loop_not_fits`: a loop, however small.
- `assign_not_fits`: any storage write.
- `read_not_fits`: any storage read.
- `pow_not_fits`: any `**`.
- `not_fits_cons`: a body is rejected whenever its first statement is.

Axiom pins: `fits_iff` and `requires_eleven_not_fits` depend on
`[propext, Classical.choice, Quot.sound]`.

## The compiler obligation (G43)

`Stipend.Obligation C gasUsed failsUnderStipend` is the conjunction of two
parts:

- **`(rule C).Fitted pinned gasUsed`** (G06): every admitted body compiles
  to code whose worst-path gas is below the stipend. `gasUsed` is measured
  with cold access costs and with EIP-2200's sentry counted; an admitted
  body has no `SSTORE`, so the sentry never fires.
- **`Enforced (rule C) failsUnderStipend`**: every rejected body fails when
  entered with at most the stipend. A compiler meets it with an entry guard
  in the compiled `receive`/fallback that reverts when `GAS` is at most the
  stipend. A full-gas `call{value: …}("")` is unaffected; a low-gas one
  fails, which "Follow-up — nested-frame failures" already allows.

`gasUsed` and `failsUnderStipend` are parameters. G43 instantiates them
with its compiled code's run.

## Review

The finder review (see [precompiles.md](precompiles.md#review)) found two
holes, both fixed: `**` was charged one unit (now rejected,
`pow_not_fits`), and an internal call's memory or alias return was ignored
(now only no or one value return, `retOk`). It confirmed the 4-unit
`require`, the 40-unit bound and the examples.

## Handoff (checkpoint 4)

- **Theorems:** `fits_iff`, `not_fits_cons`, and the examples and
  non-examples above. There is no `sorry` and no new axiom.
- **Premises:** none.
- **Checks:** `lean_diagnostic_messages` is clean on
  `Solidity/Stipend/Rule.lean`.
- **Remaining:**
  - the source semantics does not yet consult `rule` when a payment
    reaches an instance of the system (G43/G47);
  - `Obligation` is stated, not proved: it is G43's;
  - the rule is conservative: a body with one cold `SLOAD` that solc might
    fit is rejected, so the compiler must make it fail.
