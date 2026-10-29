# Source semantics S03: statements, modifiers, constructors and calls

Lane V04, checkpoint 3, covering roadmap rows S03.01–S03.04 in
[coverage-plan.md](../coverage-plan.md). Expressions are in
[source-s02.md](source-s02.md).

## Modules

| Module | Content |
|---|---|
| `Solidity/Source/Eval.lean` | `execS`, `execItems`, `forIter`, `runMods`, `callInternal`, `callAddr`, `enterInstance`, `envLoop`, `dispatch`, `pay` (one mutual definition with the expression evaluator) |
| `Solidity/Source/Semantics.lean` | Constructors (`construct`, `collectArgs`, `runInits`, `runCtorBody`), horizons (`firstDone`) |

## S03.01: structured statements

`execS` runs an `RStmt E R M k Γ Γ'` from the locals of `Γ` and returns an
`Out`. A statement either completes normally, with the locals of its output
context `Γ'`, or stops with `break`, `continue` or `return`, carrying the
locals of its input context.

| Construct | Behaviour |
|---|---|
| blocks | end their scope: `Locals.restore` drops the inner locals and checks the remaining context |
| `if` | runs the selected branch |
| `while`, `do … while`, `for` | iterate until the condition fails, `break` or `return`; `continue` re-tests the condition and, in `for`, runs the step |
| `unchecked` blocks | run their items with wrapping arithmetic; a call inside one restores checked arithmetic for the callee |
| `return e`, `return (a, b)` | write the function's return slots, then leave |
| bare `return` | leaves |
| falling off the end of a body | the return slots' values are the result, as solc compiles it |
| `emit` | evaluates the arguments and records a log (not an observation) |
| `revert E(…)`, the canonical rethrow | revert with their data |

Out-of-place `break` or placeholders are `stuck`; S01's statement contexts
exclude them.

## S03.02: modifiers and constructors

**Modifiers.** `runMods` runs a body under its modifier invocations,
outermost first. A modifier's arguments are evaluated in the function's
locals. In its body, each `_` runs the remaining modifiers and the
function body (`Ph`), any number of times, including zero. The two
pipelines differ:

- under legacy, every `_` shares the function's parameter and return
  slots;
- via IR, each `_` starts from the parameters at entry and fresh zero
  return slots, and the last invocation's returns are the result.

This is taken from the pinned upstream tests
`semanticTests/modifiers/function_modifier_multi_invocation.sol` and
`function_modifier_multi_invocation_viair.sol`: `f(true)` is `2` under
legacy and `1` via IR (`modifier_twice_legacy`, `modifier_twice_viaIR`,
`modifier_once`). [solc-alignment.md](../solc-alignment.md#modifier-placeholder-frames)
says that via IR "incoming return slots are passed". That contradicts the
upstream test the lane follows, so it is flagged for the owner of that
document.

**Constructors.** `construct` composes a contract's linearization `L`,
most derived first. Base-constructor arguments are collected derived to
base: each argument list is evaluated in the parameters of the most
derived constructor that gives it. A base that needs arguments and is
given none makes deployment revert. The order then depends on the
pipeline:

| Pipeline | Order |
|---|---|
| legacy | every contract's initializers, base first, then every constructor body, base to derived |
| via IR | per contract, base to derived: its initializers, then its body |

This is solc's order as recorded in
[solc-alignment.md](../solc-alignment.md). Control: `ctor_order_legacy`
gives `1` and `ctor_order_viaIR` gives `2` (`B is A`, `b = a` initialized
around `A`'s body `a = a + 1`). Virtual calls in a base constructor
dispatch to the most derived contract, because `Fr.contract` is the
deployed contract.

## S03.03: call frames

| Call | Behaviour |
|---|---|
| internal | `callInternal` dispatches virtually: `Glob.dispatchFn` takes the first scope of the instance's linearization that declares the function with the same parameters. It binds parameters and zeroed return slots, runs modifiers and body in a checked context, and returns the return slots. Memory and the message context are shared with the caller. Free and library functions are called directly. |
| external, to an instance of the system | `callAddr` and `enterInstance`: the value moves first (`ExecState.transfer`), then a new frame (`Fr`: `this`, sender, value, static flag, depth + 1) with fresh memory and a journal mark. `dispatch` selects the function by selector, refuses value to a non-`payable` one, decodes the arguments and encodes the returns. Empty data selects `receive`, then `fallback`; otherwise the call reverts. On a revert, `rollbackTo` undoes the frame's journal and logs and the caller re-raises the data. |
| external, to another account | the G01 events: `Event.call`, then the environment's moves from the callee strategy (`envLoop`). `answer` ends the call. `credit` credits an instance and asks again. `reenter` runs a callback into any instance at any depth, records `reentered`, and asks again. |
| call-depth limit | at depth 1024 a call fails with empty revert data (G01 follow-up "nested-frame failures") |
| static frames | refuse writes and value |
| `transfer`, `send` | calls with no data: `transfer` reverts on failure, `send` returns `false` |

## S03.04: composition, finite traces and divergence

### Horizons

Every function of the interpreter takes a horizon `n`, spends one unit
per nested evaluation, and returns `Halt.timeout` at 0. The horizon is
not a semantic restriction. The semantics of an execution is the least
horizon at which it completes (`firstDone`), and an execution that
completes at none diverges:

- `firstDone_mono`: a completion within horizon `n` is the completion at
  every larger horizon, by construction;
- `firstDone_spec`: what it finds completes, within the bound;
- `firstDone_none_iff`: an execution diverges exactly when every horizon
  times out.

No inlining depth, loop bound or recursion bound limits what completes.

Horizon independence (completing at `n` and at `m` with the same result)
is not proved in general. It is checked on a control (`horizon_stable`,
horizons 20 and 40), and a short horizon completes nothing
(`horizon_short`). The least-horizon definition makes the semantics
well-defined without it; the general theorem is a remaining obligation.

### Determinism

The semantics is a function of the elaborated program, the session
environment and the horizon, so it is deterministic by construction.

### Constructor coverage

The interpreter's matches on `RStmt` and `RItems` have no wildcard; the
ledger is in [source-s05.md](source-s05.md).

## What S03 does not do

These items are also listed under `limitations:`.

- **Gas and resource failures.** User decisions: any external frame may
  fail with a revert its caller sees, and any transaction may run out of
  gas. These are not choice points of this semantics; only the depth
  limit fails. G01's `Failures`/`withFailures` interface is not
  instantiated.
- **The stipend rule** (G06 Q3). Payments run `receive` with no stipend
  limit.
- **`fallback` with parameters.** `stuck`.
- **Calls to precompile addresses.** Treated as environment accounts;
  G01 says they behave as their definitions.
- **Library calls through `DELEGATECALL`.** External library functions
  are not modelled; internal and library calls run as internal calls.
- **`try`/`catch` and `new`.** Untyped in S01, so absent.
- **Horizon independence.** Not proved generally (see Horizons).

## Review

The reviews are recorded in [source-s05.md](source-s05.md#review).

## Handoff (S03)

Theorems: `firstDone_mono`, `firstDone_spec`, `firstDone_none_iff`,
`modifier_twice_legacy`, `modifier_twice_viaIR`, `modifier_once`,
`ctor_order_legacy`, `ctor_order_viaIR`, `horizon_stable`,
`horizon_short`, `revert_rolls_back_transient` (a reverted inner frame
restores storage and transient storage).

For S04.04: `enterInstance`, `dispatch`, `mark`/`rollbackTo` and
`construct`.
