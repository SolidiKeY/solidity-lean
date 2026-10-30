# Source soundness (lane V04b)

Lane `cloud/roadmap-l3-20261030/lane-soundness`: integrate the source
semantics of lane-semantics ([source-s05.md](source-s05.md)) with master's
G13 checker, then type soundness of the interpreter: preservation and
gap-relative progress (user decision 2026-10-30).

## Checkpoint 1: integration

The merge of `cloud/roadmap-l2-20261029/lane-semantics` into this branch
(base `8445c3f`, a `--no-ff` merge) conflicted only in shared lists
(`Solidity.lean`, `TrustAudit.lean`, `docs/coverage-plan.md`,
`docs/module-map.md`); every line of both sides is kept.

G13's checker (`Solidity/Frontend/Static/Infer*.lean`) was written against
S01 before lane-semantics changed its typing. Each break listed in
[source-s05.md's Handoff](source-s05.md#handoff-s05) is fixed:

| Checker part | Change |
|---|---|
| `Infer.lean` `constRes` | checks the third premise `e.hexLen? = none` of `Typed.const` |
| `Infer.lean` `litRes` | one `litBytes` derivation when `hexLen? = some len` (type `hexConst n.value len`); the 32 `fixedBytes` typings and the `lens` table are gone |
| `Infer.lean` `binPair` | `shift`/`exp` read `τa.shiftTy` |
| `Infer.lean` `common?` users | unchanged code; results follow `STy.common?` |
| `Infer.lean` new arms | `member` and `LVal.member` (`structMemberRes`), `structNew` (in `callIdentRes`), `extCall`, `transfer`, `send` (`memberCallOne`, `payRes`, `payOne`), `extCallValue` (`valueCallOne`), `abiEncode` (`abiRes`), `assignCopy` (in `assignRes`) |
| `InferStmt.lean` | `.expr` checks `(C.inModifier && e.isUnderscore) = false`; `.retTuple` only for a non-empty slot list; `rethrow` reads `rethrowVar? body = some d` |
| `InferComplete.lean`, `InferStmtComplete.lean` | completeness for every new constructor; `hasType_iff`, `stmtOK_iff`, `itemsOK_iff` proved again, and `wellFormed_iff` (`WellFormedCheck.lean`) unchanged |
| `InferExamples.lean` | `zero_types`: `0x00` has one type; `hexCall_typed` (below) |
| `Standalone.lean` | its `STy.isConstTy` clashed with S02's; renamed `STy.isConstOnly` (numeric constants, `hexConst` included, and string literals) |

**Receivers and call options.** `infer` stays structural over `Syn`: the
call rules need the typing of a callee's subterms (`c` in `c.f(…)`, `c`
and `v` in `c.f{value: v}(…)`), so `Res` has three auxiliary results that
no typing or lvalue projection returns: `recv` (a typed receiver, at
`a.m`), `named` (a typed call option, at `.namedArg x v`) and `withValue`
(both, at `.callOptions`). `callRes` takes the callee's results and
selects the rule by the callee's syntax.

**Overload deviation removed.** lane-static recorded that S01's per-typing
uniqueness gave `f(0x01)` with `f(uint8)` and `f(bytes1)` two derivations,
where solc reports an ambiguity. Under solc's literal typing (Q1) `0x01`
has the single type `hexConst 1 1`, which both overloads accept, so
`callInternal`'s uniqueness premise fails: `hexCall_typed` now states that
the call has no type ([frontend-static.md](frontend-static.md) updated).

**Controls** (`InferExamples.lean`, kernel `decide`; contract `K` with a
struct `P { uint256 a; }`, `g(uint256) external payable`,
`h(uint256) external`):

| Theorem | Witness | Negative control |
|---|---|---|
| `member_checked` | `p.a : uint256`, one lvalue | `p.b` untyped |
| `structNew_checked` | `P(x) : P memory` | `P()` untyped |
| `extCall_checked` | `k.g(x)`, `k.h(x)` | `k.z(x)` untyped |
| `extCallValue_checked` | `k.g{value: x}(x)` | `k.h{value: x}(x)` (not payable), `k.g{gas: x}(x)` |
| `pay_checked` | `q.transfer(x)`, `q.send(x)` on `address payable` | both on `address` |
| `abiEncode_checked` | `abi.encode(x) : bytes memory` | `abi.encode(p)` (a struct) |
| `zero_types` | `0x00` has exactly one type | — |
| `hexCall_typed` | — | `f(0x01)` ambiguous, refused |

Pins: `#guard_msgs` `#print axioms` for the new controls in
`InferExamples.lean`; `TrustAudit.lean` has a checkpoint-1 block (the four
decision theorems and the six controls).

lane-parse's modules (`Solidity/Frontend/Checked/`) do not import S01's
typing and are unaffected; they build in the full gate.

### Gates (checkpoint 1)

See the Handoff.

### Review (checkpoint 1)

See the Handoff.

## Handoff

Kept current at every checkpoint.

| Checkpoint | Status | Theorems |
|---|---|---|
| 1 Integration | in progress | `hasType_iff`, `stmtOK_iff`, `itemsOK_iff`, `wellFormed_iff`; controls above |
| 2 Preservation | not started | |
| 3 Gap-relative progress | not started | |
| 4 Close gaps | not started | |
| 5 `Failures`, `SourceSpec` | not started | |
