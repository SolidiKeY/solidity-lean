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
| `Standalone.lean` | its `STy.isConstTy` clashed with S02's; renamed `STy.isConstOnly` (the `hexConst` case it adds is unreachable: `standalone` sends a hexadecimal literal to its mobile integer type). Behaviour change from Q1: `abiArgTys` of `0x00` went from 33 types to one (`uint8`), solc's |

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
| `member_checked` | `p.a : uint256`, one lvalue, `p.a = x` | `p.b` untyped |
| `structNew_checked` | `P(x) : P memory` | `P()` untyped |
| `extCall_checked` | `k.g(x)`, `k.h(x)` | `k.z(x)` untyped |
| `extCallValue_checked` | `k.g{value: x}(x)` | `k.h{value: x}(x)` (not payable); `k.g{gas: x}(x)` (unmodelled option, recorded gap: solc accepts it) |
| `pay_checked` | `q.transfer(x)`, `q.send(x)` on `address payable` | both on `address` |
| `abiEncode_checked` | `abi.encode(x) : bytes memory` | `abi.encode(p)` (a struct): S01 refuses, solc accepts (deviation below) |
| `zero_types` | `0x00` has exactly one type | — |
| `hexCall_typed` | — | `f(0x01)` ambiguous, refused |

**Deviations found by the review** (S01's, not the checker's; the checker
decides S01 faithfully):

- `abi.encode`/`encodeWithSelector`/`encodeWithSignature` arguments are
  S01's `STy.abiArg`: value types, integral constants, string literals and
  memory `bytes`/`string`. solc 0.8 (ABI coder v2) also encodes structs,
  arrays and calldata `bytes`/`string`. `encodePacked` of a constant
  (`abi.encodePacked(1)`), which solc refuses (7279), is accepted (recorded
  in [source-s02.md](source-s02.md)).
- Call options other than a single `value` (`gas`, `salt`, several
  options) have no type (recorded S02 gap).

**Two inference engines.** lane-semantics' `Typed.infer`
(`Solidity/Source/Infer.lean`) returns one derivation per expression for
the elaborator; it is sound but has no completeness proof and makes fixed
choices where rules overlap (`assign` before `assignCopy`, `retTuple`
before `retVal`). G13's `infer` enumerates every derivation and is
complete; by `Typed.unique` (and `StmtD.unique`) both give the same
meaning. Unifying them (the elaborator reading G13's checker) is open.

**Untested here**: `encodeWithSelector`/`encodeWithSignature`, `assignCopy`
and the calldata exclusion of `LVal.member` have completeness proofs but no
kernel control.

Pins: `#guard_msgs` `#print axioms` for the new controls in
`InferExamples.lean`; `TrustAudit.lean` has a checkpoint-1 block (the four
decision theorems and the six controls).

lane-parse's modules (`Solidity/Frontend/Checked/`) do not import S01's
typing and are unaffected; they build in the full gate.

### Gates (checkpoint 1)

- Lean diagnostics clean (language server) on `Infer.lean`,
  `InferComplete.lean`, `InferStmt.lean`, `InferStmtComplete.lean`,
  `InferExamples.lean`, `Standalone.lean`, `UserOps.lean`,
  `WellFormedCheck.lean`, `Consts.lean`.
- Full gate `./run-lean.sh`: see the Handoff for the run on the
  checkpoint's head.

### Review (checkpoint 1)

Finder and skeptic (read-only, no Lean server).

Confirmed and fixed:

- `infer` evaluated `infer a` three times at `a.m` (once each for
  `memberRes`, `structMemberRes`, `recvRes`) and `infer n` once per callee
  result at `.callOptions`: now bound once (`let`).
- `frontend-static.md` still described the overload deviation, "33 types"
  and the speed bound from before Q1, listed `abi.*`, structs and external
  calls as untyped, and kept the overload item open in its handoff:
  updated.
- `member_checked` claimed "assigned" without an assignment: `p.a = x` is
  now part of it.
- The `gas` and struct-`abi.encode` controls were presented as solc
  refusals: they are S01 gaps, now recorded above (and in the docstrings).
- `hexCall_typed`'s name says the opposite of its statement; the name is
  kept (pins, TrustAudit lists) and the docstring says so.
- `isConstOnly`'s description: the real behaviour change (`abiArgTys` of a
  hexadecimal literal) is recorded instead.
- The relation to lane-semantics' `Typed.infer` is recorded above.

Answered (not defects): the auxiliary results `recv`, `named`,
`withValue` never reach `tysOf`/`lvsOf`/`inferTys` (both reviewers);
completeness covers every new constructor, none vacuously (finder);
`f(0x01)` is refused by solc too (skeptic); `extCallValue`'s shape matches
`callRes` exactly (skeptic).

## Handoff

Kept current at every checkpoint.

| Checkpoint | Status | Theorems |
|---|---|---|
| 1 Integration | in progress | `hasType_iff`, `stmtOK_iff`, `itemsOK_iff`, `wellFormed_iff`; controls above |
| 2 Preservation | not started | |
| 3 Gap-relative progress | not started | |
| 4 Close gaps | not started | |
| 5 `Failures`, `SourceSpec` | not started | |
