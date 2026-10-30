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

## Checkpoint 2: preservation (partial)

**What a well-typed run-time state is.** Most of the state is typed by
construction (S04.01): a value of type `τ` is a `Val D τ` (ranges, enum
bounds, byte lengths inside), locals are `Locals D Γ`, storage and
transient storage are `Storage D L` over the layout `Env.cellTy`, every
memory object carries its type, and calldata objects too. So
preservation of those parts holds by construction for every step. What
is not intrinsic is where **references** point (`Solidity/Source/WellTyped.lean`):

| Predicate | Meaning |
|---|---|
| `Val.RefOK E H v` | a `memory` reference of type `τ` names an object the heap typing `H` gives type `τ`; a `storage` reference of type `τ` a path with `Env.pathTy p = some τ`; no value is a `calldata` reference (the semantics creates none) |
| `DataOK`, `DataListOK`, `RValOK`, `RValsOK`, `LocalsOK` | the same for memory contents, run-time values and locals; all monotone in `H` (`HeapTy.Le`) |
| `HeapOK h` | every object of the heap agrees with the heap's own typing |
| `StOK E H s`, `EMOK` | a well-typed machine state (heap well typed, typing extending `H`) and interpreter state (with the locals) |

**Hoare triples** (`Solidity/Source/Hoare.lean`): `Hoare P m Q X` over
`EM`, with a rule for every combinator the interpreter uses (`pure'`,
`bind`, `halt'`, `lift'`, `st'`, `setSt'`, `modSt'`, `locals'`,
`setLocals'`, `sub'`, `attempt'`, `dite'`, `ite'`, `conseq`,
`cases_pre`). Preservation of an invariant `I` is a triple with `I` in
the pre- and postconditions and the halt condition; progress is one whose
halt condition is `NotStuck`.

**Proved for the memory operations** (preservation and, where they read,
progress): `alloc_ok` (the state stays well typed, the new address has the
object's type), `allocRef_ok` (the new reference agrees), `heapPut_ok`
(a write of agreeing contents keeps the state well typed; `stuck` only at
an address of another type), `heapObj_ok`, `heapAt_ok` (a read at the
type the heap typing gives is never `stuck` and returns agreeing
contents), `storRef_ok`; the heap facts `HeapOK.alloc`, `HeapOK.write`,
`Heap.alloc_le`, `Heap.alloc_ty`, `HeapOK.empty`.

**Not proved**: the triple for every interpreter function (`evalE` …
`dispatch`, deployment, transactions, callbacks). The approach is the one
`Solidity/Source/Horizon.lean` uses for horizons: a structure of triples,
one per function, at horizon `n`, and one step lemma per function. The
census below lists, per `stuck` site, the invariant the step lemmas need.
Two facts the invariant must handle, found while setting it up:

- an external call runs the callee in a fresh heap (`enterInstance`) and
  restores the caller's heap afterwards, while `St.fnLocals` keeps the
  caller's modifier locals: the invariant on `fnLocals` must hold only
  for the frame that runs modifiers, not across frames;
- `bytes(s)` of a `string memory` keeps the pointer, so a `bytes memory`
  reference may name a string object: `RefOK` must treat `bytes` and
  `string` objects of one location as compatible (the census, item
  "bug" below, fixed in the semantics).

## Checkpoint 3: gap-relative progress (partial)

**Value layer** (`Solidity/Source/ValueProgress.lean`). Each pure value
operation is never `stuck` on operands in its domain, and every elaborated
term stays in the domains:

| Theorem | Statement |
|---|---|
| `binVal_ok` | `binVal` is not `stuck` for an operator of `arith` at a numeric type, of `bit` at a bit type, of `logic` at `bool` (`BinOp.FitsAt`) |
| `cmpVal_ok` | `cmpVal` is not `stuck` for a comparison at an ordered type or one with equality (every such value has a key, `Val.key_isSome`) |
| `shiftVal_ok`, `intPow_ok` | shifts at `int`/`bytesN`, powers at `int` |
| `unaryVal_ok`, `incDecVal_ok`, `amount_ok` | `-`, `!`, `~`; `++`/`--` at a numeric type; shift amounts and exponents |
| `intRes_ok`, `fixRes_ok`, `intBin_ok`, `fixBin_ok`, `bytesBin_ok` | the arithmetic below them |
| `binOpName_admits` | the operator `toR` reads off a binary expression is one its rule kind admits (`BinKind.admits`) |
| `Typed.toR_opsOK`, `StmtD.toR_opsOK`, `ItemsD.toR_opsOK` | every operator node of an elaborated expression, statement or block is in its operation's domain (`RExpr.OpsOK`) |
| `Elaborated.body_opsOK`, `Elaborated.inits_opsOK` | so is every body, modifier argument, constant and initializer of an elaborated unit |

| `convVal_ok`, `constVal_ok`, `mkInt_ok`, `mkFix_ok`, `FixTy.scaled_mem`, `Q.toFixed?_mem` | implicit conversions of value-type values and of constants are never `stuck` (integer widening, integer to fixed point within solc's bounds, fixed-point rescaling, `bytesN` padding, enums, user-defined value types, contracts, external function types) |

`RExpr` itself does not tie a `binary` node's operator to its type, so
`OpsOK` is the fact a progress proof needs about the elaborated program
at those nodes; with it, the 30 `stuck` sites of `Value.lean` the census
classifies as `shape` are unreachable from an elaborated program, once the
interpreter walk is done.

**Interpreter, value fragment** (`Solidity/Source/ExprProgress.lean`,
`Solidity/Source/StmtProgress.lean`). `NS m` says `m` never halts `stuck`
from any state; `NSP m Q` adds a postcondition on results. Both compose
through the interpreter's binds, `sub`, `lift`, pipelines and matches.

| Theorem | Statement |
|---|---|
| `evalE_valFrag_ns` | evaluating an expression of the **value fragment** (`RExpr.ValFrag`: constants, locals of value type, `this`, unary and binary operators including `&&`/`\|\|`, comparisons, shifts and powers, `? :`, implicit conversions from value types and constants; state variables of value types and values of mappings (nested mappings included) with keyable keys, read; and assignment, compound assignment and `++`/`--` to locals, such state variables and such mapping values) that is `OpsOK` is never `stuck`, at any horizon, from any state |
| `exprNSAt` (`ExprNSAt`: `val`, `pair`, `ref`, `loc`; `val_step`, `pair_step`, `ref_step`, `loc_step`) | the induction on the horizon: expressions, operand pairs, mapping references (`RExpr.MapRef`, with the postcondition `RPost`: a storage reference names a path of its type) and lvalues (`RLVal.IsSimple`, with the postcondition `LocOK`: a local, or a storage cell of value type at its own type with a default) |
| `readAt_ns`, `writeAt_ns`, `Storage.read_isSome`, `keyStep_nsp`, `Val.word_isSome`, `cellTy_key`, `pathTy_key`, `Env.pathTy_go`, `storRef_map_nsp` | storage: a cell of value type at its layout type with a default always reads; a write at the layout type succeeds (or reverts in a static frame); a keyable key is a key step; a mapping value's path has the mapping's value type |
| `convRV_ns`, `getV_ns`, `readLoc_ok`, `writeLoc_ok`, `compound_dom` | its other steps |
| `stmtNS`, `itemsNS` (from `StmtNSAt`, `execS_step`, `execItems_step`, `forIter_step`, by induction on the horizon) | executing a statement or block of the **statement value fragment** (`RStmt.ValFrag`: expression statements, declarations of types with a default, blocks, `unchecked`, `if`, `while`, `do`/`while`, `for` with a simple initializer, `break`, `continue`, `return;` and `return e;` of a value type) in a **body frame** (`BodyFrame nps R Γ`: the locals end in the return slots, then the `nps` parameters, as `callInternal` builds them) is never `stuck`, at any horizon, in any modifier context |
| `BodyFrame.ext`, `Locals.setAt_ok`, `Locals.setAt_ok'` | declarations keep the frame; writing a return slot is never `stuck` |
| `ItemsD.toR_ns` | so is the elaboration of a typing derivation whose image is in the fragment (`OpsOK` from the derivation) |
| `RStmt.ext`, `RItems.ext`, `Locals.restore_ok`, `Out.close_ok`, `Out.up_ok` | ending a scope is never `stuck`: a statement's output context extends its input |

Controls (`Solidity/Source/SoundnessExamples.lean`, kernel `rfl`):
`addSub_ns` (S01's own `a + a`), `cond_ns`/`cond_value` (`true ? 1 + 2 : 0`
evaluates to `3`), `cb_ns`/`cb_value` (S05's `x = x + 1;` on a storage
variable is never `stuck` and takes `x` from 3 to 4), `loop_ns`/`loop_value` (`uint8 i; while (i < 3) { i += 1; }`
is never `stuck` and ends with `i = 3`); negative controls
`badBinary_stuck` (a hand-resolved `true + false` evaluates to `stuck`:
`OpsOK` is needed) and `ret_unframed_stuck`/`ret_unframed_no_frame`
(`return 1;` over locals without a return slot is `stuck`, and those
locals are no `BodyFrame`: the frame hypothesis is needed; with the slot,
`ret_framed_ns`).

The storage side conditions (`E.cellTy d.path = τ`, `E.pathTy d.path =
some τ`, a default for the value type) are checked per expression in the
fragment predicate rather than derived from the elaboration: deriving them
needs the lemma that a resolved state variable is the declaration
`Env.declOf` finds at its path (the census's `stor` class).

**What the fragment leaves out**, in the order a whole-program proof needs
it: `return (a, b)` (`setRets`), the function level (`runMods`: a body's
`break`/`continue` never leave it; `callInternal`: virtual dispatch finds
a body whose locals are the frame `BodyFrame` describes), memory (the `heap` invariant, `WellTyped.lean`), arrays and
structs in storage, internal calls and modifiers (dispatch coherence),
external calls, `emit`, builtins, and the transaction layer (dispatch,
ABI). Each is listed with its sites in the census below.

### The `stuck` census

A read-only census (finder agent, checked against the code) of all 118
`Halt.stuck` sites (`Value.lean` 30, `Machine.lean` 22, `Eval.lean` 61,
`Semantics.lean` 5), by what rules each out for a well-typed elaborated
program:

| Class | Sites | Ruled out by |
|---|---|---|
| shape | 68 | the value's type index plus the `toR` premises (`OpsOK` above for operators; `callTy`, `lengthTy`, `memberTy`, `copiesTo`, key types, `mkRet` shapes for the others) |
| frame | 18 | program coherence: bodies exist for dispatched functions and overrides (`Elaborated.bodies_typed`), locals end in parameters and returns, `fnLocals` matches the running modifier, constants and initializers at their types, constructor frames |
| heap | 13 | a `memory` reference of type `τ` names a live object of type `τ` (`bytes`/`string` compatible), aggregates hold `Data.val` elements, struct objects have their layout's fields |
| stor | 3 | a `storage` reference of type `τ` names a path of declared type `τ` (`Env.cellTy p = τ.cell`), storage element types are storage-located |
| gap | 12 | not modelled, reachable by well-typed programs (below) |
| typing gap | 3 | well typed by S01, refused by solc, `stuck` at run time (below) |
| bug | 1 | fixed (below) |
| dead | 1 | `heapAt` (`Machine.lean`) has no caller in the interpreter |

**Gaps reachable by well-typed programs** (none is on the per-constructor
ledger `semExprGaps`, which lists only constructors S01 does not type):

- dynamic ABI decoding of `calldata` parameters, static arrays, structs,
  user-defined value types and external function types (`Eval.lean`
  `decodeArgs`), and of memory arrays of non-value elements;
- ABI encoding of memory arrays and structs (returns, external-call
  arguments, `emit`/error arguments) and of external function values;
- `calldata` references (six sites, all shadowed by the decoder's
  refusal: no `cdRef` is ever built);
- getters of non-value types (`string public s`);
- `fallback` with parameters;
- the default of function-typed variables (a function-typed state
  variable read before written; function-typed locals, fields, returns);
- **storage-pointer and calldata return slots and uninitialised calldata
  locals** (new): `callInternal` zeroes the return slots before the body
  runs, and a `storage`/`calldata` type has no default, so
  `function g() internal view returns (uint[] storage r) { r = a; }` is
  `stuck` at entry although solc accepts it.

**Typing gaps** (S01 types them, solc refuses them, the semantics is
`stuck`), fixed in S01's rules and G13's checker:

- `p = S(1)` (a copy into storage) with `p` a local `storage` pointer
  (solc 7407): `Typed.assignCopy` now requires `Γ.namesLocal a = false`;
- `delete p` with `p` a local `storage` pointer (solc: "delete cannot be
  applied to storage pointers"): `Typed.delete` requires
  `(τ.loc? == some .storage && Γ.namesLocal e) = false`.

Recorded, not fixed: storage-to-storage assignment of types containing
mappings (`mapping(uint => uint)[2] a; … a = b;`, which solc refuses,
`stuck` in `loadMem`), and of structs containing mappings, which S01
types and the semantics runs as a copy of nothing (the struct's memory
layout drops the mapping, and with it every member). A fix needs a
`containsMapping` test over struct definitions (recursive through the
environment) in `Typed.assign`.

**Bug fixed**: `bytes(s)[i] = b` on a `string memory s` was `stuck`
("not bytes"): `convExplicitRV` keeps the pointer, so the object is a
string, and the byte write accepted only `bytes` objects. The write now
updates a string object in place (`Eval.lean` `writeLoc`), as solc does.

**Other findings recorded** (not `stuck` sites): `string s = "x";` and
`string constant S = "x";` at contract level do not elaborate (a string
literal does not convert implicitly to `string storage`), so the
`.strLit` arm of `storeRV` is dead; calling an external function that
takes `bytes calldata` with a memory argument has no type (memory to
calldata is not implicit in S01), which solc accepts.

**Not proved**: the gap-relative progress theorem for whole programs,
`noGaps`, and its corollary. The interpreter walk is done for the value
fragment of expressions and statements (above); the remaining
constructs need the heap, storage and frame invariants of Checkpoint 2
threaded through the walk.

## Handoff

Kept current at every checkpoint.

| Checkpoint | Status | Theorems |
|---|---|---|
| 1 Integration | done | `hasType_iff`, `stmtOK_iff`, `itemsOK_iff`, `wellFormed_iff` over S02's typing; controls `member_checked`, `structNew_checked`, `extCall_checked`, `extCallValue_checked`, `pay_checked`, `abiEncode_checked`, `zero_types`, `hexCall_typed` |
| 2 Preservation | partial | `Hoare` and its rules; `alloc_ok`, `allocRef_ok`, `heapPut_ok`, `heapObj_ok`, `heapAt_ok`, `storRef_ok`, `HeapOK.alloc`, `HeapOK.write`; for the value fragment, preservation is by construction (no reference is created) |
| 3 Gap-relative progress | partial | value layer (`binVal_ok` … `convVal_ok`, `constVal_ok`, `Typed.toR_opsOK`, `Elaborated.body_opsOK`); interpreter on the value fragment (`evalE_valFrag_ns`, `exprNSAt`, `stmtNS`, `itemsNS`, `ItemsD.toR_ns`) with storage, mappings and `return`; the `stuck` census; typing gaps fixed in S01 and G13 (`assignCopy`, `delete` of local storage pointers) and a semantic bug fixed (`bytes(s)[i] = b` on a string) |
| 4 Close gaps | not started | |
| 5 `Failures`, `SourceSpec` | not started | |

**Not done** (also under `limitations:`):

- the whole-program progress theorem (every `stuck` of a well-typed
  elaborated program's transaction or deployment is a ledger gap that
  occurs in it), `noGaps` and its corollary, and the token-like witness:
  the interpreter walk covers the value fragment of expressions and
  statements (with storage, mappings and `return`), not memory, arrays and
  structs, internal and external calls, modifiers, builtins, `emit`, or
  the transaction layer (dispatch, ABI decoding, deployment, callbacks);
- preservation for every interpreter step: proved for the memory
  operations and by construction for the fragment, not for the walk;
- the storage side conditions of the fragment (`E.cellTy d.path = τ`,
  `E.pathTy d.path = some τ`) are checked per expression, not derived
  from the elaboration;
- the remaining typing gaps of the census (storage assignment of types
  containing mappings) and the run-time gaps not on the ledger
  (storage-pointer and calldata return slots, function-typed defaults,
  getters of non-value types, `fallback` with parameters, dynamic ABI
  decoding and encoding of aggregates, calldata references).

**How to continue the walk.** Add a field per interpreter function to the
induction hypotheses (`ExprNSAt`, `StmtNSAt`, as `Horizon.lean`'s
`BelowAt`), with a postcondition that carries what the caller needs
(`RPost`, `LocOK`, the frame). `simp only [evalE]` unfolds one arm; the
heavy matchers (`convRV`, `convVal`, `keyStep`) are handled by `split` on
the general match or by per-case `rfl` equations, never by
`simp only [convVal]` (whnf timeouts). Memory needs `WellTyped.lean`'s
`EMOK` in the pre- and postconditions (the heap typing grows); frames
need `BodyFrame` from `callInternal` (the `if h : … = b.locals` check
and `Elaborated.bodies_typed`) and a dispatch lemma (the body virtual
dispatch finds has the parameters and returns of the called signature).

**Elaboration.** `ExprProgress.lean` and `StmtProgress.lean` each check
in under a minute with the language server; `SoundnessExamples.lean`
evaluates the loop and storage witnesses in the kernel in seconds.
