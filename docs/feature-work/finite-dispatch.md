# Finite source dispatch

Source admission of ordinary internal and own-external function-value calls
with scalar or function parameters and returns, plus the restricted internal
reference parameters and memory returns below. Source extraction, dependency
closure and the elaborator's dispatch are involved: the interpreter, calculus and proof
system are unchanged. This is an executable extraction boundary, not a proof of
source/native simulation or of extractor completeness.

## Supported

- **Typed source signatures.** `Frontend/SolcJson/Contract.lean` keeps a
  bounded source signature beside the native dispatch key: word widths and
  fixed-byte widths indexed by `Fin 32`, with distinct constructors for bool,
  address and nested function types. Mutability qualifiers are ignored, as the
  native function-value representation ignores them. A native key may map
  address to uint, so key equality alone never admits a call: every
  native-compatible candidate must also have the exact source signature.
- **Internal memory return.** An internal function type may return exactly
  one `bytes memory` value or one memory array of a word, `bool` or `address`
  element, beside any admitted parameters (lane CF2; before it, only
  zero-argument `bytes memory`). The signature retains that memory kind;
  several returns with a memory one through the solc import (the
  elaborator admits them, lane FU2-A), and external memory returns, remain
  refused. `scripts/finite-dispatch.test.mjs` covers receiver effects,
  invalid/unused tags and inherited overrides for this fragment.
- **Candidates.** Own, inherited and imported free/library functions, each with
  its declaration ID and model name, plus receive/fallback entries (refused
  when they match, below) and synthesized getters
  (below, "Getter targets"). Selector helpers and synthesized
  constructor-body helpers are absent: they sit in `SolcContract.internalFuns`
  with `#internalEntry` flags, which native `fnSource` excludes on every path.
- **A superset of native targets.** Candidates match on the native
  `FunDecl.sigTy?`/`extTy?` spelling, with no pruning by `fnReachable`,
  assigned values or declaration order, so every function native dispatch can
  select is included. Extra candidates may reject a usable program. Their IDs
  enter the dependency graph before member emission, and finite reachability
  then scans their bodies, callees, modifiers and specifications. Inherited
  overrides keep both the original and the most-derived declaration. External
  dynamic calls set the writer/callback-summary flag.
- **Receiver cleanup.** Imported contracts keep source metadata in
  `Contract.funs` (`FunDecl.sourceDecl`). External function-value dispatch
  computes the selector as `h - (h / 2^32) * 2^32`, takes the quotient as a
  `uint`, and converts it to `address` in a second local before the try-call,
  the unknown-selector fallback included. Native contracts (all
  `sourceDecl = none`) keep their original lowering and wider address API.
  Controls are in `Examples/Tactics/FunctionTypes.lean` (self call at address 7;
  a native self at `2^200`; the same state cleaned to zero and reverting).

- **Internal reference arguments.** An internal function type may take
  memory or storage arrays of a word, `bool` or `address` element
  (`function(uint[] memory, uint) internal returns (uint)`) and nonrecursive
  structs in memory or storage, nominally (`function(P storage)`), beside
  scalar parameters. See "Reference arguments" below.

## Refused (`solidity.functionDispatch`), and why

- Reference signatures outside the internal memory returns and reference
  arguments above (calldata, `bytes`/`string`/`bytesN`/enum/function/nested
  or nominal array elements, recursive structs, storage arrays or structs as returns,
  several returns with a memory one, any reference in an external
  signature), unknown type metadata, and missing candidate or override
  identities.
- A native-compatible receive/fallback entry: Solidity cannot name it as a
  function value.
- Source-kind collisions among native-compatible candidates (address versus
  uint). All candidates are checked, whatever a points-to approximation would
  omit.
- External dynamic calls with several return values, as in native dispatch.
- External candidates declared private/internal, and inherited or overloaded
  external candidates whose model name differs from the source name (native
  selectors hash the model name). Internal inherited dispatch is supported.

Typed states still admit unassigned function tags; the dispatcher reverts on
them.

## Tests

`node --test scripts/finite-dispatch.test.mjs` keeps the FunctionTypes positive
verdicts, keeps the false/unassigned diamonds pending, and covers the negative
cases above through the real `solc_import` command. `externalValue` must stay
`proved` (also gated by `scripts/guarded-cancellation.test.mjs`).

## Getter targets

Native external dispatch includes synthesized public getters
(`fnExternalEntry`), so the source candidate set of
this document includes them too; otherwise it would
not overapproximate native dispatch. This is a conservative extractor rule,
not a simulation theorem.

### Supported

- A getter candidate is built from the synthesized getter's primitive
  parameters and results, after its getter plan and source identity succeed.
  A validated `SourceCallable.getter` identity supplies the real selector, so
  the generated model name may differ from the source name.
- Getter declaration IDs join the call dependency graph. Their scope is the
  getter declaration header, not the mutable initializer, which still runs
  only at deployment.
- Internal dynamic calls skip getters, matching `SourceFunction.internalValue`
  and native `fnInternal`. Direct static getter calls and self calls are
  unchanged.

### Refused, and why

- A native-compatible getter whose source kind (address/uint/bytes) differs:
  the dynamic call is refused rather than the getter dropped.
- An unsupported or malformed getter plan stays an unknown candidate, so that
  contract's dynamic external calls fail with `solidity.functionDispatch`
  until an exact signature is known, even when another target would do.
  Unrelated static calls are unaffected.
- Reference-valued getters are not shortened and missing metadata is not
  guessed.

### Tests

```
node --test scripts/getter-dispatch.test.mjs
node --test scripts/public-getters.test.mjs
node --test --test-name-pattern='function types:' scripts/test-solidity.test.mjs
```

Every malformed-data case goes through the real `solc_import` command and its
specification callbacks.

## Reference arguments

Lane CF2, checkpoints 1–3: internal function values whose parameters include
memory or storage arrays of a plain value element (1, 2) or nonrecursive
structs in memory or storage (3), and whose one return may be a memory
reference beside arguments (3).

### Base refusal (reproduced on `aaa9db5`)

`function(uint[] memory) internal returns (uint)` was refused at three
points: the finite-dispatch scan (`inspectCall` reads the unknown
`uint256[]memory` component as unresolved), the declaration reader (`tyText`,
`Frontend/SolcJson/Body.lean`: "a function type with a reference parameter")
and the elaborator (`fnDispatch`: "h(…): a function type with a uint[]
parameter or return is not modelled"; pinned in
`Examples/Tactics/FunctionTypes.lean` §5). Reading
`contract C { function target(uint[] memory xs) internal returns (uint) {…}
function entry() public { …; function(uint[] memory) internal returns (uint) h
= target; h(xs); } }` with `readContract … (scanSource := Admission.scan …)`
on the base gave

```
target: diag=none body=ok
entry: diag=some `solidity.functionDispatch body=Solidity.Frontend.Gap.unsupported "solidity.functionDispatch: this call needs a finite set of typed dispatch targets" 8
```

### Supported

- **Signature.** `FunDecl.sigTy?` spells a parameter `T[] memory` or
  `T[] storage` whose element is a 256-bit word, `bool` or `address` as
  `T[]memory`/`T[]storage` (`fnRefElem?`), and a struct parameter as its
  written name and location (`Tokenmemory`, `Tokenstorage`; `fnRefStruct?`:
  the struct `Contract.structName?` resolves, nonrecursive by
  `structNonrec`, mapping-free in memory). The written name is the part of
  the table name before its members (`structDisplay`), so the key is
  nominal. A single return `T[] memory` is spelled `T[]memory`, beside the
  existing `bytesmemory`. `canonFnTy` reads an array element as a value
  component does (`uint256`/`address` are `uint`). Since lane FU1 a narrow
  word or `bytesN` element is spelled at its width (`uint8[]memory`,
  `int16[]storage`, `bytes2[]memory`), so `uint8[]` and `uint16[]` functions
  are not each other's candidates. A `bytes1` element keeps no spelling: the
  model's `bytes` is a `bytes1[]` with the same rows (`solc-alignment.md`,
  "Byte types"), so the key could not tell a `bytes` parameter from a
  `bytes1[]` one, which solc and the source key keep apart. Calldata,
  `bytes1`, enum, function, nested or struct elements and recursive structs
  keep no spelling, so no dispatch lists them. The source side
  (`FiniteDispatch.Ty.memoryArray`, `storageArray`, `nominal`) parses the
  same components and requires the exact source signature as before: an
  `address[]`/`uint[]` collision in the native key is refused. A struct's
  native key is its source name (`struct C.P`, read only after the literal
  `struct ` keyword), not its shape: a same-shaped struct's function is not
  a candidate and its body is not scanned (`struct candidates are nominal`
  in `scripts/finite-dispatch.test.mjs`; `C.P`/`C.Q` keys in
  `scripts/dispatch-signatures.test.mjs`).
- **Capture and aliasing.** The arguments of a call through a function value
  are not hoisted by the caller (`hoistCallArgs`, the expression path in
  `Arms.lean`): `fnDispatch`, `fnMemoryDispatch` and `fnTupleDispatch`
  capture each argument
  once, left to right (`dispatchCaptures`), a later call argument running
  after an earlier operand's capture. A memory reference is captured as a
  memory local (`fnRefElem?`, `fnRefStruct?`): a memory operand is the
  reference itself, so the callee's writes are visible to the caller; a
  storage operand is copied at its position. A storage reference is captured
  as a storage alias of its path, so the callee writes the caller's storage.
  Each branch is the ordinary internal call of its candidate on the captured
  names (`hoistCallArgs` keeps the stable capture without a second copy).
- **Calldata.** A calldata operand (or a memory name bound to one) passed to
  a memory parameter of a function value is refused (`calldataCheck` with
  the names of function type): solc copies it, the capture would share it.
  Through a callee that is not a name, any calldata-rooted argument is.
- **Memory returns.** `fnMemoryDispatch` binds one shared memory destination
  of the return's type in every branch, after the argument captures; a
  zero-argument dispatch keeps its original capture of the tag first.
- **Several value returns.** `(a, b) = h(x)`, `(uint a, uint b) = h(x)` and
  `return h(x);` in a function of several returns (lowered to a tuple
  assignment, `lowerReturn`) dispatch to the direct tuple assignment
  `(a, b) = g(y)` in each branch (`fnTupleDispatch`; vectors `tupleReturn`,
  `tupleAssigned` over two candidates, `tupleForward`, `tupleUnassigned`).
  A callee that is not a name (`s.f(x)`, `fs[i](x)`, `(b ? f : g)(x)`,
  `(h)(x)`) is evaluated into a fresh local of its type first, as `callValue`
  does, then dispatched (vectors `tupleCallee`, `tupleCalleeForward` through
  `return`). Only the conditional form is tested; a parenthesised declared
  function `(g)(x)` also goes through the dispatch here (not the direct-call
  shortcut `callValue` takes), so it is refused where `g` is not reachable
  as a value: fail-closed. Several returns with a memory one stay refused
  (see "Blockers" below).
- **Struct memory returns.** A single nonrecursive struct return in memory
  (`function(uint) returns (P memory)`) binds a shared memory destination of
  the struct's type in every branch (`fnMemoryDispatch`, `structReturn`);
  storage struct returns stay refused. Tested by declaration, assignment to
  an existing local and `return h(v)` (`structReturn`,
  `structReturnAssign`, `structReturnForward`). A recursive struct return is
  admitted by the reader and refused by the elaborator (`fnRefStruct?`).
- **Callee order.** solc's legacy code reads the callee value after the
  arguments, its IR pipeline before them (EVM observations `calleeOrder`,
  `calleeOrderScalar`). Under `evalOrder .viaIR` a named callee's tag is
  captured before the arguments; under the legacy schedule after them. This
  applies to scalar dispatch too (`calleeOrderScalar`).
- **Unassigned values.** A zero or deleted tag reaches the final branch:
  `Panic(0x51)` bytes in a self-call or failure-retaining frame, otherwise a
  revert.

### Narrow and byte elements (lane FU1, CF2 blocker 2)

`PrimTy` has no narrow integer: a `uint8[]` is a `uint` array whose width
lives in shape rows (`elabTyW`). The capture `dispatchCaptures` already
emits is a typed declaration, `uint8[] memory y = xs` at the component's
spelling, whose initializer is `shapeCheck`ed against the operand like any
reference local's (a storage operand copied, a memory one aliased); the
refusal ("xs has a narrow element … not whole") came from the statement's
pre-check, `narrowWholeUse?`, which knew the reference parameters of a
declared function but not of a function value. It now reads them from the
value's type (`fnTyOf?`, `fnTyOfExpr` for `callValueName`): a component
`fnRefElem?`/`fnRefStruct?` accepts is a whole use whose shape the capture
checks. `fnRefElem?` admits a word of any width and a `bytesN` element
(`N ≥ 2`; `bytes1` is the model's `bytes`, see "Signature" above);
`FunDecl.sigTy?` spells them at their width (an element `#bytes` row is
allowed); the source side (`FiniteDispatch.parseType`) parses them, so the
native key keeps the width (`uint8[]memory` ≠ `uint16[]memory`).

Tests: `narrowAlias_run` (`uint8[]` by reference, the callee's write
visible), `narrowOverflow` (the callee's `uint8` arithmetic: `6 + 250`
reverts), the two wrong-width refusals (`uint8[]` to a `uint16[]` value and
back: the capture's shape check), `byteArgs_run` (`bytes2[]`), the signature
pin (`uint8[]memory`, `uint16[]memory`, `bytes2[]memory`; `bytes` unspelled);
in
`scripts/finite-dispatch.test.mjs` "narrow and byte array elements dispatch
at their width" (memory and storage, `uint8`, `int16`, `bytes2`)
and "narrow element widths are part of the dispatch key" (a `uint16[]`
function is not scanned as a `uint8[]` candidate); in
`scripts/dispatch-signatures.test.mjs` the parsed widths and native key.
Enum and `bytes1` elements stay unspelled (refused in both scripts).

### Recorded deviations

- Legacy code calling a zero *storage* function value (never assigned,
  `unassignedStored`, or deleted, `deleted`) jumps to an invalid destination,
  an exceptional halt without data; viaIR raises `Panic(0x51)`. The model
  fails in both and keeps the `Panic(0x51)` bytes. A local unassigned value
  panics in both pipelines (`unassigned`). The EVM script accepts the legacy
  halt only for those two storage vectors.
- Under viaIR, solc copies a storage argument to memory after all arguments
  ran (`argumentOrder`: `901`, legacy `101`); this holds for storage
  structs passed to memory struct parameters too. The model copies at the
  argument's position in both schedules, for direct calls
  (`argumentOrderDirect`, pre-existing) and dispatched calls alike. The
  viaIR replay leaves the two order vectors out, so the model's viaIR copy
  point is unpinned.
- A callee that is not a name (`fs[i](…)`, `s.f(…)`, `choose(b)(…)`) is
  evaluated before the arguments in both schedules (`callValue`, and the
  tuple path's capture in `elabTuple`,
  pre-existing): under the legacy schedule solc evaluates it after them.
- A parenthesised declared function as a callee with a call among its
  arguments, `uint r = (g)(k(1));` (solc's single-element tuple callee), is
  refused since `fnTyOfExpr` types a bare function name: the argument is no
  longer hoisted, and `checkIn` rejects the nested call. It fails closed;
  `g(k(1))` is unaffected (integration review, round 2).
- The elaborator does not type-check a function value's assignment
  (`h = scalar` for a `function(uint[] memory)` local); solc rejects such
  programs. The dispatch then has no arm for that tag and reverts
  (`memWrongCandidate`, `structWrongNominal`: model-only behaviour).

### Tests

- `Examples/Tactics/FunctionTypes.lean` §6: candidate signatures (storage,
  `bytes`, scalar, narrow and struct controls), the printed dispatch (which
  arms are listed), kernel-checked runs (memory aliasing and, separately,
  the same asserts by the direct call; storage copy, storage alias, struct
  arguments in memory and storage, branches, argument order), the
  unassigned and false-observation refutations, model-only refutations on
  ill-typed assignments, and a `sol_symex`/`sol_close` proof over every
  typed state.
- `scripts/finite-dispatch.test.mjs`: replay of
  `tests/solc/FunctionValueReferences.sol` through `solc_import` in both
  schedules (the viaIR one from a `--via-ir` fixture); admission of exact memory and storage
  candidates and of a scalar argument beside a memory-byte return; nominal
  struct candidates; refusal (by the dispatch diagnostic or the reader's
  function-type refusal, checked by name) of address/uint element
  collisions, external struct parameters, storage struct returns, struct, narrow,
  byte and nested array elements, calldata references, storage mappings,
  storage-array returns, several returns with a memory one and external
  memory-array parameters and returns; elaborator refusal of a recursive
  struct; refusal of calldata passed to a function value's memory parameter.
- `scripts/dispatch-signatures.test.mjs`: the parsed source components keep
  location and nominal identity; calldata, byte, nested and function
  elements stay unparsed.
- `scripts/check-function-value-references.mjs SOLJSON MODULES_DIR [cancun|osaka]`:
  the pinned solc 0.8.34 on ethereumjs 10.1.3, legacy/viaIR × optimizer
  off/on (132 executions per EVM version; cancun and osaka both pass), the
  source of every expected observation above.

### Blockers (lane CF2, after integration)

- **Several returns with a memory one.** Resolved in lane FU2-A for the
  elaborator, direct calls and function values (`RetBinders`, "Lane FU2-A"
  below); the solc import still refuses a function *type* with a memory
  return among several (`SolcJson/Body.lean`, "this function type's
  reference return").
- **Narrow array elements.** Resolved in lane FU1 (see "Narrow and byte
  elements" under "Reference arguments").
- **viaIR storage-to-memory copy order.** solc's IR pipeline copies a
  storage argument after every argument ran (`argumentOrder`: 901); the
  model copies at the argument's position for direct calls
  (`hoistCallArgs`) and dispatched calls alike (101). A viaIR replay vector
  would pin a mismatch; changing the ordinary call's copy point under
  `evalOrder .viaIR` is outside this lane.

## Dispatch correctness

Lane CF2, checkpoint 4. `fnDispatch` builds its chain with
`DispatchArm.chain` (`Syntax/DispatchChain.lean`): one arm per candidate,
guard `tag == tᵢ` with the candidate's tag `tᵢ` (distinct: positions in
`Contract.funs`), body the elaboration of the ordinary internal call `gᵢ(y…)`
on the captured arguments (`elabScope Γ [call g]`, the path a direct call
`gᵢ(y…)` takes), then the unassigned-value failure. `Semantics/Dispatch.lean`
proves, for every chain and state:

- `DispatchArm.chain_select`: the first arm whose guard holds runs (its
  locals popped), every earlier guard being false;
- `DispatchArm.chain_none`: with every guard false, the failure runs;
- `DispatchArm.chain_tag`: for guards that evaluate to `decide (v = tᵢ)`,
  a run whose tag value is `tᵢ` (no earlier arm with that tag) runs arm `i`.

All three are over `Stmt.runC` (equal to `Stmt.run` by `Stmt.runR_eq`) and
pinned with `#print axioms` (`propext`, `Classical.choice`, `Quot.sound`)
in the module and in `TrustAudit.lean`.

What is not proved: (1) that the elaborated guards
(`checkIn … (.binop .eqB tag (.num t))`) evaluate to `decide (v = tᵢ)`;
(2) that an arm's body is the direct call of its candidate: both are
`elabCall` on the same callee and names, by construction of the elaborator,
which is `partial`. `memAlias_run`/`memDirect_run` check the same asserts
for the dispatched and the direct call on one input; no theorem relates the
two runs. `fnMemoryDispatch` and `fnTupleDispatch` write raw
`if … else if …` and are not `DispatchArm.chain`; the lemmas do not cover
them. The three dispatchers repeat the candidate loop and failure; a shared
helper would keep them from drifting.

### For lane-soundness (`roadmap-l3-20261030/lane-soundness`)

The Source layer has no dispatched call: `RExpr.call d h args` names a
static declaration (`Source/Resolved.lean`). To extend
`Elaborated.callInternal_call_ns`'s frame and its `hdec` premise to calls
through internal function values, that lane needs:

1. a resolved call through a value of type `.fn false ps rs m`, whose target
   declaration is read from the value at run time, and an unassigned value
   that halts with `Panic(0x51)` (not `stuck`);
2. `hdec` per candidate: every value of that type the program can hold names
   a declaration of the unit. The extractor's candidate set
   (`FiniteDispatch.inspectCall`: every native-compatible source function,
   overrides resolved, with no pruning) is the finite superset to state it
   over;
3. the signature premise with data locations: a candidate's `fnSig` equals
   the function type's `(ps, rs)` exactly, locations included
   (`inspectCall` requires `target.source = some expected`, and
   `Ty.memoryArray`/`Ty.storageArray` keep the location), not only up to
   `Decl.sameRets`;
4. the frame for reference parameters: a memory parameter is bound to the
   caller's heap reference (alias, no copy, unless the operand is in
   storage, which is copied at its position under the legacy schedule), and
   a storage parameter to the caller's storage pointer;
5. the callee-order schedule: under `evalOrder .viaIR` the tag is read before
   the arguments.

These touch `Solidity/Source/**`, which this lane does not edit.

## Review (lane CF2)

Read-only finder and skeptic reviews (no Lean server) of checkpoints 1–4,
with the confirmed findings and their fixes:

- Finder 1 (confirmed by the import replay): for a function-value callee the
  caller hoisted call arguments before `dispatchCaptures`, so a later
  `setFirst()` ran before an earlier storage operand's copy, and before the
  viaIR tag capture. Fixed: such arguments are no longer hoisted
  (`hoistCallArgs`, the expression path in `Arms.lean`).
- Finder 2: calldata passed to a function value's memory parameter was
  shared. Fixed: refused in `calldataCheck` (both the elaborator's and the
  import's call).
- Finder 3: a user-defined value type named `struct…` parsed as a struct
  after whitespace removal. Fixed: the nominal case needs the `struct `
  keyword.
- Finder 4 / skeptic 9: a non-name callee is evaluated first under both
  schedules. Pre-existing; recorded above.
- Finder 6: `bytes1[] memory` spells as `bytes memory` in the elaborator.
  Pre-existing; a dead arm at worst (the frontend never admits a `bytes1[]`
  candidate), not fixed.
- Finder 7 / import replay: narrow element captures lost their width rows
  (a `uint8[] memory` dispatch failed to elaborate). Fixed by refusing
  narrow elements on both sides (a refusal case in the test).
- Import replay: imported struct names are table encodings
  (`P{…}`); the keys now use the written name (`structDisplay`) and
  `Contract.structName?`.
- Import replay: a memory return beside arguments had no shape
  (`exprShape`); fixed.
- Finder 8, skeptic 11–12: stale docstrings, missing theorem docstrings,
  the `chain_select` pin and the script's usage line; fixed.
- Skeptic 1: the printed-dispatch example was a placeholder; filled from the
  elaborator's output.
- Skeptic 2–3: the docs claimed more than `chain_tag` proves and covered
  `fnMemoryDispatch`; reworded (above, and in the module docstring and the
  module map).
- Skeptic 4: nominal evidence; the admission test with a same-shaped poison
  struct function was added.
- Skeptic 5: wrong-candidate refutations are on ill-typed programs;
  labelled model-only.
- Skeptic 6–7: refusal tests now require the dispatch diagnostic or the
  reader's function-type refusal; the external memory-array parameter case
  was added; the recursive struct moved to an elaborator-level check.
- Skeptic 8: the legacy invalid-jump escape is limited to zero storage
  values, and a never-assigned storage vector was added.
- Skeptic 10: the storage-copy deviation names structs and says the viaIR
  copy point is unpinned.

## Handoff (lane CF2)

Checkpoints: 1 (memory arrays), 2 (storage arrays), 3 (memory returns
beside arguments; several value returns; nonrecursive structs in memory and
storage) and 4 (chain
selection theorems, lane-soundness notes) are implemented on
`cloud/relocated-20261031/function-values`. Still refused: several returns
with a memory one, narrow array elements, storage struct returns, calldata
arguments to function values, and every reference in an external
signature.

Gates run after the merge of master (`099bfbe1`) and the post-integration
work (SolkeyTestSuite and `check-solkey` from the earlier full run, since
that step rebuilds every Derived module): `./run-lean.sh` `lake build`
(1040 jobs, success); earlier SolkeyTestSuite run: only `Derived17` OOM-killed
(the baseline), `check-solkey` 37 mismatches (the baseline); `TrustAudit.lean`
through the Lean server ("trust: 13 dispatch theorems use only the standard
axioms"); `node --test` of `finite-dispatch` (31/31),
`dispatch-signatures` (1/1) and `getter-dispatch` (9/9);
`check-function-value-references.mjs` (132 executions, cancun and osaka);
`check-layers` (184 core modules, 0 reach the elaborator), `check-orphans`
(0 orphaned), `check-trust` (0 findings), `check-automatic --strict`
(0 pending), `check-doc-paths` (48, as on the base).

Elaboration time of `Syntax/Elab/*.lean` on the base, from an otherwise idle
`lake build`: Context 19s, Values 29s, Lower 26s, Arms 179s, Stmt 14s
(`Frontend/SolcJson/Body` 33s, `Contract` 53s). After the change these
modules were elaborated by the Lean server or under a parallel build, so no
like-for-like figure was taken; the change adds `DispatchChain` (small) to
`Stmt`'s imports and a `fnTyOf?` lookup per call to an undeclared name in
`hoistCallArgs`. `Examples/Tactics/FunctionTypes.lean` builds in 84s.

### Later reviews

- Tuple-dispatch review (read-only): no bug found; non-name callees in
  tuple assignments, the uncovered raw chain, untested forms
  (`tupleAssign`, several candidates, the unassigned value, `return h(x)`)
  and the duplicated candidate loop were documented, and the forms gained
  EVM-observed replay vectors. The refusal at `Arms.lean`'s named-callee
  `targets` check is now unreachable and was left as a guard.
- Coordinator follow-up (after integration at `099bfbe1`): non-name callees
  in tuple assignments and `return h(x)` supported and tested; struct memory
  returns supported; calldata in tuple assignments refused by the
  integration's stricter `roMentions` check (`calldataCheck` reads a tuple's
  right-hand side); `memNoCopy_reason` pins that the false observation fails
  by the assertion's panic and the program without it returns;
  `memUnassigned_halt` pins the revert (the `Panic(0x51)` bytes are pinned
  by the import replay); several memory returns, narrow elements and the
  viaIR copy order recorded under "Blockers".
- Post-integration review (read-only, 8 items, no soundness bug): the tuple
  path's callee-first order is now listed with `callValue`'s deviation;
  untested forms gained vectors (`tupleCalleeForward`,
  `structReturnAssign`, `structReturnForward`); stale "struct returns
  refused" lines and the first blocker's message were corrected. Not
  changed (recorded): the tuple path's captures stay in the enclosing scope
  (fresh names; as the named path's), the parenthesised-name shortcut, and
  the `tyText` comment in `Body.lean`, which still names only arrays and
  `bytes` among memory returns.


### Integration review (round 2, 2026-11-01)

Read-only finder and skeptic on the merge of CF1 `99a8ce42` and CF2
`6de34328` over master `099bfbe1`; no soundness defect or wrong verdict.
Fixed at integration: the frontend's tuple-value branch for calls through
internal function values (`tupleValue`, `SolcJson/Body.lean`) admitted any
callee of internal function type, so library (`L.f(x)`) and using-for
(`x.f()`) tuple assignments reached the elaborator untested; it now uses
`isValueCallee`, the non-name callees its comment names. Docs: the
callee-first deviation is stated in [options.md](../options.md), the module
map row lists tuple and struct-return dispatch, and the `(g)(k(1))` refusal
is recorded above. Open, not fixed: no tuple test with a memory return among
several (`(bytes memory a, uint b) = h()`) or with calldata through a non-name
callee; `tupleCallee_run` uses `true ? divmod : divmod`, so only the EVM
vectors check which branch runs; non-tuple `(f)(x)` and `(b ? f : g)(x)` and
the `lowerReturn` arm `ternary (call) (call)` are untested.

## Lane FU1 (followup-20261101)

**Done.** CF2 blocker 2 (narrow and `bytesN`, `N ≥ 2`, array elements; see
"Narrow and byte elements" under "Reference arguments"). Integration-review
test gaps (item 4), all in `Examples/Tactics/FunctionTypes.lean`:
`tupleCalleeDyn_run` (a conditional callee on a condition read from memory,
both branches, in a tuple assignment), `scalarCallee_run` (non-tuple `(sum2)(xs)`
and `(b ? sum2 : bump)(xs)` both ways, `bump`'s write visible),
`ternaryReturn_run` (`return b ? f(x) : g(x)` in a function of two returns,
`lowerReturn`'s `ternary (call) (call)` arm; only the chosen branch runs,
counted by `pickCounted`); and in `scripts/finite-dispatch.test.mjs`
"calldata in a tuple assignment through a callee that is not a name is
refused" (`(c ? split : other)(xs)` with `xs` calldata). These are DSL
programs (no `pure`/`view`); no solc fixture pins the tuple ternary return.

**Not done.** CF2 blocker 1 (several returns with a memory one) and, with
it, the tuple test with a memory return among several: the ordinary call
frame's `CallRet.rets` carries `Binders`, value binders only
(`Scope.lean`), and admitting a memory binder means a new constructor (or a
reference-capable binder type) matched in `CallRet.enterT`/`leaveT`
(`Semantics/Run.lean`), `Binders.decodeT`/`defaultsT` (also used by
`tryCall`/`catchData`), `RunWk`/`RunFrame`/`Callback*`, the call rules'
soundness (`Calculus/SoundCalls.lean`, `SoundCatch.lean`,
`RecursionCallback.lean`, `CallbackSound/Rules.lean`, `Closer/Leaf.lean`)
and the elaborator (`elabCallRetCore`, 19 `Binders` match sites outside
the examples, about 270 `.rets` mentions). Every edit there rebuilds the
whole library (45–70 min on this lane's 4-core VM), so it did not fit
beside the other items; no change was started. CF2 blocker 3 (viaIR copy
order, backfill) was not reached.

### Review (lane FU1)

Read-only finder and skeptic (no Lean server) on the item 0 and item 2–4
diffs. Confirmed and fixed: (1) `bytes1` elements: the model's `bytes` is a
`bytes1[]` with the same rows, so admitting `bytes1[]` also spelled `bytes`
parameters `bytes1[]memory` in the elaborator while the source key kept
`bytesmemory`; a `function(bytes1[] memory)` dispatch could list a
`bytes` function the source scan never checked. `bytes1` elements are now
unspelled on both sides (refusal tests restored). (2) `narrowOverflow`'s
docstring claimed it tests the capture's width; it tests the callee's
arithmetic, and the capture's check is the two wrong-width refusals (the
`uint16[]`→`uint8[]` direction added). (3) `ternaryReturn` used pure
callees, so it could not tell one branch from both; `pickCounted` counts.
(4) Wording: the audit's scope (the modules `import Solidity` reaches, not
the corpus or TestSuite libraries), the `canonicalOnly` control comment, a
section pointer, `abi-entry-collect.py` argument handling. Recorded, not
changed: inside `sol{}` (not the import), `AbiTy.of` ignores `#enum` rows,
so a DSL `abi.decode(b, (E[]))` decodes without the member-count check
(pre-existing; the import refuses nested enums).

### Integration review (lane FU1, 2026-11-01)

Read-only finder and skeptic on the merge of FU1 `62f41850` over master
`457130f3`. Fixed at integration: a memory-array return through a function
value now keeps full-word elements (`FunDecl.sigTy?`, `fnMemRet`). FU1 had
admitted narrow and `bytesN` returns, but the call site compares only the
type, not the element width (`exprShape`), so `uint[] memory b = h(a)` was
admitted for a `uint8[]` return, which solc rejects, and aliased the narrow
object at width 256. A narrow or `bytesN` return is refused again. Docstrings
corrected. Open: the `AxiomAudit.lean` treatment of a constant missing from
the environment as clean (not exploitable with a complete import).

## Lane FU2-A (fu2-20261102)

### Design: memory returns in the ordinary call frame

CF2 blocker 1 needs a call of several returns to leave a memory return in
the caller beside value returns (`uint a; uint[] memory b; (a, b) = f(x);`).
Two representations were considered.

1. **A new `CallRet` constructor** (`retsMem`, or a `rets` with a second
   binder list). Every `CallRet` match gains an arm: about 40 proof arms
   (`RunWk`, `RunFrame`, `RunFrameMem`, `RunFrameOwn`, `TypedRunInv`,
   `WkOver`, `FunContract`, `MemContract`, `Recursion`,
   `RecursionCallback`, `SoundCalls`, `SolkeyFragment`, `CallSummary`,
   `TermSize`, `SoundSummary`, `Stipend`, the printers and both quoters),
   and the exhaustive matches in `Solidity/Evm/Compile.lean`
   (`CallRetIn`), `Evm/Correct.lean` (`cases ret with … | rets _ => …`) and
   `Evm/MemoryCalls.lean` (`CallRet.casesOn` with five minor premises).
   Those files belong to the Codex EVM lanes and may not be edited here, so
   this option is ruled out.
2. **A reference-capable binder list for `CallRet.rets`** (chosen):
   `CallRet.rets {rs} (bs : RetBinders rs)`, where `RetBinders`
   (`Syntax/Scoped.lean`) has `nil`, `snoc` (a value) and `snocMem` (a
   memory return, with the `defaultOkS`/`mapFree` evidence `CallRet.mem`
   carries). The constructor keeps its arity, so every `| rets _` arm,
   `.rets .nil` and the five-premise `casesOn` in `Solidity/Evm/**` still
   elaborate unchanged. `Binders` itself is not changed: `tryCall` and
   `catchData` decode their returns with `Binders.decodeT`, and a memory
   binder there would need an ABI decoder; the self `try` path converts
   with `Binders.toRet`.

Semantics: `CallRet.enterT (.rets bs)` is `RetBinders.enterT`, which
declares the binders in order on the frame's parameters, a value one at
its default and a memory one a fresh default object (`State.allocDefaultG`,
as `CallRet.mem` does and solc does on entry); `leaveT` is unchanged (the
binders are left above the caller's locals, and the tuple's targets read
them: a memory target takes the callee's object, by pointer, so aliasing
is solc's). The inline rule's premise (`functionBodyExpand`,
`Premise.expandCall`) declares the binders with `RetBinders.declsThen`
(`T memory r;` for a memory one), so the premise's shape and the rule map
do not change; its soundness rests on `RetBinders.runSt_declsThen` (the
declarations run as the frame is entered) and `RetBinders.enterT_lift`
(entering over a lifted state). The function-contract rule
(`holds_callRets`) keeps its premises: a memory binder makes its "post"
false (`RetBinders.all`), so a call with a memory return among several is
inlined, never summarised by a contract. Recursive functions with a memory
return among several stay refused by the elaborator.

Proofs touched: the arms that read `enterT` of `.rets` (`RunFrame`,
`RunFrameMem`, `RunFrameOwn`, `TypedRunInv`, `FunContract`,
`MemContract`, `Recursion`, `RecursionCallback`, `SoundCalls`,
`CallbackSound`), each by an induction over `RetBinders` instead of the
former definitional unfolding; arms that only read `leaveT` are unchanged.
Checking speed: `enterT` of value-only binders no longer reduces to one
`TEnv.append` by definition, so three proofs that unfolded it
(`holds_callRets`, `Stmt.runSt_callRets`, `CallRet.enterT_snap`) rewrite
with `Binders.enterT_toRet` / `RetBinders.enterT_lift` instead; no
kernel-evaluated certificate unfolds `enterT` (`git log -S enterT` shows no
earlier speed-motivated change to it).

Baseline (base `84a2a4be`, `./run-lean.sh` on this lane's 4-core VM, fresh
`.lake`): `lake build` 67m40s wall, 1039 of 1041 jobs (`Source.Horizon` and
`Frontend.Checked.UnitExamples` OOM-killed under the 4-job build, both
outside this lane). Elaboration of the touched modules on the base, from
that build: `Syntax.Scoped` 13s, `Semantics.Run` 8.9s, `Semantics.RunWk`
17s, `Semantics.RunFrame` 13s, `Typing.TypedRunInv` 2.6s,
`Calculus.Blocks` 3.7s, `Calculus.RunFrameMem` 8.4s,
`Calculus.RunFrameOwn` 7.0s, `Calculus.SoundCalls` 6.4s,
`Calculus.SoundCatch` 2.2s, `Calculus.FunContract` 9.1s,
`Calculus.MemContract` 3.3s, `Calculus.Recursion` 8.2s,
`Calculus.RecursionCallback` 12s, `Calculus.CallbackSound.Calls` 13s,
`Calculus.CallbackSound.Rules` 6.3s, `Calculus.SolkeyFragment` 35s,
`Calculus.PrintStmt` 39s, `Syntax.Elab.Arms` 111s, `Syntax.Elab.Stmt` 12s,
`Examples.Tactics.FunctionTypes` 55s.

### Implementation (lane FU2-A, items 2–3)

- **Frame.** `RetBinders` and `RetBinders.enterT` as designed above;
  `Binders.toRet` for the self `try` (`TRun.tryCall`, `TRun.catchBytes`
  and every proof of the self path, by `rets.toRet`, with
  `Binders.toRet_noMem` where a frame lemma needs no allocation).
- **Soundness, no new premise.** The inline rule
  (`Stmt.runSt_callRets`, `Premise.sound_callRets`) by
  `RetBinders.runSt_declsThen` and `RetBinders.enterT_lift`; with callbacks
  (`ExecS.callRets_inline`, `holdsC_callRets`) by
  `RetBinders.execP_declsThen(_eq)`; the frame lemmas
  (`RetBinders.enterT_frame`, `enterT_frameM`, `enterT_own`,
  `RunInv.retEnterT_env`, `RetBinders.enterT_storage`/`enterT_keeps`);
  contracts (`RetBinders.enterT_snap`, `holds_callRets` with
  `RetBinders.not_holds_all` for a memory binder, `FunContract.forall_rets`
  and `FunContractC.forall_rets` by `RetBinders.enterT_eq`,
  `FunContract.forall_mem`/`FunContractC.forall_mem` gaining the
  `snocMem nil` case, `CallRet.isValues` of `.rets bs` now `bs.noMem`, so
  the recursive-contract rule with callbacks does not take a memory return
  among several). The premises of `functionBodyExpand`,
  `functionCallArgCapture` and the contract rules are unchanged in shape:
  `RetBinders.declsThen` writes `T memory r;` where `Binders.declsThen`
  wrote nothing, and the rule map needs no row.
- **Elaborator.** `elabCallRetCore` admits a memory return among several
  (`retMem`, not `retStorage`), declared `mv…` in the frame and the caller;
  `RetKind.rets` and the call's result list carry `LocalTy`s; a statement
  call of such a function declares the memory return with `declMem`
  (`.none`); a recursive function with a memory return among several is
  refused ("is recursive and returns a memory value among several"). A
  storage return among several keeps its refusal. A target of another
  element width is refused by the rebinding's shape check (solc rejects
  it); a narrow target of the same width is admitted.
- **Function values.** `fnTupleDispatch` admits a full-word memory return
  among several (`fnMemRet`, as for a single one); the dispatch's arms are
  the direct tuple assignments above. The solc import still refuses the
  function type (`SolcJson/Body.lean`, sibling lane's file; its refusal
  cases in `scripts/finite-dispatch.test.mjs` stand).
- **Printer, quoters.** `retBindersS?` (`PrintStmt`), `RetBinders.quote`,
  `qRetBinders`, `RetBinders.declStrs`; a tuple declaration with a memory
  binder prints as the call and its reads.

Tests: `Examples/Tactics/MemoryReturns.lean`, kernel-checked runs
(`decide +kernel`) `splitAssign_run`, `bothAlias_run` (a returned parameter
aliases the argument), `untouchedDefault_run`, `omitted_run`,
`narrowAssign_run`, `falseObservation_panics` (the false observation
panics), through function values `valueSplit_run`, `valueTernaryT_run`,
`valueTernaryF_run` (`(c ? split : split2)(5)`, only the chosen callee
runs), `valueAlias_run`; calculus proofs `untouched_proved`,
`split_proved` (`sol_symex`/`sol_close`, the value target); refusals of a
storage return among several and of a wider target (`#guard_msgs`).

Open: the closer does not resolve a memory array's length or elements after
its allocation (`[ uint[] memory b; ] b.length == 0` stays open with no call
at all, as does a single memory return's `b.length == 0`), so the calculus
examples read only the value target; the reads of the returned objects are
pinned by the runs. EVM-observed vectors were not added: running the pinned
soljson and the EVM harness (`scripts/check-function-value-references.mjs`)
was refused by this session's command policy, and fixture expectations may
not be written by hand.
