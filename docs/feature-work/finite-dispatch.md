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
  several returns with a memory one, and external memory returns, remain
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
  component does (`uint256`/`address` are `uint`). Calldata, `bytes`,
  narrow, `bytesN`, enum, function, nested or struct elements and recursive
  structs keep no spelling, so no dispatch lists them. The source side
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

- **Several returns with a memory one.** The ordinary call frame refuses a
  reference return in any function of several returns, for direct calls too
  (`elabCallRetCore`: "`memory` on a return of a function of several
  returns", or "its return … has a reference type" without a location;
  `RetKind.rets`
  and `CallRet.rets` carry value binders only). Dispatching to it first needs
  a reference-capable `CallRet.rets`/`Binders` in `Syntax/Scoped.lean` and
  its run (`TRun.call`), a core change outside this lane.
- **Narrow array elements.** `PrimTy` has no narrow integer: a `uint8[]`
  is a `uint` array whose width lives in shape rows (`elabTyW`). A raw
  capture `uint8[] memory y = xs` is a whole use of a narrow array, which the
  elaborator refuses ("xs has a narrow element … not whole"); the direct
  call avoids it through `hoistCallArgs`'s typed capture with `shapeCheck`.
  Admitting it needs the dispatch to emit that typed capture (`captureRef`,
  `Stmt.declMem` with the parameter's shape) instead of a raw declaration.
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
that step rebuilds every Derived module): `./run-lean.sh` `lake build` (result in the final CLOUD-RESULT marker; up to `FunctionTypes` without errors)
; earlier SolkeyTestSuite run: only `Derived17` OOM-killed
(the baseline), `check-solkey` 37 mismatches (the baseline); `TrustAudit.lean`
through the Lean server; `node --test` of `finite-dispatch` (31/31),
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

