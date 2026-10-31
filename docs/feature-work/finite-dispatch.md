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
  or nominal array elements, recursive structs, storage or struct returns,
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
  `T[] storage` whose element is a value type without a marker row (no
  `bytesN`, enum, string or function element) as `T[]memory`/`T[]storage`,
  and a struct parameter as its table name and location (`Tokenmemory`,
  `Tokenstorage`; `fnRefStruct?`: nonrecursive by `structNonrec`, mapping-free
  in memory). A single return `T[] memory` is spelled `T[]memory`, beside the
  existing `bytesmemory`. `canonFnTy` reads an array element as a value
  component does (`uint256`/`address` are `uint`). Calldata, `bytes`,
  nested, nominal-element or recursive references keep no spelling, so no
  dispatch lists them. The source side (`FiniteDispatch.Ty.memoryArray`,
  `storageArray`, `nominal`) parses the same components and requires the
  exact source signature as before: an `address[]`/`uint[]` collision in the
  native key is refused. A struct's native key is its source name
  (`struct C.P`), not its shape, so `P` and a same-shaped `Q` stay distinct
  (`nominalQ`).
- **Capture and aliasing.** `fnDispatch` and `fnMemoryDispatch` capture each
  argument once, left to right (`dispatchCaptures`): a memory reference as a
  memory local (`fnRefElem?`, `fnRefStruct?`): a memory operand is the
  reference itself, so the callee's writes are visible to the caller; a
  storage operand is copied at its position. A storage reference is captured
  as a storage alias of its path, so the callee writes the caller's storage.
  Each branch is the ordinary internal call of its candidate on the captured
  names (`hoistCallArgs` keeps the stable capture without a second copy).
- **Memory returns.** `fnMemoryDispatch` binds one shared memory destination
  of the return's type in every branch, now after the argument captures; a
  zero-argument dispatch keeps its original capture of the tag first.
- **Callee order.** solc's legacy code reads the callee value after the
  arguments, its IR pipeline before them (EVM observation `calleeOrder`).
  Under `evalOrder .viaIR` the tag is captured before the arguments; the
  legacy schedule keeps the original order. This applies to scalar dispatch
  too.
- **Unassigned values.** A zero or deleted tag reaches the final branch:
  `Panic(0x51)` bytes in a self-call or failure-retaining frame, otherwise a
  revert.

### Recorded deviations

- Legacy code calling a *deleted storage* function value jumps to an
  invalid destination (an exceptional halt without data); viaIR raises
  `Panic(0x51)`. The model fails in both and keeps the `Panic(0x51)` bytes.
  A local unassigned value panics in both pipelines.
- Under viaIR, solc copies a storage argument to memory after all arguments
  ran (`argumentOrder`: `901`, legacy `101`). The model copies at the
  argument's position in both schedules, for direct calls
  (`argumentOrderDirect`, pre-existing) and dispatched calls alike, so the
  dispatch stays identical to the direct call. The viaIR replay leaves these
  two vectors out.

### Tests

- `Examples/Tactics/FunctionTypes.lean` §6: candidate signatures (storage,
  `bytes`, scalar, narrow and struct controls), the printed dispatch,
  kernel-checked runs (memory aliasing and the same observation by the
  direct call, storage copy, storage alias, struct arguments in memory and
  storage, branches, argument order), unassigned, wrong-candidate,
  wrong-nominal and false-observation refutations, and a
  `sol_symex`/`sol_close` proof over every typed state.
- `scripts/finite-dispatch.test.mjs`: replay of
  `tests/solc/FunctionValueReferences.sol` through `solc_import` in both
  schedules; admission of exact memory and storage candidates and of a
  scalar argument beside a memory-byte return; refusal of address/uint
  element collisions, recursive structs, external struct parameters,
  struct returns, nominal, byte and nested array elements, calldata
  references, storage mappings, storage-array returns, several returns with
  a memory one and external memory-array parameters and returns.
- `scripts/dispatch-signatures.test.mjs`: the parsed source components keep
  location and nominal identity; calldata, byte, nested and function
  elements stay unparsed.
- `scripts/check-function-value-references.mjs SOLJSON MODULES_DIR [cancun|osaka]`:
  the pinned solc 0.8.34 on ethereumjs 10.1.3, legacy/viaIR × optimizer
  off/on (76 executions per EVM version; cancun and osaka both pass), the
  source of every expected observation above.

## Dispatch correctness

Lane CF2, checkpoint 4. `fnDispatch` builds its chain with
`DispatchArm.chain` (`Syntax/DispatchChain.lean`): one arm per candidate,
guard `tag == tᵢ` with the candidate's tag `tᵢ` (distinct: positions in
`Contract.funs`), body the elaboration of the ordinary internal call `gᵢ(y…)`
on the captured arguments (`elabScope Γ [call g]`, the same path a direct call
`gᵢ(y…)` takes), then the unassigned-value failure. `Semantics/Dispatch.lean`
proves, for every chain and state:

- `DispatchArm.chain_select`: the first arm whose guard holds runs (its
  locals popped), every earlier guard being false;
- `DispatchArm.chain_none`: with every guard false, the failure runs;
- `DispatchArm.chain_tag`: with guards `tag == tᵢ` evaluating to
  `decide (v = tᵢ)`, a run whose tag value is `tᵢ` (no earlier arm with that
  tag) is the run of arm `i`'s body, the direct call of candidate `i`.

All three are over `Stmt.runC` (equal to `Stmt.run` by `Stmt.runR_eq`) and
pinned with `#print axioms` (`propext`, `Classical.choice`, `Quot.sound`)
in the module and in `TrustAudit.lean`. The memory-return dispatch
(`fnMemoryDispatch`) is written as raw `if … else if …` and elaborates to the
same nested `ite` shape, so the lemmas apply to it after unfolding; it does
not construct `DispatchArm.chain` itself. That the arm body is the direct
call is by construction (both are `elabCall` on the same callee and names),
not a theorem about the elaborator, which is `partial`; kernel-checked runs
compare the two on inhabited inputs (`memAlias_run` and `memDirect_run` in
`Examples/Tactics/FunctionTypes.lean`).

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

