# Finite source dispatch

Source admission of ordinary internal and own-external function-value calls
with scalar or function parameters and returns, plus the restricted internal
`bytes memory` return below. Only source extraction and
dependency closure are involved: the program, interpreter, calculus and proof
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
- **Internal memory-byte return.** A zero-argument internal function may return
  exactly one `bytes memory` value. The signature retains that memory kind;
  reference arguments, mixed/multiple memory returns and external memory
  returns remain refused. `scripts/finite-dispatch.test.mjs` covers receiver
  effects, invalid/unused tags and inherited overrides for this fragment.
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

## Refused (`solidity.functionDispatch`), and why

- Reference signatures outside the zero-argument internal `bytes memory`
  return above, nominal signatures, unknown type metadata, and missing candidate
  or override identities. Reference arguments retain their refusal boundary.
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
