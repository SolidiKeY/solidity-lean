# Checked elaborated call-program progress (S05)

`Solidity/Source/Progress/CheckedPrograms.lean` connects three inputs to the
existing source progress theorem:
- a successful `Source.elaborate`;
- `Glob.prog = Source.progOf res.env`;
- P9's check of the complete function catalogue
  ([p9-checked-callgraphs.md](p9-checked-callgraphs.md)).

`CallsOK` and recursive memory preservation are derived, not premises. The
result holds for the supplied dispatch contract only, and it admits a fragment
conditionally rather than covering all of Solidity.

- `checked_fragments` returns the all-horizon progress record and the joint
  memory record ([source-preservation-allocations.md](source-preservation-allocations.md)).
- `checked_expr` gives non-stuckness, `MemOK` and current-local preservation,
  and validity of result references.
- `checked_call` covers internal calls with valid input references.
- `checked_items` keeps the original `BodyFrame`, fragment and operation-domain
  conditions and returns valid output locals.

Timeout and revert semantics, allocation inputs and named refusals are
unchanged.

`Progress/Controls.lean` uses an actual elaborated contract, its nonempty
complete catalogue and a nonempty heap. It reuses an existing source execution
and keeps the wrong-result rejection and the timeout. An elaborated abstract
declaration fails admission because it has no body. A dangling reference
refutes the memory precondition. That is a premise failure, not a new runtime
check.

Not covered: allocating expressions inside the fragment, compilation,
world/ABI entry points, callbacks, payments, termination, `SourceSpec` and EVM
refinement. All printed axioms are `propext`, `Classical.choice` and
`Quot.sound`.

## Direct emit and builtin nodes

`Progress.checked_emit` in `EmitBuiltins.lean` proves non-stuckness of direct emit nodes whose
converted arguments use the checked call fragment and whose event parameters
are elementary `keyable` ABI types. The static-frame revert is retained.

`Progress.checked_builtin` (`BuiltinAdmission.lean`) and
`Progress.checked_builtin_statement` (`BuiltinStatements.lean`) use the same elaborated-program
certificate for calls inside their arguments. The intrinsic `callTy` equation
is retained. `BuiltinFragment` explicitly admits scalar/constant expressions
and byte/string literals for the nine implemented builtin names: require,
assert, revert, Keccak, SHA256, RIPEMD160, addmod, mulmod and ecrecover.
It preserves the evaluator's pipeline-specific evaluation/conversion order,
runtime zero-modulus panic, message bytes and precompile results. Hash
arguments must be string literals and `require`/`revert` messages literals;
`ValFragC` has no builtin case, so builtins do not nest inside fragment
expressions.
Literal hashing proves fresh allocation followed by the actual heap read.

The controls include a builtin argument that calls the nonempty checked P9
catalogue; typed builtin/event executions; observable modular-argument side
effects in both pipelines; zero modulus; exact
hash/message outcomes and named refusals. Digests remain relative to Fixed,
not claims about cryptographic correctness. `recovery_failure` replaces the
precompile with one that halts (`none`); the pinned Osaka `ecrecover` never
halts (an invalid signature returns empty output), so that control exercises
the evaluator's halt branch only. The event log is the model's: the selector
and every parameter as data, with indexed and anonymous flags ignored.
`BuiltinControls.checked_event` consumes `checked_emit` using an actually
elaborated event-only unit: its function catalogue is empty, while its Boolean
argument and locals are inhabited. `checked_call_statement` consumes
`checked_builtin_statement` with the nonempty P9 catalogue and an internal
call as the require argument. Under the original P9 checker, no admitted
callee body contains a builtin or emit statement.

These are direct-node progress adapters. They do not extend the existing
callee-body catalogue checker to builtin/emit-containing bodies. Arbitrary
memory/storage/calldata byte expressions and aggregate event encodings are
outside this new admission. NS permits revert, panic and timeout and proves
neither memory preservation nor termination.


## Nonrecursive effect-body catalogues

`EffectBodies.lean` adds `EffectItems`, a syntactic body-sequence predicate.
It admits the existing value statements and their operations checks, builtin
expression statements from the existing `BuiltinFragment`, and scalar emits
whose converted arguments remain in the value fragment. `effect_items_ns`
proves progress of the containing sequence, including early return and every
non-stuck halt. New builtin/emit nodes occur at sequence positions; a nested
conditional or loop admitted as an old value statement keeps the old fragment
restriction. Builtin arguments retain the scalar/literal boundaries above.

`EffectCatalogue.lean` defines a finite, declaration-ordered proof certificate:
each function's actual selected body may call only its certified suffix.
The certificate contains body/signature/default/modifier and syntactic admission
facts, with no assumed progress theorem. Actual successful `elaborate`, program
identity and environment coherence supply the selected declaration's typing and
call-frame layout. `effect_catalogue_progress` derives all-horizon internal-call
progress; `effect_from_elaborate` consumes the actual elaborator result.
`checked_effect_call` additionally checks that the finite catalogue covers every
source function. Coverage is inclusion; uniqueness and exact list equality are
not asserted. No function may be silently omitted.

This is proof-carrying admission, not a new executable effect-body recognizer.
It is additive: the old `CallsOK` predicate, executable P9 checker and recursive
value-fragment theorems are unchanged. Recursive effect-body graphs are outside
this new certificate. No ABI/world entrypoint, termination, memory-preservation
or compiler/EVM refinement claim follows.

`EffectCatalogueControls` elaborates a source unit containing all three
functions: a leaf emits `Flag(true)` and returns true, its caller requires the
leaf's result, and a separate function asserts false. The complete certificate
is inhabited and consumed by `checked_effect_call`. The fixture uses legacy
resolution and executes both evaluator pipelines. Exact kernel-checked runs
retain the event log, static `revert []`, assertion panic, timeout, and a live
caller reference/memory prefix. Incomplete function coverage, a wrong Boolean
result and the unchanged old checker refusal are negative controls. Body sharing
for reduction is proved equal to the actual inferred program. These are Source
model observations, not solc acceptance or differential EVM results. Both
independent read-only reviews found no confirmed defect. Printed axioms are
`propext`, `Classical.choice` and `Quot.sound` only.
