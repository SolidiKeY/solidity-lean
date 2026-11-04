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

## Dynamic allocation with a checked length

`Progress/NewArray.lean` proves non-stuckness for a standalone dynamic-new parent
whose length is in the original checked value-call fragment. `NewReady` admits
memory bytes and strings, and one-word dynamic memory arrays whose element
default exists. The extra default condition is necessary: syntactic `newable`
alone does not rule out the evaluator's `new of this element type` refusal.
`new_fragment_all_ns` covers every horizon, including timeout at zero. Allocation
panic remains allowed; non-stuckness asserts neither success nor termination.

`new_from_elaborate` derives length-call `CallsOK` from actual elaboration and
the executable P9 check, and pairs progress with the existing `MemOK` allocation
rule. It uses a supplied closed value-callee allowlist, not complete-function
coverage. The allocation parent is supplied intrinsic syntax; this adapter is
not a new frontend acceptance result or whole-program memory-body progress.
The original `ValFragC` and its checker are unchanged.

`NewArrayControls` consumes inhabited nonempty memory witnesses, including a
compound length, fresh allocation, escaping reference validity, oversized-length
panic and low-horizon timeout in both evaluator pipelines. A missing enum in the
intrinsic layout has no element default: its type remains `newable`, the actual
named stuck outcome persists, and a control refutes `NS` for that input. This
negative layout is not asserted to be an elaborated Solidity enum declaration.
`NewArrayProgramControls` additionally consumes an actual legacy-elaborated
program/P9 certificate, executes the supplied allocation parent in both evaluator
pipelines, and applies the joint progress/preservation result to a live caller
reference. Read-only finder and skeptic reviews found no confirmed defect.
Printed axioms remain `propext`, `Classical.choice` and `Quot.sound`; these are
Source observations, not compiler or EVM refinement.

## Ready allocating expressions and exact arguments

`Progress/ReadyExpressions.lean` decorates the existing `AllocatingExpr` subset
with allocation readiness. `ReadyExpr` covers the original checked value
fragment, reference locals, same-type conversions, reference-result conditionals
and ready dynamic-new nodes. `eval_ready_expr_ns` proves non-stuckness at every
horizon; its projection to `AllocatingExpr` supplies the existing full memory
preservation theorem. Panic and timeout remain possible.

`Progress/ReadyArguments.lean` adds `ReadyArgs` for exact-type converted lists.
`PlainResultType` permits value types or memory-reference types, making `getV`
non-stuck without silently adding raw constants or other reference locations.
The certificate projects to `ExactArgs`, so preservation retains an earlier
reference through a later allocation. Non-stuckness holds independently of
heap validity; the separate preservation conclusion still needs `MemOK` at
entry. Passing a dangling reference can be non-stuck without being valid.

The `ready_from_elaborate` and `ready_args_from_elaborate` adapters derive the
value-callee `CallsOK` premise from actual elaboration and the P9 executable
check on a supplied closed allowlist. They do not require complete-function
coverage, certify the supplied expression's frontend acceptance, or add general
memory-body progress, new memory-callee graphs or a new executable recognizer.
Cross-type argument conversions and storage/calldata argument locations remain
outside `ReadyArgs`.

`ReadyExpressionControls` consumes actual inhabited reference-conditional and
argument runs in both evaluator pipelines: alias versus fresh result, earlier
alias plus later allocation, allocation panic, low-horizon timeout and unchanged
raw-string exclusion. `ReadyProgramControls` consumes a real legacy elaboration
and P9 certificate, then observes the supplied intrinsic conditional and exact
arguments in both pipelines while preserving a live caller reference. Finder
and skeptic reviews found no confirmed issue. Printed axioms are standard only;
no compiler/EVM refinement or universal source-coverage claim follows.

## Ready single-return memory calls

`Progress/ReadyDefaults.lean` proves progress through the actual default
return-slot path. `ZeroReady` requires an existing `Val.default` witness or an
explicit empty-memory type: bytes, string or a dynamic array. Empty dynamic
arrays need no element default because zeroing creates no elements. This is
different from `NewReady` for a requested allocation length. Fixed arrays,
structs and other unsupported defaults are not added by this certificate.

`Progress/ReadyReturns.lean` defines `singleReturningBody` with one ordinary
same-type return of a `ReadyExpr`. Its proof derives expression progress, plain
value extraction, frame-indexed return-slot writing, `runMods []` and final
`retVals` extraction. `call_single_return_ns` covers every horizon. The joint
call and expression theorems pair this progress with existing full memory
preservation; the expression case restores caller locals through actual `sub`.
No semantic body-progress or preservation oracle is supplied.

The `single_return_from_elaborate` and `single_return_expr_from_elaborate`
adapters derive value-callee admission through actual elaboration and P9's
supplied-allowlist check. Their callee is a source-function subtype carrying
membership and matching signature, and its selected body must equal the exact
typed single-return constructor. This is explicit body-shape admission, not an
executable memory-body recognizer or complete-function progress certificate.
It adds no general statement sequence, modifier, multiple-return, recursive
memory-call graph, external/transaction or compiler/EVM progress claim.

`ReadyReturnControls` consumes the source-elaborated memory identity function
and observes its alias return and default allocation, including a body timeout
that retains that allocation. `ReadyFreshReturnControls` actually elaborates
`fresh(uint256 n)` returning `new uint256[](n)`: object 0 survives, the default
slot allocates empty object 1 and the returned fresh object is 2. An oversized
length panics after the default allocation. Its call-expression control proves
non-stuckness while retaining the caller's live reference and validating the
escaped fresh reference. Both evaluator pipelines execute these legacy-resolved
bodies. The named storage-reference default refusal, `no default value`, remains
outside `ZeroReady`. Progress alone does not validate dangling input references;
the preservation triples still require `MemOK` and argument witnesses. Finder
and skeptic reviews found no confirmed defect. All printed axioms are standard.


## Complete hybrid function catalogues

`Progress/ReadyProgram.lean` derives `ReadyProgramCalls` for every function in
an elaborated unit covered by two supplied catalogues: a P9-checked value-call
graph and syntactically ready single-return memory bodies. Coverage is union
inclusion, not a disjoint partition. Each memory entry carries its actual
signature and selected-body equality; its expression may call the checked
value catalogue. The proof derives both non-stuckness and the conditional
memory-preservation triple, including every halt. Entry `MemOK` and argument
validity remain necessary for preservation. No semantic call-progress oracle
is assumed for the memory catalogue.

The derived call context also gives progress for the existing expression
fragment with all covered functions admitted. This is an expression
non-stuckness theorem, not a generic memory-preservation theorem for every
reference expression. It adds no arbitrary memory-body sequence, recursive
memory-call graph, external call, transaction or compiler/EVM refinement.
The supplied certificates are not an executable frontend recognizer or a
universal source-coverage claim.

`ReadyProgramControls` elaborates a legacy source unit with `count()` returning
2 and `fresh()` returning `new uint256[](count())`. Actual runs in both evaluator
pipelines retain object 0, allocate empty default object 1 and return fresh
object 2 with two zero elements. The call triple validates the escaped result;
the concrete expression witness also restores and validates the caller's live
reference. Omitting either function fails coverage, and the original value-only
checker still refuses the memory body. A separate elaborated identity unit
consumes the complete-catalogue theorem with a valid reference parameter and
returns the same alias. Finder and skeptic reviews found no confirmed defect.
Printed axioms are standard only.


## Ready memory statement sequences

`Progress/ReadyBodies.lean` adds `ReadyStmt` and `ReadyItems`: ready expression
statements, explicit default-ready declarations, same-type initialized locals,
plain single returns, exact ready return tuples, conditionals, blocks and
unchecked sequences. Existing value statements and loops retain their old
fragment and operation-domain checks. The new memory admission does not add
mutation, rebinding, memory loops, modifiers or general effects.

The horizon induction proves progress through the actual statement evaluator,
including return-slot writes, scope restoration and escape checks. It needs the
explicit `BodyFrame` premise. Each certificate projects to the existing memory
preservation certificate, giving a joint progress and `MemOK` theorem. Progress
alone does not establish heap validity; the preservation triple requires valid
memory and explicit local-reference witnesses at entry.

`Progress/ReadyBodyCalls.lean` lifts these sequences through modifier-free
internal calls and actual call expressions. It retains explicit selected-body,
parameter/return/frame-layout equations and return-default readiness. The
elaboration adapter derives checked value-callee admission through P9; it does
not automatically derive those frame metadata equations. Ready memory callees
may call the old checked value catalogue; arbitrary memory-call graphs and
recursive memory calls remain outside this result.

`ReadyBodyControls` actually elaborates a legacy source function that declares
an empty memory array, allocates a temporary inside a nested block, allocates a
result after leaving that block, then returns the result. Both evaluator
pipelines preserve object 0 and retain default objects 1 and 2 and the scoped
temporary 3 while returning object 4. Its call-expression witness restores a
live caller reference and validates the escaped result. Oversized allocation
panics after the two defaults; a low-horizon timeout also retains those
allocations. The storage-reference default refusal and old value-checker
refusal remain explicit.

`ReadyScopeControls` supplies direct intrinsic controls for both conditional
choices, unchecked-local restoration followed by allocation, and the singleton
reference `retTuple` constructor. These are not separately elaborated source
units or a multiple-reference return control. Finder and skeptic reviews found
no confirmed defect. Validation targets are
`Solidity.Source.Progress.ReadyBodies`, `ReadyBodyCalls`, `ReadyBodyControls`
and `ReadyScopeControls`; printed axioms are standard only. No compiler/EVM or
universal source-coverage claim follows.


## Elaborated ready-body catalogues

`Progress/ReadyCatalogue.lean` removes caller-supplied frame metadata equations
from the ready-body program adapter. Each catalogue entry supplies declaration
membership, source and selected-target signatures, actual selected body,
empty modifiers, return-default readiness and `ReadyItems`. Actual elaboration
then derives the selected body's parameter types, return types and local-frame
layout. No semantic body-progress or preservation oracle is accepted.

`ready_memory_from_elaborate` derives call progress and conditional memory
preservation for these entries. `ready_memory_expr_from_elaborate` also handles
exact ready arguments, including reference locals, through the actual call
expression and caller restoration. `ready_memory_program_calls` checks union
coverage by the supplied value and ready catalogues and covers every function
in that unit. Overlap and extra catalogue entries are not excluded; coverage is
not an exact disjoint partition. The derived expression context applies to the
existing expression fragment, while the explicit ready-argument theorem admits
the reference-argument clients. Memory bodies still call only the checked value
catalogue: arbitrary memory-call graphs and recursion are not added.

`ReadyCatalogueControls` consumes this interface on the elaborated nested
allocation, memory-parameter identity and mixed value/memory source units.
Inhabited success, allocation panic and timeout witnesses retain their existing
exact observations. The identity call expression passes and returns the same
reference while restoring its caller; the allocating call returns a fresh
reference and retains the caller's live prefix. These call-expression nodes are
built intrinsically over the elaborated programs, not new function-value
reference-argument elaboration controls. Omitting either mixed-unit function
fails coverage. A separate negative theorem rejects an invented empty-frame
body's equality with the actual selected body; this is a certificate refusal,
not an executable frontend rejection test.

`ReadyDispatchControls` puts an inherited primitive-return override in the ready
catalogue, exercising metadata derivation when the selected declaration differs
from the called base declaration. The actual legacy-elaborated body returns the
derived `true` result, preserving an inhabited caller and state in both evaluator
pipelines. This is not a reference-return override control. Finder and skeptic
reviews found no confirmed defect. Validation targets are
`Solidity.Source.Progress.ReadyCatalogue`, `ReadyCatalogueControls` and
`ReadyDispatchControls`; printed axioms are standard only. Memory validity still
requires the separate Hoare entry witnesses. No executable memory recognizer,
frontend completeness, compiler/EVM refinement or universal source-coverage
claim follows.


## Composed call expressions and arguments

`Progress/CallComposition.lean` adds `ComposedExpr` and `ComposedArgs` over the
existing intrinsic syntax. Certified memory calls may occur inside exact-type
arguments, identity conversions, reference conditionals and dynamic-new
expressions. Arguments use plain result types and preserve earlier reference
witnesses across later allocating calls. The joint horizon induction proves
non-stuckness and `MemOK`/result validity on success, retaining `MemOK` on every
halt. Actual `EM.sub` restores caller locals while keeping the reached heap.

The generic `composition_at` theorem takes the existing value-call hypothesis
and an explicit `ReadyMemoryCalls` result. The public
`composition_from_elaborate` derives both from actual elaboration, P9 and the
ready catalogue, certifying the supplied entries. The separate
`composition_program_from_elaborate` additionally requires union coverage and
derives admission for every function in the unit. Neither adapter changes the
callee-body fragment: ready memory bodies still call only the checked value
catalogue. Finite expression nesting is not recursive memory-callee-body
support or an executable frontend recognizer.

`CallCompositionControls` uses an actual legacy-elaborated memory-identity
function. Intrinsic expression nodes allocate fresh object 1, pass it through
two alias-returning calls and return it while retaining default allocations 2
and 3. A two-element argument control keeps the earlier alias to object 0 valid
while its later argument performs an allocating call. Both conditional choices
and an identity conversion consume the theorem. Allocation panic occurs before
callee entry; a low-horizon timeout retains fresh object 1 and the first
callee's default object 2. Exact runs and inhabited preservation clients cover
both evaluator pipelines and consume the complete-unit adapter.

Raw rational arguments without conversion remain outside plain extraction.
A missing-callee theorem refuses a call certificate when neither catalogue
admits its head declaration; this is syntactic admission refusal, not a claim
that its runtime body is absent. The controls build call nodes intrinsically
over the elaborated callee and do not establish function-value reference-argument
elaboration. Finder and skeptic reviews found no confirmed defect. Validation
targets are `Solidity.Source.Progress.CallComposition` and
`CallCompositionControls`; printed axioms are standard only. This proves source
heap-typing preservation, not a physical base-map relation or compiler/EVM
composition. General memory mutation/loop bodies, recursive memory-call graphs,
external/world/transaction progress and universal source coverage remain outside
this result.


## Forwarding memory-return bodies

`Progress/ForwardingReturns.lean` lifts composed expressions through an actual
single-return statement, its modifier-free body and its internal call. The
proof derives return-slot writes, extraction and frame restoration; it accepts
no body-progress or preservation oracle. The `forwarding_from_elaborate` adapter
derives prior callee admission from actual elaboration and a ready catalogue.
Declaration/signature membership, selected single-return-body equality, plain
result extraction and supported return defaults remain explicit.

`extend_forwarding_calls` extends a proved callee set with a forwarding entry
whose expression calls already certified entries. This supports explicit finite
forwarding prefixes; it is not an executable call-graph recognizer or a general
recursive-body result. The base ready catalogue and value-callee hypotheses
retain their existing restrictions. No whole-program coverage check is added
by this adapter, and multiple-return or arbitrary statement bodies are not
silently admitted.

`ForwardingControls` kernel-checks the real legacy-elaborated source functions
`fresh(uint n)` returning `new uint[](n)` and `relay(uint n)` returning
`fresh(n)`. These calls have primitive arguments, so this control does not
require function-value reference-argument elaboration. Both evaluator pipelines
execute the source bodies. Object 0 survives, both return defaults occupy
objects 1 and 2, and success returns fresh object 3. An oversized length panics
inside the callee after the defaults; the relay propagates the exact allocation
panic. Inhabited call-expression consumers retain the caller's live reference
and validate the escaped result on success and the reached heap on panic.
The distinct-declaration and wrong-signature controls check certificate/signature
premises, not executable frontend refusal. Finder and skeptic reviews found no
confirmed defect; printed axioms are standard only.

Validation targets are `Solidity.Source.Progress.ForwardingReturns` and
`ForwardingControls`. This is source progress and memory preservation, not a
physical base-map, bytecode or end-to-end compiler correspondence claim. It does
not discharge the remaining P8 concrete-producer/adequacy, runtime-frame payload
transport or H16/H19 obligations. Source evaluator and intrinsic representations
are unchanged.


## Finite forwarding-chain certificates

`Progress/ForwardingChain.lean` records a ready base catalogue and finitely many
single-return forwarding extensions. Each added entry has actual source-function
membership, signature and selected-body equality, supported defaults, plain
extraction and a composed expression referring to the earlier certified set.
`forwardFresh` refuses an added declaration already present in either the value
or prior-call list. No semantic correctness oracle for the new body is stored.

`forwarding_chain_sound` derives call progress and conditional memory
preservation by induction on this certificate. With the separate union-coverage
check, `forwarding_chain_program_calls` derives `ReadyProgramCalls` for every
function in the source unit, and `forwarding_chain_composition` admits those
functions inside composed expressions and arguments. The declaration-provenance
helper uses the existing P9 check's environment/unit correspondence.

This is finite proof construction, not an automatic graph recognizer or a
statement that the whole runtime graph is acyclic. The base may contain duplicate
entries or overlap the value list; existing value callees may recurse; distinct
declarations may dispatch to one implementation. Freshness applies to each new
extension. Coverage is inclusion, not an exact disjoint partition. Progress
retains the existing horizon/timeout semantics and does not imply termination.

`ForwardingChainControls` consumes the complete-unit theorem on the actual
legacy-elaborated allocating/relay unit. Both evaluator pipelines execute the
base leaf and the added relay, validate their returned references and retain the
caller prefix. The complete composition theorem validates caller success and
callee-panic restoration. Duplicate-addition, value-list overlap and omission of
either function have explicit negative controls; these test certificate guards,
not executable frontend refusal. Finder and skeptic reviews found no confirmed
defect. Validation targets are `Solidity.Source.Progress.ForwardingChain` and
`ForwardingChainControls`; printed axioms are standard only. General body shapes,
recursive-memory compiler support, source recognizer completeness, physical
base-map and compiler/EVM agreement remain outside this source-only result.


## Initialized-local return prefixes

`Progress/InitializedLocals`, `InitializedPrefixes` and `InitializedCalls` derive
progress and conditional memory preservation for finitely many initialized
locals followed by one composed return. Each initializer has an identity
conversion and plain extraction type, and uses the existing composed-expression
certificate. A local stores the returned reference without an additional copy
or default allocation. The actual `sub`, `Out.up`, body frame and return
extraction operations preserve reached allocations and remove prefix locals
when returning to the caller. Every halt retains `MemOK`; progress excludes
`stuck` at each fuel horizon and does not imply termination.

`initialized_from_elaborate` derives earlier callee admission from actual
elaboration and the checked catalogue. The supplied entry still needs source
membership/signature, supported defaults and exact selected-body equality.
`extend_initialized_calls` adds it to the certified list without asserting
freshness, whole-unit coverage or a global acyclicity property.

`InitializedControls` elaborates an allocating leaf and a relay that initializes
`uint[] memory temporary = fresh(n)` and then returns `temporary`. Both evaluator
pipelines return the same fresh reference, preserve the caller prefix and reached
heap, and retain the allocation panic and stopped heap on oversized input.
Inhabited consumers instantiate the joint proofs. Empty and uninitialized-prefix
certificates and an incorrect signature have negative controls; these are proof
fragment refusals, not frontend rejection. Finder and skeptic reviews found no
confirmed defect. Focused targets are the four `Initialized*` modules; printed
axioms are `propext`, `Classical.choice` and `Quot.sound` only.

Uninitialized locals, nonidentity conversions, mutation, loops and modifiers
remain outside this certificate. General memory-call graphs, source recognizer
completeness, compiler/physical-frame refinement and EVM agreement are not
established by this source-only result.
