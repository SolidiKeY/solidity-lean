# G37.03 / P4 typed internal dispatch

Lane compiler10/memory-reference-structs. Public module
`Backend/InternalDispatch.lean`; the active P1 consumer is `FrozenV3`, and
`FrozenV1`/`FrozenV2` stay for the older interfaces.

## Typed tables and the guard chain

- `InternalDispatch/Typed.lean`: candidates keep source-environment
  membership, full `Source.STy` parameter and result lists, mutability and the
  nonexternal role. Tables keep unique identities and nonzero 256-bit tag
  capacity. `Table.guard_agrees`, `candidate_agrees`, `decode_tag`,
  `decode_zero` and `decode_outside` prove selection and refusals.
- `InternalDispatch/Agreement.lean`: full-signature checks
  (`Candidate.check_complete`, `check_wrong_signature`); `Table.Complete` is an
  explicit extraction obligation, and `rep_of_complete` gives a representation
  for every eligible declaration. `eq_step` is the actual machine EQ step.
  `ObservationModel` is a separate source observation contract over
  `Source.callInternal`, not the physical P1 frame.
- `InternalDispatch/Chain.lean`: `Table.code` is a typed equality-guard chain;
  `code_agrees` matches decoding for every word, including invalid tags, and
  `compiled_correct` lifts the observation premise to the whole chain. This is
  not emitted EVM jump or call bytecode.
- `InternalDispatch/Controls.lean`: a two-candidate table with actual source
  calls in both pipelines, EQ steps, and zero/foreign tag, arity, kind,
  return, qualifier, external, duplicate and capacity refusals.
  `interpreterFrames` is interpreter-model inhabitation only.

## Frozen P1 consumers

- `FrozenV1`: selection over the v1 `Pending*` families with `CallSite`,
  `FixedSite` and `RecursiveSite` metadata (`lowerType` is index metadata,
  not a semantic lowering). V1 `RealizableEntry` has a vacuity hole and is
  not used to establish entry or nonvacuity.
- `FrozenV2`: the v2 `Pending*` families. Successful-return transport uses
  `SuccessfulEntry`; bare-revert transport uses only
  `PendingBareRevertProducer`, since the other three v2 bare-revert fields
  may be vacuous.
- `FrozenV3`: the exact per-candidate v3 `PendingCallProducer` with both
  `approved` and `admitted`. `call_claims` exposes coverage and the real
  success and revert witnesses; `selected_call_return` and
  `selected_call_bare_revert` start from an approved input, pass it through
  `required_profile` and `required_coverage`, and use the same caller's
  source outcome, with no `Entry` premise. `required_profile` is only as strong
  as `approved`: `approved := admitted` with `Iff.rfl` always discharges it.
  Every candidate needs a real bare-revert witness, so a table with a
  candidate that never reverts cannot be covered.
  `FrozenV3Controls.empty_domain_refused`: an empty admitted domain cannot
  inhabit a v3 producer.

The `*Controls` modules are dependent-selector controls (exact payloads,
wrong-payload, zero and foreign refusals), not `Pending` instances. The
physical producer and its dual runs are in [P1-CALL](p1-call-producer.md).

## Open

Source-to-intrinsic lowering of `CallSite` arguments, return and body;
approved-domain provenance; dynamic function-value calls (the source has
`Val.internalFn` but no dynamic-call `RExpr` evaluator); fixed and recursive
producers; world restoration; complete tuple and reference call expansion.
The new reference-expansion checkpoint proves the V3 frame producer for
memory/tuple return forms, an actual allocating array argument/return case,
and overlap-safe tuple word compaction. RefTupleTyped now derives the returned
prefix representation and exact source thinning; RefTupleCall emits the checked
tuple call with exact allocation cost and footprint. RefTupleControls supplies
an allocating mixed uint/array-return producer with real dual outcomes.
Finite reference-struct default framing and the owned default-return selector
are now proved, with a real cost5 nested-return dual-outcome producer. Concrete
struct-argument and whole-return rebinding controls now derive a live old nested
graph from actual checked allocation and retain its alias through another
cost5 allocation, with real success/revert and kernel-checked observations;
see `p1-call-reference-expansion.md`. G33
`Backend/MemoryOps/StructDefaults/` support is now published on master.
