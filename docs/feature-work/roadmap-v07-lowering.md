# V07: source lowering components

Partial. V07 keeps G16, G17, G18.01 and G18.06. [Modules](../module-map.md#v07-source-lowering)
work over the existing Source and intrinsic carriers (no new AST, IR, value or
state layer); no elaborator agreement, solc/EVM run or constructor is claimed.

## Scalars, conversions and reads (G16)

- `Lowering/V07/Scalar.lean`: every admitted Source integer width and sign embeds
  injectively in its 256-bit intrinsic type (`integer_range`, `integer_observe`,
  `integer_injective`), from Source value bounds only; no declaration admission.
- `Lowering/V07/Conversions.lean`: `Source.convVal` implicit integer runs with
  widening range transport (`implicit_integer_run`, `implicit_integer_transport`),
  `Source.convExplicitVal` wrapping (`explicit_integer_run`), `address_conversion`,
  `udvt_identity`. Value-level only: no cast program is emitted, and a runtime
  conversion does not establish static conversion admission.
- `Lowering/V07/SourceReads.lean`: Source local reads against intrinsic
  `Val.evalT` (`source_local_transport`). `source_pure_pair` keeps semantic
  operand positions under legacy right-first and via-IR left-first order only
  when both operands preserve the whole Source state; it commutes no effects.
  `source_local_pair` discharges that for local reads;
  `AssignmentControls.assignment_changes_state` shows an assignment cannot.

## Pipeline-ordered effects (G17)

Operands run in pipeline order; captures are read before their binders drop.

- `AssignmentOperands`, `AssignmentOrder`: `i = a` and assignment/read pairs
  (`assignReadPrefix`, `assignment_operand_transport`).
- `AssignmentSubtraction.assignment_subtraction_transport`: subtraction at every
  width with the initial difference in range. `AssignmentBoundaries` shows
  unchecked uint8 underflow wrapping to 255 in Source, which it excludes.
- `IntegerLocalFamily`: selected locals of one fixed `Source.IntTy` with value
  agreement and separate alias reflection; `assignment_family_transport` derives
  the post-family; `integer_assignment_prefix_family` inducts over arbitrary
  assignment prefixes. Not cross-width, whole-state or Source loops.
- `ReferenceCapture`, `ReferenceEffects`: `HRef`/`SRef` identity survives alias
  captures (`reference_assignment_pair_transport`), from an input address
  relation; no heap content, copy, allocation or lifetime result.

**P12 context-map interfaces.** `Lowering/V07/ContextMap.lean`: `ContextMap`
maps Source typed indices to intrinsic type/index pairs, reflecting positions
across all types (`wk_identity`, `wk_composition`, `related_cons`, `related_wk`;
no size cutoff). `Related` is a pointwise initial value relation, not an
execution relation; a mapped position is not heap alias identity.
`Lowering/V07/ContextMapWrite.lean`: `ContextMap.related_write` and
`related_assign` derive every post-binding and frame inequality from initial
alignment. `Lowering/V07/EffectfulCondition.lean`:
`condition_assignment_transport` derives the Source run, target prefix, captured
choice and caller frame for a condition `x = y`. `Lowering/V07/ShortCircuit.lean`:
`short_assignment_transport` does the same for `(i = a) && (j = b)` and `||`,
left first in both pipelines. Both cover only
`x = y` local-to-local Boolean operands, not arbitrary Boolean expressions.
`ConditionLoopControl` is a deliberately wrong consumer: a condition captured
once stays stale at every `TLoop.iterN` prefix (`every_stale_prefix`).

**Alias families and short-circuit scope.** `double_assignment_transport`
(`DoubleSubtraction`) proves `(i = a) - (a = b)` with aliasing destinations but
needs `i ≠ b`; `DoubleNegativeControls.rhs_alias_initial_formula_false` shows the
formula fails without it (via-IR gives 0, not 4). `assign_pair_all_aliases`
(`AllAliasPair`) drops the restriction: alias reflection selects the same
reached right read on both sides. `alias_rhs_sub_transport` proves the `i = b`
clause (result 0; `integer_zero_range` at every width); with the `i ≠ b` clause
this covers every alias pattern of that one expression. `ShortCircuit` allows
all `i/a/j/b` aliasing and reads the right operand after the left write;
`source_short_skip` lets a skipped Source RHS be arbitrary (even failing), but
is no compiler for arbitrary RHS, and no panic payload equivalence is shown.

**Unchecked unsigned narrowing.** `Lowering/V07/UnsignedNarrowing.lean`:
`subValue` is `subW` then `mod 2^N` for N < 256, raw `subW` at 256.
`source_sub_unchecked` covers both `Source.intRes` branches; `sub_value_run`
holds at every unsigned width with no result-range premise;
`assignment_transport`/`assignment_extension` lift it to assignment operands.
`WrappedAssignmentPair.transport` handles two wrapped assignment operands under
every alias pattern. Signed wrapping and other operators are open.

## Declaration graphs (G18.01)

`Lowering/V07/DeclarationGraph.lean` is the shape interface.
`PrimitiveGraph.produce` covers int/bool/address fields; `RecursiveGraph.produce`
adds nested dynamic/fixed arrays, struct nodes (scoped identity, not unfolded),
mappings, bounded enums and primitive-backed UDVTs, computes ranks by `rankIter`
over the node count and checks every guard before building the schema. `None`
is a component failure, never a Source rejection.

**Admission boundary.** `GraphAdmissionBoundary` builds a struct whose field
names itself inline. For every `Settings`, `direct_well_formed` (`WellFormed`,
`InProfileSyntax`) and `direct_strict_metadata_accepts` (`strictMetadataChecker`)
accept it, yet `direct_not_certifiable` shows no `DeclarationGraph` exists at
any location or size. `no_total_from_current_metadata` and
`no_total_from_strict_metadata` refute a total producer from current metadata; a
stronger G15 judgment is not refuted. The guarded witness (dynamic-array self
edge) is inhabited at every location (`certificate`, `guarded_inhabited`); the
same edge treated inline fails (`same_edge_inline_not_guarded`).

**Locations.** `RecursiveGraphControls.mapping_memory_not_certifiable`: a mapping
struct has no memory certificate. `LocationGraphInterface` revises the target:
`StructAdmissible` uses `Source.Env.hasMapping` (mapping-containing structs are
storage-only); `LocationDeclarationGraph` covers all and only admissible structs;
`ofStorage` keeps storage certificates. `LocationGraphProducer.produce` computes
it (`SelectionOK` plus `RecursiveGraph` lowering); admissible but unsupported
fields stay selected and fail rather than vanish.

**Source refusal gap.** `Admission` also requires `SourceRefusesNonAdmissible`
(local declarations via `Source.StmtD`). `LocationGraphLaws.refusal_missing`
proves it false: `StmtD.declVar` admits `Loop memory x;` for a struct containing
a mapping, because `Source.locOK` takes no `Env`. The fix is an environment-aware
location check in Source typing and the elaborator.

**P8a consumption.** `P8Bindings` takes the exact `P8a.Producer`
(`Lowering/P8/FrozenInterface.lean`): `accepted`, `acceptedSource`,
`program_origin`, `execution` (relative to the external reference),
`AcceptedGraph`, `graphForRealization`. `AcceptedGraphProducer.produce` binds
`RecursiveGraph.produce` to `acceptedSource`; `successful` gives the graph when
checks pass; `certificate_excludes_inline_self_origin` shows a graph rules out
the inline-self environment. `LocationGraphInterface.Admission` and
`LocationGraphProducer.produceAccepted` are the per-location counterparts.
Everything indexed by `P8a.Producer` is vacuous until P8-SPEC-LAW1 is resolved:
over the current `Nat` resource, `Producer` is uninhabited
([P8 admission](p8-admission.md#failure-projection-conflict)). `scalar_value` and
`source_assignment_run` ignore the producer; they only rename the environment
and are proved by `integer_related` and `source_assign_local_run`.

**Ranks and field completeness.**
- `GraphRanks.iter_bound` bounds `rankIter` by any positive valid assignment;
  `RankConvergence.iter_stable` stabilizes past a positive valid comparison
  rank; `stable_guarded` turns stability into the schema's strict inequalities.
  Neither bounds the producer's own iteration count.
- `NodeRank`: `height` counts strictly lower nodes, so `stable_at_nodes`
  stabilizes at the node count for any valid assignment, and `location_fields_ok`
  discharges the producer's rank conjunct. Comparison ranks are proof-only.
- `FieldCompleteness`: `functional` (injective names fix the target type);
  `complete`/`fields_complete`: `RecursiveGraph.lowerType`/`lowerFields` succeed
  for every `GraphTypeRel`/`GraphFieldsRel`, given injective names and support
  for every UDVT underlying in the layout (sufficient, not necessary).
- `LocalFieldSupport`: `type_complete`/`fields_complete` need `Supported` only for
  traversed UDVTs, so they subsume `FieldCompleteness`. Neither covers types
  `GraphTypeRel` lacks (bytes, string, function).

## Open

- Arithmetic beyond in-range and unchecked unsigned subtraction; checked payloads;
  constants, enums, cast programs; tuples, conditionals, updates, other conditions.
- Elaborator agreement: relate `captureExpr`/`captureBefore`
  (`Syntax/Elab/Values.lean`) to these prefixes via a `Source.RExpr` to
  `DeferredSource.Operand` producer.
- G18.01: a total accepted-source producer (needs an inhabited `P8a.Producer`);
  bytes/string/function/fixed-point fields; a valid rank from admitted Source;
  the Source refusal fix; parameter/return and whole-program admission.
- G18.06: blocked until ordered G18.02–G18.05 child certificates exist.
