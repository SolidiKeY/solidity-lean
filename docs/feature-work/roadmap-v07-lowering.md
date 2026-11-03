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

`ReferenceCaptureRelated` derives selected address/path agreement from initial
`ContextMap.Related` and mapped slots (`related_memory_capture`,
`related_storage_capture`). It proves the actual local read, target capture,
getter before scope exit, both context extensions and exact caller restoration
on dropping the temporary. Extended Source locals classify the returned value;
no Source declaration execution or heap-content relation is asserted.
`ReferenceOrderRelated.related_reference_assignment_pair` handles `(i = a, i)`
references in each actual pipeline order. It derives both captured value
relations and every reached caller binding from initial alignment; two drops
restore the updated caller exactly. No operand-separation premise is required.
`ReferenceRegisteredControls` supplies closed memory/storage capture and
distinct-reference assignment clients in the default import closure. An
arbitrary input value relation does not establish global heap alias reflection.
These supported clauses do not supply a general elaborator/operand producer,
copy/delete/lifetime validity or graph admission. G16/G17 and Backfill A/B stay
partial; the remaining G18.01/G18.06 prerequisites are unchanged.

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

- Arithmetic beyond in-range and unchecked unsigned addition/subtraction/multiplication; checked payloads;
  constants, enums, cast programs beyond full-word integer sign conversion; tuples, conditional clauses beyond local assignments, updates, other conditions.
- Elaborator agreement: relate `captureExpr`/`captureBefore`
  (`Syntax/Elab/Values.lean`) to these prefixes via a `Source.RExpr` to
  `DeferredSource.Operand` producer.
- G18.01: a total accepted-source producer (needs an inhabited `P8a.Producer`);
  bytes/string/function/fixed-point fields; a valid rank from admitted Source;
  the Source refusal fix; parameter/return and whole-program admission.
- G18.06: blocked until ordered G18.02–G18.05 child certificates exist.

## Executable location-graph component completeness

`LocationGraphCompleteness.fields_exact` derives the exact ordered target fields
from `GraphFieldsRel`, injective declaration names and support for the traversed
fields. `producer_success` then proves the actual per-location producer succeeds
from `SelectionOK`, those field premises, nonempty/distinct fields and any valid
comparison rank. The rank is proof-only; neither successful execution of the
lowerer nor the producer's computed rank checks are premises.

`LocationGraphCompletenessControls` supplies a three-node client for both
headlines, distinguishing physical declaration index2 from graph index0 and
comparison rank30 from computed rank3. This establishes component completeness relative to
structural premises; deriving them from accepted Source remains open. No P8
producer instance, independent Source execution preservation or constructor
coverage is supplied. G16/G17 and Backfill A/B remain partial; G18.01 still needs
accepted-source coverage, rank existence and the Source refusal repair. G18.06
requires the ordered G18.02–G18.05 child applications; G19 is delegated to V17.

## Unchecked unsigned addition

`UnsignedAddition` reuses `UnsignedNarrowing` width/range/modulo laws.
`add_value_run` relates actual intrinsic `addW` followed by width narrowing to
Source wrapping at every approved unsigned width, including 256.
`source_locals_run` and `source_assign_read_run` execute the actual Source
`.binary .add` expression with unchecked arithmetic; the latter assigns a local
before observing its alias in the published pipeline order.
`assignment_transport` derives target reads, captured result and every selected
postbinding from the initial `IntegerLocalFamily` and two initial reads/ranges.
`assignment_extension` uses actual operand weakening/run transport. There is no
output-range, desired-run or postrelation premise. `source_from_pair` alone is a
conditional composition helper; the concrete clauses discharge its pair premise.

`RegisteredScalarClients` supplies a closed mixed-caller client for every
addition headline, including actual pair execution and context extension. Checked Source
overflow does not establish target panic-payload transport.

Queue: G16/G17 and Backfill A/B remain partial. G18.01 retains component
completeness but still needs accepted-source coverage, rank existence and the
Source refusal repair. G18.02/.03 belong to V16, .04/.05 to V14, and G19 to
V17. G18.06 requires their ordered accepted-source applications. Constructor
coverage remains zero; checked payloads, signed wrapping and broader operand
producers remain open.

## Two effectful addition operands

`WrappedAdditionPair.source_run` executes actual Source addition with operands
`i = a` and `a = b`; `operand_run` runs the actual typed capture prefix and
CP20 addition value, reading captures before dropping temporaries. Both reuse
`WrappedAssignmentPair.sourcePost`/`targetPost` as observations of existing
operations. They introduce no execution or state layer.

`transport` derives both runs, the wrapped value relation and every selected
postbinding from an initial `IntegerLocalFamily` and initial input reads/ranges.
All aliases are permitted. Identity reflection selects the reached RHS when
`i = b`; no separation, output-range, desired-run or postrelation premise is
supplied. `extension` transports the actual operand through arbitrary thinning.
All approved unsigned widths, both pipelines and arbitrary available fuel are
quantified. These are supported operational clauses, not a general elaborator.

the lane-only fixture WrappedAdditionPairChecks.lean (not on master) covers all five partitions of the
three local roles, repeated family aliases, three-distinct overflow and in-range
controls, physical captures, complete scalar caller observations, live memory/
storage and world/global frames, and fresh-context transport. Actual stale and
deferred reads produce incorrect values. Max-plus-one runs in both Source and
target at all 32 approved widths give viaIR zero and legacy two, including256.
Addition commutes: ordered captures/caller writes distinguish schedules.
The small `dropCorrect` Boolean checks one slot; whole-caller restoration follows
from the exact generic operand run, not that Boolean alone.

Independent finder and skeptic reviews found the composition sound and requested
all alias partitions, real wrong-program, width and mixed-caller controls; these
were supplied. Finder's initial-cell wording was corrected: initial cells hold
200 and250; equal contents arise after some writes without merging identities.
Four exact standard-axiom guards extend the registry to484, preserving480 prior
sets and every old ordered observation. G16/G17 and BackfillA/B remain partial;
accepted-source graph coverage/ranks/refusal and ordered G18 composition remain
open. Constructor coverage stays zero; no checked-payload or external EVM proof
is implied.

## Unchecked unsigned multiplication

`UnsignedMultiplication` reuses the existing unsigned type, range, word-then-
narrow and modulo laws. `word_mul_eval` proves actual intrinsic `mulW` word
wrapping; `mul_value_run` narrows that actual result below256 and retains the
word branch at256. All approved unsigned widths and arbitrary input ranges
within their types are supported; result bounds derive from Source wrapping.

`source_locals_run` and `source_assign_read_run` execute actual Source `.mul`
expressions, the latter assigning a local and observing its alias in the
published pipeline order. `assign_read_operand_run` reads real captures before
dropping temporaries. `assignment_transport` derives target reads, both actual
runs, the wrapped value relation and every selected postbinding from the initial
`IntegerLocalFamily` and source input reads/ranges. No output-range, desired-run
or postrelation premise. `assignment_extension` uses actual operand weakening.
`source_from_pair` is a conditional helper; concrete clauses discharge it.

the lane-only fixture UnsignedMultiplicationChecks.lean (not on master) instantiates mixed callers: assigning
200 into old250 gives legacy80 and viaIR64, with physical captures `[200,250]`
and `[200,200]`. Same-slot200² gives64;7×3 gives21; zero is proved at every
approved width. Actual Source and target max-squared runs give1 at all32 widths,
including256; a bare checked word multiply rejects that full-width product.
Actual unnarrowed50000, deferred64 and stale80 programs discriminate wrong
lowerings. Live memory/storage references, source world, target global state
and fresh-context transport are retained. Multiplication commutes, so capture
observations distinguish operand roles rather than a reversed-product claim.
Checked Source overflow controls do not prove target panic-payload transport.

Independent finder and skeptic reviews found no proof defect. Ten exact
standard-axiom guards extend the owned registry to494, preserving all484 prior
sets and existing ordered fixtures. The new public P8 stage/cursor and aggregate
components are retained; no concrete P8 producer, accepted-source graph totality
or final aggregate/production composition is supplied here. G16/G17 and
BackfillA/B remain partial; G18.01 prerequisites and ordered G18.06 applications
remain open. G18.02/.03 belong to V16, .04/.05 to V14 and G19 to V17. Constructor
coverage remains zero; no new external compiler/EVM experiment is claimed.

## Registered headline clients

`ReferenceRegisteredControls`, `LocationGraphCompletenessControls` and
`RegisteredScalarClients` are registered through the shared import generator.
They supply25 closed proof clients:3 reference,2 graph and10 each for addition
and multiplication. None accepts a SourceSpec/P8 producer or the desired run.
The pair-helper clients discharge their pair premise with actual local reads.
Scalar clients use the existing mixed7/3 caller: assignment/read gives addition
10/14 and multiplication21/49 in legacy/viaIR order, plus concrete wrapping
controls. Reference clients allocate distinct live objects and preserve the
typed storage root. Graph clients retain the original nontrivial chain and
negative controls. All prior lane tests and observations remain unchanged.

The owned exact registry covers494 general theorems and25 registered proof
clients (519 exports). Changed/omitted copied client pins are rejected alongside
the old mutation controls. The reference theorem binders move from explicit
forall types to normal headers, preserving names, order, implicitness, premises
and conclusions; the15 signature-linter warnings disappear without suppression.
Focused kernel checks and independent reviews confirm the layout-only change.
These clients add checking to the default closure; they close no additional
source-admission, lifetime, production or constructor obligation.


## Effectful multiplication pairs

`WrappedMultiplicationPair` transports two actual integer assignments followed
by unchecked multiplication, with runtime aliasing of any of the three local
roles. Its source_run, operand_run, transport and extension theorems derive
both published pipeline runs, wrapped value agreement and the entire selected
post-family from initial reads, ranges and IntegerLocalFamily. Alias reflection
derives the reached-donor branch; no separation or desired-result premise is
supplied. The target captures operands before dropping fresh temporaries.

`WrappedMultiplicationControls` registers four closed headline clients and
inhabited controls for every alias partition, three distinct locations, live
memory/storage callers, stale/uncaptured negatives and all32 approved widths.
Legacy250 squared wraps to36; the distinct IR200*250 wraps to80. Equal numeric
products do not claim reversed operand positions are distinguishable.
Finder and skeptic found no proof defect; two copied comments were corrected.
The exact owned registry now covers528 exports, preserving all519 prior sets.
These are kernel and Lean observation controls, not external compiler/EVM
experiments. G16/G17 and both backfills remain partial. G18.01 graph admission,
G18.06 ordered V16/V14 applications, source failure/lifetime/production closure
and constructor coverage remain open; G19 remains delegated to V17.


## Full-word integer sign casts

`WordCasts` proves actual uint256/int256 conversion execution in both directions.
Source `convExplicit` and intrinsic `toInt`/`toUint` agree with the existing
wrapping definition for all input values in range, including the signed threshold.
Its assignment transports convert a fresh captured value before dropping the
existing local-assignment prefix. Initial IntegerLocalFamily and a Source read
derive the target read, actual runs, returned value relation and whole selected
post-family. Caller locals retain their original type and assigned value.
The two context-extension theorems use the actual Operand weakening runner.

`WordCastControls` registers13 inhabited clients, one for each generic theorem,
plus an inhabited mixed-family theorem. Both pipeline controls preserve semantic
operand positions: a cast assignment returns−1 while an alias read observes old7
in legacy order and reached uint256 maximum viaIR. Same-slot/repeated aliases,
fresh Boolean extension, live memory/storage callers, eight signed/unsigned
threshold boundaries in both pipelines and actual stale/checked-cast negatives
pass focused kernel/Lean observation checks. Finder and skeptic found no proof
or control defect; the two new module-map rows were placed inside the V07 table
with complete paths after the finder flagged their initial placement. No narrower cast, constant conversion, checked-panic payload,
Source admission, compiler/EVM experiment or production lowering is claimed.
The owned registry now covers555 exports; all528 previous exact sets and every
existing ordered fixture remain unchanged. G16/G17/BackfillA/B remain partial;
G18.01 and G18.06 prerequisites, delegated G18 children and G19, five Terra
rank-glue proposals and zero constructor coverage retain their prior status.


## Effectful conditional expressions

`ConditionalAssignments` transports actual Source `cond` with a local Boolean
assignment condition and local assignment branches. Its typed target prefix
captures the condition in one fresh binder, reserves a separate result binder,
executes only the selected assignment, captures its reached value and reads the
result before dropping both temporaries. Branches and condition may alias when
their types permit it, including all roles naming one cell.

The initial ContextMap relation and Boolean value reflection derive the choice,
reached reads, actual Source/target runs, returned value relation and full
post-context alignment. No branch purity, disjointness, desired run or final
relation is supplied. The exact caller state and untouched Source machine,
target storage/heap/net/balance/transaction fields remain explicit. Arbitrary
Thin extension uses the existing Operand runner. Generic value correspondence
is an explicit component parameter, not source admission or a heap compiler.

`ConditionalControls` supplies seven closed headline clients and two inhabited
mixed context witnesses. Both branches and pipelines have complete ordered
numeric observations; Boolean controls overwrite the original condition after
selection and read an aliased donor at its reached value. Actual eager, stale
condition and post-drop consumers return11 instead of7. Live memory/storage,
all-role aliases and fresh context controls are inhabited. A separate actual
Source/target division-zero conditional fixture distinguishes skipped and
selected failure by success classification only; it proves no general payload
or arbitrary-branch lowering theorem. Finder/skeptic reviews found no defect.
All571 owned axiom guards retain the555 prior sets and all old ordered fixtures.
This is G17 expression work; G19 remains delegated to V17. G16/G17/BackfillA/B
remain partial, G18 admission/composition prerequisites stay open, and no
constructor or external compiler/EVM coverage is added.
