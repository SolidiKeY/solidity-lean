# V07: source lowering components

Partial. V07 keeps G16, G17, G18.01 and G18.06. [Modules](../module-map/v07-lowering.md)
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
G16/G17 and BackfillA/B remain partial; accepted-source graph
coverage/ranks/refusal and ordered G18 composition remain open. Constructor
coverage stays zero; no checked-payload or external EVM proof is implied.

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

Independent finder and skeptic reviews found no proof defect. The new public P8
stage/cursor and aggregate components are retained; no concrete P8 producer,
accepted-source graph totality or final aggregate/production composition is
supplied here. G16/G17 and BackfillA/B remain partial; G18.01 prerequisites and
ordered G18.06 applications remain open. G18.02/.03 belong to V16, .04/.05 to
V14 and G19 to V17. Constructor coverage remains zero; no new external
compiler/EVM experiment is claimed.

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

Changed/omitted copied client pins are rejected alongside the old mutation
controls. The reference theorem binders move from explicit forall types to
normal headers, preserving names, order, implicitness, premises and conclusions;
the15 signature-linter warnings disappear without suppression. Focused kernel
checks and independent reviews confirm the layout-only change. These clients add
checking to the default closure; they close no additional source-admission,
lifetime, production or constructor obligation.


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
products do not claim reversed operand positions are distinguishable. Finder and
skeptic found no proof defect; two copied comments were corrected. These are
kernel and Lean observation controls, not external compiler/EVM experiments.
G16/G17 and both backfills remain partial. G18.01 graph admission, G18.06
ordered V16/V14 applications, source failure/lifetime/production closure and
constructor coverage remain open; G19 remains delegated to V17.


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
with complete paths after the finder flagged their initial placement. No
narrower cast, constant conversion, checked-panic payload, Source admission,
compiler/EVM experiment or production lowering is claimed. G16/G17/BackfillA/B
remain partial; G18.01 and G18.06 prerequisites, delegated G18 children and G19,
five Terra rank-glue proposals and zero constructor coverage retain their prior
status.


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
selected failure by success classification only; it proves no general payload or
arbitrary-branch lowering theorem. Finder/skeptic reviews found no defect. This
is G17 expression work; G19 remains delegated to V17. G16/G17/BackfillA/B remain
partial, G18 admission/composition prerequisites stay open, and no constructor
or external compiler/EVM coverage is added.
The historical axiom suite and the `*Checks.lean` fixtures cited above remain
lane-only. `HeadlineAxioms` registers207 exact guards (134 theorems and73 inhabited clients) for selected arithmetic,
cast, conditional, reference and structural graph theorems in the default
closure. It does not add entries to `scripts/g07-axiom-pins.json` or discharge
missing admission, producer, production or coverage obligations.

## Full-range int256 subtraction

`SignedWordSubtraction` relates actual unchecked Source subtraction to existing
signed-to-word casts, word subtraction and signed readback for every int256
input pair, with no output-range premise. Local and assignment/read transports
derive executions, value agreement and selected post-family from initial
relations; both pipeline operand positions and private captures are preserved.
`SignedSubtractionControls` supplies inhabited headline clients, signed boundary
cases, aliases, mixed live-reference frames and wrong-sign/order/stale controls.
Checked-overflow fixtures compare success classification only. Narrow signed
widths, other operators, failure payloads and production lowering remain open.


## Full-range int256 addition and multiplication

`SignedWordAddition` and `SignedWordMultiplication` reuse the signed wrapping
identities, actual sign casts and published word operators. For all int256
input pairs, unchecked Source evaluation agrees with the intrinsic result,
including overflow, without output-range premises. Initial-family local and
assignment/read clauses derive executions and post-families; typed captures
preserve semantic operand positions, caller effects and fresh context extension.

`SignedArithmeticControls` registers20 inhabited clients and executes18 signed
boundary cases in both Source pipelines and the target. Effectful capture/caller
observations distinguish legacy MAX−1 from viaIR−2 for addition and MIN+1 from1
for multiplication. Same-slot, equal-content distinct locals, live references,
missing sign readback and stale/deferred reads are covered. Checked overflow
comparisons concern success only. Narrower signed widths, other operators,
failure payloads and production lowering remain open; queue statuses unchanged.

## Explicit unsigned narrowing

`UnsignedCasts` proves actual uint256-to-uintN explicit conversion for all32
approved unsigned destination widths. Width256 preserves the input; smaller
widths use the existing intrinsic modulo operation. The Source run helper keeps
the reached state, and the local and assignment clauses discharge its execution
premise. Initial-family assignment transport derives the target read, returned
value relation and whole selected post-family; caller locals retain uint256.
Fresh capture extension uses the published operand weakening law.

`UnsignedCastControls` supplies seven inhabited clients, all32 widths across
both pipelines and checked flags, five input boundaries, repeated aliases,
equal-content distinct locals and live reference frames. Actual ordered runs
return1 and caller257 while the alias read is7 under legacy and257 under viaIR.
Stale-local and omitted-cast executions return7 and257. Independent finder and
skeptic source reviews found no proof issue. These are kernel and evaluator
controls, not external solc/EVM tests. Other source widths and signed casts are handled below;
full cast coverage, failure payloads, graph admission and production lowering stay open;
all original queue statuses remain partial or delegated as recorded above.

## All unsigned source and destination widths

`UnsignedWidthCasts` extends the explicit-cast clauses to every approved unsigned
source/destination width pair, deriving the word embedding from published
Source implicit-range laws. It reuses `UnsignedCasts.castValue` and the actual
assignment/capture program. The reached Source state is preserved; initial
family transport derives both executions, returned value agreement and the
post-family. Caller locals keep their source type, including when the result
is narrowed or widened. Context extension uses the existing operand law.

`UnsignedWidthCastControls` supplies eight inhabited headline clients and20,480
actual Source/target cases:32 source widths ×32 destination widths ×both
pipelines ×both checked flags ×five source-wrapped boundary inputs. The raw
input−1 represents each source type's maximum after wrapping; it is no claim
of negative unsigned constant admission. The uint16-to-uint8 assignment returns1
and stores257, with old/reached alias captures7/257. Repeated aliases, distinct
equal contents, stale/omitted casts, fresh context and live caller references
are covered. Independent finder and skeptic source reviews found no proof
issue. Mixed-sign casts, constant admission, generic elaboration, graph admission,
recursive lifetimes and production composition remain open; queue statuses
stay partial or delegated. These controls are kernel/evaluator evidence, not
external compiler or EVM tests.

## All signed source and destination widths

`SignedWidthCasts` proves actual intM-to-intN casts for every approved signed
width pair. It derives the word embedding, proves the destination sign-threshold
formula and uses existing typed word truncation/subtraction, signed readback
and `Val.ternary`. Width256 is identity on canonical inputs. Repeated target
value reads are pure; effectful Source operands are captured once before the
cast and scope exit. Initial-family assignment transport derives executions,
returned agreement and the post-family, retaining the caller's source type.

`SignedWidthCastControls` supplies nine inhabited clients and45,056 Source/target
cases over32×32 widths, both pipelines/checked flags and11 source-wrapped
boundary inputs, including source minimum/maximum. These are value cases,
not out-of-range constant admission. Int16-to-int8 assignment returns−128
while storing128; alias capture reads7 under legacy and128 under viaIR.
Wrong stale/omitted casts execute7/128, and an actual wrong zero-extension
returns255 where the correct cast returns−1. Repeated aliases, equal-content
distinct locals, fresh context and live memory/storage frames are covered.
Independent finder and skeptic source/control reviews found no proof issue. The finder's module-map table placement finding was corrected.

Other signed operators and checked arithmetic, mixed-sign casts outside the supplied clauses,
constants/enums, general effects/elaborator production, graph admission,
recursive lifetimes and aggregate composition remain open. G16/G17 and both
backfills remain partial; G18.01/G18.06 dependencies and delegated children
are unchanged. No external compiler/EVM test or constructor is added.

## Unchecked signed arithmetic at every width

`SignedNarrowing` proves canonical signed wrapping is identity and narrowing
after int256 wrapping equals direct narrowing. `SignedNarrowAddition`,
`SignedNarrowSubtraction` and `SignedNarrowMultiplication` reuse the existing
int256 value programs followed by signed casts. For every approved signed
width and every input pair, unchecked Source evaluation agrees with that
actual typed target, including mathematical products overflowing int256.
No output-range premise is added. Initial-family local and assignment/read
transports derive executions, returned agreement and post-families; semantic
operand positions and capture-before-drop are preserved under both pipelines.

`SignedNarrowArithmeticControls` supplies29 inhabited clients,2,304 pure cases
and192 effect cases across all32 widths/both pipelines. Source-wrapped boundary
inputs include minimum/maximum products; these are not constant admission.
Intermediate captures and final caller observations are pinned. Asymmetric
subtraction distinguishes reversed, stale and deferred reads; pure initial
arithmetic misses the assignment even when its returned value agrees. Actual
wrong unsigned cleaning/omitted narrowing, collapsed equal-content identities,
repeated aliases, mixed references and fresh context are covered. Independent
finder and skeptic source/control reviews found no proof issue.

The frame is explicitly unchecked. Checked overflow controls compare Source
success classification only, not failure payloads or rollback. Other operators,
general operand/elaborator production, graph admission, aggregate/copy/delete/
lifetimes and constructor coverage remain open. G16/G17 and both backfills
stay partial; delegated G18 children/G19 and G18.06 dependencies are unchanged.
No external compiler or EVM testing is claimed.

## Unchecked signed negation (focused verification)

`SignedNegation` reuses the signed subtraction program for0−x at every approved
width, including minimum values. Source unary evaluation and typed target value
evaluation agree; reached-state and local-read clauses use actual Source runs.
Four inhabited clients and320 wrapped-value cases cover both pipelines and all
widths. Direct int256 negation gives128 where int8 negation must return−128.
Checked minimum refusal is classification only. Eight exact guards supplement
the207 earlier registered guards. Independent finder/skeptic source reviews
passed; no assignment/family producer or general lowering is asserted.
Full checkpoint closure/default/TestSuite/fixtures and global gates remain
pending for this addition. Whole G16/G17/backfill queues remain partial and
G18 admission/composition prerequisites and delegated children remain open.

## Effectful signed negation

`SignedNegationEffects` proves `-(i = a)` using actual Source assignment and
unary evaluation, and a typed target program that writes the caller before
capturing the wrapped negation in a fresh local. Initial integer-family
alignment supplies target reads and derives all selected postbindings and
alias reflection. The caller stores the assigned value; the expression returns
its negation. The exact states frame the Source heap/world and target heap,
global state and other caller bindings. No desired run or post-relation is an
input premise, and no production frontend agreement is claimed.

`SignedNegationEffectControls` supplies repeated-alias, self-assignment,
equal-content distinct-identity and fresh-context clients with live memory and
storage references. Both pipelines retain complete assignment/capture/return
observations.384 wrapped-value runs cover all32 signed widths, both pipelines,
minimum/maximum and near-zero inputs. Concrete wrong programs expose stale
reads, omitted writes, storing the negated value, dropping the capture before
reading it, omitted narrowing and collapsed equal-content identities.13 exact
three-standard-axiom guards cover the new headlines and closed clients.

The published H24 companion is `Lowering.P8.DeclarationGraphAdmission.Producer`,
with the unchanged frozen producer as `base` and H15 graph/refusal evidence as
`declarationGraphs`. Its existence is a typed prerequisite, not a concrete
inhabitant or Source-to-EVM adequacy result. Foundational interfaces stay below
the companion to preserve the import DAG. Concrete P8/H16 realization and
ordered admitted-source aggregate applications remain open. G16/G17, G18.01,
G18.06 and both backfills remain partial or blocked; delegated G18 children
and G19 retain their owners. Checked panic/payload/rollback, general
production, recursive copy/delete/lifetimes and constructor coverage are not
added. The controls are Lean execution checks, not external compiler/EVM tests.

Independent finder and skeptic source/control reviews passed. The finder found
that the two new module-map rows were outside the headered table; their
placement was corrected without changing the module descriptions.

## Signed bitwise complement

`SignedComplement` proves signed `~x` for every approved width by reusing the
existing typed subtraction value program for `-1 - x`. The source operation
is the independent `Source.unaryVal` definition `-x - 1`; both checkedness
modes are covered. Reached-state expression transport and initial-family
local transport use actual Source evaluation and target value execution.
Only initial reads, canonical Source ranges and existing alignment are inputs;
no returned agreement or post-run premise is added to the local theorem.

`SignedComplementControls` supplies eight closed clients with mixed live
references and fresh context,768 constructed wrapped-value cases over both
pipelines/modes and all32 signed widths, and concrete controls distinguishing
correct complement from plain negation and reversed subtraction.13 exact
standard-axiom guards cover all five core laws and eight clients. The wrapped
fixture inputs do not prove constant admission. General
operand production, checked arithmetic panic/payload/rollback, graph admission,
recursive aggregates/lifetimes and whole production remain open; no constructor
or external compiler/EVM coverage is added. G16/G17 and both backfills remain
partial, with delegated children and G18 composition dependencies unchanged.

Independent finder and skeptic source/control reviews passed with no substantive finding for the signed-complement increment.

## Unsigned bitwise complement

`UnsignedComplement` uses the actual typed word `bnot` and existing width cast,
relating it to independent Source `~x` at every approved unsigned width. Six
laws establish word canonicalization, word execution, Source value/reached-state
execution, target narrowing and initial-family local transport. Only canonical
input ranges, actual operand runs in the composition helper and initial local
alignment are premises; local transport derives both runs from initial reads.
Both checked settings are supported without changing arithmetic failure rules.

`UnsignedComplementControls` contains nine closed clients, repeated aliases,
fresh context transport and a caller with live memory/storage references. Its
768 sample executions cover all32 widths, both pipelines and checked settings;
wrapped payloads include duplicate canonical values. For uint8 input5, actual
program controls distinguish250 from the unnarrowed word complement2^256-6
and unsigned negation251. Fifteen exact inline guards pin every headline and
closed client; word canonicalization and its client need no Classical.choice.

Independent read-only finder and skeptic source reviews found no substantive
issue. The actual check initially found a missing explicit fixture import and
a dependent subtype rewrite; these were fixed. Guard-query failures retained
actual smaller axiom sets and pretty-printer wrapping before corrected pins.
These are kernel operational transport and bounded Lean execution evidence,
not compiler/EVM tests or frontend selection/admission completeness.

Queue: G16, G17/P12, G18.01 and Backfill A/B remain partial; checked panic/payload,
general operands/updates/tuples, accepted-Source graph completeness and whole
production remain open. G18.02/.03 belong to V16, G18.04/.05 to V14 and G19 to
V17. G18.06 awaits their ordered admitted-source applications, recursive copy,
delete/lifetime and representation certificates. The published H24 companion
is a typed premise without a concrete P8 inhabitant; H16/P8-SPEC remains VY5.
Constructor coverage is zero. Private rank proposals remain unproved.

## Unsigned local increment/decrement

`UnsignedLocalUpdate` proves unchecked local prefix/postfix `++` and `--` at
every approved unsigned width. Six kernel laws cover actual Source incDecVal,
evalLoc/readLoc/writeLoc execution, typed add/sub value programs, old capture,
caller write, result capture and Operand.run before both fresh binders drop.
The transport theorem derives target input and every selected postbinding from
the initial IntegerLocalFamily/read/range. Alias reflection supplies target
separation for untouched cells; no desired execution or postrelation is assumed.
Exact resulting states retain each side's heap/world and nonlocal fields.

Twelve closed clients cover every headline, repeated aliases, distinct cells
with equal contents, binder/Thin extension and a caller with live memory/storage
references. The controls execute1536 wrapped boundary/sample cases across all32
unsigned widths, both pipelines and both increment/prefix flags. They observe
the old capture, caller write, returned result and final caller. Actual Source
pair evaluation and ordered target operand/read evaluations distinguish postfix
overflow followed by an alias read: legacy returns pair(255,255), viaIR(255,0),
both leaving caller0. This is a closed combination control, not a general pair
compiler proof. Wrong post-code typed reads, skipped writes and decrements
produce different observations. A checked-overflow negative recognizes the
actual Source arithmetic-panic payload before any local write; checked lowering
and rollback/payload transport are not claimed. Eighteen queried exact inline
guards pin all new headlines/clients to the standard three axioms.

Separate independent read-only finder/skeptic source reviews found no soundness
issue. The finder requested precise wrong-read wording; the negative now runs
an actual typed Val read from the post-code state. Initial normalization,
constructor-inference and control-syntax failures are retained in lane evidence.
Scratch automation candidates failed; explicit location/composition/alias steps
were then checked separately;
no new axiom, representation, budget or source-owner change was introduced.
G16/G17/P12 and Backfill A/B remain partial, including signed/general-location
updates, general operand production and tuples/failures. G18.01 and G18.06 retain
the accepted-source/concrete-P8/ordered-child dependencies stated above; G18
children and G19 remain delegated. Constructor coverage remains zero. These
kernel proofs and bounded Lean observations add no external compiler/EVM tests.

## Signed local increment/decrement

`SignedLocalUpdate` supplies six actual unchecked signed update laws at all
approved widths. Existing SignedNarrowAddition/Subtraction carry the arithmetic;
only the pure integer `changed` helper is shared with UnsignedLocalUpdate.
Source evaluation still uses its independent incDecVal, location read/write and
local environment. Target old capture, caller write, result capture and drop
use existing typed Prog/Stmt/Val/Operand. Initial canonical read and alias-family
alignment derive both executions, returned agreement and the full selected
postfamily; no desired execution/postrelation or separate target inequality is
assumed. Exact reached states frame the nonlocal fields on each side.

Twelve closed clients and1536 matrix executions cover all32 signed widths,
both pipelines, both increment/prefix flags, extrema and ordinary values, with
repeated aliases, equal-content distinct cells, fresh contexts and live refs.
At int8 MAX, prefix++ returns-128 whereas postfix++ returns127; both write-128.
Prefix decrement at MIN returns127 and writes127; postfix would return oldMIN.
Actual wide programs without narrowing return128 and-129 respectively, which
are rejected by the controls. Both-pipeline update/read observations and
cross-order negatives retain semantic operand positions. Checked Source
MAX-overflow is a separate panic-data/no-write negative; no checked target
failure, rollback or payload transport claim follows. Eighteen queried inline
guards pin all six laws and twelve clients to the standard three axioms.

Independent read-only finder/skeptic source reviews found no proof finding.
The skeptic caught a comment saying postfix MIN-- for a prefix --MIN control;
only the wording was corrected. Scratch automation failures and the successful
signed literal-range candidate are retained; expected-message line wrapping
failures changed no observations. No source-owner/representation/budget edits
or new external compiler/EVM tests were added. G16/G17/P12 and Backfill A/B
remain partial: general locations, tuples, effects/failures and production are
open. G18.01/G18.06 retain concrete producer, ordered child, representation and
copy/delete/lifetime dependencies; delegated G18/G19 ownership is unchanged.
Constructor coverage remains zero.

## Unsigned division and remainder

`UnsignedQuotRem` proves nine laws over existing Source and intrinsic values.
For canonical unsigned operands and a nonzero denominator, truncating division
is between zero and the numerator, and remainder is below the denominator.
The output range is derived, not supplied; no narrowing is needed. Source
intRes therefore succeeds in both checked settings. Reached-pair composition
uses actual Source evalPair; local transport discharges it and derives target
reads from initial IntegerLocalFamily alignment. Both pipelines are covered.

Zero is covered separately, not excluded from admission: actual Source gives
the divZero panic payload while the native intrinsic value returns plain revert.
Their36-versus0-byte observation is an explicit boundary witness, not failure
preservation. A guarded program must supply the payload; no target predicate,
Source observation or failure projection is weakened here. General frontend
selection, effectful operands and failure-program composition remain open.

Fifteen inhabited clients cover all laws, alias repetitions, equal-content
distinct cells, fresh contexts and live refs.2304 matrix executions span all32
widths, both pipelines/checked settings/operators, zeros/extrema and ordinary
pairs; reversed operands distinguish17/5=3 from5/17=0 and17%5=2 from5%17=5.
Twenty-four queried inline guards pin every headline/client; the range law and
its client use only propext/Quot.sound, others the standard three. Separate
independent read-only finder/skeptic source reviews found no substantive issue.
Operator normalization and control-parenthesis failures are retained in evidence.

Feature arithmetic remains partial: catalog evidence originally names only
Grammar.lean; propose these two owned modules as additional component evidence,
without changing the global manifest/ledger. G16/G17/P12, G18.01 and Backfill A/B
remain partial. G18.06 awaits ordered V16/V14 applications and concrete P8
producers; G19 remains V17. No constructors or external compiler/EVM tests added.

## Guarded unsigned quotient/remainder

`UnsignedQuotRemGuard` reuses the published Checked.divPG condition and
panicStmt0x12, then captures a successful result in a fresh typed local before
Operand.run drops it. Ten laws prove guard metadata/execution, exact code and
operand outcomes, and Source/local transport from initial scalar alignment.
Both Source checked modes and pipelines are supported. Nonzero succeeds with
the derived range; zero now emits the complete Source panic bytes, observed
with the existing Backend.Failure.HaltObserves predicate. No new failure
relation, encoder, Source semantics or Backend opcode emitter is introduced.

The ABI equality is the published V08.AbiObservations.panicData_transport leaf
from059eb83d, independently validated by that integration's combined gates and
rechecked through this import closure. It imports only Source.Observe and
Semantics.RevertData, so no V07 cycle or unpublished lane dependency is added.
Backend.Failure.revert_bytes_intrinsic/ofData_observes are reused read-only.
The guarded target clause is explicit; this does not prove that every reserved
frontend path selects it. In particular payload-retention mode/front-end
integration remains an obligation, not a new source-profile restriction.

Seventeen inhabited clients and2304 matrix executions cover all uint widths,
pipelines, checked modes, zeros/extrema, aliases and live-reference contexts.
Full payload comparisons reject both wrong panic0x11 and plain empty revert.
Complete prefix/result/caller observations pin capture-before-drop; the wrong
drop read is exactly17, not quotient3. Twenty-seven queried guards cover every
headline/client; the metadata law/client use propext only, others standardthree.
Independent read-only finder/skeptic source reviews passed; the skeptic's
stronger exact negative-control observation was adopted without changing the
expected result. Failed placeholder/inference checks remain in lane evidence.

Feature arithmetic and G16/G17/P12 remain partial: general effectful operands,
locations, signed division, other operators and actual frontend production are
open. Exact local panic bytes do not provide transaction rollback, session
failure projection or whole SourceSpec adequacy. G18.01/G18.06 retain the
concrete producer/ordered-child/representation/copy/delete/lifetime boundaries;
G18 children/G19 remain delegated. Backfill A/B remain partial; constructors0
and no external compiler/EVM tests were added.


### CP43: effectful unsigned quotient/remainder

`UnsignedQuotRemEffects` derives actual assignment/read `evalPair` and typed capture programs for both pipelines. Legacy uses the old aliased denominator; viaIR uses the assigned denominator. Semantic numerator/denominator positions are preserved. Canonical initial ranges and local-family alignment derive success results and reached alias relations. Zero inputs produce complete division-by-zero panic bytes after the actual assignment; the target error has no returned state, so the failure theorem frames the actual prefix and makes no rollback claim. Ten kernel laws and 21 inhabited clients cover repeated/self aliases, distinct equal-content locals, context extension, live references and caller fields. The 2304 bounded executions include extrema, both checked settings, all widths and discriminating wrong-order/reversed-capture/drop controls. These are Lean controls, not external compiler/EVM tests or whole frontend selection.

Independent read-only finder and skeptic source reviews pass. Their final diff review identified a module-map table separator; it was removed without proof changes. Registered exact axiom guards cover all 31 new laws/clients (two empty axiom sets, 29 standard three). G16/G17 and Backfill A/B remain partial; G18.01 general accepted-source admission and G18.06 ordered composition remain open on concrete P8 and delegated V16/V14 children. G19 remains V17-owned; constructor coverage remains zero. No producer inhabitant, general failure-state projection, recursive copy or lifetime closure is supplied. Checkpoint validation/export evidence is retained separately; global inventory and final whole-lane gates are not claimed passed here.


### CP44: exact panic insertion correspondence

`UnsignedQuotRemPass` proves the actual `Prog.withPanics` output equals the supported guarded quotient/remainder clauses, including assignment/read capture prefixes for both pipelines. Eight laws cover program, operand and execution equalities and compose independent Source success/zero transport from initial canonical values and alias alignment. No desired execution or postrelation premise is introduced. Result capture/drop, reached caller assignment and full panic bytes are preserved; target errors still expose no final state, so no rollback theorem is claimed. This supplies the panic-pass link for these clauses, not frontend selection or a general compiler theorem.

Sixteen inhabited clients instantiate all headlines, aliases, context extension and live references. The 2304 bounded executions run the actual pass output against Source observations; omitted-pass native empty revert differs from complete panic data, and pipeline order distinguishes zero success from division-by-zero failure. Initial test import/denominator mistakes and automation failures are retained; corrected controls pass. Independent read-only finder and skeptic source reviews pass. Exact queried guards cover all 24 new declarations. Full G16/G17/Backfill and G18.01 obligations remain partial; concrete P8 and ordered V16/V14 child applications still block G18.06. G19 remains delegated and constructor coverage zero. These Lean proofs/executions supply no external compiler/EVM testing.


### CP45: signed and unsigned less-than

`LessThan` proves actual `Source.cmpVal`/`evalPair`/`evalE` less-than transport and intrinsic `Val`/`Prog`/`Operand` evaluation for every approved signed/unsigned integer type. Ten laws include effectful assignment/read sequencing and an initial-family-derived post-alias relation. Legacy captures old right before assignment, while viaIR compares assigned left against reached right; semantic operand positions are preserved. A fresh bool result is read before dropping all three captures; the caller is exactly the assigned state, framing nonlocal fields and live references. No frontend selection, other comparison completeness, source failure projection or aggregate admission is asserted.

Seventeen inhabited clients instantiate all headlines, repeated/self aliases, distinct equal-content locals, binder/Thin extension and mixed live references. All 2304 bounded executions cover signedness, widths, checked settings, pipelines and boundaries. Complete observations distinguish legacy `-7 < 5` from viaIR `-7 < -7`. Independent finder and skeptic identified a control that conflated initial/reversed readings; distinct actual reversed-capture and uncaptured-right programs now both pin false and caller -7, and both reviewers verified the correction. Compilation/automation failures are retained. Exact queried guards cover all 27 new laws/clients. Catalog feature `comparisons` still has Grammar-only local evidence; proposed component evidence stays in the handoff. Whole G16/G17/Backfill remains partial, G18.01 general producer completeness remains open and G18.06 still depends on concrete P8 and ordered V16/V14 children. G19 stays V17-owned; constructor coverage zero. No external compiler/EVM tests.


### CP46: all six numeric comparisons

`NumericComparisons` classifies the existing intrinsic accepts/returns judgments into exactly `<`, `>`, `<=`, `>=`, `==`, `!=`, then derives their metadata for every approved signed/unsigned integer type. Ten laws relate actual independent `Source.cmpVal`/`evalPair`/`evalE` operations to typed target values, assignment/read programs and fresh Bool captures. The main transport derives the shared result and post-alias relation from initial values and family alignment; the computed-operation premise of Source composition helpers is discharged. Actual `Prog.withPanics` is proved to preserve these comparison programs. The name adapter's fallback outside the proved six-operator domain carries no preservation claim and introduces no Source admission restriction. This is numeric-only transport, not frontend selection, aggregate admission or structural equality.

Eighteen inhabited clients instantiate all headlines and all six operator witnesses, repeated/self aliases, equal-content distinct locals, context extension and live references. The 13,824 bounded executions cover six operators, signedness, widths, checked settings, pipelines and boundary pairs. Complete ordered observations and actual reversed/uncaptured programs discriminate wrong operand positions, equality/inequality opcode substitution and stale right reads. Independent read-only finder and skeptic reviews pass without findings. Initial automation, signed-type reduction and observation-format failures are retained; no expected value or budget changed. Exact queried guards cover 28 new laws/clients. G16/G17 and Backfill A/B remain partial, including nonnumeric comparison types and frontend/general effect clauses; G18.01 general producer completeness and G18.06 ordered applications remain open on concrete P8 and V16/V14 children. G19 remains V17-owned, constructor coverage zero, and no external compiler/EVM testing is supplied.


### CP47: Boolean equality and inequality

`BooleanComparisons` proves actual independent Source equality/inequality and intrinsic value/program/operand runs, including assignment/read ordering in both pipelines. Twelve laws derive initial reads and the full heterogeneous postrelation from existing `ContextMap.Related`, its position certificate, a Boolean value clause and slot maps. Every mapped binding, including live references, remains aligned both under the three fresh captures and in the returned caller; no desired execution or postrelation is a premise. Captured scalar equality commutes, but a separate actual Source operand-reordering counterexample shows that effectful expressions do not. The actual panic insertion pass is identity on these clauses. No frontend selection, G19 compiler, full world relation or admission producer is supplied.

An inhabited initial relation and nineteen clients cover the headlines, self aliases, distinct equal-content bindings, source/target binder and Thin extension, live memory/storage, Source world and target global frames. All 32 Boolean input/operator/pipeline/checked combinations have complete captured and final observations. Actual uncaptured-right and same-typed premature-drop programs distinguish wrong bindings from the proper result; swapping already-captured local values is correctly a positive control. Independent read-only finder and skeptic source reviews pass without findings. Initial elaboration, missing observation-error handling and literal-format failures are retained, with expected values and budgets unchanged. Exact queried guards cover all 32 new declarations. G16/G17/Backfill remain partial, nonnumeric comparison types and other clauses remain open, G18.01 still lacks a general concrete producer, and G18.06 depends on concrete P8 and ordered V16/V14 children. G19 remains delegated to V17, constructor coverage zero, and no external compiler/EVM testing is supplied.


### CP48: existing-admitted address/uint160 conversions

`AddressConversions` supplies 22 laws over existing Source `Fin (2^160)` addresses and intrinsic `uint` values, the representation already documented by `PrimTy.ofName?`. The typed predicate is full scalar observation agreement; canonical Source bounds derive the target value and reject dirty high words. No representation or source-profile change is introduced. The exact existing direct integer/address typing rule, including its nonpayable/unsigned/160-bit requirements, stays intact. Actual `convExplicitVal`, `convExplicitRV` and `evalE` conversion runs are proved in both directions for values, expressions, locals and assignments. Target identity/local-copy operands are justified from initial value alignment; assignment postrelations are derived through the existing integer family or heterogeneous context map. Address-value injectivity concerns scalar account addresses, not heap aliases or local-binding identity.

Two inhabited witness lemmas and thirty clients cover the headlines, mixed live references, self/repeated aliases, equal address values in distinct bindings, binder/Thin extension and both pipelines/checked settings. The 256 sample pairs use constructed wrapped address fixtures, not raw literal-admission claims. Existing wider/signed/payable typing refusals and dirty high-word disagreement are checked. An intrinsic-only capture-then-caller-write control distinguishes the retained argument from a stale caller read without claiming Source syntax lowering for that extra program. Independent read-only finder and skeptic source reviews pass without findings. Initial dependent rewrite, type inference and numeric recursion-budget failures are retained; the budget failure was fixed using the published modulus-range theorem, without raising limits or changing observations. Exact queried guards cover all 54 new declarations. G16/G17 and Backfill A/B remain partial; general frontend selection, other scalar clauses, G18.01 concrete producer and G18.06 ordered child applications remain open. G19 stays V17-owned, constructor coverage zero, and no external compiler/EVM testing is supplied.


### CP48 public-master adoption

Rebased onto published `6f3eedf0788ee1f8a3bcf230558c712ecdca04d5` after sealing the exact pre-rebase CP48 snapshot `098296afe8fcb56b12f7e05b35a55fcd0693b0a5`. All 116 existing V07 Lean files were compared byte-for-byte and preserved. Five conflicts were limited to this area's module-map registrations; both upstream and owned modules were retained, then six duplicate rows were removed while keeping their detailed descriptions. Generated roots were regenerated. New-base validation is recorded separately from the old-base checkpoint; upstream integration passes do not substitute for private-lane checks. The partial queue and producer boundaries are unchanged.


### CP49: all six address comparisons

`AddressComparisons` relates actual Source address comparisons to the existing uint160 comparison clauses without changing either representation. Six kernel laws cover observation equality, typed values, actual Source pair/assignment runs, native capture/drop and transport. Canonical initial address observations and a full context-map relation derive target reads and the reached relation, with no desired execution/postcondition premise. Actual operand effects preserve semantic positions in both pipelines. Scalar account-address equality is separate from heap or binding alias identity; no frontend selector or admission inhabitant is supplied.

Thirteen inhabited clients instantiate every headline, self aliases, distinct equal-content bindings, capture/Thin extension and mixed live-reference callers. The 864 bounded combinations cover all six operators, both pipelines/checked settings and zero/high address boundaries. Complete scalar prefix/result/caller observations accompany exact kernel state/context framing; runtime memory-presence observations alone are not a reference-identity proof. Actual reached-caller reload and reversed-capture programs distinguish wrong observations. Both independent reviewers caught a control that originally duplicated the left capture while calling itself a caller reload; its actual index was corrected with unchanged expected output, and the failure/review evidence is retained. All nineteen new laws/clients have exact queried inline axiom guards.

G16/G17/P12 and Backfill A/B remain partial, including other scalar/effect clauses and production selection. G18.01 still needs concrete accepted-Source admission; G18.06 depends on concrete P8 and the ordered V16/V14 children. G19 stays V17-owned. Constructor coverage remains zero; no external compiler/EVM tests are claimed. Checkpoint validation and raw failing global gates are recorded separately in the handoff.


### CP50: payable address construction and erasure

`AddressQualifiers` supplies nine laws for existing Source payable construction and explicit nonpayable erasure, including effectful local assignments and actual native copy operands. Initial canonical scalar reflection and mapped slot identity derive target execution and every reached mapped binding. The Source caller retains its original qualifier; only the expression result has the payable/erased type. Direct explicit nonpayable-to-payable refusal is preserved: payable construction is a separate existing Source operation. No representation, profile, frontend selector or admission producer is added.

Two inhabited context/reflection witnesses and twelve clients cover both qualifiers, pipelines and checked settings, self aliases, distinct equal-content bindings, live memory/storage and Thin extension. The 288 input combinations each execute payable, erasure and their actual Source composition with ordered scalar captures/caller observations; composition here is bounded testing, not a general kernel composition theorem. A separate intrinsic-only control overwrites the RHS after capture and distinguishes captured17 from reloaded0. Both independent read-only source reviews pass without findings. Twenty-three exact queried inline guards cover every law/witness/client. Shared automation attempts and failures are retained; no proof or runtime budget increased.

G16/G17/P12 and Backfill A/B remain partial, including remaining scalar/effect cases and general frontend production. G18.01/G18.06 retain concrete P8 and ordered V16/V14 child dependencies; G19 stays delegated. Constructor coverage remains zero and no external compiler/EVM testing is supplied. Checkpoint and failed global gate evidence is retained separately.


### CP51: enum and uint256 conversion clauses

`EnumConversions` supplies fifteen laws over existing finite Source enum values and intrinsic uint words. The capacity bound is exactly the existing graph enum representation obligation, not an admission exclusion. Canonical initial value/family or full context-map alignment derives actual Source conversions/assignments, successful native copies and reached relations. Invalid uint inputs have separate actual Source proofs for complete Panic(0x21) and reached assignment state; no native enum guard or panic correspondence is claimed.

A real three-member enum declaration, three inhabited relation witnesses and twenty clients instantiate all headlines, aliases, equal ordinals in distinct bindings, Thin extension, allocated Source memory and typed storage references. Thirty-six valid input combinations execute both conversion directions; eight invalid controls distinguish complete Source enum panic from arithmetic panic and an incorrectly successful native copy. An oversized existing Layout with ordinal2^256 versus native0 is a representation countermodel, explicitly not an admitted source profile. Thirty-eight exact queried guards cover every law/witness/client. Independent read-only source reviews pass without findings; initial reduction, capacity-instantiation and reserved-identifier failures remain in evidence, with observations and budgets unchanged.

G16/G17/P12 and Backfill A/B remain partial, including guarded native enum failure, other widths/signs/casts and frontend production. G18.01 and G18.06 retain concrete P8 and ordered V16/V14 child dependencies; G19 remains delegated. Constructor coverage remains zero and no external compiler/EVM tests were added. Exact checkpoint outcomes and raw failed global gates remain separate in the handoff.


### CP52: guarded native enum conversion

`EnumGuard` supplies eleven laws for a typed native enum range guard and actual assignment/check/capture programs. Counts below2^256 use an existing native less-than and a representable literal; full capacity uses true justified by canonical uint range. Zero and full capacities remain covered under the unchanged representation obligation. Published panic encoding/observation laws are reused read-only for exact0x21 payloads. Initial scalar-family alignment derives both actual Source/native success and native failure correspondence. Failed Source runs retain the reached assignment; native error exposes no final state, so only its actual assignment prefix is framed, with no rollback/session claim.

Sixteen inhabited clients cover all headlines, self aliases, distinct equal-content bindings, mixed reference callers and Thin extension. One hundred actual Source/native combinations cover both pipelines/checked settings and old/RHS values0,1,2,3,255. An actual early-check program wrongly accepts old0 followed by assigned3, while the proper program panics. Native-only zero/full-capacity witnesses and a maximum-word control distinguish full capacity from a wrapped bound0; no admission of empty or huge enum declarations is claimed. Both read-only source reviews pass without findings. Twenty-seven queried guards cover all laws/clients. Dependent-Decidable, Out-map and control syntax failures are retained; no expected output or budget changed.

This closes the local assignment/uint256 enum guard clause left open at CP51, not general frontend selection or native EVM execution. Other widths/signs/scalars/effects, SourceSpec admission and failure projection remain open. G16/G17/P12 and Backfill A/B stay partial; G18.01/G18.06 still require concrete P8 and ordered V16/V14 child applications, G19 stays delegated, constructor coverage remains zero and no external compiler/EVM testing was added. Exact checkpoint outcomes and raw global gate failures are separate in the handoff.


### CP53: every approved unsigned width to enum

`UnsignedEnumGuard` supplies ten laws retaining the actual Source unsigned caller type while reusing CP52's native word guard. Existing unsigned widening/range laws prove carrier agreement; the Source primitive bridge is only a width-normalization helper, while the main theorems relate actual Source execution to the independent intrinsic program. Initial family alignment derives target reads, success/postrelations and exact0x21 failure with native assignment-prefix framing. No new guard, arithmetic law, value/state layer or desired preservation premise is introduced.

An inhabited family witness and thirteen clients cover every headline, canonical uint8 maximum255, self-alias failure, distinct equal-content bindings, mixed references and Thin extension. The 4,608 executions span all32 approved widths, both pipelines/checked settings and six old/RHS cases including each width's maximum; width8 intentionally executes255 both as a normal case and its maximum. Typed inputs use existing wrapping constructors, but observations require the original tested values to be unchanged, so this is not raw literal-admission evidence. Actual omitted-guard code wrongly accepts255. Both independent read-only source reviews pass without findings; a dependent-match fixture elaboration failure was fixed by spelling the existing type directly, without changing observations or limits. Twenty-four queried guards cover all laws/witness/clients.

The supported unsigned local-assignment-to-enum clause now covers uint8 through uint256. Signed inputs, enum-to-other-width conversions, general effects/frontend selection and SourceSpec/failure projection remain open. G16/G17/P12 and Backfill A/B remain partial; G18.01/G18.06 retain concrete P8 and ordered V16/V14 child dependencies, G19 stays delegated, constructor coverage remains zero and no external compiler/EVM tests were added. Checkpoint outcomes and failed global gates are retained separately in the handoff.


### CP54: H26 P12 NEXT interface first

`P12NextInterface` freezes request-indexed `Condition`, `MemoryCapture` and `StorageCapture` records, with `ValueRelation`, `WorldRelation` and `Aligned` over existing typed values/worlds and the published `ContextMap.Related`. `Condition` carries an actual Boolean `Operand`; captures carry actual `Prog` outputs `mem R :: Γ` or `alias R :: Γ`, with real reference-path reads rather than snapshots. Pending success/revert fields specify exact Source/native observations, reached alignment/world relations and selected-reference alias reflection. No theorem, implementation, origin adapter or concrete producer instance is supplied.

The existing context map/effectful local-assignment interface is already on master from d879ac8e; related local captures are on master from1ca9802c. These definitions are imported and reused, not copied. The new interface's87-module local dependency closure is byte-identical to published6f3eedf0. Caller-supplied Source G/F/expr provenance must still be connected to actual admitted syntax/P8 origins and H25 exact authority by their owners. `initial_nonempty` is a pending input-alignment obligation, not a successful/reverting execution witness. Alias reflection only covers selected old bindings resolving to `some ref`; shape, nullability, all-reference completeness and compiler independence require reviewed relation inputs. No Source fuel/stuck/termination/admission/resource/session/copy/delete/lifetime claim or profile exclusion follows. Source locals extended in capture postconditions classify the returned value, not Source declaration execution; native failures expose no final state.

The interface is generated by `scripts/v07-p12-next-interface.py` and its exact signatures/projection axiom output are retained for relay. H26 takes priority over CP53's still-pending ordered-fixture/KeySort validation. G16/G17/P12 and the entire original queues remain partial; G18 children/G19 remain delegated, concrete P8 and ordered aggregate composition remain open.


### CP53 recovered validation after H26 relay

CP53's two proof/control modules are byte-identical to a0d5b638; H26's sealed interface remains unchanged. The original per-file, 670-guard and checkpoint build results retain their original head. At 3246b283, the altered copied unsigned guard produced the required actual kernel rejection and all34 ordered fixture files passed, including the4,608-width matrix. CP54's passing KeySort result at that same head is reused explicitly. No successful heavy check was rerun merely for metadata, and no proof, expected observation or budget changed. Both independent read-only recovery reviews passed. The raw global pin/documentation failures and pending whole-lane gates remain failed/pending; this completes the interrupted CP53 component validation, not G16/G17/P12 or the lane.


### CP55: enum-to-approved-unsigned result narrowing

`EnumUnsignedCasts` supplies seven clauses over actual Source explicit conversion/evaluation and the existing native `UnsignedCasts` operand. Initial context alignment, enum reflection, selected slot correspondence and a Source RHS read derive the native read, assignment, returned integer relation and full post-context relation. Only the result narrows; caller enum/native bindings retain the original ordinal. Width validity and enum capacity remain explicit representation obligations, not admission evidence. Generic expression transport requires its actual Source operand run; the assignment transport discharges that premise.

Eleven inhabited clients cover both pipelines/modes, aliasing, equal-content bindings, mixed live references and fresh-context capture extension. The ordered matrix executes 1,152 cases over all32 unsigned widths. A mathematical 257-member Layout value fixture distinguishes original ordinal256 from narrowed result0 and rejects wrong code that narrows the caller; it is not an admitted Source declaration/profile claim. Source/target evals and exact axiom guards are kernel checks/Lean executions, with no external compiler/EVM validation.

G16/G17/P12 and Backfill A/B remain partial; signed enum casts, other scalar clauses, general locations/effects/frontend selection remain. G18.01 lacks a concrete accepted-Source producer; G18.06 requires that producer and ordered V16/V14 child applications. G18.02/.03 stay V16, .04/.05 V14, G19 V17. Constructor coverage remains zero. H26 request contracts still provide no concrete producer. Checkpoint validation and independent reviews are recorded in the additive handoff; failed global inventory/docs gates remain failures.

Both independent read-only finder and skeptic reviews passed without findings. All35 ordered fixture files,688 cumulative kernel guards and per-file guards passed; changed/omitted/unexpected registry controls rejected and a changed copied pin failed in Lean as required. Historical raw global failures and final lane obligations remain separate.


### CP56: enum-to-signed-word transport

`EnumSignedWord` proves seven clauses for actual Source enum-to-int256 conversion and the existing native `WordCasts.assignedToInt` operand. Initial context alignment, enum reflection and slot correspondence derive the canonical RHS read, Source assignment/conversion, native run, signed result relation and full caller-context postrelation. Caller Source enum/native uint bindings retain the full original ordinal; only the returned value is interpreted as signed. No arithmetic implementation or production compiler selection is added. Capacity remains the existing representation bound, not declaration admission.

Eleven inhabited clients include real Choice3 enum assignments, self-alias/equal-value bindings, typed memory/storage references and fresh-context extension. Storage is a typed path/reference witness, not populated storage-account execution. Thirty-six actual Source/native executions cover both pipelines/modes and all three old/RHS values. Four mathematical Layout/value fixtures cover0,2^255-1,2^255,2^256-1 with signed results0,2^255-1,-2^255,-1; no admission of that enormous enum declaration is claimed. Actual native wrong eight-bit truncation and stale pre-assignment read controls are rejected. Eighteen exact inline axiom guards pin the seven laws and eleven clients.

Independent read-only finder and skeptic source reviews passed without substantive findings. This is kernel/Lean-execution component evidence, with no external compiler/EVM test. Own CP51 EnumConversions/EnumConversionControls and published WordCasts are prerequisites; CP56 alone is not standalone on current public master. G16/G17/P12 and Backfill A/B remain partial, including narrower signed enum conversions, general effects/frontend and recursive copy/lifetimes. G18.01 still lacks concrete accepted-Source producer assembly; G18.06 needs that and ordered delegated V16/V14 children. G19 remains V17, constructor coverage zero, H26 producer fields pending and unchanged. Raw global failures and whole-lane final gates remain separate from focused checks.

CP56 focused files,706 cumulative guards and all36 ordered fixtures passed; actual changed-pin kernel rejection and registry mutation controls passed. Independent source/final-diff reviews found no substantive issue. Exact-head checkpoint/global failures are retained separately in the handoff, with final whole-lane gates still pending.


### CP57: enum-to-all-signed-width transport

`EnumSignedCasts` proves eight clauses for enum conversion to every approved signed width8..256. The actual typed target adapter captures the assigned uint ordinal, uses existing word-sign conversion and signed narrowing, then drops only its fresh capture. Published `SignedNarrowing.wrap_word` supplies normalization; no new arithmetic/compiler implementation is duplicated. Initial context alignment, enum reflection, selected slot maps and Source RHS read derive independent Source/native runs, returned integer relation and full caller postrelation. Source enum/native uint caller bindings retain their original ordinal. Capacity remains the existing representation obligation, not an admission exclusion.

The new Source Env contains256 enum members. A structural member-count proof avoids deep `decide` unfolding without changing recursion or other budgets; the failed original recursion-limit check is retained. Concrete negative assignment transport is inhabited at ordinal255→int8(-1), with typed live memory/storage references, self/equal bindings and fresh-context extension. Storage is a path/reference witness, not populated-account execution. The matrix runs4,608 actual Source/native cases over32widths/two pipelines/two checked modes/six old and RHS values0,1,2,127,128,255. Another160 primitive-value/native boundary cases use a separate mathematical full-word Layout, explicitly without declaration/profile admission. Actual native missing-sign-extension and stale-initial-read controls discriminate wrong code; fullword conversion is correctly exempt from the narrower-width missing-extension counterexample. Twenty-four exact guards pin eight laws, three witness/reflection theorems and thirteen clients.

Independent read-only finder and skeptic source reviews passed. This supplies operational typed clauses, not frontend compiler selection, P8 admission or external compiler/EVM adequacy. Own CP51 enum prerequisites are included in the cumulative bundle but absent current public master; the checkpoint alone is not master-standalone. G16/G17/P12 and Backfill A/B remain partial: signed-input-to-enum, other scalar/effect/frontend and recursive copy/lifetime clauses remain. G18.01 concrete producer assembly and G18.06 ordered composition remain open; G18 children stay V16/V14 and G19 V17, constructor coverage zero. H26 frozen fields unchanged/pending. Global failures and whole-lane final checks remain distinct from component validation.

CP57 guarded per-file checks,730 cumulative kernel guards and all37 ordered fixture files passed. Actual altered-pin rejection and exact registry mutation controls passed. Both independent source/final-diff reviews found no substantive issue. Exact-head checkpoint outcomes and raw global failures remain separately recorded; whole-lane final gates are pending.


### CP58: signed-input enum guards and transport

Public b419c3cf was adopted by rebasing the34 private commits. The original CP57 head/seals remain preserved; all old owned Lean sources and private untracked files are byte-identical. Module-map conflicts retained published rows and appended missing private rows; roots were regenerated. The scheduled merge integrated only the unsigned local-update pair, not the remaining lane.

`SignedEnumGuard` proves eleven native clauses for actual signed assignment followed by a nonnegative check, fresh UInt conversion/capture, existing enum membership guard and result/drop. Rejecting negativity before UInt membership is essential at full capacity2^256; no tighter capacity exclusion is added. `SignedEnumTransport` proves nine Source/value/evaluation/assignment clauses across all32 signed widths. Initial scalar-family relation and Source RHS read derive canonical native input, actual independent runs, enum result relation and caller-family postrelation. Validity/invalidity select the exhaustive Source conversion branches; they are not preservation premises. Failure retains exact Source reached state, native assignment prefix and full0x21 payload/HaltObserves, with no final native error-state or rollback claim.

One initial witness and24 clients cover all20 laws. The6,272-case matrix covers32widths/two pipelines/two checked modes/seven old and RHS values0,1,2,3,-1,each signed minimum/maximum. Input observations ensure no boundary was truncated away. Actual wrong native programs demonstrate missing-sign rejection at mathematical full capacity and stale-before-assignment rejection of a positive RHS. Zero capacity, local self/equal identities, fresh-context extension and typed live references are included; storage is a path/reference witness, not populated-account execution. Full-capacity Layout tests are primitive mathematical controls, not declaration/profile admission. Forty-five exact guards pin all headlines/clients.

Separate independent read-only finder and skeptic source reviews passed. This is kernel/Lean-execution evidence, not frontend selection or external compiler/EVM adequacy. Own CP51 enum prerequisites remain absent public master and are included in the cumulative bundle; the checkpoint alone is not master-standalone. G16/G17/P12 and Backfill A/B remain partial, including other scalar/constants/UDVT/effect/frontend and recursive copy/lifetime clauses. G18.01 concrete accepted-Source assembly and G18.06 ordered composition remain producer dependencies; G18 children stay V16/V14 and G19 V17. Constructor coverage zero; H26 unchanged/pending. Raw global failures and whole-lane final obligations remain separate.

CP58 guarded per-file checks,775 cumulative kernel guards and all38 ordered fixtures passed, including exact registry mutation controls and actual changed-pin kernel rejection. Independent source/final-diff reviews passed without findings. Exact-head/global checkpoint outcomes and whole-lane final obligations remain separately recorded in the handoff.

CP58 proof-head library validation passed all3,465 jobs. A retained staged whitespace failure identified one extra terminal newline; cleanup removes only that newline, without changing any declaration, proof, guard or observation. Proof-head gates and final-head focused checks retain their separate provenance; raw inventory/strict-doc failures remain failures.
