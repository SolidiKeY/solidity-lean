# P1-CALL reference and tuple expansion

Checked ordinary memory and tuple calls use the existing intrinsic call
expansion and word machine. Frontend Source.CallSite lowering, general recursive
graph copying and reference-element array representation remain outside this
increment. Finite struct return defaults now have an owned checked selector;
struct-argument and whole-return rebinding controls now use a live nested
struct constructed by the checked allocation prefix.

## Producer and represented inputs

RuntimeFrameV3CallProducerRef.Form classifies the existing CallRet.mem and
CallRet.rets constructors. source_tail derives old-caller environment
preservation from actual Stmt.run. coverage covers every admitted physical
input with the same caller, map, machine, frame and cursor. returns and
bare_revert use real capture, checked execution and restoration. make constructs
the exact frozen InterfaceV3.PendingCallProducer with no ReturnClaim,
BareRevertClaim or coverage premise; ProducerGoal pins its emitted plan.

NoAliasPromotion remains an explicit static condition. admitted is exactly the
plan's physical Entry conditions, not an authenticated profile. Agreement with
approved remains hprof : AdmissionAgreement; it can be reflexive if approved is
chosen as admitted. V12 P1-PROFILE owns provenance. The producer requires real
successful and bare-reverting runs; a success-only source does not thereby
inhabit this dual-outcome class.

## Typed tuple compaction and emission

RuntimeFrameV3CallProducerRefTuple.copy_run proves actual ascending downward
copies, including overlapping intervals, exact copied words, outside memory,
stack and all other machine fields. Its three-result overlap control detects
the corruption caused by descending copies.

RuntimeFrameV3CallProducerRefTupleFrame.copy_allocator preserves the same
reached heap, map and cursor through positive reserved-frame writes, including
live array/struct representations, separation and the zeroed free region.
copy_retained preserves the complete post-body caller StateRepr below the
result interval. FrameControls instantiates both with an actual nonempty array.

RuntimeFrameV3CallProducerRefTupleTyped.ResultWords.of_repr derives typed value
words and actual HRefs from the reached expanded-body StateRepr. ResultWords.copy
transports them through real copies. prepend reconstructs the result prefix
using the existing consVal/consMem representation lemmas. compacted proves the
exact Thin.keepAll/Thin.ofExt parameter removal; the output representation is
proved, not assumed as an extra simulation premise.

RuntimeFrameV3CallProducerRefTupleCall.expand_run uses Stmt.runSt_callRets.
emit constructs Composition.Statement from a checked expanded program,
retaining its exact reached allocation cost, heap/map extension, stack,
allocator growth and bare failure. Its need is the maximum of the expanded
need and full expanded context length. The emitted result-copy interval fits
below that bound, which also supplies the reserved-word footprint. No core
compiler or frozen-interface modification is needed. This is a checked emitter
from an admitted expansion, not a universal source-admission claim.

## Inhabited source and compiled controls

RefArrayControls retains the earlier allocating array-argument/array-return
case. RefTupleControls adds a mixed uint/array return with the same real old
one-element array at128 and starting cursor130. The default result array
allocates at130, then the body rebinds its returned reference to the old
argument. A bounds-checked read gates assignment of the distinctive scalar7.
Index0 succeeds; index2 bare-reverts after allocation. Both are actual runs of
the same call and physical input family. No storage-alias local occurs in
these fixtures, so their NoAliasPromotion check is vacuous; their actual memory
aliases, nonempty heap and allocation are inhabited.

Tuple source success observes scalar7, returned/original identities0/0, heap
size2 and array length1. Actual compiled success observes stack77, cursor131,
old pointer128, caller index0, returned pointer128, scalar7, restored runtime
cursor20, sentinel99, old array length/data1/0 and unused default header0.
Source identity0 is related to target address128, not equated with it.
source_observation, target_observation and missing_export_refused are
kernel-checked in addition to the general simulation and inhabited producer.

Independent #eval source/compiled checks are in
the lane-only fixture ReferenceCallEvaluation.lean (not on master) and
the lane-only fixture TupleCallEvaluation.lean (not on master). Omitting the tuple export copies
leaves private parameter words0/128 in result slots instead of128/7. Capacity
refusal rejects the real cost1 premise at W-1; it is not a runtime panic claim.
Literal revert stays selector-refused. The old core tuple selector's refusal
is retained; these modules expose a new checked emitter rather than modifying
that selector.

## Finite struct default framing and selection

RuntimeFrameV3CallProducerRefStructDefaultTarget.PlanRuns and FieldsRun prove
actual Evm.run, exact root/cursor advances, stack preservation and unchanged
reserved words1..frame. They quantify arbitrary machines with the stated
cursor, positive frame, cursor above frame and whole-plan capacity. Primitive
child arrays, field folds and parent initialization are proved from existing
allocation instructions. Each reached child and parent has its own derived
capacity bound. No source Heap.Keeps or detached arithmetic premise is used to
assume the target frame.

selector_runs proves this for every result of the existing defaultPlanAt.
select? wraps the existing defaultPlan? result with the proof, and
selection_unchanged proves exact projection equality. The rank/depth bound,
reference-element array/fixed/mapping refusals and core selector are unchanged.

RuntimeFrameV3CallProducerRefStructDefaultCompile.declare combines existing
DefaultPlan.declare_correct with the independently proved target framing. The
owned compileStatement/compileProgram extend only finite struct default leaves
and their sequence/block/branch contexts; other leaves delegate to the published
Composition selector. The new leaf still requires b>0. compileMemoryCall uses
the existing expansion and pointer export. Core Evm/Compiler and MemoryCompile
are unchanged. Typed initial representation, allocator/separation/zero-tail
assumptions, mapFree/defaultOk and whole-plan capacity remain required.

StructDefaultControls supplies a real nested return with an existing nonempty
array argument. Its default allocates an empty bool[] child, pair and outer
struct before a bounds-sensitive read. Cost is5; index0 succeeds and index2
bare-reverts after allocation. Its frozen V3 producer retains explicit hprof.
Source graph identities are root3/inner2/child1, old array0, heap size4, empty
child and zero primitive defaults. Target root133 links to inner131 and
child130; cursor135, old array128, stack77, runtime cursor20 and sentinel99
remain correct. These are identity/base relations, not raw ID/address equality.
Both observations and missing-export refusal are kernel-checked and independently
#eval-checked in the lane-only fixture StructDefaultCallEvaluation.lean (not on master).
Capacity refusal is the real cost5 premise at W-1, not a Panic41 claim. Literal
revert, zero frame base and reference-element-array defaults stay refused.

## Struct arguments and whole-return rebinding

RuntimeFrameV3CallProducerRefStructRebindControls first constructs the old
nested struct through the checked default declaration. initial_exists derives
its full StateRepr and StructAllocatorRepr from that real source/target run.
Classical choice fixes a proof-side base map; neither execution nor the
observers evaluates that map. The admitted domain remains the generic physical
resource predicate, not a whitelist of these concrete inputs.

The call takes the old struct, old array and index, allocates another nested
default result for cost5, then rebinds the result to the old struct argument.
Index0 succeeds and index2 really bare-reverts after allocation. Source returns
old identity3, retained caller identity3 and old child identities2/1, with heap
size7. Target retains both old pointers133 and the old graph131/130, while the
unused fresh default graph occupies135..139 and the cursor advances135→140.
The full source/target observations and missing-export refusal are kernel-checked
and independently #eval-checked in
the lane-only fixture StructRebindEvaluation.lean (not on master). default_root_refused rejects
returning the fresh identity6 instead of the required old alias3. The V3
producer keeps hprof explicit, supplies real dual witnesses and proves universal
same-input physical coverage.

seed_executed and machine_runtime reuse actual checked execution/footprint to
preserve the runtime cursor word. This proof sharing avoids re-normalizing the
allocation prefix; no representation or simulation premise is added.

## Remaining validation

These owned semantic increments are proved with inhabited controls. Full lane
gates and coordinator-generated root registrations remain outstanding. The
original gate remains subject to the coordinator's VA1 H6 TypeExamples split
queue; no host result substitutes for VM validation. S03-PANIC41 remains under
VY5's serial Source evaluator ownership until release.

StructDefaults.SelectionControls ties the separate G33 source bridge's
pair/nested controls to actual defaultPlan? results and checks the source
parent/fields and nested fuel8 failure. That bridge still does not establish a
direct source-address/word-root relation. No source struct admission or frontend
CallSite lowering is enabled.

## Validation and review

Use the shared per-file gate for the three new tuple modules and evaluator
fixture; build RuntimeFrameV3CallProducerRefTupleControls for their affected
closure. Actual axiom prints use only a subset of propext, Classical.choice and
Quot.sound. Basic automation precedes the hard prefix/compaction/emitter proofs.
For the exact target observation, rfl and ordinary decide hit the unchanged
heartbeat limit; decide +kernel succeeds without increasing any budget.
Independent read-only finder and skeptic found no soundness/vacuity defect.
Their stale typed-module header finding was corrected. Both also reviewed the
new selected-plan framing, declaration selector and genuine nested-return
controls without Lean/server/build use and reported no defect. Full lane gates remain
for the lane checkpoint; no original-assignment completion is claimed here.
