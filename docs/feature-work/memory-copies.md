# Memory defaults and copies

`Solidity/Backend/MemoryCopies/**` holds partial certificate interfaces, local laws and inhabited controls for
G33 and G35.01/.04/.05/.06. It is not a frozen complete interface, and no
G33/G35 coverage is claimed. The existing intrinsic heap, storage-copy fold
and word allocator remain the only models; no second heap or evaluator is
introduced.

## Reused results

| Obligation | Reuse | Remaining work |
| --- | --- | --- |
| G33 | `Objects.DefaultBuilder`, `DefaultBuildResult`, `referenceArray_correct`, `ReferenceDefaults.compileDefault_correct`, `Objects.AllocatorRepr` | General nested/dynamic defaults; S03-PANIC41 size failure |
| G33 structs | `StructDefaults.source_pair_default`, `DefaultPlanSound` | Reused as is; their capacity premise is not a runtime panic |
| G35.01 | `copiedStruct_*` laws, `SVal`/`SFields`/`SVec.copyStToM` | Nonprimitive members, nested and dynamic aggregates |
| G35.04 | `MemoryOps.checkedSnapshotCopy`, `SnapshotSchedule`, `Heap.Keeps` | Alias versus deep-copy code and Source proofs (overlap laws `checkedSnapshotCopy_correct` exist) |
| G35.05 | `TypeGraph.Schema`, Source `zero*`/`load*` | Generic representation and traversal |
| G35.06 | `MemoryStorageCopy{Code,Compile,Laws,Source}`, `MemoryFixedMixedCopy` | Location/traversal certificates, mixed-location witnesses |

Source bytes and strings use `Source.STy`; `GraphTypeRel` has no bytes/string
constructors, and neither boundary may silently exclude approved shapes.

## Draft signatures

`Interface.lean` has the default builder certificate, storage-to-memory heap
and capacity-conditional word certificates, dynamic-length observations,
alias identity and overlap snapshots, and a finite heap traversal record that
claims no guarded-schema or total compiler coverage. The capacity-conditional
records are not yet non-vacuous: a `cost` with no room (for example `W`)
makes `StorageWordCertificate.correct` hold for empty code, as for the
existing `DefaultBuilder`. `cost` still has to be tied to the copied object's
allocation size.

`Premises.lean` has explicit boundary records with no assumed instances: the
S03-PANIC41 allocation failure and final Source state, G34 alias agreement,
and exact reached machine execution at location boundaries (G27.05,
G35.02/.03). They are not yet the producers' frozen APIs: the S03 size
predicate and the layout/path/location/refusal observations still need exact
statements.

## Interface V2: fitting allocator witnesses

`InterfaceV2.lean` (namespace `Solidity.Backend.MemoryCopies.V2`) replaces
the vacuous capacity condition. `DefaultCertificate` and
`StorageWordCertificate` each carry an `AllocatorWitness cost`: an actual
represented allocator input whose cursor fits the cost. `StorageWordCertificate`
also requires `0 < cost`. `InterfaceV2Laws.lean` derives `cost < W`, rules out
empty code (`code_ne_nil`), and refutes `cost := W` (`default_cost_W_impossible`,
`word_cost_W_impossible`). V1 stays for compatibility; consumers should use V2.
The published `Interface.lean`, `InterfaceV2.lean` and `Premises.lean`
remain byte-identical to the integration base. `SourceInterface.lean` is a
compatibility import; the existing Source certificate definitions stay in
`Interface`, including its published `Source.Hoare` import.

`InterfaceV2Roots.lean` adds an optional `StorageWordRootCertificate` companion
to an existing V2 word certificate. It fixes `base' g.val.id = cursor` and
preserves each old `Objects.Gap` below the cursor without changing V2's fields
or strengthening its existing `correct` projection.

`NewArrayLengthPanicPremise` retains all four published fields, including
`failure`. The additive `NewArrayLengthPanicInputs` in `SourceSizeInputs.lean`
has only length evaluation, successful conversion and the oversized condition.
`SourceSize` derives its panic equation and constructs the unchanged public
premise. Neither the public failure projection nor Source semantics is replaced.
Finalize-allocation/cursor-overflow semantics remain S03-PANIC41 obligations.

`ControlsV2.lean` inhabits both V2 certificates using the existing empty-array
builder and a represented allocator. Its concrete execution observes root 40,
next cursor 41 and zero length, and preserves the reserved gap [0,8]. The
positive witnesses accompany the empty-code and cost-W negative controls.

`SourceControls.lean` inhabits all five Source certificate structures. The
storage-copy witness loads a live two-element uint8 array, allocates a fresh
memory parent, preserves the old heap object and observes values 7 and 11;
index 2 panics. Bytes defaults preserve nonheap state. Timeout controls retain
the input state. These are Source executions, not a Source-to-backend
representation or compiled-code theorem.

`SourceSize.lean` derives the oversized-length panic at the reached evaluation
state. Concrete controls distinguish zero-length success, oversized-length
panic and horizon timeout. The generic theorem permits a changed reached
state; the concrete local-expression witness has no side effects.

Earlier finder and skeptic reviews checked the root/gap contract, positive
inhabitants and derived local panic result. Fresh independent finder and skeptic reviews found no semantic/API defect in
the additive correction. They verified byte-identical published interfaces,
independent panic inputs, the existing public result type and an inhabited
optional root/gap companion. Neither used Lean, builds or edits. All six
changed/new modules have zero MCP errors; the five input/proof/control modules
have no warning diagnostics. Checkpoint gates and axiom audit remain required.
Full G33/G35 implementation, total size-failure coverage, recursive traversal
and mixed-location composition remain open.

## Source traversal frame interface

`SourceFramesInterface.lean` states the next local obligations: nonheap state
is unchanged, the heap frontier grows monotonically, and every old object
retains its identity and contents. The default and storage-load families range
over every Source type and horizon, including bytes/string, nested aggregates
and recursive declarations. Outcomes are those of the existing interpreter;
these signatures neither guarantee success nor impose a new shape filter.
`Source.Horizon.Grow` and `Const` preserve events and do not prove heap growth.
The proofs must use the existing Source allocation and Hoare operations.
Physical compilation, size/finalization failures, and layout agreement remain
separate obligations; no missing producer result is assumed here.

`SourceFramesCore.lean` proves allocation-frame composition through the existing
Source bind rule and proves the allocator and typed storage reads preserve that
frame. `SourceDefaultFrames.lean` discharges all four default traversal fields;
`SourceStorageFrames.lean` discharges all five load traversal fields. These
proofs quantify over every environment, locals context, Source type, path and
horizon. They retain the real success or Halt and its reached state, even when
a child was allocated before timeout. No capacity, success or producer premise
is required for these frame laws.

`SourceRootCopies.lean` derives the complete fresh-parent Source copy
certificate from an explicit successful `loadMem` execution; its frame and
freshness observations are proved, not independent assumptions. Requested
memory type/path agreement with compiled storage layout is still separate.
`SourceFramesControls.lean` uses a declared dynamic storage array of bytes:
two empty bytes child objects are allocated at 1 and 2 and the copied parent at 3, while
the old Boolean at 0 and all nonheap state are preserved. The parent returns
the distinct child references, and index 2 panics. A fixed memory array of two
bytes references also has an inhabited default certificate. Lower horizons
time out after the first child allocation; the reached heap differs from the
input heap and is never silently rolled back.

These are Source traversal/frame and fresh-parent results. They do not prove
physical emitted-code correspondence, total successful traversal, contents for
every graph, checked allocation-size/finalization failures, or whole G33/G35
coverage. The remaining compiler and representation work stays open.

Independent read-only finder and skeptic reviews found no semantic defect in
these Source frame laws or controls. Both retain the compiler/layout/size
boundaries above. The bytes children are empty; this control does not establish
populated byte-payload copying.

## Published-interface compatibility

The integration receipt rejected a theorem named like the existing `failure`
projection. The additive correction preserves all existing public definitions,
fields and import paths, using separate input and optional root/gap records.
The signature-only companion commit precedes their constructors and controls.
No Source, admission, exclusion, dependency premise or proof budget is changed.

## Intrinsic live-copy contents

`HeapContentsInterface.lean` states the remaining live-content obligation over
the existing `SVal.Mirrors` relation. The implementation reuses
`SVal.mirrors_copyStToM`, `MVal.copyBelow_eq` and the existing strip operation.
`HeapContents.lean` constructs generic V2 `StorageHeapCertificate` inhabitants,
reconstructing full live values, including dynamic lengths and nested contents. It does not establish compiled
storage loading, Source layout agreement or recursive Source graph adequacy.
The signature commit precedes the mutual value/field/element proofs. No new
copy evaluator, capacity condition or graph selector is added. Existing
`SVal.keeps_copyStToM`, `SVal.copyStToM_id_ge` and
`SVal.copyStToM_array_len` provide framing, freshness and live lengths.

`HeapContentsControls.lean` uses live values 7/11/13, nonempty storage shadows,
a parent with child lengths 2/0/64, root identity 3 and four total objects.
Struct-held and fixed-array-held dynamic children roundtrip as well. A changed
live word 7-to-8 is rejected; the empty live child's shadow is removed.
These are observations of the existing intrinsic operations, not EVM gas or
allocation-size failure claims.

Independent read-only finder and skeptic reviews found no semantic/trust
finding, circular contents premise, new exclusion or budget change. Both
confirmed full live-content reconstruction and the explicit intrinsic-only
scope; neither ran Lean or builds. Per-file MCP errors and warnings are zero
for the three new modules. Checkpoint gates and scoped axiom reports remain
required before accepting this checkpoint.

## Fresh snapshots across overlapping old writes

`DeepCopyContents.lean` inhabits the already published
`MemoryDeepCopyHeapCertificate` using existing keeps/fresh laws and the generic
contents theorem. This uses no legacy word/default certificate or capacity
antecedent. The existing `Interface` and committed `HeapContentsInterface`
provide the signatures; no new heap, copier or certificate framework is added.

`deepCopy_schedule_contents` composes V11's published
`copy_schedule_transport` with `mirror_contents`. An explicit actual successful
old schedule transports to an actual reached grown heap: old reached objects
are kept, while the fresh root reads the INITIAL snapshot's live contents.
It assumes no unfinished G34 theorem. This is an intrinsic schedule law, not
compiled alias/path/deep-copy emission or Source refinement.

Populated controls start at [7,11,13,17], observe right overlap [7,7,11,13]
and left overlap [11,13,17,17], invalid-endpoint refusal and an empty schedule.
The actually reached old alias changes while a distinct fresh root retains the
original snapshot; an empty live object likewise receives identity1. The
negative control rejects the cascading literal [7,7,7,7], without executing a
separate streaming implementation. Finder and skeptic checked this distinction;
that wording was clarified after review. Both final read-only reviews found no
semantic/trust defect or hidden premise and used no Lean/build/server/edits.
MCP errors/warnings are zero; checkpoint gates and scoped axiom audit follow.

The compiled G33 failure path still needs H16/VY5 S03-PANIC41 finalization;
a host capacity rejection is not substituted for that behavior. Full G33/G35
compiled defaults/copies/traversal/composition remain open.

## Allocation-panic emission boundary

`AllocationPanicInterface.lean` fixes an actual Source operation and complete
reached state alongside the published panic emitter's byte-exact target slice.
It reuses `Failure.emit` and V08 `panicInput`/`panic_checked`, without another
encoder or compiler framework. `Panic41Premise` remains the explicit H16/S03
boundary; size selection and allocation finalization are not inferred from it.
The signature precedes proofs. `AllocationPanic.lean` constructs the certificate
from the unchanged typed premise and the actual published `panic_checked`
instruction theorem. The Source operation's complete reached state is retained;
Source and target machines are not related by a new simulation invariant.

Concrete oversized-length controls derive failure of actual `newArray` at
2^64 from evaluation/conversion/size facts using `SourceSize`, rather than
assuming the desired panic. The marked target has a nonempty stack/memory,
emits at byte31 across word boundaries, and halts before any suffix. The exact
packet length is36 and code length111. Memory outside the packet is framed.
Wrong Panic(0x32), empty revert and unsupported-slice `none` differ from the
observed Panic(0x41); source horizon0 and successful zero-length allocation
cannot supply its premise. This is not a claim about out-of-gas, expansion
charges, Source/target world simulation or runtime allocation-size selection.

Independent read-only finder and skeptic found no semantic defect/circular
premise or vacuous concrete control. Finder noted two untyped local `have`s
under H14; these were eliminated, and finder confirmed the fix. Neither review
used Lean/build/server/edits. Both new modules have zero MCP errors/warnings.
Checkpoint gates and scoped axiom reports are required separately.

## Production selection for nested array defaults

`NestedDefaultInterface.lean` states selection through the existing
`ReferenceDefaults.compileDefault` for fixed dimensions around a dynamic-array
default, including reference-valued base elements. The selected builder uses
the existing V2 certificate and an actual fitting allocator input. This is
intrinsic successful construction, not Source graph admission or total checked
allocation failure. The signature commit precedes `NestedDefaults.lean`. Selection is total for
all dimensions at the existing map-free element type, independent of capacity;
the implementation extracts only `compileDefault.get` with a proved `isSome`.
There is no second code generator. The exact cell cost is the right fold of
`max 1 n + n * child`, starting at1. Execution is the actual existing builder
simulation, retaining source default heap, old-cursor root, exact allocator
growth, base extension, lower cells and prior gaps. Its success capacity
condition remains explicit; no runtime failure selector is claimed.

`NestedDefaultControls.lean` supplies an actual populated represented allocator
at cursor40, with reference-valued dynamic base elements. Actual selected-code
observations are (root40,next41,old7) for no fixed dimensions, next54 for[2,3]
and next169 for[1,64]. The old live word at17 is unchanged. The selected V2
certificate is inhabited; empty code and wrong cursor55 are rejected. Target
loop results follow from checked execution, not evaluation of the target's
noncomputable loop implementation or an assumed target run.

Independent read-only finder and skeptic found no concrete semantic/trust
finding or new selector/filter/hidden capacity claim. They confirmed the
scope: fixed arrays allocate nested default children, but dynamic base defaults
are empty; populated dynamic construction, Source graph/layout refinement,
guarded recursive graphs and runtime checked failures remain separate. Neither
reviewer used Lean/build/server/edits. All three modules have zero MCP errors
and warnings; checkpoint gates and scoped axiom reports remain required.

## Runtime-length reference construction

`RuntimeArrayInterface.lean` fixes production-selected child defaults and the
complete runtime-parent cost: length+1+length*childCost. Feasibility is attached
to the entire construction, avoiding an unnecessary fitting-child condition
when the parent is empty. It extends the existing default/reference-array
framework; the signature precedes `RuntimeArrays.lean`. Child code is extracted
only from production `compileDefault` with proved selection. The same emitted
code serves every runtime size; equality follows from compiler-result
uniqueness. Empty-parent cost is1 for any child dimensions, so no fitting-child
witness is required. Whole-parent successful feasibility stays explicit.

`RuntimeNestedDefault.execute` uses the actual reference-array loop and retains
the reached heap representation, exact cursor, root address, old bases/cells
and prior gaps. `declare_correct` connects the actual scoped `TRun.declMem`
result and emitted `referenceDeclareCode`, reached `StateRepr`, allocator,
base extension and caller stack. These are intrinsic scoped-state/word-memory
results, not `Source.EM` graph or byte-addressed physical refinement.

`RuntimeArrayControls.lean` instantiates a real populated allocator and proves
root40,next41/71/1001 and preserved old word7 for runtime lengths0/2/64 with
nested child dimensions[2,3]. Same-code, empty-parent-any-dimensions and wrong
cursor70 controls are included. A separate actual populated declaration
control derives both source and target execution plus cursor71 and unchanged
caller stack from input representations, without assuming either outcome.

Independent read-only finder and skeptic found no concrete semantic/trust
finding, hidden child-capacity condition or new compiler/framework. Neither
used Lean/build/server/edits. All three new files have zero MCP errors and
warnings. Source graph admission, physical byte refinement, gas, whole-lane
adequacy and runtime size-failure selection remain separate. Checkpoint gates
and scoped axiom reports are required before accepting this increment.

## Typed traversal sibling freshness

`TraversalInterface.lean` states freshness and strict sibling identity order for the actual `SVec.copyStToM` fold on arbitrary intrinsic reference values. It introduces no traversal, graph admission or shape filter. Signature precedes implementation; compiled storage-layout refinement remains open.

`traversalFresh` proves the signature for every existing intrinsic map-free reference vector by recursion on its length, using existing copy equations, root freshness and prefix growth. Sibling roots are strictly ordered with no duplicate ids even for repeated values and nested contents. Controls copy equal trees with live child lengths2/0/64 after an old object, obtain roots4/8/9, reject4/4/9 and inhabit empty/populated certificates;64 nested values have distinct roots. This is sibling-root separation, not global descendant separation, Source graph admission, emitted storage-load traversal or physical layout.

Independent finder and skeptic identified a fixture helper lacking its intrinsic length bound. That helper now requires the bound explicitly at concrete calls. Both re-reviewed and passed without Lean/server/build/writes. All three new modules have zero MCP errors and warnings. Structural recursion replaces unsupported mutual-type induction; no statement, exclusion or budget weakened. Standalone tactic probes passed omega and explicit transitivity. Checkpoint gates and scoped axiom reports are required before acceptance.
