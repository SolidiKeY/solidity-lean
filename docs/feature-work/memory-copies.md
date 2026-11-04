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

## Compiled alias binding

`AliasBindingInterface.lean` states exact scoped alias rebinding and emitted execution, including bounds refusal, reached representation, caller stack and complete allocator preservation. Selection is tied to the existing `Objects.compilePtr`; no admission or new path compiler is supplied. The published heap-only alias interface remains unchanged.

`SelectedAlias.execute` derives the actual resolved reference, exact `TRun.rebindMem` state and emitted local store or actual bounds refusal from the existing selected pointer certificate. Successful rebinding preserves all heap objects, caller stack and any supplied complete allocator; it assumes neither path resolution nor target execution. Selection still requires actual `compilePtr` availability, not new path admission. This extends the emitted-code boundary without claiming a deep-copy emitter, Source.EM correspondence or physical byte execution.

Populated controls use an indexed fixed parent: source root0 is installed as address16, allocator40, other local24 and old payload7 remain. Index2 is compiled and actually reverts on both sides. Incorrect fresh address40 and empty code are rejected. Independent read-only finder and skeptic passed with no concrete findings, without Lean/build/server/writes. All three files have zero MCP errors and warnings. The initial fixture used the wrong literal constructor; it was corrected to the existing Simple-to-Val constructor with explicit literal range proofs, without weakening statements or budgets. Existing PtrFrag.correct, StateRepr.setMem and AllocatorRepr.localWrite supply the simulation. Checkpoint gates and scoped axiom reports are required before acceptance; whole G33/G35 remains open.

## Allocating runtime rebinding

`RuntimeRebindInterface.lean` joins exact scoped rebinding and existing emitted reference-array construction with allocator growth, retained old objects and fresh-root distinction. Whole-parent capacity stays explicit; this does not select allocation-size failures or extend Source admission.

`RuntimeNestedDefault.rebind_correct` uses the selected production child with existing `referenceRebind_correct`, deriving both scoped source and emitted target runs, reached representation, exact complete allocator growth, base extension and caller stack. `referenceArray_keeps` and `referenceArray_fresh` preserve every old typed object and distinguish every old reference from the fresh parent, using existing vector-copy and allocation laws. This requires no G34 path/rebinding premise for these existing direct-local constructors.

Controls compose an actual declaration and allocating rebind through the reached represented state/allocator on populated ownership. Initial size2 advances40to71; empty replacement reaches72 and size64 reaches1032. The replaced parent remains readable through its old reference and distinct from the fresh root. A single concatenated emitted program has the same cursor; wrong71 and skipped code are rejected. Independent read-only finder and skeptic passed without Lean/server/build/writes. All three files have zero MCP errors and warnings. Initial control annotation/automation issues were corrected after MCP inspection; no statement or budget was weakened. Whole-parent fitting success remains explicit and inhabited; Source.EM graph admission, physical bytes/gas, runtime failure selection and full G33/G35 remain open. Checkpoint gates and scoped axiom reports are required before acceptance.

## Source reference-element default arrays

`SourceLeafInterface.lean` fixes a proved existing Source leaf constructor and successful arbitrary-length `zeroElems` result, including exact child addresses, reached frontier and old-object/nonheap frame. This does not supply emitted compilation or failure selection; existing Source admission remains unchanged.

`SourceLeafDefault.elements` derives the actual `zeroElems` run for arbitrary count and explicit sufficient horizon count+2+slack: one fresh child per position at before.next+i, exact count growth and full allocation frame. `bytesLeaf`, `stringLeaf` and `dynamicLeaf` prove actual existing zeroVal instances, not assumed Source equations. `SourceLeafDefault.fixed` allocates the fixed parent through actual zeroVal/zeroData/allocRef at count+4+slack and supplies the existing complete SourceDefaultCertificate. No alternate evaluator, state model, shape selector or H16 Source edit is introduced.

Populated controls derive empty and64-element bytes-array observations, string children and dynamic children whose element type is bytes. Dynamic child defaults remain empty; no populated-child recursion is claimed. Insufficient horizon times out after one real child while preserving old content, and the wrong parent root/frontier is rejected. Independent finder and skeptic passed without Lean/server/build/writes. All three modules have zero MCP errors/warnings; proof repairs followed goal/try and existing run laws, with no budget or statement weakening. Source child/parent success does not discharge compiler/layout/physical-byte correspondence, S03 allocation failure selection or general guarded graph adequacy. Full G33/G35 remains open; checkpoint gates and scoped axiom reports are required before acceptance.

## Nested Source construction certificates

`SourceConstructionInterface.lean` extends the existing SourceDefaultCertificate with exact object count, sufficient positive horizon and last-allocated parent. It is a proof certificate over zeroVal/zeroElems, not a compiler, evaluator, Source admission rule or replacement failure semantics. Object count is distinct from word/byte allocation size and gas.

`SourceLeafDefault.construction` lifts proved leaves into complete existing Source default certificates. `SourceConstructionCertificate.elements` derives actual child traversal and exact count*child.objects growth. `.fixed` closes these certificates under arbitrary fixed-array length: objects=count*child.objects+1 and sufficient horizon=count+child.horizon+2, with the parent allocated last and full old/nonheap preservation. These are proofs of existing zeroVal/zeroData/zeroElems/allocRef, not a new evaluator or lowering framework. They can be iterated to arbitrary finite fixed nesting around the proved bytes/string/empty-dynamic leaves, without a Source admission selector.

Controls derive actual root/frontier9/10 for bytes dimensions[2,3],66/67 for strings[1,64],1/2 for an empty outer array with a large unused child, and9/10 for fixed nesting around empty dynamic children of bytes. Full certificates preserve an old live Boolean and all nonheap fields; wrong count8/9 is rejected. Independent finder and skeptic passed without Lean/server/build/writes. Direct proofs passed diagnostics; explicit fixture signatures and have types are retained. All three files have zero errors/warnings. Standalone count-arithmetic probe passed explicit successor-multiplication rewrite plus omega. Counts are Source object identities, not physical allocation size or gas; runtime failure selection, compiled layout, general guarded recursive graphs and full G33/G35 remain open. Checkpoint gates and scoped axiom reports are required before acceptance.

## Heterogeneous Source struct defaults

`SourceFieldsInterface.lean` records actual zeroVal/zeroFields success and exact Source object counts, allowing existing proved reference constructors and primitive defaults to compose. The actual environment field list remains the struct index. No new evaluator, compiler, admission or failure semantics is introduced.

`SourceValueConstruction.pureDefault` derives actual zeroVal from its static default equation; `.value` lifts proved reference constructors. `SourceFieldsConstruction.nil/cons` compose existing heterogeneous zeroFields runs with additive object counts and complete AllocationExtension. `.structDefault` uses the exact E.layout.fields index and existing Source zeroVal/zeroData/allocRef to allocate the parent last and return a complete SourceConstructionCertificate. No interpreter, compiler, admission selector or H16 Source edit is added.

Own declarations cover a uint tag, fixed bytes[2], string and dynamic bytes[] holder (six fresh objects, root6/frontier7), plus a Node with a dynamic array of its own declared type and bytes payload (three objects, root3/frontier4). Dynamic defaults are empty, so this is a concrete dynamically guarded self-reference default, not a general recursive graph/copy theorem. Controls check actual bytes/string child contents, old live Boolean and full nonheap preservation; low horizon retains the recursive-array child, and wrong root5/frontier6 is rejected. Independent finder and skeptic passed without Lean/server/build/writes. All three files have zero MCP errors/warnings; direct proofs passed and standalone count-composition probes passed omega. Object counts/horizons remain distinct from physical size/gas. Emitted layout, Source admission, allocation failures and full G33/G35 remain open. Checkpoint gates and scoped axiom reports are required before acceptance.

## Source byte-copy traversal

`SourceBytesInterface.lean` states actual typed persistent storage-cell inputs over published Source.Storage. Payload cells are indexed by the existing path and byte position. No aggregate-load success, code execution or physical layout is a premise; this interface covers persistent storage inputs and does not supply Source admission.

`PersistentSourceCell.read` reuses published G18 read_typed. `sourceByteRange_run` proves actual existing loadBytes for arbitrary payload, start and sufficient horizon; sourceByteLength_run/sourceBytesLoad_run derive the complete bytes load from actual typed persistent length/payload cells. `sourceBytesCopy` then inhabits the existing fresh-root SourceStorageCopyCertificate through the actual allocator. No aggregate-load success, alternate interpreter, compiler, physical layout or Source admission is supplied. Persistent storage is the explicit fragment; strings and broader nested storage-copy compilation remain open.

Controls use an actual declared bytes root and derive fixture-cell reads for every initialized index from Source.Storage.write_read/write_other. Complete copied payloads of lengths0/2/64 are observed after actual loadElem; old Boolean/nonheap state is retained. Wrong [8,7] is rejected against actual [7,7], and insufficient horizon times out before root allocation rather than asserting panic or gas behavior. Independent finder and skeptic passed without Lean/server/build/writes. All three modules have zero MCP errors/warnings. The interface width was made explicitly one byte in a follow-up signature commit before proof commit; direct bind reduction avoids generated dependent match-equation trouble without editing Source. Cast/finite-index fixture proofs use explicit congruence after MCP goal/try. No theorem statement, exclusion or proof budget was weakened. Standalone horizon probes passed omega. Checkpoint gates and scoped axiom reports are required before acceptance; full G33/G35 remains open.

## Source string copies

`SourceStringsInterface.lean` states the complete existing Source string-copy certificate family from actual persistent typed length/payload cells. It shares the byte-reader input boundary, without assuming aggregate success, string/bytes admission conversion or emitted execution.

`sourceStringLoad_run` consumes the proved Source byte range/length reader in the existing string load branch, preserving exact byte order and input state. `sourceStringCopies` inhabits the complete SourceStorageCopyCertificate family through the existing fresh root allocator. This shares proof infrastructure, not a bytes-to-string Source admission rule or new interpreter.

A separately declared string root stores distinct bytes[17,23]. Actual copied string payload order and empty copying are observed; old Boolean/nonheap state is retained, reverse[23,17] is rejected and insufficient horizon times out before allocation. Independent read-only finder and skeptic passed without Lean/server/build/writes. All three files have zero MCP errors/warnings; direct proofs passed. Standalone negative-control probe passed decide. Persistent Source inputs and uint256 length range remain explicit; physical storage layout, emitted compilation, allocation-size/gas failures, broader nested copying and full G33/G35 remain open. Checkpoint gates and scoped axiom reports are required before acceptance.

## Nested Source byte-array copies

`SourceNestedBytesInterface.lean` states actual existing loadElems results from typed persistent child length/payload cells. Every child receives its exact sequential fresh identity and retains its full byte payload after sibling allocation. The horizon is an interpreter budget, not gas or physical size; no aggregate load success or admission selector is assumed.

`PersistentSourceCell.transport`, `SourceByteRange.transport` and `StoredSourceBytes.transport` retain actual storage input facts through existing AllocationExtension frames. `sourceByteChildren_run` derives actual loadElems for arbitrary child byte payloads, exact sequential child identities, count growth and complete payload retention after all sibling copies. `sourceNestedBytes_copy` derives the dynamic parent load and existing SourceStorageCopyCertificate, keeping every child payload after parent allocation. No compound run is assumed; no new interpreter, admission selector or Source/H16 edit is added. Horizon is an explicit sufficient interpreter budget, not gas/physical allocation size.

Own declared bytes[] controls copy [[17,23],[]] with children1/2 and parent3/frontier4, checking final payloads and references. Empty parent reaches1/2;64 empty children reach parent65/frontier66. Wrong root2/frontier3 is rejected; insufficient horizon7 times out before allocation in the populated control. Independent read-only finder and skeptic passed without Lean/server/build/writes. All three modules have zero MCP errors/warnings. Explicit finite-index signature types were corrected in a separate pre-proof commit; proof repairs followed MCP goal/try and existing bind laws, without weakening a statement or budget. Standalone child-address arithmetic probes passed omega. This is a persistent two-level Source bytes-array fragment; general recursive graphs, physical layout, emitted compilation, size/gas failures and full G33/G35 remain open. Checkpoint gates and scoped axiom reports are required before acceptance.

## Heterogeneous Source storage copies

`SourceStoredFieldsInterface.lean` indexes actual loadElem/loadFields proof families by the exact path, field types and starting index. AllocationExtension describes the reached memory growth while retaining original storage inputs. No second interpreter/compiler, Source admission or desired struct-load equation is introduced.

`SourceStoredValue.primitive` derives nonreference loadElem from actual typed cells; `.bytes`/`.string` use proved copy inputs transported through allocation frames. `SourceStoredFields.nil/cons` compose actual existing loadFields runs with summed Source object counts and complete framing. `.structCopy` indexes the exact E.layout.fields list, derives actual struct loadMem and the existing SourceStorageCopyCertificate through fresh parent allocation. The proof families describe existing operations and do not introduce another evaluator/lowering framework or assume a desired aggregate run.

Own declared Bundle controls preserve uint42, bytes[17,23] and string[65], with children1/2 and parent3/frontier4. Actual field reads, final child payloads and complete old/nonheap framing are checked; wrong root1/frontier2 is rejected, and horizon8 times out before allocation. Independent finder and skeptic passed without Lean/server/build/writes. Main direct proofs passed; concrete constructor and horizon/count annotations were repaired without changing statements. All three files have zero MCP errors/warnings; MCP goal/try and standalone count arithmetic probes are retained. Object counts/horizons are Source quantities, not physical size or gas. Persistent finite fields only: compiled layout, Source admission, allocation failures, general recursive graphs and full G33/G35 remain open. Checkpoint gates and scoped axiom reports are required before acceptance.

## Source stored-reference closure

`SourceStoredReferencesInterface.lean` states witnesses in the existing SourceStoredValue certificate at exact Source types, horizons and object counts. It extends proof closure for nested structs and dynamic arrays; it does not select an admitted shape, execute another evaluator, or supply physical code.

`SourceStorageCopyCertificate.allocates` derives the complete allocation extension from its actual load and root allocation. `SourceStoredValue.structValue`, `.emptyArray` and `.byteArray` close the existing certificate families under nested struct fields, empty arrays at any element type, and dynamic byte children. Exact object counts and sufficient horizons compose through existing Source operations; persistent static inputs transport through intervening allocations. No aggregate execution equation, new interpreter or Source admission selector is assumed.

Own declared Outer contains two copied Inner structs and a byte-array field. Distinct inner roots3/6, byte-array root7 and outer root8/frontier9 are checked; bytes[17,23], string[65] and empty sibling payloads survive. A declared Node contains an empty Node[] and bytes, reaching root3/frontier4. This empty self-reference is not general recursive graph coverage. Old Boolean/nonheap state, wrong alias root and timeout controls are retained. Concrete payload/identity observations use small typed projections and kernel decide, avoiding large dependent equality reduction within the unchanged proof budget. Independent read-only finder/skeptic passed, including the final projections; neither used Lean/server/builds or wrote files. All three new modules have zero MCP errors/warnings; standalone horizon arithmetic probes pass. Full checkpoint gates and scoped axiom receipts remain required before acceptance.

These are Source execution/frame/count proofs, not physical storage layout, emitted code, gas/size failures or general graph admission. Generic semantic-value equivalence beyond actual Source runs is not added. Full G33/G35 remains open, including local compiler/composition work; producer boundaries remain VY5 H16/S03-PANIC41 then memory-reference-structs, V11 G34/G35.02/.03 and V10 G27.05. No public interface, premise, exclusion or proof budget is changed.

## Source stored-element traversal

`SourceStoredElementsInterface.lean` states a count-indexed proof family over existing loadElems, retaining actual element type, path and starting index. Fixed/dynamic array closure witnesses reuse SourceStoredValue and exact child/parent counts; no new evaluator or Source admission selector is introduced.

`SourceStoredElements.nil/cons` compose actual loadElems from the existing SourceStoredValue family at any element type, transporting persistent inputs through sibling allocations. `.dynamicCopy` derives actual readLen/loadMem and fresh parent allocation; `.fixedCopy` uses the type's fixed count without an artificial length cell. `SourceStoredValue.dynamicArray/fixedArray` close the same proof family with exact summed child counts plus one parent. No desired aggregate execution, new evaluator/compiler or Source admission selector is supplied.

Own declared Node copies two child Nodes: their arrays are empty, one payload is bytes[17,23] and the other empty. Children occupy roots3/6, their parent array7, root payload[65] at8, and outer Node9/frontier10. Typed observations retain exact child references and payloads. A separate uint256[2] copies [42,7] with parent1/frontier2 and no child allocations; an empty generic traversal also reaches1/2. Complete old/nonheap framing, wrong alias and timeout-before-allocation controls are included. Independent read-only finder/skeptic passed both initial and final controls; neither used Lean/server/builds or wrote files. Direct main/control proofs passed per-file diagnostics; all three modules have zero errors/warnings, standalone count-composition probes are retained. Checkpoint gates/scoped axiom receipts are required before acceptance.

The proof family composes finite certificate trees, including this populated recursive declaration instance; it does not select certificates for every approved graph or establish generic semantic-value equivalence beyond actual Source execution. Physical layouts/emission, gas/size failures, complete Source-to-target refinement, general graph admission, five-location composition and full G33/G35 remain open. Local compiler/composition work remains, alongside the unchanged VY5 H16/S03-PANIC41, V11 G34/G35.02/.03 and V10 G27.05 boundaries. No public interface, premise, exclusion or proof budget is weakened.

## Intrinsic traversal footprints

`TraversalFootprintInterface.lean` states exact heap identity growth, parent-last allocation and separation for sequential intrinsic deep-copy subtrees. These are obligations about existing copyStToM, not a new traversal/compiler, physical word costs or Source admission.

`liveObjectCount`, `fieldObjectCount` and `elementObjectCount` are proof measures of existing intrinsic live values; they do not execute copies or count storage-only shadows. Mutual `valueCopy_count/fieldsCopy_count/elementsCopy_count` prove exact growth for actual copyStToM at every existing mapping-free type. `copy_parent_last`, `copy_root_index` and `liveObjectCount_positive` derive the parent identity and nonzero reference footprint. `traversalFootprint` inhabits the count/parent-last interface; `traversalPairFootprint` composes exact counts and separates the two roots around the intermediate allocation boundary. Its generic fields do not explicitly quantify every descendant's interval membership.

Populated controls retain an old array and copy a three-level dynamic/fixed tree with duplicate equal branches and nonempty storage-only shadows. Seven new identities are allocated (root7/frontier8); a second equal tree reaches root14/frontier15. Concrete descendant IDs[[1,2],[4,5]] and all live payloads[7,11] are checked. An empty live array allocates one object despite its shadow;64 complete branches consume193 identities. A struct-held array is also certified. Wrong shared root and shadow-inclusive count are rejected; existing generic contents certificates retain the full live roundtrip. Counts are object identities, not physical words, bytes, fuel or gas; no new capacity premise or shape exclusion is introduced. Mapping copying remains outside the existing mapFree domain, not a new restriction.

Independent read-only finder and skeptic passed, including final explicit type annotations and unchanged old-object observation; neither used Lean/server/builds or wrote files. Skeptic's scope nuance is recorded: generic pair facts concern roots/counts/boundary, while descendant identities are concrete controls. All three new modules have zero MCP errors/warnings; direct count/parent-last proofs passed, empty-heap inference and zero-add normalization were repaired, and MCP/standalone arithmetic probes pass. Checkpoint gates and scoped axiom receipts remain required before acceptance.

This extends intrinsic traversal obligations only. It does not prove general recursive Source graph admission/adequacy, a compiled storage-copy selector, physical storage/layout/emission, checked size/gas failures, five-location composition or full G33/G35. Those and final lane-end run-lean remain open, with local work still available and unchanged VY5 H16/S03-PANIC41, V11 G34/G35.02/.03 and V10 G27.05 producer boundaries. Public interfaces, premises, exclusions and proof budgets are unchanged.

## Published dependency adoption

The lane adopts published master6f3eedf0788ee1f8a3bcf230558c712ecdca04d5. Its accepted bounded snapshot imports TraversalInterface, TraversalFresh and TraversalControls from producerbec559c82c084ecbb55de5dc4aabc4fdcfde355a; the rest of this branch remains unintegrated work. The owned Lean modules and prior feature documentation were preserved byte-for-byte during rebase. Only append-only module-map conflicts required resolution; existing published rows take precedence, with one row per module. Root regeneration removes duplicate imports created by union merging. No theorem statement, premise, exclusion, Source semantics or proof budget changes.

The original G33/G35 queue remains partial. Published P1 native-unwind/activation and P10 linked-backedge leaves do not supply full PROFILE/CALL closure. H24 checked-input obligations remain explicit; no P8 admission inhabitant or general physical copy preservation is supplied. H16/S03-PANIC41 remains VY5-owned and unmerged; existing V11 G34/G35.02/.03 and V10 G27.05 boundaries remain unchanged. New compositions must use the published dependency without treating these bounded leaves as whole-lane closure.

Independent read-only finder/skeptic confirmed unchanged owned Lean proofs and master compatibility. They found duplicate traversal map rows and stale Interface/SourceInterface descriptions after rebase. These were fixed by retaining published rows for integrated modules and preserved corrected rows for unintegrated modules, with one row per module. No Lean/server/builds or writes were performed by reviewers.

## Compiler-selected reference children

`SelectedArrayDefaultInterface.lean` extends the existing DefaultBuilder proof family to runtime parents over any production-supported reference root and fixed wrappers. It carries the actual compileDefault result and a fitting represented input for the entire parent, without a separate unused-child capacity premise. No new selector, builder, emitter or Source admission classifier is introduced.

`fixed_selection_total` lifts actual existing compileDefault support through arbitrary fixed wrappers; `primitive_struct_selected` discharges the base support fact for primitive-member structs. `fixed_default_cost` retains exact word-cell demand including each fixed parent and child. `selectedArrayDefault` extracts the actual production result, and execution/declaration correctness reuses existing referenceArray_correct/referenceDeclare_correct. The same emitted code handles all runtime lengths; empty-parent demand is one cell, with no separate child-fitting premise. This is a proof-family extension over DefaultBuilder, not a second compiler or emitter.

Populated controls compile actual Pair[] and Pair[2][] construction: length2 reaches cursor47 and55 respectively, length64 fixed-struct children reaches489, empty reaches41 from40; old payload7 survives. The nested source identities are5/8 and3/4/6/7 with all Pair fields zero. An actual scoped declaration executes the existing emitted code, retains caller stack and reaches55. Selection, whole-parent allocator witness, code equality across lengths and wrongcursor54 rejection are inhabited. Arbitrary fixed dimensions retain an empty-parent witness without requiring child room. Source refers here to existing intrinsic typed execution; Source.EM graph/layout adequacy is separate.

Independent read-only finder/skeptic passed, including final explicit dependent type annotations; neither used Lean/server/builds or wrote files. All three modules have zero MCP errors/warnings. Direct proofs passed after namespace/root parameter and concrete HRef/uint inference repairs; failed MCP probes and passing standalone cost arithmetic probes are retained. Checkpoint gates/scoped axiom receipts remain required before acceptance.

Coverage is conditional on the EXISTING compiler supporting the base root; unsupported cases remain explicit, with no claim that every approved Source shape is now selected. These successful word-memory constructions retain an explicit, inhabited whole-parent fitting bound; they do not discharge checked size/panic failures, general struct-reference compiler selection, recursive Source admission, full storage-copy compilation or five-location composition. Full G33/G35 and lane-end run-lean remain open, with unchanged VY5 H16/S03-PANIC41, V11 G34/G35.02/.03 and V10 G27.05 boundaries. No Source/public interface/premise/exclusion/budget change is made.

## Source copy horizon extension

`SourceCopyHorizonInterface.lean` states exact result and reached-state preservation for existing loadMem/loadElem/loadElems/loadFields/loadBytes under added interpreter fuel, once the lower run is not a timeout. Non-timeout refusals are retained; timeout is not identified with gas or allocation-size failure. No Source evaluator or admission classifier is added.

`CopyHorizonExtends.bind` composes exact non-timeout observations at the actual intermediate state, retaining failures and their effects without rollback. Mutual `loadMem_horizon/loadElem_horizon/loadElems_horizon/loadFields_horizon/loadBytes_horizon` derive fuel extension for every existing type/path/count, without shape or success premises. `sourceCopyHorizons` inhabits the universal certificate, and the success corollary retains the exact returned value and state. The only condition is that the lower observation is not timeout; non-timeout stuck/revert observations remain included.

Own declared bytes[][] controls copy nested bytes[17,23] with roots1/2/3 and outer4/frontier5, preserving child payloads and arbitrary extra fuel. A64-byte zero payload retains root1/frontier2 and exact contents. Existing mapping refusal remains the identical stuck halt and state for arbitrary added fuel. A real low-fuel run first allocates an empty child, then times out at frontier2 with fuel6; fuel7 succeeds at root3/frontier4. Thus removing the timeout condition would be false. Old live Boolean/nonheap state is retained even on this partial timeout, using existing allocation-frame laws.

Independent read-only finder/skeptic passed. Finder identified an untyped intermediate observation equality; its explicit type was added and re-reviewed. Neither reviewer used Lean/server/builds or wrote files. All three files have zero MCP errors/warnings. Direct recursion proofs passed after bind normalization, typed halt equality, namespace and empty-fuel arithmetic repairs; failed alternatives and passing final MCP/standalone probes are retained. No heartbeat increase or proof escape is used. Checkpoint gates and scoped axiom receipts remain required before acceptance.

This is generic preservation for already completed non-timeout copy traversals, not termination/admission for all recursive Source shapes, a physical compiler refinement, allocation-size/gas semantics or full G33/G35 completion. Interpreter timeout is kept distinct from size panic and out-of-gas. Source/H16 files and public interfaces/premises/exclusions/proof budgets are unchanged; VY5 S03-PANIC41, V11 G34/G35.02/.03 and V10 G27.05 boundaries and remaining local implementation/composition work remain open. Final lane-end run-lean is pending.
