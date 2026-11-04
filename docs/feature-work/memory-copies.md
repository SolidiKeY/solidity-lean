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

## Source default horizon extension

`SourceDefaultHorizonInterface.lean` states exact non-timeout result/reached-state preservation for existing zeroData/zeroVal/zeroElems/zeroFields under additional interpreter fuel. It reuses CopyHorizonExtends and adds no evaluator, admission selector or physical allocation premise.

Mutual `zeroData_horizon/zeroVal_horizon/zeroElems_horizon/zeroFields_horizon` preserve exact non-timeout results and reached states for every existing type/count/field list under added fuel. They reuse CopyHorizonExtends.bind and existing Source operations, without a success/shape premise or new evaluator. `sourceDefaultHorizons` inhabits the universal certificate. The three `.horizon_exact` laws for SourceConstructionCertificate, SourceValueConstruction and SourceFieldsConstruction derive actual successful baseline runs from each existing certificate at slack0, then prove added fuel returns exactly that value and state.

Own declared Node has an empty dynamic array of Node, bytes[2] and string. Defaults allocate root6/frontier7 with fixed byte children2/3, parent4 and string5; construction/field certificate results remain exact under arbitrary slack. Scalar false retains the original state.64 byte children allocate root65/frontier66 with exact extra-fuel stability; empty dynamic default reaches1/2. An existing storage-reference default refusal remains the same stuck halt and state. Fuel6 first allocates Node's dynamic child then times out at frontier2; fuel16 succeeds, proving unconditional timeout stability false. Old Boolean and nonheap frame are retained on the partial run; wrong root5/frontier6 is rejected.

Independent read-only finder/skeptic passed with no findings; neither used Lean/server/builds or wrote files. All three files have zero MCP errors/warnings; direct main and control proofs passed first attempt. Passing MCP baseline normalization and standalone successor-fuel probes, with failed alternatives, are retained. Checkpoint gates and scoped axiom receipts remain required before acceptance.

These are exact initialized-result and observation laws, not general termination/admission, physical allocation room, Source-to-EVM refinement or checked size/gas failure semantics. The lower non-timeout condition remains necessary; successful constructor bridges obtain it from actual existing execution certificates. Full G33/G35, general compiler selection, storage-copy compilation, five-location composition and final lane-end run-lean remain open. No public interface, Source/H16 file, premise, exclusion, proof budget or trust expansion is made. VY5 S03-PANIC41, V11 G34/G35.02/.03 and V10 G27.05 boundaries remain unchanged, alongside remaining local work.

## Fresh repeated Source storage copies

`SourceStoredFreshInterface.lean` strengthens the existing stored-value proof family with a positive reference allocation count, a fresh parent allocated last, and two actual loadElem runs with distinct roots and retained first-root contents. No new copy evaluator or storage-success premise is introduced.

`sourceReferenceCopy_of_success` inverts actual memory-reference loadElem success, derives the real loadMem run and parent allocation, and constructs the existing full SourceStorageCopyCertificate with its parent-last identity. `SourceStoredValue.copy_result/fresh` obtain success from the existing family and derive a positive object count rather than assuming one. `copy_twice` composes two actual runs under preserved persistent inputs: exact doubled count, strictly increasing roots and first-root contents retained after the second copy. Full certificates also retain their existing old-object/nonheap laws. `second_timeout` derives the real second-zero-fuel halt at the first reached state, without rollback. Three stored-family `.horizon_exact` laws retain exact value/field/element results under added fuel.

Own declared Envelope holds bytes[] and bytes. Two populated copies produce roots5/10 and frontier11; empty copies3/6/frontier7;64-child copies67/134/frontier135. Concrete final observations retain both [17,23]/empty child payloads, first/second array references1/2 and6/7, parent struct references3/4 and8/9, and both long lengths64. Actual full repeated-run certificates, positive reference counts, canonical horizons and a second-copy timeout retaining the first root are inhabited. Wrong shared root5/5 is rejected; old Boolean/nonheap state survives both copies. These are Source object identities and counts, not physical byte/word costs.

Independent read-only finder/skeptic found no semantic defect. They noted an untyped intermediate that was removed via direct composed-frame projections; final mode-specific storage input proofs and the fix were re-reviewed and passed. Neither reviewer used Lean/server/builds or wrote files. All three modules have zero MCP errors/warnings. Main proofs needed an explicit zero-fuel exception result type; fixtures needed per-mode static cell reductions. Passing MCP/standalone budget arithmetic probes, with failed alternatives, are retained. Checkpoint gates and scoped axiom receipts remain required before acceptance.

Generic retention here concerns the actual first copied object and existing full copy/frame certificates; no new universal semantic-value equivalence relation or all-descendant Source graph admission theorem is claimed. Complete compiled storage copying, physical correspondence, checked size/gas failures, general recursive admission and five-location composition remain open, alongside final lane-end run-lean and remaining local work. VY5 H16/S03-PANIC41, V11 G34/G35.02/.03 and V10 G27.05 boundaries remain explicit. No public interface, Source/H16 file, premise, exclusion, proof budget or trust expansion is made.

## Typed paths below copied heaps

`CopyPathInterface.lean` states live-content correspondence and reference identity bounds for observations below existing copyStToM outputs, indexed by the existing intrinsic Path. Counts are object identities; this does not supply Source admission, a compiler or a physical path resolver.

`copyPathObserver` is a proof-only fold of existing intrinsic Path through existing Heap.field/index; its mapping arm eliminates the existing Empty memory mapping object. No new path representation, Source resolver, evaluator or compiler is introduced. `mirror_path` transports existing recursive mirrors below every typed path. `copy_path_contents` proves exact live content, `copy_path_absent_iff` matches live absence, and `copy_path_bounds` places every successfully selected reference inside the actual copy allocation interval. `copiedPaths` inhabits the signature. Existing mapFree and typed heap constraints are retained.

`copyPathObserver_keeps` transports actual selected values through existing Heap.Keeps. `copy_path_contents_keeps` retains live contents after preserving growth. `copy_paths_separated` proves every successfully path-selected reference from the first copy has smaller identity than every such reference from the second copy, extending earlier root-only generic separation. This does not claim every allocated object is reachable by a path or supply recursive Source graph admission.

Controls retain an old object and copy nested dynamic/fixed arrays with live values7/11 and storage-only shadow99. Reference paths select1/2/4; after another copy the corresponding descendants are1 versus8. Full child contents, arbitrary-path bounds and generic cross-copy separation are inhabited. Empty arrays,64 children, a struct field, fixed/dynamic overruns, absent shadow elements and wrong payload99 rejection are checked. Object identity ranges are not physical word costs, gas or allocation-size failures.

Independent read-only finder/skeptic found no semantic defect, including the existing-Path observer architecture and nonvacuous controls. Concrete fixture normalization needed explicit typed equalities and ordered rewrites; final all-three-file MCP diagnostics and warnings are empty. Direct proofs were attempted first; failed MCP alternatives and standalone arithmetic probes are recorded with checkpoint evidence. Neither reviewer used Lean/server/builds or wrote files. Checkpoint gates and scoped axiom receipts remain required before acceptance.

This is intrinsic typed copy observation only. Full G33/G35, compiled general defaults/storage copying, recursive Source admission/adequacy, physical correspondence, checked size/gas failures, five-location composition and final lane-end run-lean remain open. Unchanged producer boundaries: VY5 H16/S03-PANIC41 finalization/cursor overflow then memory-reference-structs; V11 G34/G35.02/.03; V10 G27.05. Public interfaces/premises, Source files, exclusions, proof budgets and trust are unchanged; remaining local work exists.

## Snapshot paths across overlapping writes

`SnapshotPathInterface.lean` states live contents and descendant allocation bounds for actual memory snapshots after old-object capture schedules, including the exact reached prefix before checked refusal. It reuses existing runCaptures and its failure decomposition; none is not a Source panic or gas result. No new schedule or memory-copy implementation is introduced.

`snapshot_paths_of_mirror` turns the preserved actual recursive snapshot mirror into all-path content and reference-range observations. `snapshot_path_success` uses existing copy_schedule_transport at an actual reached old heap; `snapshot_path_failure` uses existing copy_schedule_none_first to expose an executed prefix, the failing checked operation and the preserved snapshot observations. `snapshotPaths` inhabits both obligations. Observation corollaries prove exact absence and strict separation from every old heap reference. No generic G34 result or desired target execution is silently assumed.

Controls copy a nested dynamic/fixed tree, retaining seven old identities and allocating snapshot identities7 through13. Actual overlap writes old leaf0 in both directions: right shift reaches[7,7,11,13], left shift[11,13,17,17], while the fresh nested snapshot path still reads11. Universal path bounds7<=id<14 and old-reference separation are inhabited. A real successful first write followed by an out-of-bounds step returns none; the displayed reached prefix retains its changed alias and unchanged snapshot. An empty child path remains absent. One real write followed by64 empty endpoint captures preserves every snapshot path. Wrong cascading contents, snapshot payload7 and rollback-to-original observations are rejected. None denotes existing checked schedule refusal, not panic, timeout or out-of-gas.

Independent read-only finder/skeptic passed, including final repairs, without Lean/server/builds or writes. Main proofs passed the direct first attempt. Controls needed kernel normalization of a concrete HRef and definitional heap equality rather than nonexistent general heap decidability; the long schedule reuses existing successful-cons/end-repeat laws. All three modules have zero MCP errors/warnings. Failed MCP probes and passing standalone arithmetic alternatives are retained with checkpoint evidence; no proof budget increase or forbidden escape. Checkpoint gates and scoped axiom receipts remain required before acceptance.

These laws concern actual intrinsic capture schedules and memory snapshots. They do not prove compiled generic memory-copy selection, a streaming-copy implementation, physical addresses, recursive Source admission, checked size/gas failures or five-location composition. Full G33/G35 and final lane-end run-lean remain open, with local implementation work and explicit unchanged VY5 H16/S03-PANIC41, V11 G34/G35.02/.03 and V10 G27.05 producer boundaries. Public interfaces, Source semantics, premises, exclusions, proof budgets and trust are unchanged.

## Runtime default allocator growth

`RuntimeGrowthInterface.lean` states the connection between an actual reached complete allocator and the existing compiler GrowsAllocator relation. RuntimeGrowthExecution combines real emitted execution, reached scoped representation, that existing relation, old bases and caller stack. It adds no compiler, allocator model or size-failure semantics.

`allocator_cursor_unique` derives the unique represented cursor from the existing free cell. `growsAllocator_of_reached` converts an actual reached complete allocator into existing Objects.GrowsAllocator: every represented input cursor equals the one used by execution. `allocatorGrowth` inhabits the signature. RuntimeNestedDefault.declare_growth/rebind_growth derive real scoped and emitted executions from the existing production-selected child proofs, then retain the compiler growth relation, reached scoped representation, old bases and caller stack. RuntimeGrowthExecution.next_input uses the existing GrowsAllocator.nextInput; no new allocator/compiler relation or evaluator is introduced.

Populated controls construct actual selected nested reference defaults at cursor40, reaching71. A checked combined budget passes through the declaration to a replacement using existing AllocationInput, then composes the two actual growth relations using existing GrowsAllocator.comp. The emitted concatenated instruction list has exact cursor71+replacementCost and retains caller stack; empty replacement reaches72,64 children1032. Input cursor uniqueness is inhabited. Wrong growth30 versus actual31 is refuted at the same represented input; skipped code cannot reach72. An impossible W-sized room predicate is rejected without claiming runtime panic, revert, timeout or out-of-gas.

Independent read-only finder/skeptic passed, including final concrete Fin.val normalization, without Lean/server/builds or writes. Main direct proofs passed first attempt; controls needed explicit numeral cursor projections before omega in two budget goals. All three modules have zero MCP errors/warnings. Failed MCP inline-goal probes and passing standalone arithmetic alternatives are retained in checkpoint evidence; no proof budget increase or forbidden escape. Checkpoint gates and scoped axiom receipts remain required before acceptance.

Coverage remains successful production-selected intrinsic nested-array construction under an explicit fitting represented input. This bridges the required allocator-growth relation; it does not discharge total compiler selection for all Source shapes, checked size failures, physical correspondence, full G33/G35 or five-location composition. Source/H16 and public interfaces/premises/exclusions/proof budgets/trust are unchanged. Remaining local work and VY5 H16/S03-PANIC41, V11 G34/G35.02/.03 and V10 G27.05 dependencies remain open; final lane-end run-lean is pending.

## Default statement compiler selection

`DefaultSelectionInterface.lean` ties selected default declarations to actual Construction.compileStmt results. The support statement consumes existing compileDefault availability and introduces no compiler/emitter branch, Source admission predicate or capacity premise for selection.

`default_statement_selected` proves support in existing Construction.compileStmt for every defaultable/map-free root already supported by ReferenceDefaults.compileDefault, retaining its older Objects compiler fallback. `defaultSelection` inhabits the universal interface, and selectedDefaultDeclaration extracts only the actual returned statement certificate. Nested, fixed-wrapper and primitive-struct corollaries reuse existing child selection laws. Selection has no capacity premise. `default_statement_cost` identifies the compiler's exact default demand; SelectedDefaultDeclaration.execute uses the actual returned cert.correct, real intrinsic declaration success and explicit existing AllocationInput/frame/StateRepr inputs to derive emitted success, reached state, old bases, caller stack and GrowsAllocator. No new compiler, emitter, admission predicate or desired execution premise is added.

Controls use populated complete ownership at cursor40. Actual statement compiler outputs construct an empty dynamic reference array and an empty fixed array (cursor41), fixed wrappers[2,3] over dynamic uint arrays (54),64 fixed reference children (168), and a primitive Pair struct (42), retaining caller stack. Generic wrapper selection and exact returned-selection equality are inhabited. Wrongcursor53 and skipped execution are rejected. A struct with a bool[] field remains actually rejected by this compiler; this is an open implementation gap, not an approved exclusion. Zero-base selection refusal is kept distinct from runtime failure and capacity semantics.

The first signature commit omitted explicit C indices; its failed diagnostics were overlooked before committing. A separate signature-only correction specifies C and passed diagnostics before proof code was committed. Main proof repairs expose existing compiler branches with typed changes and exhaustive intrinsic array cases, normalize the allocation cost and state indices, and use the correct Semantics namespace. A passing MCP array-case probe and failed alternatives are retained. Controls needed intrinsic Var.user labels. Final all-three-module MCP errors/warnings are empty. Independent read-only finder/skeptic passed the interface, body, controls and final repairs without Lean/server/builds or writes. Checkpoint gates/scoped axiom receipts remain required before acceptance; no proof budget increase or forbidden escape is used.

This proves statement support over the EXISTING child compiler's supported domain and actual successful execution with checked room. It does not repair unsupported reference structs, prove total compilation of all approved Source shapes, checked allocation-size/gas failure semantics, recursive Source admission/adequacy, physical byte layout, storage-copy compilation or five-location composition. Full G33/G35 and lane-end run-lean remain open, with local work and explicit unchanged VY5 H16/S03-PANIC41, V11 G34/G35.02/.03 and V10 G27.05 boundaries. Public interfaces, Source files, premises/exclusions/proof budgets/trust are unchanged.

## Populated resolved singleton copies

`SingletonCopyInterface.lean` states a populated primitive singleton-array word-copy certificate and its root/gap companion. The typed primitive representation and a fitting allocator witness stay explicit. Code composes the existing allocator and typed-store emitters; this is a resolved-value copy fragment, not a storage-load compiler or a full dynamic traversal.

`singleton_copy_source` identifies the existing copyStToM fold with actual allocation of the typed populated object. `singleton_copy_run` composes existing allocateArray_run and writeFieldWord_run. `singleton_copy_allocator` reuses complete AllocatorRepr.allocatePrimitive/setArray and actual Heap.set_alloc_self, so the target represents the populated copied source heap rather than an unrelated default. singleton_copy_result retains exact two-cell demand, cursor root, old bases/lower cells, machine frame and all earlier gaps. singletonWordCopy constructs both the nonvacuous V2 word certificate and its root/gap companion, using generic live-content roundtrip. Typed primitive ReprV and an actual fitting AllocatorWitness2 are explicit. The length law proves the actual copied dynamic array has length1. No replacement allocator, traversal, representation or evaluator is introduced.

Populated controls emit uint11 and Boolean true copies from a represented old heap: root40, next42, length1, payload11/1 and old payload7 retained. Two actual emitted copies return roots40/42, advance to44, preserve first payload11, initialize second payload7 and retain caller stack[77] below the returned pointers. Actual source copies have distinct IDs3/4 and both live lengths1/contents. Reserved object gap, typed live roundtrip and every old identity's separation are inhabited. Empty code, zeroed wrong payload and costW certificates are rejected. A boundary room predicate is false at W-1; this is not a runtime panic, revert, timeout or out-of-gas proof.

Independent read-only finder/skeptic passed, including final repairs, without Lean/server/builds or writes. Main direct proof repairs normalized closed singleton bounds and fresh references and used existing MObj.setElem_dyn, preserving its irreducible implementation. Passing MCP normalization alternatives are retained. A whole-machine normalization control hit the existing200000-heartbeat budget; it was replaced by typed composition of the two proved emitted-run equations, without increasing budgets. Boolean representation uses definitional equality and the gap witness has explicit types. All three modules have zero MCP errors/warnings. Failed alternatives and standalone arithmetic probes are retained with checkpoint evidence. Checkpoint gates/scoped axiom receipts remain required before acceptance.

This is a resolved primitive SINGLETON value copy at exact word-cell cost2, including nonzero data. It does not compile storage reads, general lengths, nested aggregate copying, recursive Source graph admission or byte-physical/gas behavior. Successful execution retains checked room; allocation-size failure semantics are not supplied. Full G33/G35 and final lane-end run-lean remain open, with remaining local implementation/composition work and unchanged explicit VY5 H16/S03-PANIC41, V11 G34/G35.02/.03 and V10 G27.05 boundaries. Public interfaces, Source files, premises/exclusions, proof budgets and trust are unchanged.

## Loaded singleton copies

`LoadedSingletonInterface.lean` connects the existing primitive-expression compiler to the populated singleton copy body. Source evaluation and compiler support stay explicit; the target load run and primitive word representation are derived, not premises. This does not claim general array-copy selection or arbitrary-length copying.

`loaded_singleton_transport` replaces the literal push with an actual loaded-word prefix. loaded_singleton_success uses existing val_sim to DERIVE the word, ReprV and compileVal prefix run from actual expression evaluation and StateRepr, then reuses singleton_copy_result. loaded_singleton_refusal derives the existing target revert when the supported expression reverts; the allocation suffix is not executed. loadedSingleton inhabits the signature. storage_singleton_rhs/decl derive actual MRhs.copy and TRun declaration equations from an actual resolved path and singleton storage lookup. loaded_singleton_declare_correct links expression evaluation to that SAME stored singleton value and proves actual emitted declaration success, full reached StateRepr/allocator, root/local pointer, old bases, caller stack and lower-cell framing. No target run or primitive representation is a premise, and no alternate compiler/evaluator/allocator is introduced.

Controls construct an actual typed contract with uint[] stored, a populated singleton storage value and matching WordStore/ReprStore, Sim and complete allocator. The emitted expression contains SLOAD; it reads index0 through the existing checked storage compiler. For every FinW payload, the actual copy declaration reaches cursor42, local pointer40, header1 and exactly that stored payload at41, retaining reserved cell7=99 and stack[77]. Identical code loads11 and23 from different input stores; a wrong literal11 after stored23 is refuted. Actual MRhs storage-copy source equations are inhabited. Index1 is out of bounds and both source expression and target loaded-copy code revert before allocation. This bounds-refusal control does not claim whole-array copy of an empty array must revert.

Independent read-only finder/skeptic passed, including final qualification/type/normalization repairs, without Lean/server/builds or writes. Direct proofs needed existing grown-state constructor normalization, explicit root/stack projections, canonical typed index literals and constructive SLOAD membership (Instr has no generic decidable equality). Passing source-normalization MCP probe and failed alternatives are retained; final all-three-file MCP errors/warnings are empty. No heartbeat increase or forbidden escape. Checkpoint gates/scoped axiom receipts remain required before acceptance.

The generic expression is linked to the actual copied singleton by explicit same-value evaluation and lookup equations; automatic source-expression/path selection is not proved. The fixture actually reads that array's element. No Construction.compileStmt branch/whole-program selection is added or claimed. General lengths/nested aggregate copying, Source.EM/H25 authority/byte-physical adequacy, checked size/gas failures, general defaults and five-location composition remain open. Full G33/G35 and lane-end run-lean remain unfinished, alongside remaining local work and explicit unchanged VY5 H16/S03-PANIC41, V11 G34/G35.02/.03 and V10 G27.05 dependencies. Public interfaces, Source files, premises/exclusions/proof budgets/trust are unchanged.

## Canonical singleton storage paths

`CanonicalSingletonInterface.lean` makes the copied storage path select its own existing typed index-zero expression and emitted declaration code. This removes the independent expression/evaluation input for the singleton fragment; existing checked path support, resolution and singleton lookup remain explicit.

`canonical_singleton_supported` derives expression support from the existing checked storage-path predicate. canonical_singleton_evaluation proves the index-zero bound and actual child lookup from path resolution and singleton lookup, using existing Storage.find_appendM and typed primitive view laws. The caller no longer supplies an independent expression or evaluation equality. canonical_singleton_declaration reuses the loaded-declaration simulation to derive real MRhs/TRun copy, emitted run, full reached StateRepr/allocator/root/local/framing. Failed path resolution propagates to both source declaration and target revert; the canonical code contains the existing SLOAD. canonicalSingleton inhabits all four interface fields. No new path representation, resolver, type checker, compiler branch or evaluator is introduced.

Controls represent an actual uint[][] matrix containing [[payload]], including both dynamic headers and the nested data slot. For every bounded uint payload, canonical copying of matrix[0] reaches cursor42, local/rootpointer40, leafheader1 and exactly that payload at41, retaining reserved7=99 and caller stack77. Source lookup, derived evaluation, actual storage-copy source equation and actual emitted load are inhabited. Stored23 cannot produce literal11. The invalid outer path matrix[1] fails resolution, source copy declaration and emitted declaration, with no allocation suffix executed. These controls copy the selected primitive singleton LEAF beneath a nested path; they do not copy the entire parent reference graph.

Independent read-only finder/skeptic passed without Lean/server/builds or writes. Direct evaluation proof needed local zero-index normalization and existing SVal.view_prim. Scratch MCP alternatives are retained honestly as failures; final all-three-module MCP errors/warnings are empty. Controls passed their direct first attempt. Standalone source-observation equality probes and checkpoint evidence retain the proof method. No heartbeat increase or forbidden escape. Checkpoint gates/scoped axiom receipts remain required before acceptance.

The independent same-value expression premise is removed, but successful checked path resolution and a singleton-value lookup still define this fragment. Arbitrary lengths, copying entire nested/recursive graphs, Construction.compileStmt/whole-program selection, Source.EM/H25 authority or byte-physical adequacy, checked size/gas failures, general defaults and five-location composition remain open. Full G33/G35 and lane-end run-lean remain unfinished, alongside local work and unchanged explicit VY5 H16/S03-PANIC41, V11 G34/G35.02/.03 and V10 G27.05 boundaries. Public interfaces, Source files, premises/exclusions/proof budgets/trust are unchanged.

## Canonical allocating rebinding

`CanonicalRebindInterface.lean` states actual storage-copy rebinding of an existing memory local, complete reached ownership/allocator, unchanged other lower cells, all old objects kept and strict fresh identity. The existing canonical path selects the load. This is a singleton-leaf fragment, not general G34 path compilation or whole-profile admission.

`canonical_rebind_source` identifies the actual MRhs/TRun storage-copy branch. canonical_rebind_correct composes existing canonical expression support/evaluation, loaded singleton execution, adopted ownership and StateRepr.setMem/localWrite. It derives source and emitted success, complete reached StateRepr/AllocatorRepr, cursor root, exact local pointer, caller stack, old bases and lower-cell framing. Existing SVal.keeps_copyStToM and copyStToM_id_ge supply all-old-object preservation and strict fresh-root separation; these are cited master laws, not new traversal results. canonicalRebind inhabits both success and failed-path fields. No new compiler, evaluator, allocator or path representation is introduced.

Controls use an actual nested storage matrix [[payload]] and a represented populated old array at16 with payload7, shared by two memory locals. For every bounded uint, copy rebinding redirects local2 to40, advances allocator40→42, writes length1/payload at40/41, preserves local1=16, old payload17=7, reserved7=99 and caller stack77. The actual source retains the other old alias, installs fresh source identity1 and keeps old object0. Existing selected alias code on the same input keeps pointer16/cursor40, and its actual source equation/certificate are inhabited. The target observations reject treating copy as alias. Invalid outer index1 yields actual source and emitted rebind refusal.

Independent read-only finder and skeptic PASS with no findings, without Lean/server/builds or writes. The generic proof passed its direct first attempt. Controls needed the correct intrinsic MPath.var constructor, qualified Word, explicit grown-state normalization and local with_unfolding_all around the concrete existing heap accessor; proof budgets were unchanged. The interrupted VM transport was restored in the original checkout before resuming. Failed scratch probes are retained; final arithmetic MCP decide probe passes. All three final per-file errors/warnings are empty. Standalone freshness probes retain their actual outcomes. Checkpoint gates and sealing remain required before acceptance.

This is allocating rebinding of the existing canonical primitive singleton-leaf fragment and a concrete alias comparison. It does not prove arbitrary lengths, entire nested/recursive graph compilation, general G34 path admission, Construction.compileStmt selection, Source.EM/H25 authority/byte-physical adequacy, checked size/gas failures or five-location composition. Full G33/G35 and lane-end run-lean remain open, with local work and unchanged explicit VY5 H16/S03-PANIC41, V11 G34/G35.02/.03 and V10 G27.05 producer boundaries. Public interfaces/premises/exclusions, Source files, budgets and trust remain unchanged.

## Finite populated primitive arrays

`PrimitiveArrayInterface.lean` states resolved-value copying for arbitrary finite primitive lists, extending the populated singleton fragment through existing allocation and typed-store code. A typed per-element word relation and an actual fitting allocator witness are explicit. Runtime storage-load selection and checked size/gas failure semantics are separate obligations.

`primitive_array_source` reuses SVec.copyStToM_prims to identify the actual source copy with one allocation of the populated object. arrayWordsCode composes finite unrolled calls to the existing writeFieldCode; its run theorem uses writeFieldWord_run. Exact selected-word and outside-range lemmas describe the reached memory. The allocator proof reserves once through AllocatorRepr.reserveArray, fills only that gap through writeGap, proves actual typed ArrayRepr from PrimitiveWords and adopts through adoptReservedArray. It derives complete ownership/free-tail/live reservations rather than assuming the desired post-heap. primitiveArrayWordCopy inhabits nonvacuous V2 and root/gap certificates with exact cost length+1, old bases/cells, caller frame and actual live-content roundtrip.

Controls use the represented populated ObjectArrayExamples allocator, with old payload7 at17. For every fitting bounded uint list, emitted code writes its exact length and every actual indexed payload, preserves old17=7 and caller stack77. Empty copies allocate one header (40→41); [11,23] allocates three cells (40→43); a64-element populated copy advances40→105 with final payload64 at104. Fitting certificates and source live lengths/contents are inhabited. Wrong zeroed payloads and empty code are rejected. A non-fitting room predicate is false; this is not a runtime panic, revert, timeout or out-of-gas theorem.

Independent read-only finder/skeptic found no semantic defects and confirmed existing allocator/store APIs are reused without a replacement compiler or evaluator. Both identified untyped local have facts (H14); these were fixed with explicit equation types and named typed frame/cursor facts, then both reviewers passed the repairs. Neither reviewer used Lean/server/builds or writes. Direct proof repairs exposed the constructed end-cursor value and local target; controls needed explicit existential/index types and the passing MCP rfl cursor-cell proof. Failed MCP alternatives and standalone bounded-address probes are retained honestly. Final all-three-module MCP errors/warnings are empty, with no proof-budget increase or forbidden escape. Checkpoint gates/sealing remain required before acceptance.

This is arbitrary FINITE RESOLVED primitive-array word initialization with statically unrolled stores, including empty/long/nonzero payloads. Runtime storage loading and length-driven traversal selection, arbitrary nested/recursive graph compilation, Construction.compileStmt admission, Source.EM/H25 authority/byte-physical adequacy, checked size/gas failures and five-location composition remain open. Full G33/G35 and lane-end run-lean remain unfinished, with remaining local work and unchanged explicit VY5 H16/S03-PANIC41, V11 G34/G35.02/.03 and V10 G27.05 boundaries. Public Interface/InterfaceV2/Premises, Source files, premises/exclusions, budgets and trust are unchanged.

## Loaded finite primitive arrays

`LoadedArrayInterface.lean` connects finite expression lists compiled by existing compileVal to populated array initialization. Explicit supported expression evaluation supplies actual typed values; no desired target run is an input. Linking these values to a copied storage path stays explicit. This is finite unrolled expression loading, not runtime length-driven traversal selection.

`primitive_loads_run` applies existing val_sim to every compiled expression and derives actual word representations and load runs. Loads are emitted in reverse list order to put words in source order; Val.evalT is read-only, and the success input requires every source evaluation to succeed. array_stack_run consumes those actual words through existing writeFieldWord_run, and loaded_array_transport connects it to the earlier primitive-array allocator proof. loadedArray inhabits the generic success certificate. storage_array_rhs/decl identify actual MRhs/TRun copy of the resolved storage value; loaded_array_declaration derives full reached StateRepr/allocator, exact root/local pointer, old bases/lower cells and caller stack. The actual storage lookup and expression-list evaluation link remain explicit. No desired target execution, new expression evaluator or replacement compiler framework is assumed.

Represented controls use array bound128, empty initial heap, reserved7=99 and caller stack77. One fixed pair code reads actual storage indices0/1 for arbitrary bounded uint values and allocates length2/payloads at40/41/42, cursor43 and local1=40. Source TRundecl copy is inhabited. Empty loaded copies advance40→41. The64-element control reads index0 repeatedly from an actual64-fold replicated storage value, reaches cursor105 and retains its payload at104; this is not a generic index-range selection theorem. Wrong zeroed second data is rejected. A failed head expression at index2 has successful pair-tail loads first, then source expression/target loaded-copy refusal; this does NOT claim that MRhs.copy of the valid whole array fails.

Independent read-only finder/skeptic PASS with no findings, including final unused-simp-argument cleanup. Neither used Lean/server/builds or writes. Main generic proof passed its direct first attempt. Control repairs corrected the too-small initial representation fixture bound, syntax/closed-length arguments, typed uint storage equality and nonwrapping cursor normalization. The control bound128 is only a fixture choice; generic certificates retain their original Sim/StateRepr and capacity premises. Failed scratch probes and passing final MCP rfl probe are retained; standalone count probes retain actual outcomes. Final all-three-module MCP errors/warnings are empty. No heartbeat increase or forbidden escape. Checkpoint gates/sealing remain required before acceptance.

This connects finite statically unrolled EXISTING expression loads to populated array copies, with explicit successful source list evaluation and actual storage-value linkage. Automatic copied-path/index selection, runtime length-driven traversal, general nested/recursive graph compilation, Construction.compileStmt admission, Source.EM/H25 authority/byte-physical or physical-stack/gas adequacy, checked size/gas failures and five-location composition remain open. Full G33/G35 and lane-end run-lean remain unfinished, with local work and unchanged explicit VY5 H16/S03-PANIC41, V11 G34/G35.02/.03 and V10 G27.05 boundaries. Public Interface/InterfaceV2/Premises, Source files, premises/exclusions, budgets and trust are unchanged.

## Canonical finite primitive-array paths

`CanonicalArrayInterface.lean` states copied-path selection of every finite index read, derived load inputs and actual declaration correctness. A compiled path-check prefix also runs for empty arrays, preserving invalid-path refusal. The count is static and linked to the actual copied source value; this does not yet select a runtime length-driven loop.

`canonical_array_evaluation` derives each actual index bound, storage-child lookup and primitive evaluation from the copied path's actual resolution/whole-array lookup. canonical_array_inputs builds all ordered indices with List.ofFn and proves supported source mapM evaluation; no independent expression/evaluation linkage premise remains. canonical_array_guard executes existing compileSPath and discards its returned slot, preserving the exact machine on success. canonical_array_declaration composes that guard with existing loaded-array correctness to derive actual MRhs/TRun success, emitted declaration, full reached StateRepr/allocator, exact root/local pointer, old bases/lower cells and caller stack. canonical_array_refusal proves actual source/target refusal for every static count, including zero. canonicalArray inhabits all three fields. Existing typed path/evaluation/compiler and allocator frameworks are reused.

Controls represent matrix=[payloads] under bound128 with exact outer/inner storage headers and all actual indexed data. For every fitting finite uint list in that fixture, matrix[0] copies its full primitive leaf: root/local40, cursor40+length+1, actual length at40 and every actual payload at41+index, reserved7=99 and stack77. No source-expression list or evaluation proof is a caller input. Pair values are arbitrary/distinct; a64-element source containing1..64 reaches cursor105 and payload64 at104 through all selected indices. Actual source-copy declarations, empty success and wrong-zero rejection are inhabited. matrix[1] refuses in source and emitted code for any count; the explicit invalid-empty control confirms the guard still executes when there are no element loads. This copies the entire selected primitive leaf array, not the containing reference graph.

Independent read-only finder/skeptic PASS with no findings, without Lean/server/builds or writes. Direct proof repairs normalized Option.bind/storage array views/list lengths and the typed literal index; controls needed explicit unfolding of the owned values wrapper. Two unused simp arguments were removed. Failed MCP scratch alternatives are retained honestly; final all-three-module MCP errors/warnings are empty. Standalone finite-index probes retain actual outcomes. No heartbeat increase or forbidden escape. Checkpoint gates/sealing remain required before acceptance.

The count remains STATIC and is linked to the actual copied source value length by the success theorem. Runtime length discovery/loop selection, Construction.compileStmt admission, general nested/recursive aggregate copying, Source.EM/H25 authority/byte-physical or physical-stack/gas adequacy, checked size/gas failures and five-location composition remain open. Full G33/G35 and lane-end run-lean remain unfinished, with local work and unchanged explicit VY5 H16/S03-PANIC41, V11 G34/G35.02/.03 and V10 G27.05 boundaries. Public Interface/InterfaceV2/Premises, Source files, premises/exclusions, budgets and trust are unchanged.

## Published storage endpoint adoption

Rebased the preserved lane history onto published master b419c3cf4f642ae519b66bebc26cdf2f7cf93574. ControlsV2 and InterfaceV2Roots are now reused from its accepted increment. All112 existing owned Lean files remain byte-identical to the saved pre-rebase head6355081481fbe0db7d5a354dba2180dac8361780; a backup branch and hash/range-diff evidence preserve the original history. Resolved module-map overlaps by retaining unique rows and replayed the historical ControlsV2 compatibility sequence; final published interfaces and premises match master exactly. Generated roots were regenerated after rebase.

`PublishedStorageInterface.lean` consumes the ON-MASTER StorageOps.ProducerInterface.ReachedEndpoint at the unchanged LocationStepPremise boundary, as authorized by H26. The reached endpoint's actual execution field remains explicit; no universal producer or Source/physical adequacy is inferred. The new V11 PhysicalByteWorldInterface still has an uninhabited numeric byte-load program field, so its concrete producer remains pending.

The exact StorageOps API was introduced on master at3ede7f2fdb671391b09809bb4a0ee4661de4c195 in `Backend/StorageOps/ProducerInterface.lean`. published_storage_step projects its ReachedEndpoint.execution into the unchanged LocationStepPremise; publishedStorageConsumer composes a preceding actual execution ending at that SAME endpoint input. published_storage_same_store transports StateEndpoint only when target stores agree, retaining all graph representation, finite-run/hash/region/query/bound/transport fields. No global producer is manufactured and no pending law is discharged by assumption conversion alone.

Controls reuse the published concrete scalar SSTORE endpoint plus the represented ObjectArrayExamples allocator. Actual primitive-array allocation/population [11,23] at40 advances to43, then the scalar SSTORE writes1 atroot0. The reached endpoint certifies that same final target. Complete reached allocator ownership, old payload7 at17, both new payloads and returned root/caller stack40,77 survive the storage-only step. Existing primitive_array_source identifies the actual allocated source object. The skipped-store endpoint is rejected because its final storage word is0 rather than1. Both the original published scalar and the mixed-location consumer are inhabited. This is a concrete intrinsic word-model composition, not all five location certificates or a Source/physical compiler proof.

Independent read-only finder/skeptic PASS with no findings, including independent verification of all112 preserved proof hashes, exact published API usage and mixed execution/ownership controls. Neither used Lean/server/builds or writes. Main consumer proofs passed directly; the negative control needed explicit Out.ok injectivity rather than dependent elimination of a function-containing machine equality. Failed MCP scratch probes and standalone injectivity candidates are retained; final all-three-file MCP errors/warnings are empty. No proof-budget increase or forbidden escape. Checkpoint gates/sealing remain required before acceptance.

H26 allows this explicit-field consumer while concrete general producers remain open. In particular V11 PhysicalByteWorldInterface.Producer supplies no numeric-byte-load inhabitant; V10's reached scalar endpoint is not general G27.05 or Source origin/authority closure. Original VY5 H16/S03-PANIC41, V11 G34/G35.02/.03, V10 G27.05 boundaries remain unchanged. Full-profile defaults, runtime array-length traversal, general nested/recursive graph copying, alias/overlap closure, size/gas failures, all-five-location composition and lane-end run-lean remain open. Published Interface/InterfaceV2/Premises and accepted ControlsV2/InterfaceV2Roots are byte-identical to master; Source files, premises/exclusions, budgets and trust are unchanged.

## Runtime storage-array word traversal

`RuntimeStorageArrayInterface.lean` states a constant emitted copy body whose length and payload come from actual storage. The existing loop controller and allocator are reused. Initial typed ReprAt and complete allocator/checked room remain explicit; no Source-path compiler or size/gas refusal semantics is asserted by this interface.

`storage_read_turn` proves the actual SLOAD/MSTORE loop body. storage_read_iter/loop reuse the existing copyRangeCond/rangeMachine and loopIterN/loopRun semantics, with a finite termination witness of payload length+1. No evaluator fuel, new traversal bound or approved-shape cutoff is assumed. storage_read_enter reads the actual header, computes its data slot, invokes existing allocateArrayCode and installs loop controls. runtime_storage_array_run executes the SAME constant instruction list for every runtime length, producing exactly the earlier arrayWordsMachine; transport reuses its populated allocator proof. storage_array_words derives header and typed words from initial ReprAt, not a desired target run. runtimeStorageArray inhabits the full actual source-copy heap/allocator/root/base/gap/frame success contract.

Controls reuse the represented ObjectArrayExamples heap (two populated children and a reference parent). Actual storage supplies length and contents, while the destination allocator starts at40. The same runtimeStorageArrayCode copies an empty array (cursor41), arbitrary pair values (cursor43) and64 distinct words1..64 (cursor105, last payload64 at104). The generic fixture proves every selected payload, full reached allocator, unchanged source store, caller stack77 and old payload7 at17 for every fitting uint list shorter than128. That bound is a control representation choice, not a generic compiler exclusion. Existing source freshness separates the new root from every old identity. Wrong zeroed payload and an empty source value inconsistent with the actual header are rejected. A false room predicate is kept distinct from runtime panic/revert/timeout/out-of-gas semantics.

Independent read-only finder/skeptic PASS with no findings, including unused-simp cleanup. Neither used Lean/server/builds or writes. Direct repairs normalized the commuted nonwrapping destination address, existing stack-list swaps and the exact result constructor; a redundant tactic after a closing rewrite was removed. Controls needed direct storage-frame rewriting from the already-proved machine-shape equation. Three unused simp arguments were removed. Failed MCP scratch alternatives and standalone loop-bound probes are retained honestly; final all-three-module MCP errors/warnings are empty. No heartbeat increase or forbidden escape. Checkpoint gates/sealing remain required before acceptance.

This is runtime LENGTH-DRIVEN primitive storage-word copying at an already resolved symbolic source slot, under the existing typed initial storage representation and complete allocator/checked-room inputs. Source SPath/Construction.compileStmt selection, declaration/rebinding integration, general nested/recursive aggregate copying, Source.EM/H25 authority/byte-physical or physical-stack/gas adequacy, checked size/gas failures and five-location closure remain open. Full G33/G35 and final lane-end run-lean remain unfinished. Existing VY5 H16/S03-PANIC41, V11 G34/G35.02/.03 and V10 G27.05 boundaries, public interfaces/premises, Source files, exclusions, budgets and trust are unchanged.

## Runtime array path and binding integration

`RuntimePathArrayInterface.lean` states existing compileSPath followed by the runtime storage-array body and existing local stores. Code has no static count or payload parameter. Actual path resolution/source lookup, complete initial ownership/allocator and fitting room remain explicit; existing Source MRhs/TRun declarations/rebindings and failed-path behavior are the proof boundary, not whole-program Construction selection.

`runtime_path_array_body` uses existing spath_sim and Sto.find_of_findLive to obtain the actual represented operand at the SAME resolved/copied storage path. It invokes the runtime storage-header loop with no source-slot/value oracle or count/payload code parameter. runtime_path_array_declaration composes the actual Source MRhs/TRun copy with existing StateRepr.adopt/consMem/localWrite. runtime_path_array_rebind uses the existing setMem/localWrite rules, preserves every old object through SVal.keeps_copyStToM and separates the fresh identity by copyStToM_id_ge. Both derive full reached StateRepr/allocator, exact root/local pointer, caller stack and lower-cell/base framing. Failed path compilation yields actual source RHS/declaration/rebinding refusal and target revert before allocation, including empty arrays. runtimePathArray inhabits all four interface fields.

Controls represent matrix=[payloads], an old populated uint array at16 with payload7, and two locals initially aliasing that old object. The same emitted declaration code works for all fitting fixture lengths: it installs fresh root40 at newlocal3 and retains both old locals1/2=16. The same rebind code redirects local2 to40, retains local1=16 and old payload17=7, and preserves caller stack77. Generic observations cover every actual indexed payload, the correct runtime length and next cursor40+length+1. Arbitrary pair values, empty rebinding (cursor41) and64 distinct values1..64 (cursor105, last64 at104) are inhabited. Actual source rebinding retains the other old alias. Invalid matrix[1] fails in both source and emitted declaration/rebind, including the empty case. Keeping the old destination pointer16 is rejected. Fixture bound128 is only a represented control choice.

Independent read-only finder/skeptic PASS with no findings, without Lean/server/builds or writes. Main proofs and all controls passed their direct first attempts. The warning audit removed unused storage-bound arguments from private heap/allocator fixture helpers; no public premise changed. Final all-three-module MCP errors/warnings are empty. Optional standalone lookup-injectivity probes retain actual outcomes. No heartbeat increase or forbidden escape. Checkpoint gates/sealing remain required before acceptance.

This proves runtime path-to-primitive-array body/declaration/rebinding simulation over the existing intrinsic MRhs/TRun boundary. It does not add a Construction.compileStmt branch or whole-program selector, cover all nested/reference aggregate graphs or arbitrary Source graph refinement, or discharge Source.EM/H25 authority/byte-physical/physical-stack/gas adequacy, size/gas failures or five-location closure. Initial StateRepr, path support/actual lookup and checked allocation room remain explicit. Full G33/G35 and final lane-end run-lean remain open, with unchanged VY5 H16/S03-PANIC41, V11 G34/G35.02/.03 and V10 G27.05 boundaries. Public interfaces/premises, Source files, exclusions, budgets and trust are unchanged.

## Arbitrary live primitive arrays

The signature-only PrimitiveArrayLiveInterface requires an intrinsic live-length bound, equality of the actual storage value’s memory copy with its live canonical copy, and transport of existing storage representation. Storage shadows remain in the original value; no new source shape or capacity premise is introduced. Proofs and runtime transport remain pending at this interface commit.

`primitiveArrayLive` inhabits the interface for EVERY typed primitive array, with arbitrary intrinsic live vector and storage shadow. The bound follows from SVal.array; primitive_live_vector uses structural recursion and master Grown.prims_cons. primitive_live_copy proves equality of the original value’s existing copyStToM result with the canonical live copy; primitive_live_representation preserves existing header, limit and live element facts. runtime_primitive_live_success transports the existing header-driven runtime loop to the ORIGINAL value’s copy, retaining allocator, exact fresh root, base extension, below-cursor framing and gaps. No count/payload code parameter, source mutation, new shape exclusion or new capacity premise is introduced.

Controls inhabit arbitrary shadows and empty/64-element certificates. The actual runtime control is an empty live array with retained nonzero storage slot23 on the populated master example heap: root40/cursor41, memory40/41 zero, old memory17=7, and original storage23 retained. A negative control rejects copying23 into memory41. The long case is a certificate control, not a new runtime execution witness.

Independent read-only finder and skeptic PASS with no findings, without Lean/server/builds or writes. Direct proof attempts exposed unsupported ordinary induction on mutually inductive SVec; structural recursion with existing Grown.prims_cons handles dependent projections. Controls use explicit rewrite arguments and existing Out.ok.inj. All three modules have zero MCP errors/warnings; no heartbeat increase or forbidden escape. Gates and sealing are recorded separately in the checkpoint handoff.

Scope remains primitive-array copying at an already resolved slot under initial storage representation, complete allocator and fitting-room inputs. Shadow-aware source-path/declaration/rebinding wrappers, whole Construction selection, general nested/recursive/reference graph code, full default/allocation failure implementation, Source.EM/H25 authority/physical/gas adequacy and five-location closure remain open. Full G33/G35 and final lane-end run-lean remain unfinished. VY5 H16/S03-PANIC41, V11 G34/G35.02/.03 and V10 G27.05 dependencies, public fields/premises, Source semantics, exclusions, budgets and trust are unchanged.

Final documentation reviews corrected the three new module-map keys to the existing Backend/MemoryCopies convention and separated earlier lane-owned primitive_array_source/runtime_storage_array_success from reused master lemmas in the handoff. No proof changed.

## Live primitive-array path bindings

RuntimeLiveArrayInterface states additive body/declaration/rebinding contracts for the actual typed primitive array returned by storage lookup. It retains existing runtimePathArray code and full source-copy, allocator, root, local/stack/frame, old-object and freshness obligations. Live length comes from the value, with checked room explicit. The signature-only checkpoint precedes proofs and inhabited controls; existing interfaces and premises remain unchanged.

runtimeLiveArray inhabits all interface fields for EVERY intrinsic primitive-array storage value. runtime_live_array_body obtains the same actual source reference, slot and value through existing spath_sim/findLive and invokes runtime_primitive_live_success on that ORIGINAL value. runtime_live_array_rhs/decl_source/rebind_source unfold existing MRhs/TRun on the actual lookup, without replacing the storage value or requiring a canonical no-shadow lookup. Declaration and rebinding reuse the existing runtimePathArray code and StateRepr.adopt/consMem/setMem and AllocatorRepr.localWrite, complete allocator, exact root/local/caller-stack/lower-cell framing, BaseExtends, Heap.Keeps and fresh identity. Refusal reuses existing runtime_path_array_refusal. No new compiler, IR, evaluator, code parameter or shape premise is introduced.

Private regression fixtures adapt the preceding represented nested matrix test to retain shadow71, including the symbolic WordStore cell immediately after the live payload. They prove actual declaration/rebinding execution for arbitrary fitting fixture lists (<128), pair11/23, empty and64 distinct elements; old aliases and old payload7 survive, the fresh local points40, the long cursor is105 and last payload64 is at104. Source memory rebinding retains the original shadow-bearing storage value. A full reached allocator proves the memory cell beyond the live payload remains zero; a negative control rejects copied shadow71. Invalid nested paths (including empty arrays) still refuse before allocation, and retaining old destination pointer16 is rejected. Fixture bound128 is only a represented example choice; the generic result uses the intrinsic value and its actual live length.

Independent read-only finder and skeptic PASS with no concrete proof findings, without Lean/server/builds/writes. All seven generic proofs passed direct first attempts. A fixture map roundtrip needed Function.comp_def, SVal.view_prim and explicitly applied List.map_id; the negative tail needed explicit address normalization. Final MCP diagnostics/warnings are empty for all three modules. Terminology was clarified to symbolic_shadow_input: this is a symbolic WordStore witness, not byte-physical adequacy. No heartbeat increase or forbidden proof escape. Checkpoint gates and seal are recorded in the handoff.

This closes the arbitrary-shadow primitive-array path binding gap at the existing MRhs/TRun and symbolic EVM boundary. Whole Construction.compileStmt selection, general nested/reference/recursive graph compiler and default coverage, checked allocation/size/gas failure code, Source.EM/H25 authority, byte-physical/stack/gas adequacy and five-location closure remain open. Initial StateRepr/storage representation, supported path, actual resolution/lookup and fitting allocation room stay explicit. Full G33/G35 and final lane-end run-lean remain unfinished; VY5 H16/S03-PANIC41, V11 G34/G35.02/.03 and V10 G27.05 boundaries and all public interfaces/premises, Source semantics, exclusions, budgets and trust remain unchanged.
