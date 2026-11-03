# V12 runtime-frame producer foundation (H10)

This is an early **partial P1** checkpoint, not general runtime-call or source-to-EVM closure. H10 authorizes V12 to build G37/G38/G39 producers. The helper branch is `codex/solidity-v12-v17-20261031/v12-flow-calls-help`, from published `e7cc378c275eafe7a047c63f672bedbed2fec6ff`. The original frozen base is `2fe1f8932f96be15b00df03ba2cde46f64a87758`; the original branch and all seals remain preserved at `7c2675f63fc938b5f57515f375bdbf645b24090c`. This document is the committed checkpoint handoff; its revision is the containing commit. External sealed metadata records the full resulting head without a self-referential commit hash.

## Typed interfaces

All modules are under `Solidity/Backend/InternalFlow/`; all use existing intrinsic syntax, states, execution and checked target certificates.

- `RuntimeFrameSemantics.statement` and `.program` replace an intrinsic `callRec f d args ret thunk` by its existing finite supplied `thunk ()` call body, recursively over finite syntax. `statement_run`, `program_run`, `program_outcome` prove exact execution equality. The existing runtime ignores `d` for a fixed thunk; this does not remove source elaboration/unrolling exhaustion or establish body-depth independence.
- `RuntimeFrameTarget.ofProgram`, `.ofStatement`, `.compile`, `.compileStatement` transport actual published `Evm.Memory.Calls` certificates along that equality. No simulation certificate is assumed. Original selectors/refusals are unchanged. `callRec_index` compares only the SAME thunk at two indices.
- `RuntimeFrameTransport.exported` composes `CallRet.enterT` extension with actual body extension, weakens the original caller tail, drops private body locals and exports the actual result with `leaveT`. `call_return`, `target_return`, `target_recursive_return` expose actual Args evaluation/body execution and full dependent result. Target theorems require a genuine checked certificate, reached `StateRepr`, exact frame room and actual `AllocationInput`; they conclude actual emitted execution, reached representation, unchanged evaluation stack, `BaseExtends` and exact `GrowsAllocator`.
- `RuntimeFrameStack` implements target word saves/pops using the existing machine instructions and a pointer loaded from target memory. `push_run`, `pop_run`, `push_pop` prove actual execution. Push/pop composition explicitly requires a positive pointer, nonoverlap and no wrap; payload memory remains written. Popping places the recovered word on the evaluation stack.
- `Solidity.Backend.InternalFlow.RuntimeFrame.Arena` (defined in `RuntimeFrameSaved.lean`) relates a genuine represented source state to one bounded reserved-frame operation. Header and payload are above all current locals, below the heap boundary and distinct, with no-wrap. `reserved_write`, `pushed_repr`, `popped_repr` preserve full existing scalar/storage/fragile/array/struct/ref-field representation under reserved writes. `pushed_allocator` proves zero allocator growth. `save_reference`/`save_scalar` consume real represented caller bindings and actual load/save execution. Arena is not a permanent callee scratch reservation.

These public theorem signatures, including all dependent contexts/extensions and premises, live in the named modules. There is no new evaluator, AST, world, execution oracle or trust shortcut.

## Inhabited client and complete observations

the lane-only fixture RuntimeFrameControls.lean (not on master) constructs a real compiled prefix, initial representation/allocator, actual reached caller and capacity. Caller scalar locals are 9/11. Object0 is `[7,11]`, object1 `[21]`; two caller aliases reference object0; persistent roots are 7/31. Prefix allocation cost is 5, cursor261.

The actual nested `callRec` body mutates object0 to `[13,11]` and root0 to29. Default result objects2/3 are empty. Private object4 is `[17,19]`; private scalar23 and parameter rebinding do not replace the caller tail or exported old0 identity. Call cost5, final cursor266, peak local need11. The typed actual endpoint derives representation and allocation premises from prefix execution; no desired midpoint is supplied.

Four runtime saves capture old0, its alias, scalar9 and distinct object1. Four pops recover words onto the evaluation stack, leaving `[256,256,9,259,77]`, not merely the original `[77]`. The complete ordered target vector in `captured_call_complete` is:

```
[256,256,9,259,77,266,110,256,256,9,259,99,11,9,256,259,
 256,256,2,13,11,1,21,0,0,2,17,19]
```

This includes pointer100 restored110, payload cells110–113, sentinel127, every observed caller/result cell and every object length/element. `private_cells` additionally retains physical private cells7–11 `[256,23,256,256,263]`; logical drop does not erase them. `captured_roots` proves29/31 on the SAME full target execution. `source_endpoint_after_save` couples a real typed save to the checked callee endpoint, but does not prove arbitrary callee preservation of unrepresented scratch words.

Controls reject wrong alias/scalar capture, malformed runtime pointers, overlapping header/payload, insufficient frame premise and header overlapping caller locals. The last two are premise failures, not runtime rejection. `bottom_exhaustion` is actual exhausted intrinsic execution and `bottom_refused` actual compiler refusal. Original public selector still refuses this callRec; the owned selector admits the inhabited finite body. Published `RetBinders.snocMem` now permits mixed source entry; `mixed_source_entry` checks its actual default allocation and scalar0 while `mixed_target_refusal` retains the current emitter refusal.

## Checks, failures and reviews

The focused fixture passes in19.253s under serial Lean `-j1`, `LEAN_NUM_THREADS=1`, enforced12GiB/no-swap and120s. Sampled aggregate RSS1,358,760KiB; cgroup peak727343104. All53 actual builtin `#print axioms` reports have exact ordered pins in the lane-only fixture check-axioms.py (not on master); only the original `propext`, `Classical.choice`, `Quot.sound` sets occur. Missing/duplicate/reordered/altered-axiom/diagnostic host controls pass. The scoped guard accepts only that exact checked resource receipt; it is not a general log parser.

Cold current-master import checks timed out at121.516/121.524/121.983s while completing different dependencies. Necessary focused dependency preparation subsequently passed, then Target/Transport passed4.491s. Failed termination, deep kernel-recursion, parser and200000-heartbeat proof attempts are retained raw; small named checked boundaries fixed them without increasing limits. Current Stack/Saved/Transport source and imports pass. Final runtime/import gate passes1.546s: Lean4.24.0 (797c613eb9b6d4ec95db23e3e00af9ac6657f24b), Lake5.0.0-src+797c613, KeySort and all five owned imports (121 jobs), cap12GiB/swap0. Layer/orphan/trust checks report0 findings. No unchanged original aggregate/raw/full retry occurred.

Independent read-only finder and skeptic reviewed the actual sources and inhabited controls without Lean/builds. Both passed with the finite-body, one-operation Arena, popped-stack and missing generic scratch/dispatcher boundaries explicit. Final exact-commit artifact review is separately sealed with external evidence.

## Remaining owned P1/P4 and P2 boundary

P1 still requires compiler-derived generic callee scratch-footprint preservation, whole-context capture/restore, runtime return-control and a recursive dispatcher. Existing finite Calls expansion is not an unbounded source/target simulation. These are now OWNED producer work, not a claim to be waiting for an external runtime producer. The new mixed primitive/memory `RetBinders` result export is another ready owned producer obligation. P4 still needs actual dependent signature guard/candidate agreement and compiled selection links.

P2 belongs to readonly-external. Its required actual typed contract has the shape:

```
world.callFrame handle entry context = .ok (next, result)
-- result : State (contracts k) entry.locals
-- entry : ContractWorld.Entry (contracts k) α; handle : ContractWorld.Handle k
-- context.isStatic = true, with an actual admitted nonempty read-only body
```

This is an OPEN producer requirement, not a theorem or assumed discharged premise here. Current published `World.callFrame` rejects nonempty computed-static bodies, so that legacy equation cannot certify the intended nonempty client. The readonly owner must provide the genuine computed-static execution/frame interface. No replacement world evaluator is introduced.

## Entire original queue accounting

Every original item remains partial: Work1/G37.01 general frames; Work2/G37.02 unbounded recursion; Work3/G37.03 full-signature dispatch; Work4/G36 general mixed loops/structured early control; Work5/G38 exact failure bytes/frame/world composition; Work6/G39 target transient/transaction/callback transport; BackfillA general frame/result/recursive prefix; BackfillB mixed unwind/reset/rollback. This helper foundation does not close any parent item.

Original complete aggregate/raw/full timeouts, unreached TestSuite/sort, docs normal/strict exit1 and frozen-document additions remain actual failed/pending mandatory obligations on the original branch. Original fixtures/pins/seals remain there and are not claimed validated against this helper's newer master API. Kernel target-model proofs are distinct from physical EVM/gas, external compiler tests, source lowering, ABI, callback/world rollback and EIP1153 agreement. No goal status changed, no publication/push/merge occurred.

## P1-02: derived mutating/allocating fragment footprint

`RuntimeFrameFootprint.lean` adds `Footprint.Words lo hi before after`, equality on an actual half-open interval of word memory. It is a relation over the existing machine, not a second execution semantics. `declare` and `rebind` strengthen published `newArray_correct`/`rebindNew_correct` with preserved reserved words. The actual allocator cursor/header writes are above the heap boundary or at cell0; the actual new/rebound local is below the reserved interval. `array_write` and `write_local` derive interval preservation for a REAL old-object mutation from represented heap bounds. The latter consumes genuine compiled value certificates and actual source value/index evaluation, preserving RHS → receiver → index order. No `Heap.Keeps` or arbitrary-callee preservation premise occurs.

`fragmentCode` uses existing emitter snippets for an old-array write37, a private size2 declaration and allocating size1 rebinding. `fragment` composes their exact execution/representation/allocator laws over an abstract intrinsic state. Its genuine remaining premises are reached `StateRepr`, allocator ownership/cursor, positive local base, actual old typed alias binding and index0 liveness, cursor+5<W, local destinations below the interval, and full local room. The theorem derives a successful actual execution and reserved-word preservation. `restore` composes an actual successful fragment with an existing runtime pop; its footprint premise is DISCHARGED by these leaves in the client. `popped_allocator` derives exact zero allocation cost for that pop.

The appended `Checks.FootprintClient` reuses the actual populated prefix/caller. `public_selection` and `selected_code` prove the real `Memory.compileProg` selector emitted precisely this fragment under a block; no substitute emitter is assumed. `derived_footprint` derives the saved input/allocator from real prefix execution and a typed save, obtains the actual compiled endpoint, and identifies it with the derived fragment execution. `pop_endpoint` carries full reached `StateRepr`, exact recovered old alias on the evaluation stack and total growth5 through the SAME execution. Its reserved interval `[100,128)` is proved nonempty and contains both header100 and payload110. The existing 53 theorem declarations and their ordered builtin axiom sets remain unchanged; new reports are additive.

The exact source endpoint now has four objects: old0 `[37,11]`, unrelated1 `[21]`, private2 `[0,0]`, rebound-private3 `[0]`. Old caller aliases remain0, other alias1; caller scalars remain9/11; roots7/31. Scope exit drops the private local while its physical cell6 retains pointer264. Cursor advances261→266, frame need6, header returns111→110, saved payload110 remains256. The SAME complete target endpoint has stack `[256,77]` and the ordered stack+memory observation:

```
[256,77,266,110,256,99,11,9,256,259,256,264,
 2,37,11,1,21,2,0,0,1,0]
```

The memory addresses, in order, are0,100,110,127,1,2,3,4,5,6,256,257,258,259,260,261,262,263,264,265. Separate roots are7/31. Controls reject claiming unchanged old contents, private-result escape, wrong saved alias, swapped scalar destinations, omitted cursor growth and empty private allocation. An actual compiled out-of-bounds write returns exact bare revert; suffix absorption retains that class, not fault. There is no successful failed State, returned allocation frontier, rollback, bytes or absence-of-body-effects claim. The exhausted-capacity negative is a false PREMISE, not runtime rejection.

A concrete-state instantiation hit the unchanged200000-heartbeat ceiling (45.359s, sampled RSS10,277,556KiB; raw failed log retained). An imported abstract composition of the SAME emitters passed3.36s; the unchanged concrete fragment then passed21.36s. Limits and expected observations were not raised or weakened. Remaining failed modular-pointer/control elaboration logs are retained; only the final successful fixture and its exact axiom output count as validation. No prior held aggregate/raw/full/docs gate was retried.

This is a structural footprint leaf and an inhabited scoped fragment, not arbitrary whole-callee scratch preservation or unbounded recursive execution. P1 still needs structural coverage of the other admitted compiler clauses, whole-context restoration and return-control/dispatcher; P4 remains pending. All eight original Work/Backfill items remain partial as listed above. H10 authorizes these missing P1/P4 producers as OWNED work; they are not external-producer waits. P2 stays with readonly-external.

P1-02 final focused fixture passes24.927s (sampled aggregate RSS1,357,288KiB, cgroup peak750071808 bytes) with87 exact builtin reports, original53 plus34. the lane-only fixture check-footprint-axioms.py (not on master) guards the complete new output and tests missing/duplicate/reordered/altered-axiom/empty-axiom/diagnostic/resource-receipt corruption. The previous53 guard remains unchanged for the previous sealed output. Final import/versions/KeySort passes2.007s under12GiB/no-swap; actual Lean4.24.0/Lake5.0.0-src+797c613. Layers188/0, reachable1308/orphans0 and trust1323/0 checks pass. Independent read-only finder/skeptic source/guard/document reviews passed; exact committed-artifact reviews are sealed separately. No reviewer ran Lean/build/server.

## P1-03: compositional finite call frames and callRec transport

`RuntimeFrameComposition.lean` retains the EXISTING typed `Calls.Program`/`Calls.Statement` in `Composition.Program`/`Statement` together with a derived `safe` proof. `ProgramSafe`/`StatementSafe` quantify actual represented input machines and successful emitted executions: `StateRepr L b frame F sigma base machine`, `b + checked.need <= lo <= frame`, and the genuine `AllocationInput` for `checked.cost sigma` imply `Footprint.Words lo frame machine target`. The proof field is never supplied as a future oracle by the selector: constructors below derive it. Failure results expose no successful final State or scratch memory.

`nil`, `cons`, `block`, `branch` and `equivalent` compose actual published constructors. `cons_cost` exposes the source-reached tail cost; actual prefix soundness produces the reached representation and `GrowsAllocator.nextInput` supplies its REAL tail budget. `branch_cost` uses the actually evaluated condition and selected branch; maximum frame need remains distinct from reached allocation cost. Existing exact condition code and jump equations account for both branches and scope drops. Generic `assign`/`declareValue` accept genuine compiled values (including memory reads); pointer argument declarations/copies, default primitive results, primitive array declarations/rebinding/defaults derive footprints from actual emitted stores and representation/cursor laws. No `readOnly`, `withinM`, `Heap.Keeps` or unconditional fragile liveness is imposed.

`compileProgram`/`compileStatement` structurally traverse the existing finite intrinsic syntax. `compileCall` consumes the ACTUAL published `expandNone`, `expandVal`, `expandMem`, expansion agreement and `memoryReturn`. The latter's final pointer-copy store is separately proved below the scratch interval using the expanded output-context length bound. Its metadata check is a FOOTPRINT-CAPABILITY guard, not a global source admission change, runtime rejection, or approved exclusion. Public selectors and default refusals remain unchanged. Nested calls, direct array/storage writes, loops, unsupported default/reference categories and storage/tuple results remain unfinished selector coverage; some of these are admitted by other existing producers. `nested_coverage_hold` and `mutating_coverage_hold` explicitly prove public admission alongside this selector's refusal, preserving the P1-02 mutating fragment rather than pretending it was generalized.

`normalizeStatement` consumes the existing exact `RuntimeFrame.statement_run` equation, retaining code/fragment/need/cost and scratch soundness. `compileRecursive` therefore produces a certificate INDEXED BY THE ACTUAL `Stmt.callRec`, for its supported finite supplied body. `recursive_index` compares different quotation indices only for the SAME body thunk. It does not remove source unrolling exhaustion, prove body-depth independence or compile unbounded recursive source execution. `recursive_exhaustion` remains exact exhausted execution and the new selector refuses it; the original public `Calls.compile` callRec refusal also remains. Whole-context restoration, runtime return control/dispatcher and general unbounded correspondence are still owned P1 work.

`reflag` transports across a KERNEL-PROVED equality of actual fragment flags; no liveness/flag promotion occurs. The client proves `before.frag = Frag.init Caller` from its real nonempty prefix. Named generic code/metadata projections avoid repeated concrete certificate normalization.

### Actual clients, endpoints and observations

`Checks.CompositionClient` starts from the SAME genuinely executed caller prefix: two distinct nonempty arrays `[7,11]` and `[21]`, two aliases of old0, scalars9/11 and roots7/31. Arguments evaluate memory old0 then scalar9; the typed ordered observation is `(9, some 0)`. The selected memory call allocates default result2 `[]`, private3 `[0,0]` and nested-private4 `[0]`. Its branch tests the actual scalar parameter against9. It binds the result to old0, privately rebinds the memory parameter to private3 and drops nested/private argument frames. The caller's ordered result/tail identities are0,0,1,0, scalars remain9/11 and old contents remain `[7,11]`/`[21]` in this independent client. This is not a replacement of the P1-02 old-content mutation37 or the first nested callRec mutation13 controls.

`public_code` proves the actual published `Calls.compile` singleton code equals the owned selected code. `export_decomposition` links that SAME code to its real checked expansion plus the published `returnPointerCode`. Before export the physical argument slot6 holds private pointer262 while the return slot8 holds old pointer256. Export overwrites slot6 with256; neither logical private-frame dropping nor pointer export erases private cells9/10.

The before-export complete stack+memory vector is:

```
[77,267,111,9,11,9,256,259,256,262,9,256,262,265,0,2,0,0,1,0]
```

Its memory addresses are0,100,110,1,2,3,4,5,6,7,8,9,10,261,262,263,264,265,266. `target_endpoint` derives actual prefix representation and capacity from the initial allocator/costs, performs a REAL typed scalar save, applies `Composition.endpoint`, then uses the derived scratch interval for the actual pop. Full final `StateRepr`, caller-tail/result transport, `BaseExtends`, stack and exact growth6 survive at that SAME endpoint. Frame need is10; prefix cost5 plus call cost6 gives genuine initial budget11. Final cursor is267 and header100 returns110. The complete final vector is:

```
[9,77,267,110,9,99,11,9,256,259,256,256,9,256,262,265,
 2,7,11,1,21,0,2,0,0,1,0]
```

The memory addresses are0,100,110,127,1,2,3,4,5,6,7,8,9,10,256,257,258,259,260,261,262,263,264,265,266. Roots remain7/31. A skipped branch (parameter9 compared with10) allocates ONLY its default result2: cost1/cursor262 and empty result reference2, with the same maximum frame need. Wrong argument/destination, private result escape, saved scalar, cursor and insufficient-frame-premise controls remain distinct. The last is a false premise, not runtime rejection.

Independent primitive-return and void clients also use the real compiler and actual populated prefix. The primitive call returns9+5=14 before privately setting its scalar argument23; caller left becomes14 while right remains11. Its complete stack+memory vector at addresses0..8 is `[77,261,11,14,256,259,256,256,23,14]`, cost0. The void call privately sets the parameter23 but caller left/right stay9/11, with vector at addresses0..7 `[77,261,11,9,256,259,256,256,23]`. Both have proved public/owned code equality. Storage/tuple result cases are not claimed.

The actual callRec-indexed client proves its source outcome, metadata and code agreement and `recursive_target_endpoint` retains the SAME reached source/target frame and scalar recovery. This is finite intrinsic transport with real allocation/aliases; it is not unbounded recursion or full G37 closure.

### Code equality and scoped checks

`RuntimeFrameCodeEquality.lean` is a sound data comparison over existing `Instr`/instruction lists, not a second AST, evaluator or admission rule. It rejects loop nodes even against themselves. `instruction_sound`/`code_sound` turn only a proved true comparison into actual equality. The actual public/owned52-instruction equations use these theorems and `decide +kernel`; the diagnostic compiler `#eval` listing alone is NOT proof. An attempted automatic DecidableEq derivation was rejected and never adopted; no global equality instance or native trust shortcut was added.

Whole-certificate/code projections hit the unchanged200000-heartbeat limit, including an isolated public projection. Initial Cartesian/combined equality proofs also hit it. A nested constructor comparison has a checked soundness proof (5.047s), and the SAME public code projection then checks by kernel computation (2.890s). There is no claim that this repairs the original aggregate/full gate. Every raw failure and diagnostic source is retained. Named slot/metadata proofs resolved independent dependent-type errors; no program, observation, budget or original proof pin was weakened.

The COMPLETE current fixture passes54.596s under the unchanged120s bound, serial `-j1`/`LEAN_NUM_THREADS=1` and hard12GiB/no-swap. Sampled aggregate RSS1,564,112KiB; cgroup peak982409216 bytes. All160 builtin axiom reports are checked by the lane-only fixture check-composition-axioms.py (not on master): the previous87 remain byte/order/axiom-set identical, with73 additive guards. Source declarations before the appended namespace are byte-identical except two imports. Strict missing/duplicate/order/axiom/diagnostic/receipt controls pass. Final actual Lean4.24.0/Lake5.0.0-src+797c613/KeySort and import closure pass2.222s (123 jobs). Layers188/0, reachable1310/orphans0 and trust1325/0 pass. No unchanged original cached/raw/full/documentation failed gate was retried.

All eight original queues remain partial. Next ready owned work includes connecting the general dynamic write footprint to the structural selector, nested call coverage, whole-context save/restore, runtime return control/dispatcher and then P4 dependent guard/candidate agreement. P2 remains readonly-external's actual computed-static producer requirement. No independent-work-exhaustion, goal administration, source/world/physical EVM closure or publication is claimed.

## P1-04: caller-alias mutation across a checked call frame

`Solidity/Backend/InternalFlow/RuntimeFrameMutation.lean` adds
`Mutation.write`, `compileStatement`, `compileProgram`, `compileCall` and
`compileRecursive`. The old selectors and public compiler remain unchanged.
The new successful-execution scratch proof consumes actual checked value and
index certificates and the reached `StateRepr`; it follows RHS, receiver and
index evaluation in that order. The actual bounds guard establishes the live
array element. Value/index reversion and out-of-bounds reversion absorb the
remaining instructions. No extra liveness premise, `Heap.Keeps`, read-only or
`withinM` restriction is imposed on this mutating body.

The additive selector covers dynamic primitive-array writes through a local
reference, and composes existing block/branch/declaration/assignment
certificates. Calls use the existing public expansion/equivalence/memory-return
constructors. The explicit output-context bound remains required by the
scratch capability. Storage/tuple results, other memory-path shapes, nested
calls in bodies and general recursive execution are still unsupported here.
`compileRecursive` concerns only the unchanged finite supplied thunk.

The inhabited `Checks.MutationClient` uses a real allocating prefix and a
selected direct memory-result call. Public `Calls.compile` emits the same code
as the owned structural certificate. The callee changes old object 0 from
`[7,11]` to `[37,11]`, allocates private/default objects, privately rebinds its
parameter, and exports object 0. A subsequent caller write through the returned
alias changes it to `[37,41]`; the other old alias sees the same contents, while
distinct object 1 remains `[21]`. The complete source and target vectors retain
all physical default/private objects, caller scalars 9/11, roots 7/31, protected
stack 77 and captured scalar 9. Actual reached call/suffix cost is 6, frame need
10 and final cursor 267, from initial cursor 256 and prefix cost 5.

`target_endpoint` obtains the populated representation and allocation input
from the actual prefix, performs typed scalar save, consumes the derived full
program certificate, and executes the real pop with scratch preservation. It
returns the SAME reached `StateRepr`, `BaseExtends` and composed
`GrowsAllocator`, rather than assuming an intermediate state or simulation.
`target_complete`, `target_after_call` and `target_roots` pin the ordered
observations separately. Source/content, wrong escape, unrelated write,
scalar and cursor controls have positive baselines. Three distinct actual
source/target failures test RHS read, index read and bounds failure; all are
bare revert, with suffix absorption and a not-fault control. Error-valued
results supply no failed State, allocation frontier, rollback, byte payload,
absence-of-earlier-effects or world/callback theorem.

Independent read-only source finder and skeptic reviews found no confirmed
issue in this adapter/client. Their exact committed-artifact reviews and the
actual bounded commands/resources/axiom reports are recorded in the new P1-04
handoff and evidence. All prior seals and failed mandatory gates are retained.
Every original Work1–6 and Backfill A/B remains partial: whole-context runtime
capture/restore/return dispatch, nested calls, unbounded recursion, dependent
signature guard/candidate agreement (P4), general mixed/early-control loops,
exact live byte-journal failure and target transient/world composition remain
open. P2 computed-static execution is readonly-external's producer obligation.
No goal administration, publication or full-lane completion is claimed.

## P1-05: nested checked call-frame scratch composition

`Solidity/Backend/InternalFlow/RuntimeFrameNested.lean` supplies
`Nested.compile`, `compile_without_calls`, `height_call`, `reflagProgram`,
`reflagProgram_code`, `normalizeProgram`, `normalized_fields` and
`compileNormalized`. Its private traversal composes the existing actual
`Composition.cons/block/branch/equivalent/memoryReturn` constructors and
`Mutation` leaves. Public call expansion/equivalence remains the existing
`Calls.expandNone/Val/Mem` API. Existing selectors and reserved producers are
unchanged. No new AST, evaluator or target simulation premise is introduced.

`compile` computes the number of ordinary-call body levels from the actual
finite intrinsic syntax; there is no caller-supplied search/depth limit. Each
expansion replaces one call level with the existing argument/default/body
scope scaffolding. No completeness theorem for all source profiles is claimed.
The output is still a real `Composition.Program`: its full checked target
certificate and scratch proof are derived, not proposed assumptions.
No-call syntax agrees with the previous mutating selector. Storage/tuple
returns, other unsupported leaves, loops and early-control extensions retain
refusal. The memory-return context-size capability bound remains explicit.

`normalizeProgram` retains exact code, fragment, need, allocation flag and
source-indexed reached cost, using only `RuntimeFrame.program_outcome` to
transport the existing actual certificate. `compileNormalized` concerns the
existing FINITE supplied callRec thunk, including real exhaustion/refusal;
it does not implement an unbounded recursive target dispatcher or remove the
source unrolling boundary. P4 dependent signature agreement remains open.

The populated `Checks.NestedClient` first obtains the same actual caller
prefix (old0 `[7,11]`, alias0, distinct1 `[21]`, scalars9/11, roots7/31).
An outer memory-return call invokes a genuinely nested memory-return call
under a scoped block. The inner selected branch changes old0 to `[37,11]`,
allocates/rebinds private objects and returns old0. The outer result receives
that returned reference before dropping the inner local frame. The caller
then writes through it, so both old aliases and the returned reference observe
`[37,41]`; unrelated1 remains `[21]`. Both result-entry default objects2/3
remain physically present as `[]`; private4 is `[0,0]` and nested5 is `[0]`.
The original fixture and its192 ordered reports are preserved additively.

The actual public `Calls.compile` emits the same code as this derived owned
certificate. Syntax height is2, reached suffix cost7, frame need13 and final
cursor268 (prefix cost5 from256). `target_endpoint` derives the reached
representation/capacity from the real prefix and `GrowsAllocator.nextInput`,
executes typed scalar save, consumes the SAME nested program's checked
endpoint and scratch proof, then executes the actual pop. Final `StateRepr`,
`BaseExtends`, `GrowsAllocator`, protected stack and scalar recovery are tied
to that endpoint. The complete31-word snapshot includes every addressed
caller/private local and heap cell, runtime pointer/payload and sentinel;
roots are checked separately. No supplied midpoint or heap-content oracle is
used. Wrong alias, private escape, old content, scalar, cost and cursor
controls retain successful baselines.

The nested out-of-bounds variant proves exact intrinsic and target bare
revert, suffix absorption and not-fault. It yields no failed State, frontier,
absence of prior effects, rollback, payload bytes or world result. The fixed
finite callRec client has the same code/source outcome; changing only its
quotation index0 to900 does not establish unbounded recursion. Both public
and unnormalized recursive selectors still refuse it.

Independent source and final artifact reviews, exact ordered axiom pins,
actual commands/timings/resources and retained failed probes belong to the
P1-05 immutable handoff/evidence. All original Work1–6 and Backfills A/B remain
partial. The next ready owned P1 work is whole-context runtime capture/restore
and return control, plus remaining nested capability coverage; P4 still needs
actual dependent frontend guard/candidate links. General recursion,
general mixed/early-control loops, live byte/frame/journal failure transport
and target transient/world/callback execution remain open. P2 computed-static
execution is readonly-external's producer obligation. No original full-gate
failure is relabeled, no goal is administered, and no publication or lane
completion is claimed.

## P1-06: actual caller-cell recovery, with preserved stack

`Solidity/Backend/InternalFlow/RuntimeFrameRestore.lean` supplies `Restore.code`
and `run`: actual runtime pop followed by store into the chosen original
caller cell. `stack`, `destination` and `outside` pin exact machine effects.
The original positive-pointer/separate-payload conditions remain explicit;
if destination equals the pointer cell, no pointer-preservation claim is made.
`after_fragment` composes a genuine successful run and its derived scratch
`Words` proof with the same restore instructions, retaining exact saved-word
and evaluation-stack observations. It does not supply a simulation oracle.

`consume_run` proves an actual physical temporary clobber followed by writing
the recovered stack word into the caller destination. `local_repr` retains the
FULL existing reached `StateRepr` once that top word is proved to equal its
represented local word. It covers any intrinsic local type by its genuine
`Idx`; it does not repair arbitrary malformed inputs or infer fragile liveness.
`uint_unique` discharges the inhabited scalar's representation match.
`contextCells` and `cell_member` derive all physical caller cells from the
original intrinsic context. `saveCells` and reverse `restoreCells` assemble
only existing instruction slices, not another state evaluator.

the lane-only fixture RestoreFrameControls.lean (not on master) imports the unchanged checked
nested-call fixture from the SAME build cache. That dependency was freshly
kernel-checked with all227 original ordered builtin reports before producing
its import object; its exact source/object hashes and receipt are recorded.
This focused preparation is not a raw/cached/full assignment gate pass.
`represented_repair` consumes the actual nested mutating call endpoint, proves
the recovered scalar equals the source-transported reached local, then restores
a clobbered cell while retaining the SAME full reached representation,
`BaseExtends`, exact allocator growth7 and protected stack `[77]`. Changed old
contents `[37,41]`, unrelated `[21]` and physical private/default objects are
retained; no pre-call heap restoration is inferred.

The separate five-binding machine client saves ALL cells1–5 of the populated
Caller (scalars11/9 and references256/259/256), executes the real nested call,
actually overwrites those cells with0, then restores in reverse order. The
complete34-word target snapshot pins all caller/private/heap cells, saved
payload110–114, pointer110, cursor268, sentinel99 and protected stack77; roots
remain7/31. A pre-restoration snapshot shows the clobbers, and wrong-order,
wrong-destination, wrong-alias, cursor/stack and exact body-revert controls
have positive baselines. This is a concrete full-context machine witness,
NOT a generic whole-context `StateRepr` restoration theorem or recursive
runtime dispatcher. Generic multi-binding source/frame closure and return
control remain P1 obligations. Error outcomes supply no failed State, rollback,
absence of earlier effects or byte/world result.

H10 update: P4/G37.03 is transferred to compiler10/memory-reference-structs;
earlier prospective P4 work notes are superseded. V12 continues P1 then G38/G39.
The exact P2/P5/P6 packages relayed by the coordinator were independently
checksum-verified and fetched into local remote refs without changing the
checkout. They are unfinished development inputs, not published/integrated
prerequisites or discharged hypotheses. P2 still requires execution-linked
`Invocation.RuntimeFrames` history and P3 `RawAt`; P5 still requires an actual
LoopCert, reached representation/frame and FiniteLoopRoom; P6 still requires
initial WordFrame/W-fit/source-memory representation and live index evidence.
Their precise heads/signatures and private combined staging status are retained
in evidence/handoff. None is converted into an axiom or counted as final closure.
All original Work1–6/Backfills A/B remain partial, with Work3 now peer-owned.
Original mandatory gate failures, prior seals and the unchanged blocked goal
are preserved; there is no publication, master merge or goal administration.

## P1-07: whole-context capture/restore and numeric store-stage refinement

Current registry supersedes the historical queue notes above: V12 owns current
P1/G37.01, then G37.02, G38 (with V11 P6b), and G39 (with VY4 P7 e0895784).
Backfill A/B continue within those groups. G36.01 belongs to V17, G36.02 to
VY2 and G37.03/P4 to memory-reference-structs; they are not V12 work items.
No moved producer is reimplemented here.

Before this item, origin/master was fetched and inspected at
`febf70a6ba99df908a69499aca026381c3993102`: its entrypoints merge does not contain
these frame/context or P6 modules. The existing helper was fast-forwarded to
the already verified authorized peer tree
`d0ed4ba9004eef84ef7dab2f826b5f0e269686f5`. Exact P2/P5/P6 heads and module hashes
remain recorded; no reserved source was repaired and no master branch changed.
The focused P6 consumer closure is checked here; this does not pass the entire
combined root or any producer's original final gate.

### General current P1 interface

`RuntimeFrameContext.lean` proves `Context.restore_many`, `restore_context`,
`capture_many`, `capture_context` and `program`. All use the existing
`Restore.saveCells/restoreCells`, actual Evm.run and intrinsic Ctx/Idx/State.
There is no new evaluator, source judgement, depth admission limit or desired
simulation field. Arbitrary finite contexts/list lengths are quantified.

Capture inputs are the genuine full StateRepr, local boundary, runtime pointer,
non-overlap, reserved-frame headroom and W no-wrap bounds. Its actual instruction
induction DERIVES the captured payloads, pointer advance, unchanged caller
words/exterior fields, full initial StateRepr and zero GrowsAllocator.
Restore induction DERIVES actual reverse pop/store execution, ALL original
caller words (including symbolic Slot words), protected stack, pointer reset,
post-body exterior memory and machine fields, and allocator preservation.
These fields belong to the AFTER-body machine, not a rollback to the before
machine. Physical symbolic-slot encoding is not inferred.

`Context.program` takes an actual Composition.Program, represented input,
its real allocation capacity and actual intrinsic source result. It obtains
body execution/StateRepr/BaseExtends/GrowsAllocator/Words from the existing
checked endpoint and derives reached capacity with nextInput. Captured words
are not assumed: actual capture and the derived body footprint supply them.
The output names actual save, body and restore run equations and their SAME
machines, complete sandwich execution, exact reached allocation cost, final
protected stack and every typed caller cell. StateRepr(out.st) is asserted
at the AFTER-BODY, BEFORE-RESTORE machine. Final old caller words do not model
arbitrary source assignments to those locals: source-frame/return/export
agreement and runtime return control remain separate P1 obligations.

`ContextRestoreControls.lean` closes this full generic pipeline using the real
populated prefix, prefix producer, real capacity, selected nested memory-result
call, source output and growth7. The complete34-word target vector retains
all aliases/scalars, both defaults/private objects, cursor268, saved payloads
and stack77. A second actual captured path writes persistent root p=29 through
Memory.compileStmt, overwrites all five caller cells and restores them from
actual captured payloads. Its typed scalar/reference transport is derived
from prefix StateRepr, not an assumed midpoint. Roots remain29/31, explicitly
rejecting rollback to7/31. Wrong ordering, zero context and symbolic-word
controls retain the actual semantics; source alias liveness is not invented.

### Exact P6 store-stage consumption

`RuntimeFrameBytes.lean` imports the unchanged relayed PhysicalWordFrame and
PhysicalByteJournal APIs. `Bytes.initial_cell` derives an INITIAL sparse
numeric WordFrame from an actual represented numeric read; selected-cell
32-byte W-fit is proved independently of frame capacity. `byte_run` and
`clobber_run` execute the existing Environment.runCrypto PUSH/MSTORE code;
`consume_frame` couples it to the actual word clobber/recovery and derives
its reached WordFrame and exact word bytes. `scalar` derives the captured-word
match from genuine source ReprV and retains full reached StateRepr. Symbolic
slots are explicitly unrepresentable at this numeric byte boundary.

`ByteRestoreControls.lean` discharges initial representation and W-fit from
the SAME real nested-call endpoint. The saved scalar9 is temporarily257, then
recovered into caller cell2; both word and byte tails retain77. Exact byte
observations include both exterior sentinels17/23, all32 bytes, embedded zeros
and the distinct intermediate257 image. The actual following live REVERT reads
those recovered32 bytes and retains them before any separately supplied
checkpoint. Wrong scaling, source capture, length/class, symbolic encoding and
W-capacity controls have inhabited positive baselines.

This is a numeric STORE-STAGE refinement, not a compiler for dynamic pop
loads/arithmetic, whole-memory identity, physical EVM/gas theorem or external
world/transaction rollback. The byte REVERT follows successful word recovery;
it is not an invented payload for an error-valued Evm.Out or THalt.data.
P2 execution-linked source History and V13 RawAt still require their actual
source-world producers; P6a is not counted as the later P6b/G38 closure.

Prior227/27 source and axiom inventories remain unchanged. Their checked
import object is authenticated against sealed source/object hashes and the
unchanged transitive source closure. New per-file report sets, real resource
receipts, failed attempts and independent reviews are in the P1-07 sealed
handoff/evidence. No new original aggregate/raw/full retry or gate waiver is
claimed. The active four groups and relevant Backfills remain partial;
original failed gates/seals and the unchanged blocked goal are preserved.


## P1-08: primitive result export after a private typed frame

`RuntimeFrameResult.export_result` consumes the producer's reached `StateRepr`
and emits an actual load from the reached primitive result cell followed by a
store into the old caller destination. It derives the complete representation
of the resulting source assignment and scope drop from published
`StateRepr.setVal`, `StateRepr.drop` and `CallResultRestore.state_drop_set`.
The source and target share the actual reached result, not an assumed desired
post-state. Private physical cells remain present. Mutated heap contents,
current fragile-alias evidence and post-body world fields are retained.

This scoped primitive export does not establish whole-context restoration for
arbitrary source assignments, a call compiler, dynamic return dispatch or
unbounded recursion. The new client has two distinct same-typed caller values,
a distinct private result, a protected evaluation stack and cursor/sentinel;
wrong result/destination and private-erasure controls supplement its complete
ordered source/target observations. Actual check receipts and review results
are recorded in the checkpoint handoff, including failures.

The helper was rebased onto published
`959aefa8e7a46c5164f72a21cdf901b64d6805e9`; the sealed pre-rebase head
`61b92d1a2c25034feb1877faaf478b857ae38835` remains bookmarked. Replaying the P2
merge required restoring its exact committed `SourceCallFrame` blob from
`51f604df3a9e5ed9c254f2d292cf18c1a0743d32`, including input calldata, rather
than authoring a producer change. Four duplicate root registrations were
removed while retaining their earlier imports. Previous authentication of
fixture objects is not promoted across this changed upstream source closure.

P1/G37.01, G37.02, G38, G39 and relevant Backfills A/B remain partial. G36 and
G37.03 remain with their registry owners. Original raw/full/cached/doc failures
and all prior seals remain preserved; no unchanged final-gate retry is claimed.

P1-08 checked evidence: the final module/import closure passes (95 jobs), and
`ResultExportControls.lean` passes in3.278s with15 exact ordered builtin axiom
reports. The populated reached frame also comes from actual `entryCode`
execution; `whole_run` composes entry and export using `run_append_ok`.
Only standard axioms occur. The generic zero-cost allocator law retains its
actual allocator-ownership premise; the client observes the cursor but does
not claim an inhabited allocator witness. Layer/orphan/trust and strict report
corruption checks pass. Independent read-only finder/skeptic source reviews
report no confirmed finding and ran no Lean/server/builds.

Three changed-prerequisite preparations timed out at120.608/121.730/121.324s;
the narrow remaining LeafShare preparation then passed8.898s. The initial
fixture parser/decidability failures (including Lean-generated recovery
axioms in failed output) remain raw failed evidence, not deliverables. The
corrected fixture has no recovery axiom. Actual final runtime check reports
Lean4.24.0/Lake5.0.0-src+797c613 and successful KeySort/import build in1.851s.
Every check retains hard12GiB/no-swap enforcement and serial-j1 execution.
Earlier fixture objects are not recertified across the upstream rebase by
source-byte preservation alone. No original failed full/raw/cached/docs gate
is relabeled or repeated.


## P1-09: reached reference export and fresh memory-result head

`RuntimeFrameReference.export_reference` obtains the actual typed reference and
its address from reached `StateRepr.pointers`. Its real load/store transfers
that reference into an old caller destination; existing `setMem`/`drop` laws
supply FULL reached representation. `export_head` instead exports at the next
caller level, using genuine frame room and `drop`/`consMem`. `leave_memory`
states the exact intrinsic `CallRet.mem.leaveT` environment, retaining both
original default/map-free premises. No independent saved-caller environment
agreement, full call-body compiler or runtime dispatcher follows from it.
The zero-cost old-destination allocator law retains genuine ownership and
positive-origin premises; the nonallocating public fixture uses b=0 and does
not claim an inhabited allocator witness.

The owned client consumes the unchanged published populated
`MemoryCompileExamples.fixture_six_cells`. Actual source/target slices change
old object0 from[7,9] to[37,9], retain scalar9, export distinct object1[4], then
write through that returned alias to obtain[53], keeping the other old alias
and its[37,9] contents. Complete ordered source/target snapshots include both
objects, aliases, stack77 and private physical cells. A deeper private frame
copies result0 from cell6 into fresh caller head4, replacing the distinct
private result1 pointer while retaining private11 at5 and pointer16 at6.
Wrong reference/destination, old contents, private erasure/escape and revert
controls have actual successful baselines.

These concrete entry/next-use instruction slices are not public compiler
selection proofs. An attempted additional compiler-link formulation exited137
at the enforced12GiB cap, produced no closing proof reports and was not
adopted. Its exact source/receipt remain failed evidence. The failing
individual declaration was not isolated; no unique normalization cause or
missing-producer claim is made. Public selector/constructor sharing and
abstract certificate endpoint composition remain ready owned work.

The final26-report fixture passes5.155s; the generic head module passes2.917s.
The initial new fixture parser/closed-bound/source-normalization failures are
retained; the corrected proof uses the actual finite intrinsic execution and
only standard axioms. Two source-keyed public fixture preparations timed out
at121.644/121.768s; narrow SoundCalls and Compiler preparation subsequently
passed40.629/21.538s, then the actual published fixture target passed6.669s.
No original aggregate/raw/full/docs gate was retried or relabeled.
Fetched master a9697221 contains new struct/browser work, but no matching
reference-export interface; this independent adapter retains its existing
959aefa8 development base rather than duplicating or editing those producers.
P1/G37.01, G37.02, G38, G39 and relevant Backfills remain partial. Transferred
G36/G37.03 groups, previous seals/observations/pins, and blocked goal remain
unchanged. Exact gates/resources/reviews and the current immutable handoff
record the kernel-versus-compiler/world boundary.

The concrete `memory_return_agrees` control instantiates actual `CallRet.mem`
with its original true default/map-free premises. All26 exact builtin reports
are pinned, with the preceding25 in unchanged order and axiom sets. Independent
read-only finder/skeptic source reviews found no confirmed issue and ran no
Lean/build/server. Their allocator/compiler/source-caller boundary cautions
are retained above. Actual final runtime gate reports Lean4.24.0,
Lake5.0.0-src+797c613 and successful KeySort/import build2.370s. Strict corruption
and structural checks, complete command/resource receipts and exact artifact
reviews are recorded in the immutable checkpoint handoff.


## P1-10: actual checked-program reference/export/use composition

`RuntimeFrameReferenceProgram.after_reference` now consumes the existing
published `Calls.Program` and its actual frame need/cost/soundness. It derives
the reached machine/reference/address map from the producer, then executes the
real export and returns FULL reached `StateRepr`, exact export write, protected
stack, `BaseExtends` and `GrowsAllocator`. `after_reference_then` consumes a
following checked program and derives its actual input from the genuine summed
capacity via `GrowsAllocator.nextInput`. `revert_absorbs` retains the exact bare
revert alternative without inventing a failed state, cursor or world rollback.
No new evaluator, AST, admitted fragment or simulation record is introduced.

The actual public `compileProg` selector and source/cost/frame facts are sealed
in the new `ReferenceCompilerFacts` import boundary. Its `Calls.plain` bridge
closes all concrete producer, representation and cost-zero capacity premises.
`ReferenceCompilerEndpoint` derives the SAME complete ordered10-cell target
vector from that actual reached representation and address map. The next
public compiled alias write changes object1[4] to[53], while object0 remains
[37,9], scalar9/aliases and stack77 survive, and physical private cell4 remains
pointer20. That last field follows existing `Mutation.safe` and a proved sound
code-data equality to the actual public next code; it is not an assumed frame
relation. Wrong alias, original contents, missing subsequent mutation and
private erasure are rejected with successful baselines.

An actual bad-index compiled suffix instead has source `.error .revert` and
target bare revert; arbitrary following instructions are absorbed. This does
not classify panic/payload/exhaustion/divergence or reconstruct their state.
The nonallocating b=0 client discharges real zero-cost `AllocationInput`; its
allocator implication is not inhabited allocator ownership or a cursor
observation. General callers with allocations retain the exact existing
cost/ownership/room premises in the interface.

Final facts15 reports pass4.551s; the final public client13 reports pass8.932s,
all standard axioms, with unchanged proof/time/resource limits. Isolated
selector2.381s and small imported projection facts replace the earlier combined
137 formulation, which remains failed and was never rerun. These are genuine
represented/observed endpoints, not the earlier unproved whole-machine
functional equality; no timing comparison is claimed as proof of that stronger
statement. New syntax/rewrite failures are retained raw, corrected without
budget changes. Previous26 reports and all prior sources/pins remain unchanged.

P1/G37.01 remains partial: saved-caller source agreement, capture/restore and
actual runtime return control still need their full composition. G37.02,
G38/G39/world and relevant Backfills remain open; G36/G37.03 remain transferred.
No original cached/raw/full/docs failed gate was repeated or relabeled. Exact
checks, source/toolchain/cache bindings, independent reviews and all remaining
queues are in the immutable checkpoint handoff.


## P1-12: implemented frozen restoration premise

`RuntimeFrameRestoredRepresentation.lean` proves the exact frozen v1
`RestoredRepresentationClaim` and constructs `restorationProducer`. No frozen
signature changes. Typed captured-index recovery, primitive encoding uniqueness
and actual storage-path slot uniqueness derive caller-word agreement from the
source environment equation, two real representations, BaseExtends and explicit
NoAliasPromotion. Current fragile liveness and current heap contents remain
those of the reached state. Logical locals impose no physical-word constraint.

The populated client runs an actual old-object memory mutation and actual
restore instructions. It retains two aliases, a distinct object, private local,
scalar9, stack77, changed heap53 and the saved payload/cursor. Wrong old heap,
wrong alias and dead-to-live promotion are rejected. Source and target mutation
facts and the reached representation are checked independently; saved payload
is explicitly constructed, not claimed as a new whole call-lowering theorem.

Read-only finder and skeptic source reviews found no correctness issue and
requested the inhabited client/alias-promotion control, now supplied. General
call-source agreement, arbitrary workspace reuse, runtime return dispatch and
unbounded recursion remain open. This implements only PendingRestoration;
G38/P6b, G39/P7 and relevant Backfills remain partial. G36/G37.03 stay transferred.
Historical full/raw/cached/docs failures remain failed, with no retries here.

The concrete client uses reflexive context extension and already source-agreeing
caller words. It does not demonstrate clobbered-cell recovery, private-prefix
reconstruction or inhabited storage-alias path transport. The general theorem
quantifies those typed cases only under its explicit frozen premises.


## P1-13: actual captured checked-body composition

`RuntimeFrameCapturedProgram.endpoint` now composes genuine context capture,
checked body execution and restoration with the frozen full representation
proof. Saved payload, reached machine/address map, target phase/whole runs,
BaseExtends and exact GrowsAllocator are derived outputs. Actual source caller
tail equality, current alias-fragment compatibility, body/result frame bounds,
runtime arena bounds and AllocationInput remain explicit real premises.

The populated client discharges these premises: scalar9 exists before capture,
then an old aliased array changes7→37, an independent array remains4, and a
private reference binder is pushed. Actual capture outputs [20,16,16,9]; final
stack77/cursor10 and ordered cells [20,16,16,9,20,2,37,9,1,4] come from the same
reached StateRepr/address map. It has non-reflexive private context extension.
Wrong source caller scalar, old heap value and un-restored cursor are rejected.
Separate phase execution equations are in the generic endpoint; the concrete
endpoint also supplies whole execution and captured/recovered relations.

`bare_revert` derives capture→actual checked failure and suffix absorption.
Its inhabited bad-index body distinguishes bare revert from fault; it does not
claim restoration executes after failure, a failed State, rollback or bytes.
Both clients have b=0 and zero heap cost: GrowsAllocator is the genuine existing
conditional law, not an inhabited allocator cursor or ownership claim. The
runtime-frame cursor is a distinct explicitly initialized scratch word.

Finder/skeptic read-only source reviews pass. Exact frozen interface signatures,
previous sources/fixtures/pins and historical failed gates remain unchanged.
General call-source agreement, return/export scheduling, runtime return control,
uncapped recursion and G38/P6b/G39/P7/world remain open; G36/G37.03 transferred.
