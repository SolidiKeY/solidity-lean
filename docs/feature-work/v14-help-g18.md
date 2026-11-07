# V14 H10 aggregate lowering helper

This helper is partial. The original V14 lane and its frozen base are preserved separately. The helper was rebased onto published master `febf70a6ba99df908a69499aca026381c3993102`; duplicate Source/checker work is archived at `refs/archive/v14-help/pre-master-e986` and its prior immutable exports remain intact. Published Source semantics and both checkers are unchanged here.

`Backend/Aggregates/ByteParameters.lean` imports a runtime raw calldata byte region into the existing intrinsic typed memory heap. `entry_region` derives the absolute selector-adjusted offset and extent from actual successful `Source.cdTail`. `entry_payload_exact` requires a four-byte selector and actual frame calldata equality. Capacity follows from the published 64-bit entry length check, rather than a supplied target resource oracle. `copy_related` proves the actual `Source.cdToMem` allocation and intrinsic target allocation contain the same byte words, retaining separate Source and target identities. `new_local`, `old_local` and `target_old_heap` establish the pushed reference, weakening of all existing locals and preservation of every old target object. This is a value/frame importer, not a literal emitter or whole compiler simulation.

`Backend/Aggregates/ByteParameterControls.lean` inhabits entry decoding with nonempty selector/payload, two old Source objects and two old target aliases. Fresh identities are Source 2 and target 1. It checks old byte contents, runtime-input dependence, zero-length copying, omitted-selector failure, malformed ABI extent and reversed/past-end slices. Zero-length copying does not claim a separately decoded empty ABI argument. Source globals, compiler frame production, recursive copy/delete, nested/reference-element aggregate lowering and EVM execution remain open.

## Private P5 producer

The exact committed P5 input `61db3cac4067c3035b240d7f51f354b509facd90` was checksum-verified and privately merged at `07c9ce38776da84bb6923302a81ca18d729c1459`. This is unfinished peer development input, not published master. Its five `Evm/MemoryLoop*Horizon*` modules remain read only. Finite transport requires actual `LoopCert`, `StateRepr`, body frame bound and `FiniteLoopRoom`; recursive body fuel and an enclosing/global horizon bridge remain open. The byte importer has no matching assumed loop theorem to replace. No Source-to-IR bridge or G36.03 divergence follows from staging P5.

## Reviews and validation

Separate independent read-only finder and skeptic reviews inspected actual statements and controls, without Lean/server/builds. Finder requested selector/frame provenance, actual pushed-local observation and inhabited alias/heap controls; these are implemented. No confirmed soundness or ownership issue remains in their code review. Exact 24-name/count standard-axiom whitelist reports (raw `#print axioms` plus a fail-closed Python audit, not `#guard_msgs`) and actual final gates are recorded in the checkpoint handoff; failed attempts are retained separately, never relabelled passes.

## Remaining original queue

G43 payment/send/transfer and world/history/stipend asymmetry: partial. G36.03 effectful finite-prefix/divergence: blocked on actual V12/G37 and general Source/world transport. G44.01 constructor Source argument lowering: partial; V07/V09 production missing. G44.02 artifacts and G44.03 creation/frame consumers: partial. G45.01 selection, G45.02 frames, G45.03 control labels and G45.04/.05 assembly/encoding: partial. G45.06 fetched executable composition: blocked on pinned decoder/step and structured-loop producers. Backfill A/B: partial. H10 G18.04/.05: partial; this byte parameter leaf closes neither whole item. The original goal is not complete.

The final mandatory full gate exited 124 at the unchanged 180-second wall limit (one Lean worker, aggregate peak 1,538,312 KiB; no OOM). Default build was unfinished; TestSuite and SolKey were not reached. This is a failure, not inherited-pass evidence. KeySort passed (2 jobs), Lean 4.24.0 / Lake 5.0.0-src+797c613. Structural, orphan and trust gates pass; checkpoint1 final raw docs exits1 with48 missing and39 ambiguous findings (see correction below). Full baseline comparison and final integration remain separate. Independent guard reviews found empty-census and duplicate-report acceptance; the audit now requires exactly 24 unique queries, rejects duplicate reports and has eight positive/negative regression controls, including optimized Python.

C5: relative to published master `febf70a6ba99df908a69499aca026381c3993102`, there are no Source or Frontend/Static changes. The d7291b76 calldata references/slices/cdToMem/checkers are consumed read only. Registry update moves G45.03 execution meaning to revert-outcome-specs, G45.04/.05 to master and G18.06 to V07; original V14 partial head `22a1b53ecd0d50272d26e2758bafaead52bf247d` is preserved. Current helper item remains G18.04/S02-CD-AGG; next are G18.05, G44.01 and G43, with a fresh master inspection before each item.

Exact published-base full-gate comparison also exits 124 at 180 seconds. It used a separate source checkout at `febf70a6ba99df908a69499aca026381c3993102` with the same single cache, cap, no-swap and thread settings; no required full gate is waived. Cold-progress differences do not prove a timing regression or equivalence. Neither full run reached TestSuite/SolKey. The initial multiset comparison preceded later handoff wording: final checkpoint1 raw output also contains one owned ambiguous Arms module citation. Thus checkpoint1 no-new versus published/private is FAIL, not PASS; against frozen there are additionally two inherited missing Yul paths and one inherited ambiguous Arms module citation. See checkpoint3 correction; raw failures/seals are retained.

`entry_value` consumes the actual `Source.cdArg` producer. `raw_parameter_related` retains its read-only calldata reference, relates that actual Source value to the new typed object and derives full extent and capacity from the tied entry/frame. This does not assert that Source dispatch allocates memory: only the separate `source_copy`/`copy_related` theorems concern explicit `cdToMem` conversion. The inhabited `entry_reference` exercises the actual raw reference importer.

The independent P5 focused cold-closure attempt also timed out at 180 seconds before all five producer targets and signature command completed. The private package is checksum-verified but its combined local kernel gate remains pending; no owned theorem imports it or claims its premises are discharged. This unchanged failed gate is not repeated.

Final owned focused import closure passes, including the actual raw-reference consumer and inhabited client. The final 24-theorem axiom/signature query passes separately; only propext, Classical.choice and Quot.sound occur. `RefRelated` is snapshot byte-value agreement: no readonly/aliasing operation simulation is inferred for the mutable intrinsic target object. Separate finder/skeptic source and audit reviews accepted the repaired code. The final root-wide gate remains pending after the last additive owned proofs; earlier actual combined/base/P5 180-second failures remain raw failures and are not retried unchanged.

## Checkpoint handoff

Source checkout `/workspace/solidity-v14-help`, published base `febf70a6ba99df908a69499aca026381c3993102`, private producer merge parent `07c9ce38776da84bb6923302a81ca18d729c1459`. Exact committed head, source hashes, complete signatures, commands, raw outcomes and exports are bound in the immutable external handoff under `/workspace/v14-master-rebase-artifacts/checkpoint1`. Original V14 branch/head/base and older seals are preserved. This checkpoint is partial; G18.04/S02-CD-AGG has ready remaining work, including general aggregate/reference-element and operation preservation. No goal transition is made.

## Checkpoint2: actual typed slice execution

`Backend/Aggregates/ByteSlices.lean` proves exact `Source.evalE` of the existing typed `RExpr.slice` over three input locals and an arbitrary populated caller tail. The result is the actual `sliceR` result mapped to `RVal`, with the complete original locals and `Source.St` preserved on success or failure. `import_slice` derives both uint256 index typing and the intrinsic object length bound from the actual entry and slice bounds, evaluates the typed expression, relates its actual raw reference to the imported target object and derives the exact untruncated extent from selector/frame provenance. Object length bounds are not physical EVM memory headroom or gas facts. No evaluator, expression AST, source representation or semantic profile is changed.

`Backend/Aggregates/ByteSliceControls.lean` inhabits the Source global record, evaluates an actual local slice and its invalid-range/empty cases, and reuses checkpoint1's two Source objects and target caller aliases. It proves exact success bytes [8,9], unchanged complete Source state/heap identity, protected caller locals, empty-range reference and ordered empty revert bytes; wrong Source allocation, halt bytes and omitted slice origin are rejected. This is local-expression/value/frame evidence, not a deployed call, readonly operation simulation or source-to-fetched-EVM theorem. Its explicit unused fixture global functions are not a claim about pinned EVM behavior.

Current audit expands to 42 exact headline/control names; the same fail-closed guard and eight regression controls remain mandatory. Whole-root/TestSuite/SolKey and P5 combined gates remain pending after the retained180s failures; no unchanged failed heavy gate is retried. Source and Frontend/Static remain unchanged (C5). G18.04/S02-CD-AGG is still partial, including ready remaining nested/reference-element calldata source semantics and general aggregate operation lowering. These owned missing Source operations are not labelled an external prerequisite. G18.05 is not declared finished or started as a replacement.

Checkpoint2 final gates: 64-job focused import closure and 42-theorem kernel axiom/signature query PASS; exact-name42 whitelist audit and 8/8 optimized-Python regression controls PASS; layers/orphans/trust/diff PASS. Checkpoint2 raw docs remain exit1 (48 missing,39 ambiguous), including the owned ambiguous Arms module citation; no-new versus published/private is FAIL in that seal. The later correction preserves this raw failure; frozen no-new also remains failure. Separate source finder/skeptic accepted actual new statements, typed clients, preserved caller state and precise limits. No new full gate is claimed; retained full/base/P5 failures and final root/TestSuite/SolKey pending remain binding. Exact new head, signatures, hashes and gate/review evidence are sealed in `/workspace/v14-master-rebase-artifacts/checkpoint2` after commit, preserving checkpoint1.

## Checkpoint3: actual owned S02 calldata aggregates

This implements new missing Source operations under the explicit H10/S02-CD-AGG ownership assignment, rather than duplicating d7291b76. Source.State/Val and both Frontend/Static checker files are unchanged. Fresh master `959aefa8e7a46c5164f72a21cdf901b64d6805e9` was inspected: its relevant Source blobs match published base `febf70a6` exactly; its latest calldata-origin edit is a reserved frontend import change, consumed read only.

`Source/CalldataLayout.lean` derives inline static head dimensions from existing types. The existing `STy.oneWord` implementation moved unchanged into Types; `isValueTy` reuses it. `indexLoc`/`readLoc` now use actual typed byte/string/dynamic-array/fixed-array calldata locations. `cdNested` consumes the existing cdTail bounds/length/failure ordering and adjusts its real base; static-array elements use their complete inline stride (64 bytes for uint[2]). All writes at new locations retain readonly refusal; existing memory-invariant/progress statements are preserved with new cases. Source slice typing now admits strings and represented static reference elements and continues to refuse dynamic-base slices (native2148). Direct static-root slicing remains native1227/4802; root static entry, structs, dynamic-element fixed shapes, general nested copying and final lowering remain open. No admitted whole-profile closure is claimed.

An investigated origin-carrying Value representation was warned about, checked and then superseded when pinned native evidence showed dynamic-base slices are refused. Its uncommitted draft, original logs and checksum evidence remain under the task evidence drafts directory. The final implementation retains the exact published Val.cdRef Nat API and carries each nested base in typed read locations. No other owner file was changed to accommodate a representation refactor.

`Source/CalldataAggregates.lean` proves actual nested read run/state/region facts and exact execution composition for one and two typed local indices, covering real parent bounds, child failures and successful caller-state transport. It assumes no desired execution, world preservation or target simulation. `NestedCalldataControls.lean` inhabits actual decoder and expression paths for bytes[], string[], uint[][] and uint[2][] slices. Full caller state, old heap objects/aliases, exact empty revert versus Panic0x32, copied string bytes34/51, actual uint[][] result21, static64-byte stride and readonly rejection are observed. Wrong bytes, stride, allocation and halt controls remain discriminating.

Pinned solc0.8.38+1835d247 SHA6c74ffba acceptance/refusal checks pass seven cases in 60-second budget, with complete ordered compiler errors retained. This is compiler acceptance/encoding evidence, not EVM execution. New Source expression progress PASS26s, statement progress PASS72s, initial checker/hasType_iff closure PASS110s and focused control closure PASS; final scoped 91-theorem audit and final gates are tracked in the checkpoint handoff. All original raw failures and earlier seals remain immutable. Current G18.04/S02-CD-AGG remains partial with ready remaining work; G18.05/G44.01/G43 and every original obligation remain in QUEUE.

Checkpoint3 final gate evidence: focused control/import closure and all91 kernel axiom/signature queries PASS; exact91-name whitelist and8/8 audit regressions PASS; nativecompiler7/7 PASS; Source ExprProgress PASS27s and StmtProgress PASS72s; final Infer/InferComplete/hasType_iff closure PASS123s. Layers/orphans/trust/diff PASS. Actual new whole ./run-lean.sh attempt FAIL124 at unchanged180s during existing Frontend.Checked.UnitExamples (maxoneworker, aggregateRSS6,787,244KiB, cgrouppeak8,630,501,376bytes, swap0,noOOM). Default build unfinished; TestSuite/SolKey NOT REACHED. The prior exact-published-base full gate also failed180s; no timing-equivalence or inherited-pass waiver is inferred. Whole-source/full integration remains incomplete. The initial checkpoint3 docs gate also found the owned ambiguous citation; raw1 and failed no-new results are retained. The separate documentation correction removes it, after which published/private multiset equality is checked again. Frozen no-new remains failure. Final committed source/actual gate hashes and exact signatures are sealed at `/workspace/v14-master-rebase-artifacts/checkpoint3`.

## Documentation evidence correction

Checkpoint1 and checkpoint2 handoffs incorrectly described final documentation multisets as matching the published/private baselines. Their actual final raw logs and SLICE-DOC-COMPARISON show one additional owned ambiguity from this document referring to the Arms module without qualification. Earlier comparison snapshots predated that wording. These sealed outputs remain immutable; adjacent corrections bind their manifests and record the no-new FAIL. The citation is removed here. The corrected current comparison must be read separately: raw docs still FAIL1 on inherited missing paths; zero new findings versus published/private is never a whole-docs PASS. Frozen-base no-new still FAILS on the inherited two missing Yul paths and one ambiguous module citation. No reserved documentation is edited.


## Checkpoint4: exact scalar-array copy and conversion outcomes (G18.05 partial)

Fresh origin/master `eba99fe7` was fetched before this leaf; its Source evaluator/types/calldata files are unchanged from the inspected published base. No duplicate implementation was added. `Solidity/Source/CalldataCopy.lean` consumes the existing actual cdToMem and convRV arms: ordered pure decodeWord traversal returns its original halt with the complete original caller state, or allocates one fresh typed array after all validation succeeds. Old nonfresh cells are retained on both outcomes. The failure premise in the specialized corollary is the actual decoder result, never a desired simulation or preservation oracle. Generic element types may still refuse; no recursive-copy closure is inferred.

`Solidity/Backend/Aggregates/CalldataCopyControls.lean` inhabits bool words1/0/dirty2 with two populated old objects and aliased caller locals. Two valid elements copy in exact order; actual copy-then-read returns true then false at their distinct indices; wrong order is refuted. The dirty third element returns exact empty revert, no partial allocation and unchanged complete state, including through the actual implicit conversion arm. An empty copy still allocates a fresh empty array; wrong panic bytes and wrong allocation are refuted. This is kernel Source interpreter evidence, not general Source-to-NEWBackend lowering, pinned EVM execution or native compiler execution of this client.

Focused import closure passes73jobs. A separate exact22-query standard-axiom guard and8 audit controls preserve the previous91-query audit unchanged. Original raw proof/admission failures are retained. New registration requires final full confirmation; the prior unchanged full180s timeout and unreached TestSuite/SolKey remain unresolved rather than being rerun for activity or called passed. Documentation raw failure and frozen comparison remain separate from published/private no-new equality. Serial Lean-j1, fixed12GiB/no-swap, real admission, writer lease and all proof/time budgets are unchanged. Per-file MCP is unavailable; bounded per-file/import-closure CLI fallback is used. Independent finder/skeptic review outcomes and exact gates are in checkpoint4's sealed handoff. G18.04 remaining aggregates/general lowering and G18.05 recursive/location/copy/delete policy remain owned ready/open work; original V14 obligations stay partial.

Checkpoint4 final handoff: parent `0de70d4fd1143d04466c64e694969eb84a2a9569`; final focused runtime/KeySort/73-job closure/22 scoped signature and axiom output PASS in3.99s, peak aggregate876064KiB, oneLean, child563781632bytes, noOOM/swap. Layer/orphan/trust/diff and8 audit regressions PASS. Raw docs FAIL1, complete current finding multiset identical to corrected published/private86 findings; frozen no-new FAIL retained. Source finder and skeptic accepted proof; skeptic's wording finding was fixed by removing untested lazy-read language. Guard finder/skeptic accepted separate exact22 audit and partial claims. Final reviewed delta adds actual staged copy/read order controls. Exact commands, theorem signatures/premises, checksummed sources and remaining every-item queue are exported in the checkpoint4 handoff; no full goal closure.


## Checkpoint5: derived copy extent and actual indexed access (G18.05 partial)

Fresh origin/master `eba99fe7` was fetched before this leaf; relevant Source evaluator/calldata/state files remain unchanged from the published helper base. Checkpoint4 is preserved. The new Source proof module derives list length and every positional decoder equation from actual ordered successful validation. It proves actual readLoc over the newly allocated typed array and composes cdToMem with that read on the actual grown heap. No desired run, preservation or simulation premise is supplied. Successful validation is the actual decoder traversal equality, which can refuse for unsupported element types. Derived capacity here is Source array extent only, never physical memory/gas availability.

The new access controls reuse the existing populated caller and dirty-bool fixture. They derive the second positional decoder/read observation, distinguish a successful copy followed by Panic0x32 (grown heap retained) from dirty validation followed by an unreachable out-of-bounds read (original exact empty revert and original state), and check empty-copy bounds, nonzero byte origin, wrong origin and false rollback. These are finite kernel Source interpreter consequences only. General aggregate lowering, recursive copies/delete policy and EVM behavior remain open.

The touched module closure passes75jobs. Independent proof finder/skeptic and separate guard/document reviews are recorded in checkpoint5's handoff; exact18 scoped axiom/signature queries and8 audit regressions preserve prior91/22 audits. Per-file MCP remains unavailable; bounded CLI fallback uses one Lean-j1, unchanged12GiB/no-swap/180s budget, real admission and writer lease. Earlier proof/layout errors are retained raw and repaired. Under H12, full end-of-lane checks are checkpoint-only; the unchanged prior full180s timeout and unreached TestSuite/SolKey remain unresolved without a repeated failed heavy attempt.

Relayed P10 frozenV1 producer `515ac91d782115d65d2b1a53c2ad7445efc708ee` was checksum-verified and fetched only to its exact private peer ref. Its Bridge interface/witness are read-only and not imported into core or identified with Source semantics. Current copy proofs have no P10 premise to replace. Local combined kernel validation of that producer is not claimed. Site-to-source/compiler origin, valid-jump scanner, PaddingCorrect, Osaka/G45.03 and resource/world/transaction/trace obligations remain open. No reserved G45.03 work is taken over. Immutable source/dependency hashes and precise interface references are in checkpoint5's P10 receipt.

Checkpoint5 committed handoff: parent `9c8ce1ba39930fbed67065c8096822930ee559eb`; focused75-job import closure plus18 scoped signatures/axiom queries PASS4.99s, peak aggregate824232KiB, oneLean, cgroup529162240bytes, noOOM/swap. Exact18 axiom audit and8/8 optimized-Python controls PASS; checkpoint layer/orphan/trust/diff PASS. Raw docs FAIL1; complete86-finding published/private multiset equality PASS separately; frozen no-new FAIL remains. Independent source and guard finder/skeptic reviews ACCEPT; requested extent wording correction applied. Exact theorem signatures/premises, source/dependency hashes, raw attempts, full-failure boundaries and every-item queue are exported under checkpoint5. Goal and all broader obligations remain unchanged.


## Checkpoint6: memory alias conversion and local deletion (G18.05 partial)

Fresh origin/master `63d3f9232416629146ab2f0a40d756dc9be43845` was fetched and inspected before this leaf. The relevant Source evaluator/machine/state are unchanged; these new consumers duplicate no published implementation. Source/MemoryLocalDelete proves the actual same-type conversion identity at every existing budget and TOTAL actual local array/bytes deletion: budgets0/1 time out with original state; the sufficient branch allocates a fresh empty Source object and updates only the selected local. The theorem does not assume sufficient fuel, a desired execution or preservation/simulation certificate. No Source implementation, semantics, static checker, profile, observation, fuel or proof budget changed.

The inhabited client actually copies calldata bool1/0 into object2, obtains an alias through real identity conversion atbudget0, creates typed branch-local extensions through existing EM.sub, deletes one local and reads false through the other alias. Success installs empty object3, preserves both old caller objects0/1 and the old copied object2, and retains full caller state with only the actual heap growth; the branch-local extensions drop from the outer context while the explicit internal result records their final values. Exhausted deletion retains the completed copy but allocates no empty object. Wrong rollback, alias panic and excess allocation are refuted; byte-local deletion is also inhabited. Existing typed RExpr.delete controls expose actual evaluator layering: budget3 invokes primitive deletion2 successfully; budget2 invokes primitive1 and times out. These are new exact clients of unchanged budgets, not changed old fixture limits. Source fresh identities/branchlocals are internal proof observations, not new admitted external observations or physical EVM allocation claims.

The first per-file check passed88.11s; generic module cache build passed96.32s under existing180s/12GiB/no-swap limits. A warned local proof optimization was attempted after reading history, failed to close compiled match cases, and was archived with its real14.78s exit1; the prior valid exact proof was restored and reused from cache. No theorem/premise weakened, no limit raised and no failed receipt overwritten. Final touched76-job closure passed2.81s. Exact22 headline/control signatures/standard axioms and8 audit regressions are recorded in checkpoint6's handoff; prior audits remain unchanged. Independent proof and guard finder/skeptic reviews inspect the actual statements/controls/ownership. Per-file MCP unavailable; bounded CLI fallback and writer lease remain in force.

P10 frozenV1 is now genuinely on published master (20d28dfb integration, inspected63d3f923); current Source proofs still contain no P10 execution premise to replace and do not import Bridge into core. P1 frozenV1 `f4fa6f12d54e5cfda235f9783fe6b9d19330d178` was checksum/bundle verified and fetched only to its exact private peer ref. Its signatures and exact blob/hash are retained in the checkpoint6 receipt; Pending* required fields have NO instance/proof/axiom and stay unproved. No local combined P1/P10 kernel validation or runtime-frame implementation is claimed. P1 running-prefix/divergence/recDepth, G38 payload/panic, G39 world/transient and separate P2 static-world obligations remain open. Source/compiler Site origin, valid-jump scanner, PaddingCorrect/Osaka and resource/world/trace closure also remain open. Reserved owners and optional-vendor hold stay intact.

G18.04 further aggregate shapes/lowering and G18.05 recursive/location/copy/delete policy remain ready/open; this checkpoint is Source kernel composition only, not completed general aggregate lowering or EVM/source/world correspondence. Every original Work/Backfill obligation and reassignment remains in checkpoint6 QUEUE. H12 end-of-lane checks are checkpoint-only; unchanged prior full180s timeout and pending root/TestSuite/SolKey are not relabelled passed or rerun for activity. Raw docs failure and frozen no-new failure remain distinct from corrected published/private multiset equality; previous metadata retraction/seals are preserved.

Checkpoint6 committed handoff: parent `329d8dc6641af76183d2cdd720f28cf3a84232f8`; final touched76-job closure and22 scoped signatures/axioms PASS3.32s, peak aggregate772328KiB, oneLean, cgroup479424512bytes, noOOM/swap. Cold generic proof build96.32s stays explicit, with the failed optimization14.78s/rawsource and exact restoration archived. Exact22 audit and8/8 controls PASS; checkpoint layer/orphan/trust/diff PASS. Raw docs FAIL1, complete86-finding equality to published helper basefebf/private07c9 PASS separately; frozen no-new FAIL retained. Independent source/guard finder/skeptic ACCEPT, no remaining findings. P10 published diff is documentation plus api def→theorem at the unchanged API type; P1 Pending signatures remain unproved/ref-only. Exact committed head, theorem premises, source/dependency hashes, all raw outcomes, queue and immutable artifacts are in checkpoint6's final handoff; goal remains incomplete.


## Checkpoint7: typed bool-array value/frame import (G18.04/.05 partial)

Fresh origin/master `23d8677d` was fetched/inspected before this leaf. Relevant Source evaluator and aggregate modules are unchanged; neither published master nor inspected V07 early Scalar consumer supplies this bool-array adapter (V07's scalar producer there concerns integers). No arithmetic/selector/Source/representation owner code is duplicated or edited. New Backend/Aggregates modules consume the existing typed Source bool values and intrinsic RefTy.array(.prim.bool), MObj/State.allocPush/Heap.readAddr representations. They introduce no AST, source/EVM evaluator, type/profile change or desired simulation premise.

Actual ABI entry stride32 with a genuine four-byte selector is transported through cdNested_region; real requested length and byte extent are derived. Actual successful ordered decodeWord validation derives target logical array capacity and exact uint index (<2^64<2^256, no truncation). The adapter allocates a real intrinsic bool array with the source values in order, binds that actual reference as the new top local, preserves old typed locals and protected heap objects, and relates independent actual Source-copy and target heaps/identities. Joint indexed reads use actual Source cdToMem/readLoc and intrinsic Heap.readAddr. General Source/caller-frame/readonly/world representation is still OPEN, never supplied as an assumed desired simulation or silently discharged.

lowerCopy is total only OVER A SUCCESSFUL ABI-ENTRY PROOF and fixed matching frame/data/selector. It computes the existing ordered Source validator and returns a typed target value/frame or the exact Source.Halt diagnostic. This error channel is NOT a machine/TRes halt. phase_error_iff_copy_error reflects exactly the actual Source copy's error/full original caller state in this phase, not G43 source-success/machine-revert, physical memory exhaustion or fetched-EVM agreement. Truncated-input controls establish cdTail entry rejection; an unconditional raw-byte importer and whole source expression/compiler lowering remain ready/open work. No wrapper is labelled new instruction selection.

Inhabited ABI data has two real bool words1/0; source heap contains two old bytes objects/aliasedlocals, target caller has a protected bytes object with distinct words170/187 and aliasedlocals. Source freshid2 and target freshid1 remain distinct. Top-local binding, ordered bool contents, actual second-index reads and protected old object/local observations pass. Dirty third bool2 has a successful entry but fails ordered validation with exact empty revert/full original Source state and phase diagnostic; wrong target success/refusal/order are refuted. Empty entry/array and truncated real ABI controls pass. This is kernel model value/frame evidence; no new external compiler/EVM observations or parent closure.

Independent proof finder requested an explicit top-local binding law/control; target_new_local/new_parameter fix it. Skeptic requested the successful-entry precondition remain explicit; it is documented and not weakened. Final independent source/guard reviews and exact34 scoped signatures/axioms,8 audit regressions, touched76-job closure and checkpoint gates are recorded in checkpoint7's handoff. Initial dependent-match proof failures are retained raw, then fixed by actual validation case analysis. Per-file Lean MCP unavailable; bounded CLI fallback uses fixed oneLean-j1/LEAN_NUM_THREADS1/12GiB/no-swap/180s/writer lease and unchanged proof/fuel/node/test limits. Prior audits/caches/seals remain intact.

P1 interface is now genuinely on published master23d8677d, but its Pending* structures remain unproved (no producer instance follows from publication). P10 and V15 return-copy bounds are also published. Current bool-array code has no P1/P10 machine premise to replace and imports no Bridge. Actual runtime-frame/source/compiler origin, running-prefix/divergence/recDepth, payload/panic/world/transient, jump scanner/PaddingCorrect/Osaka/resource/transaction/trace closure remain open; local combined producer validation is not claimed. The exact P1 published-vs-frozen documentation delta is retained read-only in checkpoint7's evidence. Reserved ownership and optional-vendor hold remain unchanged.

All original/helper items remain enumerated in QUEUE. G18.04 further aggregate shapes/general lowering, G18.05 recursive/location/copy/delete lowering and unconditional raw-entry import remain ready/open. Under H12, end-of-lane checks are checkpoint-only; unchanged failed heavy full180s gates are not repeated for activity or called green. Full/root/TestSuite/SolKey/strict/cumulative final confirmation stays pending. Raw docs and frozen no-new failures stay distinct from complete no-new findings against exact published helperbasefebf/private07c9. No goal administration or completion.

P1 V1 hold (coordinator warning2026-11-02): RealizableEntry has a confirmed vacuity hole and may be satisfied without realizing a real entry. No current bool-array or other aggregate proof uses it or imports InterfaceV1. Any future realization-dependent step must await InterfaceV2 and remain explicitly open; other V1 signatures are unaffected. Publication does not cure this defect, and no V1 realization proof/instance is counted as evidence.

Checkpoint7 committed handoff: parent `49f7c530052b066931a7f97766cfb41a364d7187`; final touched76-job closure plus34 scoped axiom/signature queries PASS3.28s, peak aggregate770000KiB, oneLean, cgroup448479232bytes, noOOM/swap. Exact34 audit and8/8 optimized-Python controls PASS; checkpoint layer/orphan/trust/diff PASS. Raw docs FAIL1; complete86-finding equality to exact published helperbasefebf/private07c9 PASS separately, frozen no-new FAIL retained. Independent finder/skeptic source+guard reviews ACCEPT after binding-gap fix and explicit successful-entry boundary. Exact committedhead/signatures/premises/raw outcomes/P1hold/queue/sourcehashes and immutable exports are in checkpoint7's final handoff; no parent/goal closure.


## Checkpoint8: actual decoder/conversion and total entry phase (G18.04/.05 partial)

Fresh origin/master `19bf3ba6` was fetched/inspected before this leaf; relevant Source evaluator/aggregate modules unchanged and no duplicate entry consumer published. SourceCopy is an actual client of existing Source.decodeArg for calldata bool arrays and Source.convRV into memory, not another evaluator or AST. sourceCopy_run proves its complete actual entry-error/copy outcomes. lowerEntry now EXECUTES the real cdTail entry check before word validation; unlike checkpoint7 lowerCopy, it takes no successful-entry premise. Frame.cd=selector++data and four-byte selector consistency remain explicit.

Entry_error_iff_source_error reflects exact Source.Halt and FULL original caller state in both directions for the actual decoder/conversion client. Successful_import derives actual Source memory reference/heap/state and the intrinsic typed value/frame/independent-heaps relation, using checkpoint7's actual capacity calculation. This is still a Source diagnostic/value adapter, not machine/TRes/G43 asymmetry, whole-function dispatch/signature/minimum-whole-head/argument-index production, readonly/general-frame/world, compiler emission or physical EVM/resource agreement. No admission predicate, semantics, profile, observation or budget changed.

Inhabited controls reuse real valid/dirty/truncated/empty ABI data and populated independent Source/target callers. Valid source decoder+conversion returns memoryref2 and joint Source/intrinsic second readfalse, with related targetref1. Dirty third bool returns empty revert/original Source state. Truncated input is now checked by the TOTAL phase as well as actual Source decoder, without constructing an entry-success proof; no allocation is observed. Empty entry allocates a related empty object. Wrong success/refusal/allocation are refuted. Initial state-pair/head-width/name ambiguity and recursion-limit failures remain raw; fixed using the published head-width fact and explicit names, NEVER increased maxRecDepth or any other limit. Touched78-job closure passes; exact19 signatures/axioms and8 audit regressions are tracked in checkpoint8's handoff.

P1 V2 exact peer `c3765ded747e55983ea8280ca0b6f0f945672dc5` was checksum/source/bundle verified and fetched to its private ref, not merged into core. V2 replaces the applicable V1 Pending structures; the active realization quarantine is LIFTED FOR V2. Use V2 for future pending producer premises, without restating or weakening them. Existing V1 Emission/Entry/Returned/ReturnClaim/BareRevertClaim/RecursiveEmission/recursiveSource/coherence/PendingRestoration remain their exact declarations. Current aggregate code has no P1 premises to replace and derives nothing from V1 RealizableEntry. Prior warnings remain historical sealed evidence, not a hold against V2.

V2 still supplies NO Pending instance/proof. Actual SuccessfulEntry couples Entry and successful statement.run for the same caller; RevertingEntry couples exact bare revert. Ordinary witnesses do not establish all-caller/profile coverage; fixed-thunk required_successful_entry is per depth; recursive existence is at one positive index, need not recDepth and does not imply all-index feasibility. Non-revert structures' bare-revert duty may remain vacuous; the failure-specialized producer requires its own actual reverting entry. Frozen declarations/full signatures/blob hashes are retained verbatim in the V2 receipt. No local combined P1 kernel validation, general runtime-frame realization or simulation is claimed. Publication integration/rebase remains for the next actual integration after coordinator announces the master SHA; no competing goal/continuation.

All original Work/Backfill/helper items remain partial/open/reassigned as recorded in QUEUE. Ready aggregate/conversion/generallowering work remains; whole-lane dependencies do not block this leaf. H12 end-of-lane checks remain checkpoint-only, prior unchanged full180s failure and root/TestSuite/SolKey/strict/cumulative gates remain unresolved. Raw docs/frozen no-new failures remain separate from complete equality to exact published helperbasefebf/private07c9. No Source/Static/reserved implementation edits, Bridge/core import, budget increase or goal administration.

Checkpoint8 committed handoff: parent `114d1305efee7a741c6c752d8d5c6ffc65bd13a9`; final touched78-job closure+19 scoped signatures/axioms PASS3.01s, peak aggregate770376KiB, oneLean, cgroup449691648bytes, noOOM/swap. Exact19 audit and8/8 controls PASS; checkpoint layer/orphan/trust/diff PASS. Raw docs FAIL1; complete86-finding equality to exact published helperbasefebf/private07c9 PASS separately; frozen no-new FAIL retained. Independent source/guard finder+skeptic ACCEPT with whole-dispatch/index/minimum-head limits explicit. V2 checksum/source/bundle/ref verification PASS; Pending instances unproved, no current aggregate P1 premises. Incorrect control-source gitpath lookup128 repaired to actual tests/runtime-frame path and retained in the receipt. Exact committedhead/typedpremises/raw outcomes/V2limits/everyitemqueue/immutable source hashes are in checkpoint8's handoff; goal unchanged/incomplete.


## Checkpoint9: actual typed conversion and scoped caller transport (G18.04/.05 partial)

Fresh origin/master `91d7b7e6` was fetched/inspected before this leaf: no duplicate aggregate expression consumer and relevant Source evaluator unchanged. New modules use actual existing RExpr.conv(.local here), with the real admitted Conv proof for calldata bool-array to memory. No AST, evaluator or Source semantics is replaced. Eval_expr_run derives actual evaluation at n+2 Source budget as the existing memory copy; eval_expr_zero/one retain exact exhaustion. ScopedCopy actually decodes the argument, captures caller locals, uses EM.sub to add one typed calldata local, evaluates that expression and drops only the extension. ScopedCopy_run derives complete success/error transport to checkpoint8's actual decoder/converter client and preserves the actual grown heap/caller state, not an assumed frame oracle.

Low-budget law covers ALL0/1 cases explicitly: entry rejection precedes expression evaluation; a successful entry then times out without element validation or allocation. Dirty bool data atbudget0 times out, while budget2 reaches exact empty revert. Truncated entry atbudget0 retains its decoder revert, not timeout. Value/frame lowerEntry can succeed while expressionbudget0 times out; an inhabited negative control exposes this distinction. Scoped_error_iff therefore applies only at the real two-layer minimum n+2 and concerns Source.Halt, not EVM gas/TRes/G43 or machine-resource correspondence. No existing budget/fuel/recursion/node/test/time limit changed or exhausted case silently dropped.

Controls preserve aliased caller locals and both old objects, prove actual scoped resultref2/heap relation/actual second-readfalse with intrinsic targetref1, and cover empty input, dirty data, truncated entry and timeout-vs-revert. Source expression uses actual Glob/typed context; whole-function dispatch/signature/minimum-head/index production, general Source/frame/readonly/world/constructor/compiler lowering, emitted/fetched bytes and physical resources remain OPEN. These are kernel model Source-expression/value-frame consumers, with no new external compiler/EVM observations or profile changes.

Initial proof normalization and recursion-limit failures remain raw; repaired using normalized existing run equations/direct actual read, never increased limits. One exec transport disconnected during an initial read; provider reported same environment connected/running, retry verified unchangedf7029c40 before any edit. No VM/goal reset or recreation. Exact22 signatures/standard-axiom queries,8 audit regressions, touched80-job closure and independent source/guard reviews are recorded in checkpoint9's handoff. Per-file MCP unavailable; bounded CLI fallback, fixed12GiB/no-swap/180s/j1/LEAN_NUM_THREADS1/4GiBhostreserve and writer lease remain.

P1 V2 is now on published masterd4e72c5d. SuccessfulEntry may be used, but required_bare_revert can remain vacuous in the three non-revert producers; one-caller/index admission is not all-caller coverage. Reverting-run/all-caller claims must retain exact typed premises pending V3, never inferred from those fields. Current aggregate code has NO P1/P10 import/premise or realization/revert/coverage claim, so no vacuous field is consumed. V2 readiness does not supply Pending producer instances. Earlier V1 warning/V2 relay receipts remain historical immutable evidence; optional-vendor hold/reserved ownership unchanged.

All original/helper Work/Backfill remain partial/open/reassigned in QUEUE. H12 end-of-lane checks occur only at checkpoints; unchanged failed heavy full180s gate is not repeated for activity and root/TestSuite/SolKey/strict/cumulative final confirmation remains pending. Raw docs/frozen no-new failures remain separate from complete equality to exact helperbasefebf/private07c9; prior corrections/seals preserved. No goal administration/completion or parent closure.

Checkpoint9 committed handoff: parent `f7029c40ec2f379e7d1c5a9c14305719d002aa62`; final touched80-job closure+22 scoped signatures/axioms rawPASS4.03s, peak aggregate775472KiB, oneLean, cgroup449724416bytes, noOOM/swap. SameVMreattach lostsession81968 but completedlog/fullqueries survived, nojob remained andunchangedhead/files wereverified; adoptedthisreceiptwithout rerun. Exact22 audit and8/8 controls PASS; checkpoint layer/orphan/trust/diff PASS. Raw docs FAIL1; complete86-finding equality to helperbasefebf/private07c9 PASS separately; frozen no-new FAIL retained. Independent source/guard finder+skeptic ACCEPT. Sourcebudget0/1/n+2, actualentry→expression order, P1V2bare-revert/allcaller caveats andno machine/gas claim are explicit. Exact committedhead/typedpremises/failedattempts/sourcehashes/queue/immutable exports are in checkpoint9's handoff; goal unchanged/incomplete.


## H14 incremental deletion producer (not completed checkpoint10)

Fresh master fcd5ba31b93d5b1cbe9bd3f36732dc7e4048eb00 was inspected;
no equivalent aggregate deletion consumer exists. BoolArrayDelete proves
actual default_heap allocation and run_var local rebinding over intrinsic
State/Idx/HRef and existing TRun.deleteMem, without a simulation premise.
Focused CLI check passes; default_heap uses propext and run_var uses only
propext, Classical.choice, Quot.sound. Per-file MCP/lean_multi_attempt and
coord-tools are unavailable. CLI automation trials are retained, including
failed dependent decide/rfl/omega attempts and unavailable sol_prove/sol_chain
(the core does not import tactic frontends). Expanded simp-only reduction
succeeds; no budget or representation change. The initial admission refusal75
launched no process; H1 task-cache advice restored the unchanged guard.

H14 cascade statements in TERRA-TODO.md defer routine populated alias,
contents/local/heap preservation controls. Joint Source deletion transport
and its timeout distinction remain Sol soundness work. This is NOT a complete
checkpoint or G18.05 result. Read-only finder and skeptic find no source flaw;
both require the pending inhabited controls before checkpoint closure.
Solidity.lean is untouched; new-module registration waits for the H14 generator.
No full gate rerun: previous full timeout124, raw docs1, frozen no-new1 and
all original missing compiler/world/frame/fetched execution obligations remain.


### H14 deletion soundness increment

`BoolArrayDelete.delete_related` derives the actual Source deletion postheap
relation at budget n+2 to the independently fresh intrinsic empty allocation.
There is no assumed initial relation: newly allocated defaults have equal
contents regardless of prior contents, while their IDs remain independent.
This does NOT establish caller/alias history preservation; populated controls,
low-budget Source cases and routine heap/local statements remain in TERRA-TODO.
Actual target deletion is the separately proved run_var equation, not EVM code.

Scratch automation emulates lean_multi_attempt as clarified by H14: six
examples try simp-only, decide, omega, rfl, sol_prove and sol_chain. Raw failed
attempts and the repaired proof are retained. The empty value witness and
empty-index extensionality supply the steps automation did not close; no
budget changed. Focused new-module/import closure passes (72 jobs,1.68s,
peak Lean/Lake829120KiB, one Lean, no OOM/swap). Scoped delete_related axioms
are exactly propext, Classical.choice, Quot.sound. Independent read-only
finder/skeptic review this delta; no Source/Frontend/Static/reserved changes.
Registration remains pending the H14 generator; Solidity.lean untouched.
This remains an incremental partial result, not completed checkpoint10.
Original full/docs failures and all outstanding queue obligations remain.


### H14 old-object deletion preservation increment

`BoolArrayDelete.delete_preserves_related` now consumes an actual prior
Related object and derives that its Source cell is distinct from the fresh
allocation using Source.Heap boundedness. It then preserves that same object's
contents through actual n+2 Source deletion and the actual intrinsic default
allocation/local-rebinding result. Target references are weakened by the real
heap extension; Source/target identities are independent. No freshness,
old-contents preservation or desired simulation premise is assumed.

Six scratch candidates were checked before the manual witness/freshness steps;
the failed exit1 is retained. The scoped signature/axiom check passes with
propext, Classical.choice, Quot.sound. Changed-module closure passes72jobs
in1.89s, peak aggregate832580KiB, oneLean, cgroup539639808bytes, noOOM/swap.
All original fixed budgets and writer lease remain. Masterfcd5ba31 is unchanged
and supplies no duplicate helper deletion consumer. The coordinator reported a
capacity interruption during review; source, raw logs and branch were verified
intact, with no surviving Lean/Lake job or competing continuation.

Old heap-content preservation is not caller-local alias binding preservation,
world/history correspondence or synchronized verdicts. Routine controls,
local/heap projections and a total-budget old-content corollary remain in
TERRA-TODO. Populated inhabited joint controls, registration generator and
checkpoint10 gates remain unfinished. No full/docs failed gate is rerun or
relabelled, no Source/Static/reserved implementation is changed, and the
original queue/goal remains incomplete.


### Private V07 integer-array consumer increment

All remaining deletion-local projection/control glue is delegated in
TERRA-TODO under H14; no completed checkpoint10 is claimed. Fresh master
88d68150b5ea0087dc9d50502088a6a34efcce48 was fetched/inspected and adds no
equivalent consumer. To continue independently ready G18.04/.05 work,
IntegerArrays consumes the exact sealed V07 Scalar checkpoint
5d45c086bce93a47140327112333019f923ebdd7 (blob
0ca8696879e8d121071a1bca38632e572dff7507, SHA256
2e0e760d63885f01e5c19c5a8dd8bb5903d78cf5ec96a052846003b8746e4b3d).
No foreign branch is merged or reserved producer edited. A narrow private
source-keyed stage reuses existing oleans by symlink, compiles that exact
producer source and audits its four scalar headline axioms before consumption.
Initial source-root/search-view failures1 are preserved, then repaired with
explicit root and cache symlinks, never a replacement implementation.

The new owned module adapts every actual Source.IntTy to V07.integerPrim and
integerValue, preserving its numeric observation. Actual ABI region and
ordered decodeWord validation derive object capacity, not an extra capacity
premise. copy_related proves actual Source cdToMem allocation and intrinsic
typed allocation carry the same ordered converted values, with independent
fresh identities. No integer arithmetic/width theorem, Source evaluator,
untyped AST or machine semantics is reimplemented. Source width remains in
Source values; target signed/unsigned carriers are the existing intrinsic
primitives, not a new arbitrary-width runtime representation.

Six scratch candidates were tried for each proof before manual steps. Final
private per-file/signature/three-axiom check passes1.90s, peakLean/Lake785328KiB,
oneworker,cgroup427839488bytes,noOOM/swap. Producer check passes2.51s with
standard axioms only; all three consumer theorems use standard3 axioms.
The success validation equation remains explicit. Total-error adapter,
inhabited signed/unsigned dirty-word/order/empty/populated-caller controls,
old/new-local and heap projections remain in TERRA-TODO. Finder requested the
new-local equation be listed; it is now included. This is provisional private
kernel evidence, NOT an integrated standard build or source/compiler/EVM proof.

No Solidity.lean hand edit: registration waits for H14 generator, toolkit still
absent. Standard combined validation is pending exact V07 incorporation;
original full124/docsraw1/frozenno-new1 and all queue obligations remain open.
No new external compiler/EVM tests or whole-lane completion claim.


### Integer-array total validation adapter increment

`IntegerArrays.lowerCopy` now executes the full actual ordered decodeWord
validator at every supported Source.IntTy, allocating only in its successful
branch with capacity derived from the actual entry/validation. The new
`error_iff_copy_error` proves BOTH directions of exact Source.Halt agreement
with actual Source.cdToMem, including the unchanged complete original state
on validation failure. The actual successful ABI-entry and frame/input
consistency equations remain explicit. This is not a machine revert/stipend/
resource/world relation and does not discharge G43.

Six scratch candidates and two failed dependent normalizations are retained.
Splitting the actual adapter match and projecting constructor equalities
closes the soundness proof, without assuming the desired result. Scoped
standard3 axioms/private per-file check passes2.04s, peak797472KiB, oneLean,
cgroup435388416bytes, noOOM/swap. Exact private V07 producer stays unchanged;
standard combined checking remains pending producer incorporation. Finder
requested precise wording: failure precedes allocation, so the result says
unchanged original state, not an executed rollback operation; corrected.

H14 routine successful/error match equations are now recorded for Terra.
Actual Source argument-header/decode/conversion composition without an
entry-success premise remains Sol work, as do general source/frame admission
and physical realization. Inhabited width/order/dirty/empty/populated-alias
controls, generated registration and checkpoint closure remain unfinished.
Master88d68150 was fetched/inspected unchanged; no reserved edits, goal changes,
full failed-gate repetition, expected-verdict or budget changes occurred.


### Integer argument header/decode/conversion increment

IntegerArrays.sourceCopy now calls actual typed Source.decodeArg for calldata
arrays of any Source.IntTy, then the existing convRV at its existing budget0.
sourceCopy_run derives the real header-error versus conversion ordering.
lowerEntry executes that actual cdTail before lowerCopy; the new
entry_error_iff_source_error removes the successful-entry premise and reflects
exact Source.Halt/full unchanged original state in BOTH directions. Actual
selector length4 and frame.cd=selector++data remain explicit. The index is a
provided Source argument index; no whole-dispatch/signature/minimum-head/index
producer or general Source/frame/compiler admission is inferred.

This uses actual Source budget behavior, not EVM gas or expression fuel.
Conversion/allocation and ordered validation remain actual native operations;
no new AST, Source evaluator, copy implementation, desired simulation premise
or target semantics is introduced. Failure is before allocation, not an
executed rollback journal. General payment/world/history and fetched/resource
correspondence are unchanged open obligations. Private V07 Scalar5d45c086
binding/validation remains the exact prior input, not a published prerequisite.

Scratch six-candidate trials for run law and full error law fail1 and are
preserved; typed decoder run/actual header splitting supply the hard steps.
Final private per-file/scoped two-axiom check passes1.99s, peak812716KiB,
oneLean,cgroup446328832bytes,noOOM/swap; both headline axioms standard3.
Same saved VM/head verified after startup, no surviving job or goal operation;
master88d68150 fetched/inspected unchanged. No Source/Static/reserved changes.

Routine lowerEntry match equations and successful-import composition now
join H14 TERRA-TODO, with inhabited signed/unsigned, dirty/order/empty/caller
controls and local/heap projections still pending. Standard combined build,
generated registrations and checkpoint closure remain pending; no unchanged
failed full/docs gate repeated or relabelled. Original queue remains partial.


### Generic integer typed expression and caller-scope increment

Within IntegerArrays.Expression, conversion_allowed derives the ACTUAL Source
implicit conversion for calldata→memory integer arrays at every Source.IntTy.
The first naive rfl expression constructor failed; the generic implicit
judgment needs reflexive element equality. Six admission trials included a
200000-heartbeat whnf failure, retained raw. Explicitly exposing the existing
decidable self-equality and simplifying boolean conjunction proves the judgment
without a new premise, native shortcut or changed budget. No Source/checker
representation or global instance is altered. Actual RExpr.conv carries that
proof; eval_expr_run proves real evalE at n+2 equals native cdToMem.

scopedCopy executes actual argument decode, extends the real typed locals,
uses actual evalE through EM.sub, then drops only the added local extension.
scopedCopy_run proves the full reached state/result equals native sourceCopy
at n+2 on header error, word-validation error and success. Source budget is
explicit, not gas or physical runtime-frame availability; exhausted 0/1 cases
are unproved routine TODO obligations, not excluded from the admitted profile.
No whole compiler/dispatcher/minimum-head/index/general frame admission follows.

Private V07 exact source binding is unchanged. Six-candidate run/scope trials
and their failures remain raw. One final doc-comment syntax error is fixed
(module comment before namespace); the failed exit1 is retained. Final private
per-file + three headline axiom queries passes3.88s, peak848608KiB, oneLean,
cgroup477888512bytes, noOOM/swap. conversion_allowed uses only propext;
eval_expr_run/scopedCopy_run use standard3 axioms. No proof/test/fuel/node/time
limit increase. Same saved head verified after readiness race; no goal changes.
Master147eeb0c adds proof tooling, not a duplicate aggregate consumer.

H14 low-budget equations, exact scoped error iff, success composition and
inhabited signed/unsigned/dirty/truncated/empty/populated-alias controls remain
in TERRA-TODO. Generated registration, standard combined checking and original
checkpoint10 closure remain pending. Original failed full/docs gates and all
original Work/Backfill obligations remain unchanged, no lane closure claimed.


### Generic integer actual copy/index observations

copy_read_related consumes published actual Source cdToMem/readLoc execution
and actual intrinsic Heap.readAddr on the independently freshly allocated
array. Real entry and ordered validation derive values.length, capacity and
exact uint index representability; no desired read or integer-width oracle is
assumed. The returned typed value and its actual numeric observation agree
with the Source positional value through V07.value_related at every IntTy.
The native Source final state is the actual complete copied state.

copy_first_out consumes the first invalid index length. Its uint conversion
is still derived from real ABI extent, including extent0. Actual Source
returns the exact published panicData.index bytes on the grown copied state;
heap.next is derived to be original+1. Actual intrinsic readAddr returns none.
These are distinct native/logical carriers, not a machine-panic, gas or byte
execution relation. Original-state validation failure remains distinguished
from successful copy followed by read failure; no rollback mechanism is added.

Six scratch candidates for each goal fail1 and remain raw. A scratch capacity
witness application syntax error is fixed without changing statements or
budgets. Final private per-file/two-scoped-axiom/signature check passes4.59s,
peak843700KiB,oneLean,cgroup476295168bytes,noOOM/swap; both axioms standard3.
Independent read-only finder and skeptic find no issue. No Source, primitive
memory, scalar producer or reserved implementation is reimplemented/edited;
actual published laws and exact private V07 binding are consumed read-only.

H14 routine target-contents extraction and inhabited signed/unsigned/order/
wrong-handle/dirty/empty/first-bad-index controls remain TERRA-TODO. No control
or whole-profile completion is asserted. Generated registration, combined
validation, low-budget/scoped success glue, original checkpoint10 and all
original Work/Backfill final obligations remain open. Master147eeb0c was
fetched/inspected unchanged; no unchanged failed full/docs gates repeated.


### Selected calldata expression versus validated snapshot boundary

CalldataRead.expr is the actual typed indexArray of the calldata-array local
and a uint256 index local. eval_read_run derives native evaluation from the
published generic Source index law and selected decodeWord, preserving the
complete original state. imported_read derives the Source uint256 bounds from
actual ABI extent and compares this real selected read to the imported
intrinsic array's typed/numeric read. Its whole-array validation premise stays
explicit: a successful selected read does NOT supply that premise.

selected_success_import_error makes the semantic boundary visible: actual
selected-word decoder success and actual whole traversal error derive direct
Source-expression success and eager lowerEntry failure. This is not a machine
counterexample, G43 fix or approved profile exclusion. General calldata-read
lowering must preserve lazy selected-element validation; eager import cannot
be promoted to that compiler by assuming away dirty unselected words. No
human semantic choice is requested and no admitted profile is narrowed.

The inhabited uint8 data [255,256] witness remains a concrete H14 TODO; word256
must be encoded as30zero bytes++[1,0], since existing word helper truncates to
one UInt8. Source before the direct read keeps old heap/caller, distinct from
copy-then-bad-read's grown heap. All numeric/signed/order and native-versus-EVM
boundaries remain explicit, with no new Source/EVM semantics or reserved edits.

Six-candidate scratch trials and failed dependent readLoc/header normalizations
remain raw. Published equation rewriting closes the readLoc dependency without
budget changes. Final private per-file/three-axiom/signature check passes4.24s,
peak857660KiB,oneLean,cgroup488550400bytes,noOOM/swap; all3 standard axioms.
Separate read-only finder and skeptic find no issue, with inhabited controls
still pending. Masterd886729d fetched/inspected; it adds proof-cost tooling,
not a duplicate array consumer. Exact private V07 source remains unchanged.

Generated registration, standard combined validation, H14 routines/controls,
low-budget laws and all original Work/Backfill closure remain unfinished.
Original full124/docsraw1/frozenno-new1 preserved without unchanged reruns;
no goal, pin, profile, proof/fuel/test/time/resource budget or verdict changes.


## Published integration and inhabited eager-validation boundary

Requested H14-F rebase onto8eec153a5670d3153114596f1ccab2b1acbb6afc is complete
on the SAME helper branch. Old eac8dc8e/all seals are preserved under the
pre-integration ref and archives. P5 exact61db3cac remains an ancestor.
Only registration/docs conflicts occurred; published root/order were preserved
and owned imports regenerated with coord-tools/register.sh. Aggregate code,
TERRA and tests were byte-identical immediately after rebase. Separate finder
and skeptic accepted preservation/ownership. Source/Frontend/reserved producer
implementations were not changed to make the rebase or proofs pass.

V07 Scalar is now published, exact blob0ca8696879e8d121071a1bca38632e572dff7507.
Active private lookup injection is removed. Focused normal-source build of
IntegerArrays passes72jobs134.92s within180s, oneLean,peak910936KiB, noOOM/swap.
P1 V3/P10 published components replace relay-source use; no P1/P10 premise
occurs in these array consumers. P1-PROFILE remains open (approved:=admitted),
recursive witness coverage/absence of a recursive V3 instance are not inferred
away. Original Source/frame/world/fetched-byte obligations remain open.

IntegerReadBoundaryWitness constructs actual ABI head32/length2 and words255,
256, with correct full second-word encoding30zeros++[1,0]. The Source caller
contains two old heap byte objects and two aliases to address0. Real geometry,
selected decode success, traversal error and inhabited_boundary are proved;
the Source typed read at budget2 returns uint8 255 and the complete BEFORE
state, while actual eager lowerEntry returns Source.revert[]. No desired-run,
decoder or representation oracle is a premise of this inhabited theorem.
This closes the specific pending [255,256] control and substantiates the lazy/
eager mismatch. It does NOT claim machine revert, G43, an exclusion or a general
calldata compiler. No profile, expected verdict or semantic definition changed.

Shared try-tactics/gate tools run inside the original guarded Docker runtime
(j1/LEAN_NUM_THREADS1,12GiB,noSwap,180s,local writer lease). MCP package is absent;
CLI toolkit fallback used, daemon remains stopped. Initial admission75 failures
launched no Lean; H1 task-cache advice restored the unchanged guard without
removing data/seals. Container Git trust is scoped only to this checkout.
Toolkit-created root-owned logs were made readable without content changes.
Literal length decide hit the unchanged recursion limit; first successful rfl
length proof replaced it. All raw refusals/failed trials are retained.

Final focused build/per-file/axiom checks pass: witness-final4.13s,peak759268KiB,
oneLean,cgroup513335296bytes,noOOM/swap. Geometry has NO axioms; three remaining
headline witnesses use only standard3. Root imports for the three owned
modules are generated. Other H14 controls, low-budget/projection/success glue
and root/import/full/strict/trust/docs final closure remain outstanding. The
older full124/docs failures remain raw, not renamed green. No goal reset,
completion, model/pin/budget change, push, merge-master or PR occurred.
