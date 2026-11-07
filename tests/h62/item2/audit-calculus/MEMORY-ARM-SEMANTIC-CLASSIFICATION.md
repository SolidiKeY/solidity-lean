# Typed memory-arm soundness roles

Guarded regression: memory soundness must retain source/receiver/index order, exact typed scope drops and every field/mapFree/default/new-array/step guard. NoPanic and simulation must not become normal-return or full-halt-equality claims.

Complete frozen-selected Solidity/Calculus/SoundMem.lean and all 16 named signatures match frozen/current master bytes. Prior 901 rows and owners are unchanged. All 5283 candidates remain accounted: 917 reviewed, 4366 pending; 3746 owners confirmed and 1537 unresolved. Zero fresh joint witnesses. Exact signatures/section history are bound for every row; supporting definitions/generated declarations receive no extra credit.

MSrc.mvalT_noPanic excludes panic only, not source failure. copyStToMG_push retains the actual map-free source, typed pushed value/environment and exact Grew.lift identity. Other interfaces conclude conditional Premise.Runs under the supplied modality/state, not normal execution or formula truth.

Rebind, reference write, assignment and delete dispatcher theorems require their EXACT computed-step equations; arbitrary premises cannot replace q. Alias/copy/new-array and field/index branches retain variable/complex receivers, primitive/reference sources and simple/other index cases. Comments naming NonSimple describe usage, not added theorem hypotheses. Fresh k names are unchanged, not runtime gas or checking budgets.

Primitive variable-index unfolding captures source then index and drops two locals. Primitive complex-receiver unfolding captures source, receiver and index, dropping three. Reference complex-receiver unfolding captures receiver/index then reads src.up.up, dropping two. Receiver/index captures that change failure priority use existing nonpanic/revert-only simulation facts internally; no caller success or panic-exclusion premise is invented.

Existing TRes.Sim equates successful states, relates errors by panic equivalence and first-to-second exhaustion, and rejects mixed success/error. It is not equality of every halt label. Field receivers retain mapFree and field-type proofs; deletion also retains defaultOkS. New-array capture requires SIMPLE uint length and newArrOk, retains the actual grown heap, fills either storage or memory destination, then drops exactly one local. Both destination writes may fail. No physical memory/allocator/copy correctness, source compiler totality or gas/fork/world adequacy follows.

Exact source/signatures and complete result/capture/dispatch/destination rosters remain off Git under /workspace/h62-successor-evidence/memory-arm-roles-v77 and /workspace/h62-successor-bulk/memory-arm-roles-v77 with path/size/hash manifests. Fresh mastera8f684928 inspected/already adopted. No producer source, statement/definition, budget, axiom, exclusion or toolchain changes; no new kernel/runtime/cache/performance acceptance.

For coordinator-side review, census claims remain bound by hash only until referenced bytes are pulled and verified. Off-Git data/evidence remain on this VM under H44; local checks/reviews do not establish coordinator intake, semantic acceptance or proof validation. Delivery is coordinator-pending.

Whole assignment and four audit checkpoints remain incomplete. H28 actualCallerFields/extractionActuallyChanges/replay pause and Raw/Context waits persist; the missing SelectedHeapBoundaryWitness documentation request remains with vy3-compilation. No duplicate ping, gate pass or STOP release inferred. Historical unavailable-byte gaps remain explicit.

Accounting and101controls PASS; documentation path gate PASS exit0. Complete acceptance remains FAIL exit1:4366 classifications pending. No proof/runtime acceptance.
