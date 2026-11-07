# Creation layout and execution-slice classifications

Guarded regression: wrapper-entry local execution and byte/source-map bounds must not imply arbitrary constructor execution, frontend provenance or full-EVM/compiler adequacy. Keep embedded arithmetic certificates and explicit continuation/bounds premises.

Complete frozen-selected Solidity/Backend/Creation/Execution.lean, Solidity/Backend/Creation/ExecutionChecks.lean, Solidity/Backend/Creation/Placement.lean, Solidity/Backend/Creation/PlacementChecks.lean, Solidity/Backend/Creation/Regions.lean and Solidity/Backend/Creation/Provenance.lean; all26 named signatures match frozen/adopted master. Prior1409 rows/owner map unchanged;1435 reviewed/3848 pending of5283;3746 confirmed owners/1537 unresolved. Zero fresh joint witnesses; unresolved owners unguessed and anonymous/generated declarations separate.

Exec means existence of successful finite fuel for the local raw-byte runner. Code bytes used by CODECOPY are distinct from instruction stream bytes. PUSH reduces to word modulus; reads/CODECOPY zero-pad, memory tracks bytes rather than gas/rounded allocation. Unsupported instructions, truncated PUSH, underflow and fuel exhaustion have no successful derivation. This is not full EVM/gas/account/CREATE semantics or a1024-stack-cap model.

fetch_encode decodes actual intrinsic instruction bytes with arbitrary tail. Extra fuel preserves an already successful run; determinism requires two actual Exec proofs. Push/copy prefix theorems require exact continuation execution, while RETURN/REVERT construct finite local halts and ignore suffix. Read bounds, whole-list identity and empty-memory write are byte-model laws.

wrapper_exec and placed_exec start at the wrapper stream with empty stack/memory and arbitrary code source. Placement supplies runtime-length and offset-alignment certificates with typed Immediate limits; installs returns runtime only at that entry. The pre prefix appears in code layout but is not executed as a constructor. Artifact installation similarly supplies local wrapper execution, not source compilation/constructor/world adequacy.

Bounded patchAt length/get/frame/commutation retain actual interval limits and disjointness. Source-map Section covers wrapper/runtime/arguments; exact slice and bounds hold for supplied Artifact records. Provenance carries generated-byte and independently bounded supplied source ranges; global bounds and byte identity do not prove source anchors, frontend mapping fidelity or equal source/generated span widths.

Existing boundary placements255/257, runtime lengths31/32/33/255/256 and negative known-byte examples were read without fresh execution or named-row credit. wrongSource_exec genuinely specifies a different returned vector for its concrete malformed offset. Existing axiom-message guards are source inventory only, not a new audit.

No source, statement, dependent definition, interface, budget, axiom, exclusion or toolchain edit; no fresh Lean/kernel/replay/runtime/performance acceptance. Exact sources/signatures/rosters/dataset stay off Git with path/size/SHA manifests, hash-bound until coordinator pull/verification; delivery pending. Historical unavailable bytes UNVERIFIABLE; reclaimed duplicates archive-restorable. Original queues unfinished; H28 extraction/replay pause, Raw/Context waits and all STOPs retained. Documentation dependency owner: solidity-v07-v11-20261030/v08-world-lowering.

Accounting and115controls PASS; documentation path gate FAIL exit1 (inherited ExecutionTransport.lean reference). Complete acceptance remains FAIL exit1:3848 classifications pending. No proof/runtime acceptance.
