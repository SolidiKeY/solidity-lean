# Shadow-write and merge classifications

Guarded regression: dropping a shadowed write must preserve halt/exhaustion distinctions; successful update merging cannot imply unconditional return, arbitrary modality exchange or transformation completeness.

Complete frozen-selected Solidity/Calculus/RewritePast/Merge.lean and all24 named signatures match frozen/adopted master. Prior1191 roles and owner map unchanged;1215 reviewed/4068 pending of5283;3746 confirmed owners/1537 unresolved. Zero fresh joint witnesses; generated declarations separate.

Spine recognition follows only the first argument recursively (or exact term equality for onSpineS). Recognized inner failure propagates to outer failure. Exhaustion propagates back only with actual inner failure, positive recognition and outer exhaustion; returns-or-exhausts remains a disjunction. Compiled/recursor recognizer equality grants no positive recognition.

Global replacement commutes with elements that write neither storage nor memory, with operands evaluated at fixed sigma0. Explicit storage/memory equations retain Option failure. ShRel permits both successful globals differing in storage/memory, with equality of each component only when its pending list is empty. It also permits original none while transformed evaluation differs, provided transformed none or a pending shadow term halts. Thus dropSh_rel is not arbitrary-list evaluation equality. Held-local substitution equality is unconditional but supplies no return witness.

Dropping exhaustion transport retains every pending storage/memory term returns-or-exhausts and transformed exhOk. It yields original exhOk and only the implication from transformed exhAny to original exhAny. Formula transport holds_upd_dropSh uses empty pending lists and is one-way. holds_upd_total requires actual U.totalB=true before changing modality; this is not source/compiler totality.

mergeK tries seqPar, storage, memory, then local-memory merge. Modality selection uses agreement, otherwise first update totality, otherwise second update totality, otherwise fails. mergeP requires both selection and update merge success then drops shadowed writes. Every soundness interface retains exact Option success and transformed holds premises.

Binder handling first attempts direct absorption, optionally all-leading-binder absorption with reorder, then guarded lift/recursion only if t.notMem or U.keepsNext; otherwise failure. absorbBind falls back unchanged when inapplicable; leading absorption proceeds innermost first. mergeAt traverses universal/hidden binders and indexed update spines; mergeRun zero is identity and successors merge inner pair first. mergePast tries n+1 merges without reordering before fallback with reordering. Full term/update/formula cases and all definition/proof branches were read; no execution or completeness credit follows.

No source, statement, dependent definition, interface, budget, axiom, exclusion or toolchain edit; no fresh Lean/kernel/replay/runtime/performance acceptance. Exact source/signatures/rosters/dataset remain off Git with path/size/SHA manifests, hash-bound until coordinator pull/verification; delivery pending. Historical unavailable bytes UNVERIFIABLE; reclaimed duplicates archive-restorable. Original queues unfinished; H28 extraction/replay pause and Raw/Context waits retained. No STOP release.

Accounting and115controls PASS; documentation path gate PASS exit0. Complete acceptance remains FAIL exit1:4068 classifications pending. No proof/runtime acceptance.
