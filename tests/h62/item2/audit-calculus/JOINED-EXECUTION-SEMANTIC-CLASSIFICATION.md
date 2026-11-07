# Joined-sequence execution roles

Guarded regression: joined local assignments must preserve the original condition snapshot, ordered dependent writes, unselected RHS non-evaluation and every selected error/halt. Full execution equality is not unconditional success.

Complete frozen-selected Solidity/Calculus/Sound/JoinSequence.lean and all10 named signatures match frozen/current master bytes. Prior651 rows and owner map unchanged. All5283 candidates accounted:661 reviewed/4622 pending;3746 owners confirmed/1537 unresolved. Existing source statements are reviewed, not newly proved; zero fresh joint witnesses. Generated declarations remain separate.

The snapshot lemma preserves the fresh Boolean head while writing an original local. program_runSt matches ordered writes to their typed program. guard_runSt and guarded_runSt evaluate only selected RHS values in order, preserving failures and applying the exact continuation after selected writes; skipped writes leave the snapshot state for the continuation. joined_runSt records the original simple Boolean once, retaining that value after writes. joined_drop_runSt removes exactly the fresh snapshot and preserves the entire selected TRes, including halts/errors.

joined_sound and captured_sound already assert semantic Premise.Runs for either modality and every supplied typed state without validity, arithmetic or totality premises. This is stronger than mere syntactic rule availability, but does not imply a successful result or source compiler totality. captured_drop_runSt identifies the dispatcher's exact captured block: the inner block pops no locals; capture alone pops the snapshot.

joinPlan_sound additionally requires EXACT Upd.ifJoin? c.lower thn els=some(inr body). The proof reconstructs both decoded local-write programs; singleton-plan selection, decoder failure or forbidden JoinBoundary branches contradict that equation internally. Those checks are not new outer premises, and no claim the planner always selects a sequence is made. Fresh validation of all these proofs/axiom sets remains open.

Bulk source snapshot, signature bindings and static truth/plan roster remain off Git under /workspace/h62-successor-evidence/joined-execution-roles-v60 and /workspace/h62-successor-bulk/joined-execution-roles-v60 with path/size/hash manifests. Fresh master658d1b1d1 adopted with prior head archived and merge history retained. Zero production Lean modules/lines changed; no statement/dependent-definition/budget/axiom/exclusion/toolchain change.

Whole assignment and four audit checkpoints unfinished. H28 actualCallerFields/extractionActuallyChanges/replay pause, Raw compatibility/Context Classical.choice waits, rejected prototype and timing/reserve STOPs persist. No new runtime/cache/performance acceptance. Historical missing exact bytes remain UNVERIFIABLE.

Documentation gate FAIL exit1: adopted-master Solidity/Yul/Compilation/P20InterfaceV2Controls.lean cites missing tests/h62/item2/audit-v09-passes/P20InterfaceV2Controls.lean. Exact citing bytes/master and full failure log archived; no local Yul/scanner edit or waiver. Accounting and93controls pass; complete acceptance remains FAIL exit1.
