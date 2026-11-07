# Local unwind control classification

Guarded regression: nested rollback controls must distinguish persistent/transient stores, restore the intended checkpoint and preserve immutable emitted payloads without treating local success as rollback or claiming world/catch completeness.

Complete frozen-selected Solidity/Backend/Failure/UnwindChecks.lean: nine named closed controls, exact frozen/adopted-master signatures. Prior1525 rows and owner map unchanged;1534 reviewed/3749 pending of5283;3806 confirmed owners/1477 unresolved. This file remains unresolved semantically: Q-SEM-OWNER-03 did not name it.

Witness uses distinct Fin17/Fin19 stores. Root/middle/deep/resume carry1/2,7/11,13/17,15/18. Inner custom bytes de/ad at31 restore middle; outer be/ef/00/ff at64 after resume restore root. Nested execution discharges both Fits bounds and both stack bounds using the marked two-element stack. Payload bytes are obtained before checkpoint restoration. These are existing closed local checked executions, not Solidity catch/world semantics or whole compiler totality.

Memory probes distinguish root17,middleaa,deepbb,resumecc at0 and restoredmiddle48 at31; they are finite observations. Wrong-store controls negate exact bad CheckpointRel targets through functionality and concrete contradictions, rather than inventing impossible global premises. Successful returns keep live deep/middle stores and update that live memory; they do not restore root.

Existing guard_msgs/axiom inventories remain source text, not a fresh axiom or kernel replay pass. Zero fresh joint witnesses. No source/statements/dependent definitions/interfaces/budgets/axioms/exclusions changed. H28 extraction/replay pause and all STOPs remain. H145 evidence is prepared for private archival, publication pending receipt. Other historical unavailable exact bytes remain UNVERIFIABLE; exact archive-backed duplicates remain restorable.
