# Routine G18 follow-up (H14 cascade)

These statements are NOT proved or assumed by the checked storage client. Add them in NEW `Solidity.Backend.Aggregates.G18StorageFrames`, importing G18StorageClient; keep the producer modules unchanged. Namespace Solidity.Backend.Aggregates.StorageClient.

- `source_other`: `∀ q, q ≠ cell 0 → sourceAfter.read q = source.read q`. Routine: unfold the actual sourceAfter write and apply published Source.Storage.write_other.
- `target_other`: `∀ {U} (q : Path (.ref (.struct "Basket")) U), Path.Diverges (selected ⟨0,by decide⟩) q → targetAfter.find q = target.find q`. Routine: take the actual save equation from updated, rewrite the existing find/save match-equality laws and apply SVal.findM_saveM_diverges. No desired save/run premise.
- `missing_find_exact`: `target.find (selected ⟨99,by decide⟩) = none`. Routine: project the checked negative_controls isNone result and apply the existing Option.isNone equivalence.

Try shared standard automation first. No sorry/axiom stubs, frozen signature edits, Source edits, proof-budget increases or whole-profile claims. Keep Option failure distinct from source/EVM failures. These are G18 helper consequences, not paused G48-G51 premise-only work.
