# Routine G18 follow-up (H14 cascade)

These statements are NOT proved or assumed by the checked storage client. Add them in NEW `Solidity.Backend.Aggregates.G18StorageFrames`, importing G18StorageClient; keep the producer modules unchanged. Namespace Solidity.Backend.Aggregates.StorageClient.

- `source_other`: `∀ q, q ≠ cell 0 → sourceAfter.read q = source.read q`. Routine: unfold the actual sourceAfter write and apply published Source.Storage.write_other.
- `target_other`: `∀ {U} (q : Path (.ref (.struct "Basket")) U), Path.Diverges (selected ⟨0,by decide⟩) q → targetAfter.find q = target.find q`. Routine: take the actual save equation from updated, rewrite the existing find/save match-equality laws and apply SVal.findM_saveM_diverges. No desired save/run premise.
- `missing_find_exact`: `target.find (selected ⟨99,by decide⟩) = none`. Routine: project the checked negative_controls isNone result and apply the existing Option.isNone equivalence.

Try shared standard automation first. No sorry/axiom stubs, frozen signature edits, Source edits, proof-budget increases or whole-profile claims. Keep Option failure distinct from source/EVM failures. These are G18 helper consequences, not paused G48-G51 premise-only work.

- `selected_type` in the new G18StorageFrames module: `∀ i, env.pathTy (cell i) = some (.int .u8)`. Routine actual client of published `array_path`: use this client's declared Basket field path `⟨⟨none,"root"⟩,[.field 0]⟩`, storage location, `.int .u8`, dynamic length `none`, and the actual field-type equation. This proves typing only, not source bounds or full path lowering. Additional inhabited `path_append` and `mapping_path` applications remain unproved; do not mark them done from the existing bare-definition controls.

## Integer mapping consumer follow-up

Keep the proved producer modules unchanged. Add routine consequences in a NEW `Solidity.Backend.Aggregates.G18ScalarMappingCorollaries`, importing G18ScalarMappingControls and published G18Storage. Namespace ScalarMapping.Controls.

- `mapping_path_client`: for `t : Source.IntTy` and `b : Bool`, `(env t).pathTy ⟨⟨none,"entries"⟩,[.key (keyBytes b)]⟩ = some (.int t)`. Apply the published `mapping_path` to root `⟨⟨none,"entries"⟩,[]⟩`, actual mapping type `.mapping .bool (.int t)` and actual keyBytes; do not only unfold the bare definition.
- `copy_code_length`: `code.length = 4`. Routine structural reduction; not a gas/fuel/stack-limit theorem.
- `copy_self`: `∀ (c : Sample) (key : Bool), Evm.run (StorageOps.TargetOperations.copyCode (slot (K := .bool) base key) (slot (K := .bool) base key)) (beforeTarget c) = .ok (beforeTarget c) 0`. Apply published `run_copy_self`. Do NOT infer raw Source-cell identity: writing an implicit default may change cell presence.

All three remain unproved/not assumed by the current copy certificate. Their Source/target profile and physical-hash boundaries remain unchanged.

## Source mapping phase consequences

Add routine glue only in NEW `Solidity.Backend.Aggregates.G18SourceMappingCorollaries`, importing G18SourceMappingControls. Namespace ScalarMapping.SourceMachine.Controls. These statements remain unproved and unused by the producer.

- `sequence` for each actual `c : ScalarMapping.Controls.Sample`: the existing Source EM computation `do let v ← Source.readAt frame (ScalarMapping.Controls.path true) (.int c.ty); Source.writeAt frame (ScalarMapping.Controls.path false) v; pure v`, run at `(locals c,state c)`, equals `(.ok (.int c.a c.ha),(locals c,afterState c))`. Routine: published Hoare.run_bind and the two actual results of certificate. This is a client of existing helpers, not a new execution semantics or an elaborated assignment theorem.
- `account_frame`: afterState retains the selected account's balance, nonce and code and every other account. Routine published ExecState.apply/World.set_get/set_other; keep actual address inequality. No physical Source-target frame inference.
- `zero_horizon` for actual `c` and `G : Source.Glob (E c)`: instantiate existing ScalarMapping.Controls.zero_horizon at `[.bool]`, frame, `(locals c,state c)`. No claim that a Glob or SourceSpec instance is inhabited, no timeout-to-divergence conversion.

Try shared automation first. No Source edits, profile assumptions, budget increases, new axioms or sorry stubs.
