# RAW-435: frozen typing dependency fails mandated migration toolchain

Status: RESOLVED FOR THIS LANE by coordinator clarification: this lane uses v4.24.0; v4.35 is migration-batch-only. Raw passes unchanged on v4.24.0. QRAW-435 is answered; no producer repair/overlay is requested. Historical options below are closed, not approval requests.

Historical v4.35 reproduction follows; it is not a current blocker.
Worker: solidity-h62-2-20261106/audit-typing.
Repository: /workspace/solidity-lean.
Branch: codex/solidity-h62-2-20261106/audit-typing.
Base: c6f550e281a7e5affa9a99bc2cdaed556dec00e4.

## Exact reproduction

`python3 scripts/h62/item2/audit-typing/build_typing_values.py`

It verifies every planned source against the frozen Git object, verifies the official archive SHA256, uses the repository writer lock, LEAN_NUM_THREADS=1, explicit -j1, --memory=11000, --tstack=131072, isolated outputs and a continuous 4 GiB reserve guard. No old cache, statement edits, raised heartbeats or trust shortcuts. The 300-second limit is an external subprocess bound, not a proof-budget increase.

Official binary: /workspace/h62-audit-typing-tools/lean-4.35.0-linux/bin/lean.
Archive SHA256: 7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d.
Actual Lean: 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release.
Actual Lake: 5.0.0-src+eb6cafb.

The plan contains 28 unchanged files. KeySort exits 0 (1.408 s), AST exits 0 (6.529 s), SpecSyntax exits 0 (2.010 s). Raw exits 1 (3.612 s), with no timeout or reserve stop. Five errors in unchanged `Solidity/Syntax/Raw.lean`:

- 597: `f.drop 1` is String.Slice, but HashKind.ofName? expects String.
- 650: String.Slice has no toList field at `(s.drop 9).toList`.
- 665: `(rest.drop 8).dropRight 1` is String.Slice, but splitTopCommas expects String.
- 682: `List.find? c.endsWith` no longer has the required String → Bool function type.
- 684: String has no dropRight field.

Evidence: /workspace/h62-audit-typing-evidence/typing-values-build-plan.json; typing-values-build-results.json; Solidity_Syntax_Raw.lean.build.log.

Confirmed import path: Typing.Values → Semantics.StorageWt → Semantics.Storage → Semantics.Storage.Values → Semantics.Value → Semantics → Syntax.Checked → Syntax.Scoped → Syntax → Syntax.Raw.

## Required producer action

Raw is outside this worker's sole write scope. Additive audit declarations cannot fix Raw during its own upstream elaboration. The v4.35.0 pin and unchanged public statements remain binding. No repair is proposed to any theorem premise/conclusion.

QRAW-435 [sources: H62/H63 migration pin; exclusive audit-typing scope; RAW-435 reproduction]: Which authorized dependency handoff should unblock typing validation?

1. Raw migration producer supplies a reviewed compatibility patch/overlay under its ownership, preserving the original public interfaces; coordinator authorizes consumption under the isolated migration exception.
2. Coordinator supplies an already-approved, source-correlated v4.35.0 dependency overlay with hashes and interface-fidelity evidence; worker validates it before consumption.

Until one exists, retain dependency blocker RAW-435. Neither option authorizes this worker to edit Raw or weaken interfaces. No relay.sh exists locally; ticket is saved for coordinator retrieval, not claimed delivered to an external recipient.

## Reviews and limits

Independent read-only finder verified all 28 source hashes, topological order and actual five diagnostics. Independent skeptic confirmed the transitive path and that additive downstream helpers cannot fix upstream compilation. Neither used Lean/server or edited files. Both confirmed a genuine typing dependency blocker.

This blocks full assignment completion and the affected typing imports. It does not imply that every remaining frontend module or scanner/fixture backfill is blocked. The Closure source subset has passing witnesses; all global checkpoint obligations remain unfinished. Other unaffected backfill remains available after the required coordinator handoff.
