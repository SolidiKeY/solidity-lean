# H55 source-relations

Base: `4d3790eadb8a5212233bc7d5e345817476b2f590`. Repository: `/workspace/solidity-lean`. Branch: `codex/solidity-h55-sol-20261106/source-relations`.

The coordinator lease correction makes all seven listed existing source paths migration inputs, not write leases. No existing producer/consumer source has been edited. Production migrations await an actual owner notice, accepted handoff, and exact transferred files. New work is confined to this document and `tests/h55/source-relations/`, `scripts/h55/source-relations/`. This is not full assignment completion.

## Runtime and boundaries

Actual Lean 4.24.0, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b; Lake 5.0.0-src+797c613. A local Docker source check of `Solidity/KeySort.lean` printed KEYSORT_PASS under 12 GiB memory and equal memory+swap limits (no swap), one CPU, `LEAN_NUM_THREADS=1`, explicit `-j1`. The reproducible bounded runner saves command, output, exit, elapsed time and enforced runtime bounds outside git. A pass of this prerequisite alone is not a proof-suite or acceptance pass.

The original checkout was clean on `work`, at 8bf83218. `git ls-remote origin refs/heads/master` returned the exact assigned base. Fetch advanced origin/master to that base; the task branch was created there after ancestry checking under the repository writer lock. No reset, push, merge or PR occurred. The goal tools expose stop_goal but not get_goal in this session. No replacement goal was created.

## Queue status

1. Shared inferencer implementation and exact adapters: production edits blocked by the lease correction. Read-only design and standalone backfill proceed. Both fuel and choice order of the Option interface, and exact list Res including auxiliary receiver/slot/call-option results and InferComplete statements, must survive. Selecting the head of the exhaustive list is not an established adapter.
2. Unified value relation and locals/context-map equivalences: production edits blocked by the same correction. Existing primitive correspondence supports exactly bool, uint256 and int256; IntValueRel also supports narrower integer widths with intrinsic range evidence. Backend.Scalar.ValueRel observes ABI words, a different codomain. It must retain signed two’s-complement and full word observation. P12NextInterface.ValueRelation is world-indexed and supports reference relations; replacing it by a scalar-only relation would lose its contract.
3. Consumer requests and controls: read-only census and standalone acceptance are in progress. Owner identity/transfer requests go to the coordinator, not inferred from retired notices.

H58 HOLD remains in force: no Outcome/Word edits, git-ref relays, single-state-file rewrite, generated axiom audit, or outcome-folding work. No theorem weakening, premise/exclusion changes, heartbeat increase, sorry or new axiom is authorized.
