# TF-handoff: exact gate identity for done

Production change: `scripts/coord-tools/handoff.sh` now validates `HEAD`
for every supplied gate directory before allowing `done`. It requires a
readable regular file whose stripped contents equal the canonical full current
Git commit ID. Missing/non-file identities and read/decode failures refuse;
empty, malformed, symbolic, abbreviated and stale identities cannot equal HEAD.
The prior whitespace-trimming behavior is preserved. Symlink resolution follows
the existing regular-file semantics. No new success path is introduced.

For any stable inputs, new `done` success implies old success: gate parsing,
nonempty aggregate PASS rows, clean tracked worktree and artifact creation are
unchanged. The extra condition is universally required gate identity. For
`partial` and `blocked`, the original identity branch is preserved verbatim.
No `gate.sh`, `seal.sh`, generated root, Source, compiler or producer code changes.
No Lean checking or compiler/EVM claim is involved in this shell/Python fix.

## Controls

Run from the checkout root:

```sh
python3 tests/terra-20261103/handoff/test_gate_identity.py -v
bash -n scripts/coord-tools/handoff.sh
git diff --check
```

The controls execute the real script in disposable Git repositories. Gate rows
are supplied **synthetic test data**, not executions of real build/test gates.
They cover missing/empty/malformed/stale/unreadable/non-file identities, both
orders of current+missing directories, unchanged valid/clean success,
failed gates, dirty tracked files, absent gates and non-done preservation.
Refusal checks preserve preexisting output sentinels and require the specific
identity or legacy gate/clean-worktree diagnostic. The default-output control
reads the returned artifact path and both complete artifacts, retaining exact
notes, checkpoints, repository, base and full head; it does not merely compare
fixture-created paths.

Independent baseline against unmodified production: 12 tests, three failures
(missing, mixed and non-file HEAD bypasses). This diagnostic run is retained;
it is not a run of frozen Terra acceptance and does not reset its failureCount.
After production repair and stricter refusal oracles: 13 tests pass.

## Frozen historical contract and repair acceptance

The exact fixture archive for
`1e847b3396c843b2635432b8ddc7a3d3e55894e6` was relayed and verified with
SHA256 `b00d51085ac5a68b12c2749adb8107c22e291d8040d7cc757aeedc5656ceb30a`.
It is retained read-only outside the checkout with its original RED output and
independent reviews. `accept.py` is byte-identical to the frozen file
(SHA256 `d76178219219972aca36e73d623fbb4b811c9937d7c4068acb0a78f2966a415f`).
The historical README is retained unchanged alongside it.

The original twelve cases remain present. Only the assigned refusal oracles
for `done_failed_gate`/`done_dirty_tracked` and the observed-default-output
predicate were strengthened in `test_cases.py`. All twelve pass against the
repaired production script; all thirteen independent identity controls pass.
The exact notes, checkpoints, commits, module additions/deletions and complete
stdout/Markdown/JSON checks are retained by the original suite.

The immutable historical acceptance cannot certify this authorized production
repair: it pins the old production hash
`7178b318b537235ab0624294220d1fdd1c479e4e72e18518d6942f75a9627368`,
requires exactly three fixture files and permits an artifact-only commit.
The repaired script hash is
`de3a19b22cf9a29a26e194d0312a858093ca31a015fd6bc2590678068b675d97`.
A historical snapshot replay remains RED at missing HEAD. An isolated repaired
snapshot with exact frozen files refuses at the source-pin check before tests.
Both raw outcomes are preserved. No hash check, inventory check, acceptance
file or original red receipt was changed to manufacture a pass.

Coordinator decision is pending for a reviewed repair-snapshot acceptance
contract or a separately reviewed repair adapter with an exact new source pin
and explicit fixture inventory. This is not yet a scope-complete accepted
packet, despite the passing 12+13 tests. Synthetic gate rows remain test data;
no real build gates or Source/Lean/EVM execution is claimed.

Read-only finder and skeptic reviewed production scope and controls without
running Lean/server/builds. No production defect was found. The skeptic noted
that identity refusals should demand their diagnostic; that oracle improvement
is included. Final repair-snapshot acceptance/review remains pending the explicit contract decision.

No Lean modules were added: registration and area-row proposals are empty.
The original P8a producer/SourceSpec dependencies and all holds remain unchanged.

## Authorized replacement contract

The coordinator authorized a new frozen repair snapshot contract on 2026-11-04.
`accept_repair.py FULL_REVIEWED_HEAD` supersedes only acceptance of this repaired
snapshot. The earlier pending-decision paragraphs above describe retained
history, not the current authorization. All historical bytes/RED/reviews are
archived in `historical.tar.gz`; `accept.py` remains unchanged.
`inventory-mapping.json` retains every original method source and its replacement,
including all assertions, backend invocations, artifact bytes and refusal checks.
The new contract pins production commit d1e97dd121c9edd01ae9dcdec2e80d0c41a1d97d,
source SHA256, all historical member hashes, all artifact paths, exact 12+13 case
names and current committed bytes. The contract and its own manifest are pinned
by the mandatory reviewed full current commit argument (avoiding recursive hashes).
No synthetic gate receipt establishes actual build or semantic correctness.
