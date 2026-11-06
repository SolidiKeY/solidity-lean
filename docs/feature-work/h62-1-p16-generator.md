# H62 item 1: P16 generator — partial handoff, H70

Base `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`; branch
`codex/solidity-h62-1-20261106/p16-generator`. The VY1/VY3-owned
`Solidity/Yul/Interfaces/P16.lean` remains unchanged. Its pinned bytes and
published `origin/master` at `96788a95383b6295dc13774ef681297adf1337a7` both
hash to `d766f5f4edd680fbfdc79f207a6776a0c87e6f93c18c93ba34c991dd09edaec7`.
The pinned and published files each contain the same 39 imports and 33 doc
blocks. The owner VMs/heads are not published here, so this is not a census of
their unpublished changes. H70 says both owner ticket relays were accepted;
that is not their approval of ordering, integration, or an original-file edit.

## Prototype and acceptance boundary

`generate.py --check` compares output with the unchanged base file; `--render`
prints output without editing it; `--migration --patch` prints the proposed
owner-only marker patch. `census.py` checks every registered import and block
against the target, including exact bytes and ordering; `--target PATH` accepts
an owner snapshot. `census.py --baseline` independently compares the frozen
fragment collection to the exact base commit in Git. Baseline file names and
hashes are inventoried. Missing, changed, extra, malformed and unregistered
fragments are rejected. Documentation accepts one nonempty balanced Lean doc
comment per fragment. These are external checks, not kernel proofs.

Proposed owner-qualified registrations and deterministic order are documented
in `scripts/h62/item1/p16-generator/registrations/README.md`. Independent owner
additions use separate paths and sort after the frozen baseline; a disposable Git
fixture merges actual registration/import/documentation triples in both orders,
then renders them, and demonstrates a same-path conflict. The fixture does not
prove that the order is appropriate for future owner changes, nor that imports
are acyclic. A producer omitted from both owner registrations and the interface
is inherently invisible without reconciling live owner diffs. Names do not
authenticate ownership. Edits to the inventory or baseline require review.

The marker patch is `tests/h62/item1/p16-generator/proposed-owner-p16.patch`.
The separate `tests/h62/item1/p16-generator/proposed-gate.patch` proposes checks
for generated output, live-target census and pinned baseline census in the
checkpoint/full gate. Neither patch is applied; both are pinned-base proposals
and must be regenerated/reviewed against live integration heads. The gate uses
`--migration`, whereas unmodified baseline checks omit that option. The
baseline gate needs the pinned commit in the object database.

## Coordinator and owner requests

H70 confirms relay acceptance by `solidity-inline-assembly5-20261031/vy1-words`
and `solidity-inline-assembly5-20261031/vy3-compilation`. Please relay to both:

* Provide exact live head SHAs and read-only snapshots or diffs for
  `Solidity/Yul/Interfaces/P16.lean` and the P16 producer additions, so the
  registered inventory can be reconciled without editing owner files.
* Review `scripts/h62/item1/p16-generator/registrations/README.md`, specifically
  the owner-qualified naming, uniqueness, and lexical extension order; state
  agreement or the exact required ordering changes.
* Review the two proposed patches at the paths above and identify the owner who
  will apply the P16 marker and the integrator who will apply the gate patch.
  Relay acceptance alone is not approval to apply either patch.

## Verification, reviews and outstanding gates

The scoped Python suite currently has 14 tests. It covers exact baseline
reproduction, missing/extra/order/body drift, removed and tampered baseline
fragments, joint fragment/hash tampering against the pinned Git source, bad
registration and missing source, invalid/injected comments, unexpected files,
nested comments, CRLF, proposed patch application, actual independent Git
merges in both orders and a same-name conflict. Passing tests do not establish
Lean elaboration or semantic correctness. Commands and output are exported in
`/workspace/h62-p16-evidence/` with checksums.

Independent read-only finder and skeptic reviews used no Lean server. They
identified monolithic inputs, missing independent reconciliation, malicious doc
text, ignored entries, byte-fidelity and nesting issues; fixes and controls were
added. Their remaining substantive concerns are live producer reconciliation,
owner agreement, gate adoption and full validation. Both reviewers rechecked the final CRLF and merged-fragment fixes read-only and
found no further concrete defect in those fixes; neither ran fixture tests in
their read-only environment. Their reviews do not close the outstanding gates.

The coordinator-pinned official archive SHA-256 matches
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Lean reports 4.35.0 (commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`),
Lake 5.0.0-src+eb6cafb. The earlier bounded KeySort MCP diagnostic returned
zero errors. The attempted affected P16 diagnostic was stopped when dependency
build processes were observed without the required explicit `-j1`; its result
was `diagnostics_unavailable`, not a pass. The first attempt also failed because
`/usr/bin/time` was unavailable. A second MCP retry also spawned dependency builds without `-j1` and was stopped.
A subsequent `bash ./run-lean.sh` used the pinned toolchain, an isolated Lake
build directory, `LEAN_NUM_THREADS=1` and an alternate TOML with explicit
`-j1`; the observed compiler command confirmed the flag. KeySort built, but
the build failed in existing out-of-scope migration files: `Solidity/Hash/
CollisionBound.lean:407` unsolved goals, `Solidity/Language/FixedPoint.lean:152`
failed generalize, and `Solidity/Frontend/Checked/Token.lean:38` had a changed
`String.ofByteArray` constructor. It was stopped after 114.139 seconds, exit
143; this is a failed, incomplete gate, not a successful build. The full log,
configuration and memory-guard record are in `/workspace/h62-p16-evidence/`.
The guard did not report a resource stop. These failures must be relayed to the
migration owners; this lane cannot edit their files. No affected acceptance gate
or before/after timing comparison has passed. Maintain no swap and 4 GiB
headroom, and stop for a greater than 10% slowdown. No declarations, statements,
premises, axioms or sorries changed; no Lean proof is claimed by this work.

Setup note: initial extraction of scoped prototype inputs before the prior
checkpoint did not acquire the writer lock. Subsequent writes and Lean checks
used the lock; no other writer was observed and no owned original was changed.
Keep all four work-queue checkpoints and in-scope backfill open until accepted.
