# H62 item 11: EVM lemma extraction

Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. This is an initial
read-only census, not a completed checkpoint or extraction. Run
`python3 scripts/h62/item1/evm-lemmas/census.py` from any directory; it scans
EVM, Backend, and Lowering Lean source in sorted order and writes no output
files. Its line-based patterns identify candidates, not a complete semantic
proof of all cases; multiline or differently named declarations need manual
review. EVM Examples and MemoryCopies Controls filenames are excluded by assignment.

Independent read-only finder and skeptic reviews (no Lean server) located seven
`run_cons_revert` definitions and seven named `Storage.Loc` inequality sites,
including a nested case; the scan also found an inline proof.
The public `Solidity.Evm.Prog.run_cons_error` in `Evm/Correct.lean` generalizes
the former, but its import cost and dependencies require measurement. The
`Evm.Slot.ne_data` theorem is about a different type. Nested descendants require
separate coverage; symbolic location inequality does not establish inequality
of hashed concrete words without the existing injectivity and coverage premises.
The three allocation-cost definitions do not have identical reductions, and
the fragment certificates belong to different indexed inductives. Preserve
all existing definitions, declarations and signatures when extracting proofs.

The seven cons-revert consumer files and most other consumer files are outside
the supplemental five-file lease. No relay script was found under `/workspace`;
exact-file owner coordination and registration remain outstanding. A census or
unused helper is not a substitute for integration. All four extraction checkpoints,
proofs, baseline/after timing, acceptance, final validation and post-change
independent reviews remain open. No Lean theorem, premise or representation has
been changed by this census.

Post-change read-only finder and skeptic reviews identified the overly broad
filename exclusions and incomplete location count; both were corrected. Neither
review used a Lean server. The initial creation of these two files was performed
without the required writer lock; concurrent writer status was not checked. Subsequent
changes and commit preparation used the lock.

H70 routing: the host-only relay accepted an owner ticket for V14. Exact revert consumers, first-statement and tail revert cases, nested location cases and owner requests are recorded in `tests/h62/item1/evm-lemmas/case-accounting.md`. This is static source accounting; no owner permission, extraction or passing proof gate is inferred.


H70 waiting backfill: `tests/h62/item1/evm-lemmas/LocationFixture.lean` proves
symbolic child and grandchild inequalities, reverse orientations, and distinct
siblings under an index inequality; equal indices give a negative control.
`RevertFixture.lean` proves first-error, revert specialization and tail-error
sequencing and shows intrinsic revert satisfies the premise for any supplied
state and tail; it does not construct a closed state. These are isolated,
unregistered fixtures; no consumer, frozen statement, representation or
concrete hashed-word injectivity claim changed.

Lean 4.24.0 / Lake 5.0.0-src+797c613: bounded locked `lake -f
tests/h28-sol/literal-grammar/runtime.toml env lean -j1 --tstack=131072`
passed for LocationFixture (0.370 s) and RevertFixture (1.122 s after witness).
Location child/grandchild axioms: `propext`, `Quot.sound`; distinct siblings:
none. Revert fixture axioms: `propext`, `Classical.choice`, `Quot.sound`.
The first RevertFixture check failed because Lake's reported fetched KeySort
object was absent; Hashes, Keccak and RevertBytes objects were also absent.
Four generated traces were removed and a serial `lake --no-cache ... build
Solidity.Semantics.Run` with a private cache rebuilt them; the retry passed.
Independent read-only finder and skeptic reviewed each fixture without a Lean
server; neither found a material defect. Fixture checking is not affected-file
validation, extraction acceptance, or a before/after performance comparison.
Original-file owner agreement, module registration, final gates and timing
remain pending.


H70 follow-up while owner deliveries are pending: the sequencing fixture now
checks panic and nonempty revert-data heads and a successful intrinsic require
followed by a reverting tail, for every supplied state. The location fixture
uses the existing `Loc.word_data_alias` for distinct sibling offsets and gives
a root/child alias in the one-word, constant-hash model. The latter is not an
EVM/Keccak collision. Both fixtures passed bounded serial Lean checks; the
independent read-only finder and skeptic found no material defect. These are
fixture proofs, not integration, closed-state existence, external tests, or
before/after performance evidence. The owner-delivery routing now identifies
`claudecloud/move5-20261106/v14-g43` for the seven EVM consumers and V10 for
the staged StorageOps consumers; delivery is not owner agreement.


## Fresh-thread coordinator handoff

Four backfill items are committed after base: census `67374c2d0`, source case
accounting `752b1cda0`, isolated proofs `224fc8a75`, and boundary cases
`62678f7d7`. Continue in the same VM environment
`ccarenv_b64_Y2NhcmVudl9jYThlOGFmZmQ3OWM4MTkxOGM0YjllODhhNDY4OGU1OA`,
checkout `/workspace/evm-lemmas`, branch
`codex/solidity-h62-1-20261106/evm-lemmas`, base
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. The original persistent goal
concerns the whole frozen H62/H63 assignment; do not create or reset it. Its
`get_goal` interface was unavailable in this worker. A previous `stop_goal`
reported blocked; a later invocation lacked trusted source-turn context, so no
new transition should be inferred from this handoff. The coordinator must
resume the original goal and inspect its actual state.

H70 latest routing: V10 received the StorageOps request; delivery to current
`claudecloud/move5-20261106/v14-g43` is pending for seven EVM consumers.
Routing is not agreement. Exact paths and symbolic/word distinctions are in
`tests/h62/item1/evm-lemmas/case-accounting.md`. Await both owners before
editing their originals. The supplemental five-file lease remains as supplied;
the H55 EVM Examples and MemoryCopies Controls exclusions remain binding.
All four production extraction checkpoints, registration, affected/final
validation, acceptance, independent post-extraction reviews, and same-resource
before/after timings remain open; stop for a slowdown over 10%. No production
proof or interface was changed. The isolated fixture evidence and SHA256
manifest are at `/workspace/h62-evm-lemmas-h70-boundaries/`; its patch ends at
`62678f7d7839f515b152e462386bb51bd2d2e961`, before this handoff-only commit.
Lean 4.24.0 / Lake 5.0.0-src+797c613 were used for this non-migration lane.
The migration-only official 4.35 pin is separate. Use the writer lock, serial
Lean `-j1`, no systemd-run, no swap and the stated 4 GiB reserve. A missing
cache object issue and repair are recorded above. No merge, push or publish.

## H82 successor: symbolic location extraction

The authenticated H82b intake supplies the frozen assignment and scope and confirms
the final stopped heads. The successor merged all three storage-chain member heads
before continuing their queues. Earlier exact-file waits for proof-only Codex work
are superseded; Claude-owned consumers and trust-sensitive changes remain outside
the live write scope. No migration timing STOP is released by this intake.

The existing shared hashed-separation module now proves symbolic child and
grandchild inequalities once. Four unchanged private statements in PushTransport,
NestedPopTransport and TargetPrimitivePop are exact instances. The inherited
location fixture uses the same public laws and retains sibling equality, distinct
indices, reverse orientations and unconstrained-word alias controls. Existing
operation definitions, representations, query cases and finite-run numeric
premises are unchanged. No new production module or import edge is introduced.

Standard automation failed on both general location goals; the original depth
arguments passed the scratch checks. The affected build passed 119 jobs and the
three consumer axiom guards. Single warm before/after samples for the shared file
and those consumers stayed within the 10% limit; page caches were not normalized,
so these measurements do not establish a statistical speedup. Raw dispatch errors
from a missing host Docker PATH are retained separately from Lean results.

This is a partial extraction: the other symbolic consumers, concrete-word uses,
allocation and fragment lemmas, Claude-owned revert consumers, complete audit
witnesses, generic control correspondence and final combined gates remain open.
The current live toolchain remains Lean 4.24.0; no v4.35 cutover is implied.

## Remaining consumer timing boundary

A second packet instantiated the shared laws in eight further owned consumers,
retaining every numeric word-injectivity application and its covered-location
premises. The affected build passed 145 jobs and all eight candidate per-file
kernel checks passed. Four single warm timing comparisons exceeded the 10% limit:
TargetClearRepresentation, TargetArrayWrite, PrimitiveCycleNumeric and
NumericRetainedCycle. The entire second packet was rejected and all eight
original proof bodies were restored. The rejected patch, raw cold and warm
measurements and failed timing disposition remain off Git. No unchanged timing
retry, gate relaxation or production acceptance is inferred from the kernel
passes. The first committed shared-law extraction remains separate.
