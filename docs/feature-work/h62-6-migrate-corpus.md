# H62/H63 Corpus toolchain migration

This isolated overlay remains **blocked and incomplete**. No producer ownership
was transferred, no original Lean file or root toolchain pin was edited, and no
push, merge, PR, deployment or cut-over was performed.

Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Branch: `codex/solidity-h62-6-20261106/migrate-corpus`.
Repository: `/workspace/solidity-lean`.
Original frozen prompt identifier supplied by launcher:
`ef334e40480cb8325ca7943fbc986e0d359a7b8928d753133302e731e3f266f2`.
The existing goal was retained; get_goal is not exposed and coordinator has
explicitly confirmed that optional inspection absence is not a blocker.

## Census and frozen boundaries

The nine assigned files are byte-identical to the pinned base. Source census
records 340 local modules, 331 outside-directory dependencies, and eight direct
outside imports. Every outside dependency maps to exactly one migration owner.
All 639 scoped expected rows are retained: 552 derived, 68 proved, 11 refuted,
one excluded, two skipped, five unsupported. No exclusion or premise changed.
The full 774-row expected table is also hash-pinned.

[Source hashes](../../tests/h62/item6/migrate-corpus/frozen-sources.json) freeze all
source bytes, including unnamed examples, program bodies and proof budgets.
They are not elaborated API compatibility evidence. The interface probe generator
is supplied for a separate type-expression inventory once imports build.
[Case summary](../../tests/h62/item6/migrate-corpus/frozen-case-summary.json) is
small; full census/case/dependency outputs stay off Git with final checksums.

## Toolchain and resource policy

Official new pin: `leanprover/lean4:v4.35.0`, Linux x86_64 archive SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Actual Lean: 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`;
Lake: `5.0.0-src+eb6cafb (Lean version 4.35.0)`.
Old Lean: 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`;
Lake: `5.0.0-src+797c613 (Lean version 4.24.0)`.
All five coordinator input SHA256 checks passed.

KeySort passed on both versions before migration validation. Its preliminary
sampled RSS increased from 307396608 to 638472192 bytes; wall fell from
2.211549377 to 1.809531277 seconds. This resource regression is escalated to
migrate-root-gate; it is not a full-directory performance comparison.

The VM hard cgroup memory cap is 16 GiB; the driver samples complete task
process ancestry, including detached MCP sessions, at 200 ms. It stops above
12 GiB aggregate RSS or below 4 GiB host/cgroup headroom. Host swap total is zero;
cgroup swap.max is max, so no cgroup swap prohibition is claimed. No systemd-run
or shared/per-master cache retrieval is used. Official binaries are unchanged;
private symlink sysroots add explicit `-j1`, serial worker locking and no changed
proof budgets. `LEAN_NUM_THREADS=1`. Private TOMLs disable artifact caches and
use isolated output directories; they must not enter the final patch.

## Gates and measurements so far

* Clean old attempt: exit 1 after 2032.551216607 s, sampled aggregate RSS
  3510403072 bytes. An added 12 GiB virtual-address cap caused thread creation
  failure at Calculus.TermSize. This attempt is **invalid as a baseline**.
* Removing that inappropriate address-space cap: TermSize passed in
  34.209311049 s, sampled RSS 1267032064 bytes. This focused run is not a clean
  full build. A fresh full old retry remains required.
* Clean new diagnostic build: exit 1 after 60.376878436 s, sampled RSS
  1675653120 bytes; no resource stop. Outside-scope dependency failures are
  recorded below. This failed run supplies no valid performance delta.
* Five finite boundary fixtures passed old-toolchain per-file MCP diagnostics:
  complete, success true, no errors, no failed dependencies. The fixtures cover
  successful execution, require(false) rejection/revert, assert(false)
  rejection/panic. They do not establish global compiler totality or new-version
  compatibility. MCP Python shutdown emits a known event-loop warning after the
  successful diagnostic response; driver exit is zero.
* Acceptance v5 passes byte mutation, missing/immediate/nested module controls,
  stopped-child exit-zero handling, external SIGTERM cleanup, detached 32 MiB
  descendant accounting/cleanup, and synthetic timing-policy controls. Identical
  synthetic measurements pass; exactly 10% escalates; above 10% stops; failed,
  nonfinite, mismatched-source/config/cache/target/AS records are blocked.
* Static baseline: 857 core modules reach neither elaborator nor checked parser
  adapters; generated roots and fragments match. These are not a full new gate.

## Independent reviews

Read-only finder and skeptic used no Lean server and made no edits. Confirmed
findings fixed: process cleanup and external termination, false-success stop
status, preflight headroom, misleading hard-limit labels, detached process
accounting, nested source injection, benchmark provenance, nonfinite values,
required fields in both records, and strict decimal >10% threshold. Both final
comparison reviews found no remaining blocker for the clean old retry.
The initial AS-capped run and failed MCP setup attempts remain preserved as
failed evidence. They are never counted as passing gates.

## Owner requests and remaining queue

[Exact-file requests](../../tests/h62/item6/migrate-corpus/owner-requests.json):
`DEP-SYNTAX-RAW` goes to migrate-syntax for String/Slice API errors at
Solidity/Syntax/Raw.lean:597,650,665,682,684.
`DEP-CALCULUS-LINEARCOUNTERMODEL` goes to migrate-calculus for the proof mismatch
at Solidity/Calculus/LinearCountermodel.lean:134.
Both are actual transitive corpus prerequisites. Requests are prepared for
coordinator retrieval; relay.sh is absent, so no delivery/acknowledgement is
invented. No existing owner file was edited.

Still required: successful fresh clean old baseline; owner dependency overlays
and any resulting exact-file coordination; successful new build of all nine
modules; cross-version elaborated interface comparison; deterministic corpus
acceptance and full affected/final repository gates; valid paired timings with
any regression escalated and >10% slowdown stopped; final finder/skeptic evidence
review; final patch/bundle and checksum manifest. The goal remains unfinished.

Evidence directory: `/workspace/migrate-corpus-evidence`.
Reproduction tools: `scripts/h62/item6/migrate-corpus/`.
Final committed head, artifact hashes and all command outcomes will be recorded
in the external HANDOFF.md and final-state.json after the final local commit.
