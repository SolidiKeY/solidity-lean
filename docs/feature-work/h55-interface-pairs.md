# H55 interface-pairs: standalone preparation

Batch: solidity-h55-sol-20261106. Branch:
`codex/solidity-h55-sol-20261106/interface-pairs`.
Published base: `4d3790eadb8a5212233bc7d5e345817476b2f590`.
Repository: `/workspace/solidity-lean`.

## Authorization and queue state

The latest coordinator correction makes every listed existing file a migration
INPUT, not a write lease. No existing producer/consumer file has been edited.
Production changes require a notice naming the actual current owner, accepted
handoff and exact transferred file list. This is a typed dependency,
`CoordinatorLeaseNotice(owner, acceptedHandoff, exactPaths)`, currently pending;
owner/path lookup belongs to the coordinator. No human scope decision is requested.

Ordered queue status:
1. Selection frame/premise and memory-word conversion acceptance preparation:
   standalone controls only. Production statement collapse remains pending.
   Boundary-link and fixed/dynamic path-room standalone proofs now use the actual
   published APIs. Shared schema equivalences and conditional link conversions
   preserve map policy and typed path costs; no production migration is claimed.
2. Stack room: standalone arithmetic predicate/Boolean guard prototype with
   exact equivalence, an exact Scalar.safeHeight correspondence and overfull-height
   controls. Whole-program production guards and consumers remain unmigrated.
3. Production consumers: census saved, no migrations. External owner patches
   and integrated affected-module/full gates remain pending.

P10 V1 retirement, Word/Outcome unification, all H58 HOLD work, Source/Core
ExtCall, shared roots/maps/pins, and theorem/premise/exclusion changes are absent.
No new production module requires central registration at this checkpoint.

## Exact conversion boundaries

- Frame V2 downgrades to V1; V1 upgrades only with its SAME-code peak,
  input admission and full capacity witness. Roundtrips retain the original
  potentially nonminimal peak. The existing 1025-PUSH counterexample remains.
- Compiler V2 is V1 plus the full relation witness. Runtime V2 is V1 plus
  its exact declared-input-height, unchanged nonstack-frame, relation and
  successful-IR witness. Downgrade uses that witness to reconstruct the
  compiler nonemptiness premise; it does not assume source adequacy.
- Storage heap contents imply the old keeps/freshness fields through existing
  theorems. Word upgrade needs the full represented allocator witness;
  merely `cost < W` is insufficient. Both word roundtrips preserve code and
  witness data. Root equality/gap transport remain separate companion obligations.
- BoundaryLink consumes Rep with a fixed nextBase; MappedBoundaryLink consumes
  the SAME selected midBase. `mapped_output_iff` gives an existential map,
  not equality to a chosen map. No unconditional link equivalence is proposed.
- Fixed room uses `max 1 count`; dynamic room uses live heap length plus one.
  A shared success-conditional schema must retain the actual indexed reference
  and its cost, including vacuity when path resolution fails. These room
  predicates are not interchangeable.

## Verification boundaries and resource policy

Per-file Lean MCP tools were unavailable after tool discovery. Standalone
controls use bounded direct Lean CLI checks with explicit `-j1`,
`LEAN_NUM_THREADS=1`, `--tstack=131072`, 12 GiB hard Docker memory limit,
zero container swap, and a monitored 4 GiB enclosing-VM/host reserve. Heavy
checks are serial under the repository writer lock; no systemd-run, swap/cap
increase or maxHeartbeats change was used.

Refactor slowdown warning was given before any source change. Speed-motivated
history and Gate G0 were inspected. Only a baseline can be recorded while
production is held; a matched before/after comparison and the >10% stop rule
remain required when actual migration occurs. No performance pass is claimed.

Actual toolchain: Lean 4.24.0 (797c613eb9b6d4ec95db23e3e00af9ac6657f24b),
Lake 5.0.0-src+797c613. KeySort prerequisite uses its actual dependency-free
source. This prerequisite is not full affected-module or runtime acceptance.

The first dependency probe is INVALID: missing Python inside the minimal image
produced an empty command-substitution loop and exit zero without work. Its raw
receipt is retained and never counted as a proof pass. The explicit 158-module
queue then built current imports, but the initial runner lacked complete
provenance/cleanup/sampling; its receipt is preliminary only. Hardened gate
receipts supersede it and validate exact target completion markers, source and
artifact hashes, actual process serialism, cleanup and container exit/OOM state.

Standalone theorem checks establish only the listed Lean contract conversions
and arithmetic/schema facts. They do not prove compiler/source adequacy,
production consumer wiring, whole-program emitted-code capacity guards, producer root/gap adequacy,
or whole-assignment completion. Separate root/gap obligations do transport
across the exact V2 word roundtrip; they are not manufactured from a basic
certificate. External native/source-runtime tests have not
been substituted for Lean proofs.

## Independent reviews

Read-only finder and skeptic preparatory reviews used no Lean, server, builds,
tests or writes. Both rejected unconditional V1/V2 equivalence, fixed/chosen map
identification, and fixed/dynamic cost identification. Both required original
peak and allocator witness retention. Finder also identified masked shell
failure, missing interruption cleanup, incomplete source provenance and absent
actual process validation in the first runner; these were fixed and independently rereviewed.

Final standalone review findings, fixes and receipts are appended below.
Full-scope Terra acceptance remains pending together with production migrations;
a preparatory review is not that acceptance. No Terra full-scope attempt has
been represented as successful.

## Handoff and artifacts

Raw bulk evidence and cache packs stay off Git under
`/workspace/scratch/h55-interface-pairs/`; a committed SHA256 manifest binds
the sealed evidence/cache artifacts. No `ship-cache.sh`, push, merge, PR, goal
reset/duplication or empty result-marker commit is authorized or performed.
The final external handoff records the full committed head, patch/bundle paths,
checksums and pending obligations. The entire assignment remains unfinished
pending the actual owner handoff, production migrations, matched performance,
full affected-module/control gates and full-scope acceptance.

## Sealed standalone checkpoint

The final queue contains 259 modules (the historical 158- and 257-module receipts
remain archival). All final gates pass using the final runner and exact recorded
source/artifact hashes:

| Command suffix to `python3 -B scripts/h55/interface-pairs/bounded.py` | Result | Wall |
|---|---|---|
| `inputs` | PASS | 39.686s |
| `runtime` | PASS | 2.478s |
| `acceptance` | PASS | 3.009s |
| `baseline` | PASS | 22.169s |

The final direct Lean check passes 22 manual axiom reports, using only propext,
Classical.choice and Quot.sound (some use none), with no new axiom/sorry. The
259-module replay uses current artifacts; it is not claimed to recompile them
all. Direct standalone controls are rechecked by Lean, not served from a test
module cache. Exact commands, source hashes, outcomes and decisive output are
in `evidence/gates.json` and the referenced raw logs/receipts. Final observed
minimum headroom exceeds 11.38 GB, above the required 4 GiB reserve; sampled
process observations and structural serial queue evidence are distinct.

Both independent read-only reviews cleared the final standalone scope after
confirmed fixes; their findings and fixes are saved in `evidence/reviews.txt`.
The same-map premise in a standalone conversion is not authorization to add
an assumed premise to production consumers. An owner must derive it from the
existing domain or retain the map policy.

The pre-migration baseline has 27 measurements, three per each of nine input
files. `evidence/baseline-summary.json` records all values. There is no
post-migration performance result because production inputs remain unchanged.
The greater-than-10% slowdown stop rule is still binding.

No full-scope Terra attempt has occurred. Full affected-module/default/control
gates, production root/gap adequacy and matched performance at the migrated
head remain pending. The goal is blocked on CoordinatorLeaseNotice after
completing this useful standalone backfill, not complete and not paused for H58.

Artifacts are sealed in `/workspace/scratch/h55-interface-pairs/`. The committed
`tests/h55/interface-pairs/BULK.sha256` binds the off-git evidence archive and
Lake cache pack. The external final handoff records full head and final exports.
