# H62 item 4: generic Yul Views controls

Status: blocked partial implementation, not a completed checkpoint or assignment.
Branch: `codex/solidity-h62-4-20261106/generic-yul-views`.
Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Repository: `/workspace/solidity-lean`.
Export/handoff/evidence: `/workspace/h62-generic-yul-views/`.
The final committed head and artifact hashes are recorded in that directory's
`handoff.json` and `SHA256SUMS`; this document cannot contain its own commit hash.

## Scope and preserved originals

Writes are confined to this document and
`tests/h62/item4/generic-yul-views/` and
`scripts/h62/item4/generic-yul-views/`.
Every one of the 868 original `Solidity/Yul/Views/*.lean` files matches its base
Git blob byte for byte. No frozen statement, premise, exclusion, observation,
representation, generated root, central module map or axiom pin was changed.
No merge, pre-gate, push, publication or deployment was performed.
The clean older `work` branch remains preserved. The assigned branch was created
at the exact base after fetching it and verifying it is an ancestor of fetched
`origin/master`. No prior lane branch existed locally or remotely.

## Checkpoint 1: census (partial)

The deterministic lexical inventory covers all 868 Views modules, including
286 Controls modules. It records 9,929 declarations/guards: 6,271 theorems,
3,423 definitions, 29 abbreviations, 79 structures, 39 inductives, 2 named local
instances, 2 examples, 1 constant, 4 `#guard` and 79 `#guard_msgs` commands.
The Controls subset contains 3,026 theorems, 2,058 definitions, 5 abbreviations,
2 local instances, 4 guards and 79 message guards.

Every record retains the exact source statement prefix and SHA256, the command
body hash, separate expected-message comment/hash when present, source location
and a preserved/read-only/pending-owner disposition. Every file has a SHA256.
These are lexical source identities, not elaborated Lean statement hashes or
an enumeration of every conjunct/semantic branch. No observation was deleted:
whole-source blob equality provides the preservation boundary. A detailed
semantic classification and owner migration disposition remain open.

The supplied audit is `refactor-audit-20261106.md` (SHA256
`31ab16906906a9b22fd28700aacc72d2ee0ffe81cea723ae209eb28e5299286a`).
Items 9/11 describe analogous twin-file/helper/fixture techniques; their named
Backend/Evm targets are outside this lane. Item 16's table-plus-lemma technique
applies here; its Raw/vector generator work stays H55. No Raw/vector generator
was duplicated. All five coordinator input hashes passed their supplied manifest.

## Checkpoint 2: semantic packet and typed fixtures (partial)

`tests/h62/item4/generic-yul-views/GenericByteObjects.lean` introduces `ByteObjectFixture D`, `ByteObjectFacts f`,
and `byteObjectFacts f`. The latter is parameterized over arbitrary byte lists,
physical base addresses and residual memory, with the original length premise.
Its fields retain exact header, intrinsically typed bytes/string decoders,
all live payload positions, all outside bytes, the actual `ObjectByte` source
relation and idempotence. Its proof composes existing universal semantic laws;
it does not decide the table or introduce a new source language/state.

`tests/h62/item4/generic-yul-views/Fixtures.lean` contains seven typed rows: lengths 0, 2, 1, 31, 32, 33 and 64;
aligned/unaligned/zero bases and nonzero residuals. These are backfill, not
additional original cases or a completed migration of 3,026 control theorems.
Two candidates retain exactly the types of `ReadControls.byte_component` and
`ReadControls.byte_component_decode`. All original declarations remain intact.
The files contain `#print axioms` commands, but those outputs are NOT available:
the candidates have not compiled against the pinned migrated dependencies.
Static scanning found no added sorry, axiom, native_decide, trust shortcut or
raised proof budget. This is not a kernel axiom-set claim.

## Checkpoint 3: correspondence and acceptance (partial)

The two exact-type candidate instances and original declarations appear together
in the fixture module. It also references the existing crossing-slot refusal,
dirty-bool rejection and endian negative theorem unchanged. The remaining
negative/refusal inventory is preserved at the source level, not fully rerun.

Reproduce static acceptance from the repository root:

```sh
python3 scripts/h62/item4/generic-yul-views/acceptance.py \
  --inputs /workspace/h62-coordinator-inputs \
  --evidence /workspace/h62-generic-yul-views/evidence
```

This verifies all 868 base blobs and the exact file universe, reproduces the
inventory byte for byte, checks coordinator input hashes, runs seven adversarial
scanner controls and a cleanup regression (child ignores TERM), and scans the
additive Lean source for prohibited shortcuts. Its explicit result is
`STATIC_ACCEPTANCE_PASS`, never `RUNTIME_GATE_PASS`.
The 7.3 MiB inventory and reproduction are off git, with checksums.

## Checkpoint 4: measurements and runtime gates (blocked)

Official pinned archive: `lean-4.35.0-linux.tar.zst`, SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Lean reports 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`;
Lake reports 5.0.0-src+eb6cafb (Lean 4.35.0).
`lean -j1 --tstack=131072 Solidity/KeySort.lean` passed with exit 0,
no diagnostics, 1.564 s wall and 506,564 KiB max child RSS.
The earlier `/usr/bin/time` setup attempt failed because that binary is absent;
it is separately retained, never counted as a passing KeySort attempt.

The full gate used an off-git base-source snapshot at
`/workspace/h62-generic-yul-views/validation`, a fresh v4.35 cache and the same
`./run-lean.sh`. Only snapshot toolchain/Lake execution configuration changed:
cache disabled and explicit `-j1 --tstack=131072`; original source files remained
unchanged. A snapshot Git index was required by repository registration tools;
the initial missing-index setup failure is separately retained.

The actual run passed both layer checks (857 core modules, zero forbidden
paths), then compilation failed in unchanged `Hash/CollisionBound.lean:407`,
`:660`, `:680` and `Language/FixedPoint.lean:152`, `:170`, `:184`, etc.
Subsequent guard-message sorryAx output is fallout from failed base proofs,
not an introduced source axiom or a passing proof. The run was interrupted after
these failures: historical `full-gate.json` records exit -15, 75.839 s wall,
1,714,671,616 bytes peak sampled aggregate RSS. It is not a completed gate.
All members of its owned process group 1439 were verified quiescent.
Both the helper and original fixture depend on CollisionBound through
`Yul.Views.WordMemory -> Yul.Views.Bytes -> Roadmap.Contracts`.

The VM has a 16 GiB cgroup and no host swap. The bounded runner applies 12 GiB
per-process RLIMIT_AS, samples aggregate RSS against 12 GiB, and reserves 4 GiB
using the minimum of host availability and cgroup headroom. It enforces one
observed Lean process, 300 s per Lean process, and verifies owned-group cleanup.
No systemd-run was used. The old full-gate result predates runner cleanup fixes;
the later cleanup regression validates those fixes separately.

There is no valid before/after timing delta. After dependency relay, warm the
same dependency closure with the same pinned release, cache/resources and serial
flags; measure original ReadControls and the exact owner-overlay plus helper
under matched conditions, preserving logs for both. Include all affected
modules and table checking, not just the two small instances. Stop and report
if slowdown exceeds 10%. Then run the full affected gate and original negative
coverage. Do not count setup/failure timings as proof or performance results.

## Independent reviews and fixes

Independent finder `/root/finder` and skeptic `/root/skeptic` performed read-only
reviews without a Lean server, builds or fixes. Confirmed census findings were
fixed: guard expectations/attributes attached to wrong commands, quoted `where`
identifiers, fail-open empty roots, and two omitted named local instances.
Confirmed runner findings were fixed: surviving descendants after leader exit,
cgroup-aware headroom, and inaccurate hard-aggregate-cap labels. The cleanup
control kills a child ignoring TERM and verifies no live member remains.
Final handoff consistency reviews found no additional defect or overclaim.
Final reviews support an accurate partial/blocked handoff and grant no Lean,
full-gate, timing or completion approval. Review evidence is `evidence/reviews.json`.

## Typed blockers and exact resume actions

- `DEPENDENCY_MIGRATION_REQUIRED`: `Solidity/Language/FixedPoint.lean`
  (full-gate failure) still needs an owner relay. The initial Hash blocker is
  superseded by H70 below: its exact overlay was supplied and targeted checking
  passed in isolation; full affected validation remains pending. H70 also records
  the current Roadmap/Storage blockers. These originals remain outside our write
  scope; no local repairs were attempted.
- `OWNER_RELAY_REQUIRED`: VY2 exact-file agreement is still absent. No `relay.sh`
  exists in this checkout. The coordinator can retrieve this committed request:
  approve/apply a migration of `Solidity/Yul/Views/ReadControls.lean` and a new
  shared module Solidity/Yul/Views/H62ControlFacts.lean (proposed, not yet created), only after candidate
  Lean/axiom/timing checks pass. No absence of reply is treated as permission.
  The module-map registration row proposed for the owner is:
  `Solidity/Yul/Views/H62ControlFacts.lean | Typed byte-object control packet;
  arbitrary bytes, base and residual; exact header/payload/decoder/framing laws.`
  New generated roots/maps/pins must be registered by the owner/coordinator.

Resume on this original VM and branch with the existing persistent goal. Do not
create/reset a goal or launch a replacement thread. `get_goal` was not exposed;
the coordinator explicitly confirmed that optional inspection absence is not a
blocker. After dependency relay, compile/minimize both additive modules, inspect
real axiom outputs, complete semantic case dispositions/negative coverage,
prepare exact owner migration patches, measure matched before/after, and rerun
full gates. All four checkpoints remain unfinished. No human scope/exclusion
or premise decision is requested; the blockers require owner coordination.


## H70 Hash relay consumption (partial, still blocked)

The owner relay from `solidity-h62-6-20261106/migrate-hash`, head
`a3f49ee0ec1829e63022c90194048d5a1ffe0d22`, source `2a18afcd`, supplied the
CollisionBound overlay with SHA256
`3aebc61f1a1979d4e36d669e3c33f5ae8c848d38a3ca0574c62329bdc154bbff`.
That exact hash and patch applicability passed. The overlay was applied only to
the isolated validation snapshot; assigned-checkout originals remain unchanged.
Independent read-only finder/skeptic reviews found no statement/trust/budget
change; the finder compared all 91 lexical declaration signatures unchanged.

The bounded targeted `lean -j1 --tstack=131072 Solidity/Hash/CollisionBound.lean`
check passed, exit 0, 4.630 s wall, 610,770,944 bytes sampled peak RSS, one Lean
process and verified group cleanup. This resolves the earlier direct Hash
compile failure locally for this exact overlay, not its full affected gates.
The following bounded `lake --fail-fast build Solidity.Yul.Views.ReadControls`
failed, exit 1, 8.457 s wall, 724,402,176 bytes sampled peak RSS, one Lean process
and verified group cleanup. No retry, proof shortcut or budget increase followed.

New exact owner relay requests:

- `TRUST_GATE_STOP`: `solidity-h62-6-20261106/migrate-roadmap`,
  `Solidity/Roadmap/Contracts.lean:1104`, theorem
  `Solidity.Roadmap.PublicCorrectness.transfer`. The unchanged guard expects no
  axioms; v4.35 reports `propext`, `Classical.choice`, `Quot.sound`. Owner analysis
  and resolution under the existing trust policy are required. No permission to
  update a guard/pin, expand trust or bypass the stop is inferred.
- `DEPENDENCY_MIGRATION_REQUIRED`: `solidity-h62-6-20261106/migrate-storage`,
  `Solidity/Storage/HashedLayout.lean:376`, dependent elimination fails; downstream
  axiom guards at 417/420 also fail after the proof error. Relay a validated
  owner repair. This source remains outside this lane's write scope.

The Language relay for `Solidity/Language/FixedPoint.lean` and VY2 exact-file
agreement on `Solidity/Yul/Views/ReadControls.lean` and proposed
Solidity/Yul/Views/H62ControlFacts.lean are still pending. `relay.sh` is host-only;
its absence is not an installation task or an independent blocker.
The additive lemma and seven rows still lack real Lean/axiom/refusal validation;
no full gate, timing delta or checkpoint completion is claimed.
Saved evidence: `evidence/h70-hash-consumption.json`,
`evidence/h70-hash-overlay-check.{json,log}` and
`evidence/h70-views-dependencies.{json,log}` under the export directory.
