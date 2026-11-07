# SOL-PC: optional B16 precompile agreement

Status: **bounded proofs and local acceptance implemented; central registration
and full repository validation pending**. No full B16, G51, G47 or
RUNTIME_GATE_PASS claim. Original base
`b6ba0696102a7a038afe2ed333c09dff397cc5b2`; assigned branch
`codex/solidity-sol-20261103/precompile-agreement`, repository
`/workspace/solidity-lean`. Published dependency `8495f1deb0a95dd6b9301822d8649ab76b217681`
was adopted in `095dfb1fdb69ec5dbff4adcee18aac7438b48232`. The proof checkpoint is
`b25eb32497033bac6c4085872df21e8de9c4baa1`; publication `f77cf60d3cea8f7f1db8db29cc027532b0cd3fce`
is now adopted in merge `8c93d6ed6e9270aa19d965b857559c37c08fb3d8`.

## Current queue and acceptance

| Work item | Current result | Evidence / remaining work |
|---|---|---|
| All 18 address/gas/length/malformed rows | Complete pinned scope inventory | `inventory.json`: actual address/dispatcher checks, 75 unchanged input hashes, theorem and fixture map. |
| Arbitrary-length IDENTITY output and charge | Kernel proofs pass | `Identity.lean`: complete success/failure tuples, preserved successful account map/substate, exact gas, exact/one-short and unrepresentable-cost boundaries; no length-zero restriction. |
| All common algebraic rows | Kernel proofs pass | Addresses 1–4, 6–8, 10; BLAKE2F at size ≥4 or zero header. All word-rounding classes, general big-endian header/padding law, actual vendor error flags and full-consumption controls. |
| Fork/representation backfill | Exact counterexamples recorded | MODEXP empty minimum and 1025-byte bound mismatch; 33-byte input conversion truncation. BLAKE2F short-header mismatch. No producer/vendor changes or crypto premise. |
| Boundary tests, trust, scope checker | Local gates pass | 69 public theorems, 82 explicit public declaration axiom pins, 204-declaration audit, 143 mapped pinned core `#guard`s and 27 additional computed boundary `#guard`s; 32 Python mutation tests. |
| Final repository gates / integration seal | Pending central integration | Five generated-root imports, five area rows and 82 central axiom inventory entries are intentionally proposed, not written. `run-lean.sh --bridge` stops at stale roots; central axiom gate reports 0 errors / 82 unrecorded pins. |

`Bridge/tests/precompile-agreement/required-coverage.json` is the reviewed
address/theorem/fixture map. `Acceptance.lean` imports/checks every public
name. `Axioms.lean` pins the actual reported sets; all are subsets of
`propext`, `Classical.choice`, `Quot.sound`. `AllDeclarations.lean` also audits
private/generated declarations. Nothing assumes crypto implementation equality.

Run the local acceptance gate after the pinned inputs are available:

```sh
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1
python3 Bridge/tests/precompile-agreement/verify.py
python3 Bridge/tests/precompile-agreement/test_inventory.py
python3 scripts/check-precompile-agreement.py
```

`verify.py` holds the checkout writer lock, runs one Lean process at a time
with `-j1 -M11264 --tstack=131072`, and enforces ≤12 GiB RSS, zero process
swap and ≥4 GiB available reserve through `run-file.py`. The receipt binds
all proof/acceptance sources, input pins, exact commands, working directories,
resource outcomes and logs. The Python checker validates that saved evidence;
it is not itself a kernel or external EVM test. The exact 45-source logical
input closure and one success per command are mandatory. Duplicate/omitted
inputs, swapped logs, wrong working directories, late failure footers, missing
proofs, unsupported promotion and success-only malformed gas claims reject.

The initial mutation run exposed an unknown-address `KeyError`; it is fixed,
and its raw failure is retained in `evidence/mutations-first-failure.log`.
The final 32 tests pass (`evidence/mutations-final.log`). Independent finder
and skeptic reviews also found/fixed exact-build-record, log-source, footer
and working-directory evidence gaps; their final re-reviews report no remaining
confirmed findings (`evidence/proof-reviews.md`).

## Proof and computed-test boundaries

The agreement proofs import the actual pinned vendor precompile module.
IDENTITY's output/frame/gas result is general over arbitrary byte arrays,
account maps, substates and supplied gas. Other crypto rows prove numeric
charging against the actual vendor success flag; they do not infer successful
native verification from core validity. SHA/RIPEMD/ECREC affordability laws
cover all inputs, including their vendor successful-empty-output behavior.

BLAKE2F's all-length `blake_padding` states the actual relation between
right-padded core headers and unpadded vendor headers; `blake_gas` and
`blake_zero_gas` cover every price-common domain. The generic malformed-size law and
flag-2 error law consume all supplied gas. Controls include all
0/1/2/3/4/212/213/214 lengths, final flags 0/1/2, endian-sensitive headers,
rounds−1/rounds/rounds+1, nonzero bytes and word/pairing boundaries.

Core cryptographic valid/invalid vectors are computed tests, not new kernel
crypto equality proofs. In particular valid point-evaluation vectors and
bad-proof/versioned-hash controls are the exact pinned `PointEval.lean`
`#guard`s mapped by line/hash and freshly executed in the 45-input build.
Additional computed vectors cover unsupported address length classes, field
bounds, invalid G1/G2 subgroups, MSM discount 1/128/129 boundaries, and P256
r/s bounds. Unsupported addresses 11–17 and 256 remain open against the vendor.

The vendor subprocesses have logical default bodies and separate native
implementations; `ffi_logical_mismatch` records why logical stub success is
not native curve validity. No subprocess or opaque compression/hash output
is equated to core crypto. A supplementary native MODEXP output attempt failed
on missing external `ffi.ByteArray.zeroes` / `memset_zero` symbols. Both the
original `BoundaryVectors.lean` attempt (despite its subsequent printed marker,
`EXIT=1`) and the isolated `NativeModexpProbe.lean` attempt are preserved.
The passing suite excludes that open native probe. The kernel-proved
`modexp_base_truncation` states exactly the input conversion counterexample
and core output, not a vendor native output theorem. Failed direct-output
proof attempts remain in the diagnostic logs; no budget was raised.

## Cache setup now cleared

The historical missing `Mathlib.Data.Nat.Log` blocker below is resolved.
Received pinned archives were extracted serially using existing `leantar`,
without rebuilding Mathlib or changing any revision. Evidence includes the
898-key requested cache manifest and the 168-key Batteries supplement (with
possible overlap), archive SHA-256 manifests, extraction commands/outcomes,
and `pinned-input-build.log`. All 45 actual core/vendor inputs compiled
successfully, executing their existing core vectors. The largest recorded
input-build RSS is below 1.3 GiB; proof checks remain below 0.4 GiB.

Actual toolchain: Lean 4.24.0, commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`; Lake `5.0.0-src+797c613`.
`Solidity/KeySort.lean` passes fresh `lean -j1 -M11264 --tstack=131072`
with `EXIT=0` (`evidence/KeySort-kernel.log`). This does not turn the held
full repository gate into RUNTIME_GATE_PASS. No goal was created/reset or
marked complete. `get_goal` is unavailable in this tool catalog.

## Pending central registrations

`Bridge/tests/precompile-agreement/registration-proposal.json` contains
five imports for the generated Bridge root, one area row per new module
(proposed `docs/module-map/precompiles.md`), all 82 exact central axiom entries,
and importing-consumer test commands. The task's exclusive-write/H21 hold
forbids lane edits to generated roots, area maps and shared axiom registries;
central integration must apply them and rerun the full repository/Bridge gates.
No core dependency on Bridge is introduced. H16 Source and frozen Core ExtCall
remain untouched. SignedMod helper `584d34226053a12ae8e7cf82f58da44c177b54c5`
and its separate worktree/evidence remain preserved; its three modules already
landed and are not duplicated here.

## Historical records

The sections below preserve earlier source-only/cache-blocked observations;
they are not the current acceptance status.

## Exact reference and boundaries

The vendor is EVMYulLean `047f63070309f436b66c61e276ab3b6d1169265a` with
its existing documented compatibility/H7 patches. `inventory.json` pins actual
core files, Bridge manifest, vendor source closure and provenance by SHA-256;
the upstream vendor checksum gate remains authoritative. No vendor/pin edits.

The actual precompile definitions are in
`Bridge/vendor/EvmYul/EVM/PrecompiledContracts.lean`; the dispatcher in
`Bridge/vendor/EvmYul/EVM/Semantics.lean` has arms 1–10 only. BLS addresses
11–17 and P256 address 256 are unsupported at this pin, not shared rows.

* MODEXP is a fork mismatch: core minimum 500 and EIP-7823 length bound
  1024, vendor minimum 200 and no such bound. Empty input already gives
  gas 500 versus 200 by reading the definitions. Vendor converts the base
  through UInt256. No universal MODEXP equality is proposed.
* BLAKE2F uses right zero padding in core `readNat d 0 4`; vendor prices
  `fromByteArrayBigEndian (d.extract 0 4)` without padding. For byte `[1]`,
  these are 16777216 and 1. That malformed length fails both implementations,
  so price-formula equality must not be confused with charged-gas equality.
  With 213 bytes, the header domains coincide. The actual vendor runner
  uses `ffi.BLAKE2`, not the similarly named subprocess `BLAKE2_F` wrapper.
* BN_ADD/BN_MUL/SNARKV and point evaluation invoke Python wrappers via
  `totallySafePerformIO`; its kernel body returns `Inhabited.default`,
  while `implemented_by unsafePerformIO` invokes native IO. Their returned
  values and error behavior cannot be equated to core crypto by assumption.
  RIPEMD160 likewise uses a subprocess. SHA256 and BLAKE2 compression are
  opaque extern functions. No cryptographic equality premise is introduced.
* Vendor insufficient gas returns false, empty account map, zero remaining
  gas, unchanged substate and empty output. Crypto-error branches may also
  consume all gas after a sufficient-gas check. A common gas formula alone
  does not assert that every malformed call deducts only that formula.

## Historical setup blocker and exact cache request

Actual tools: Lean 4.24.0 commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`; Lake
`5.0.0-src+797c613`. Source `/workspace/.setup/activate.sh`, then explicitly
set `LEAN_NUM_THREADS=1` (activation defaults to 4). Initial VM: 17 GiB,
16 GiB available, no swap. Cache tooling used `ulimit -v 12582912` and
explicit Lean `-j1`; writer lock is
`/tmp/solidity-lean-feature-groups-20261025/writer.lock`.

The existing Mathlib cache is incomplete: no `Mathlib/Data/Nat` artifacts.
Restoration command, run in Bridge:

```sh
lake env .lake/packages/mathlib/.lake/build/bin/cache get Mathlib.Data.Nat.Log
```

Result: exit 1, attempted 334 / downloaded 0 / failed 334,
`CONNECT tunnel failed, response 403`. The missing `auto` source checkout
was restored at its unchanged manifest revision before that request.
No Mathlib rebuild, network bypass, vendor update or repin was attempted.

The committed environment utility
`Bridge/tests/precompile-agreement/CacheRequest.lean` imports only the already
compiled pinned Cache tooling. It does not import/compile Mathlib and contains
no theorem. Its successful serial run generated the exact 898 archive names
in `Bridge/tests/precompile-agreement/evidence/cache-request.tsv`, covering
all direct Mathlib imports in EvmYul and Conform and their cache closure.
These are Mathlib cache keys, not artifact SHA-256 digests. Host transfer must
retain the pinned package revisions and provide the artifact checksums too.
The coordinator's `xfer-mathlib-ae` transfer is not present on this VM.

**Q-CACHE [setup; H23 cache authorization]:** How should the exact pinned
cache closure in `cache-request.tsv` be supplied?

1. Transfer the matching coordinator `xfer-mathlib-ae` artifacts and checksum
   manifest to this VM: permits resuming kernel validation with unchanged pins.
2. Restore supported proxy access to the existing Azure cache endpoint:
   permits the pinned cache client to download the same closure.

Neither option authorizes rebuilding Mathlib, changing statements or changing
vendor pins. No design decision is required for rows already assigned to
remain unsupported/fork/FFI-open. `get_goal` is absent from the tool catalog;
the existing goal was neither recreated nor reset.

## Gates and review handoff

Evidence directory: `/workspace/solidity-lean/Bridge/tests/precompile-agreement/evidence`.

| Command | Outcome |
|---|---|
| `python3 scripts/check-precompile-agreement.py --inventory-only` | PASS: 18 unique source addresses, actual vendor dispatch/definitions and hashes. |
| `python3 Bridge/tests/precompile-agreement/test_inventory.py` | PASS: 12 tests including omission of each address, duplicate/address mutations, changed/missing hash, invented proof and hidden unsupported row. |
| `python3 scripts/check-precompile-agreement.py` | Expected exit 1: theorem/fixture mapping, kernel proofs, axiom pins and final gates pending. Not an acceptance pass. |
| Serial cache hash utility | PASS, 898 cache archive keys; see environment evidence for command. |
| `lake env lean -j1 --tstack=131072 Solidity/KeySort.lean` then frozen `solkeycheck` | PASS, exit 0: 377 taclets, all 131 read-bearing annotations covered/matched; `evidence/keysort.log`. |
| `(cd Bridge && sha256sum --check vendor/EvmYul/SHA256SUMS)` | PASS, exit 0; `evidence/vendor-checksums.log`. |
| Actual-vendor Lean proof gates | PENDING: missing pinned Mathlib cache. |
| `./run-lean.sh --bridge`, kernel/trust/axiom acceptance | PENDING: no final runtime pass claim. |

Separate read-only finder and skeptic reviews completed for the source
inventory milestone; neither used Lean or a Lean server. Finder confirmed the
18 source observations and found weak address/definition and core-module checks.
Skeptic independently found the mapping issue, missing closure-pin enforcement,
and `parseArgs` dropping the first cache root. All were fixed. The reviewers
confirmed the corrections and 12 passing Python tests; skeptic independently
checked all 20 direct Mathlib roots appear in the 898-key request. Both approve
only the source inventory, with kernel proofs, EVM controls and final acceptance
explicitly pending. See `evidence/reviews.md`. Any new modules' central root/module-map
registration is deferred to H21 integration; no central files are changed.

## Published dependency adoption

Coordinator publication `059eb83d4e1d494f42c532513ffbcd3e65adaf75` was
fetched from origin/master and adopted on this same lane branch by merge
`2ee2266425da6b950a1731103289e71f97902299`. Its parents preserve the
sealed lane head `f99245421406baa70a89f1015e393f19fe56ea19` and the exact
published commit. The original assignment base remains unchanged in the lane
report. No lane work was reset or discarded; no push or default-branch merge.

Read `integration-20261103-checkpoints.md`: this lane is not among the imported
checkpoints, and no lane-specific precompile integration document is present.
All pinned precompile inputs and this lane's payload were byte-identical after
adoption. Inventory-only check, 12 Python mutation controls, and the original
19-file seal verification passed again. This is not a new kernel or runtime
pass; the earlier KeySort evidence is historical, not a post-merge full build.

H24's declaration-graph companion supplies no concrete P8 inhabitant and does
not change this optional B16 task's premises or add a new producer dependency.
H16/H19 and Core ExtCall freezes remain binding. The coordinator announced the
master Lake/Mathlib transfer separately; `Mathlib/Data/Nat/Log.olean` is still
absent on this VM. No cache retry, rebuild or new proof composition was attempted.
The existing Q-CACHE request is pending that transfer; no new decision is asked.
The original sealed handoff remains historical evidence for its payload commit.

Separate read-only dependency-adoption finder and skeptic reviews both passed
with no findings and without Lean/server use. They confirmed exact merge parents,
unchanged precompile inputs, passing inventory/12 controls and the retained cache
blocker. Evidence and current handoff: `evidence/dependency-adoption.md` and
`evidence/dependency-adoption-gates.log`.

## Published dependency adoption, 2026-11-04

Adopted exact origin/master `6f3eedf0788ee1f8a3bcf230558c712ecdca04d5`
via merge `46a0d1cbd77dd0a5fb7cece924b4c277c1f0ccc2`, preserving prior lane
head `465a25548d51b7485fdfd988cff717019d2a97bd`. Relevant precompile inputs
are unchanged; this published increment contains no precompile lane artifacts.
Source inventory, 12 controls and `register.sh --check` pass. Generated roots
were already current; no new roots, module-map rows or composition were added.
Separate read-only finder/skeptic adoption reviews pass without findings or
Lean/server use. Coordinator-reported full integration passes are not a local
runtime gate or B16 proof. Mathlib delivery remains separately pending, and
`Mathlib/Data/Nat/Log.olean` is still absent. No original obligation is discharged
by this adoption. Current handoff and evidence: `evidence/dependency-adoption-20261104.md`
and `evidence/dependency-adoption-20261104-gates.log`. No new question is raised.

## Published selected-module delivery, 2026-11-04T122441Z

Adopted `b419c3cf4f642ae519b66bebc26cdf2f7cf93574` on the original branch via
`e98653edc48f5e9c3b81f4cbc09102bf64d79b8b`, preserving the original lane head.
Its three SignedMod modules exactly match helper `584d34226053a12ae8e7cf82f58da44c177b54c5`.
The helper branch/worktree, tests, axiom consumer, raw failures and bundle remain
preserved separately and are not all claimed imported. Read the published
`integration-20261104T122441Z-precompile-agreement.md` for the bounded delivery.

Both independent read-only adoption reviews pass without findings or Lean/server
use. Precompile inventory/12 controls, generated roots and central axiom inventory
pass locally; coordinator-reported full publication gates are not a local full
B16 acceptance. Original precompile inputs are unchanged and Mathlib Log.olean
is still absent. No original proof obligation is completed by these unrelated
partial producer/interface deliveries. All original queue/holds remain binding.
Current adoption handoff: `evidence/dependency-adoption-122441.md`; exact gate
commands/results: `evidence/dependency-adoption-122441-gates.log`.

## Published dependency adoption, 2026-11-04T182351Z

Adopted exact publication `89373e34cdfd6bb5db7054b1c204d01edffc5fa7` via
`abd77535e8ec11e45f642ce30a8f44c9603e7ecf`, preserving original work and
helper snapshot `584d34226053a12ae8e7cf82f58da44c177b54c5`. Relevant precompile
inputs and SignedMod modules are unchanged. Inventory/12 controls, roots and
central axiom inventory pass; both independent read-only adoption reviews pass
without findings or Lean/server use. No new composition or local full-build
claim. Original Mathlib transport and all unfinished precompile proof/final
obligations remain pending. Receipt: `evidence/dependency-adoption-182351.md`;
commands/results: `evidence/dependency-adoption-182351-gates.log`.

## Published dependency adoption and sealed proof handoff, 2026-11-05

The proof payload was committed before fetching/adopting the next publication.
The merge has exact parents `b25eb32497033bac6c4085872df21e8de9c4baa1` and
`f77cf60d3cea8f7f1db8db29cc027532b0cd3fce`. All 75 pinned inputs, repository instructions
and owned payload bytes are unchanged; master contains no competing precompile
implementation. Both independent read-only adoption reviews pass without
findings or Lean/server use. No global cache freshness follows from adoption.

Post-adoption serial kernel/consumer/vector/pin gates pass again, as do all
32 mutations, scope evidence, trust scan (3938 sources, 0 findings), document
paths and fresh KeySort. Central gates remain held: five root imports/five
area rows, and 82 unrecorded axiom entries with zero axiom errors. The actual
full gate stops before its build at stale generated roots. No protected shared
registration edit, full Bridge build or RUNTIME_GATE_PASS is claimed.

Current commands/timings/outcomes: `evidence/post-adoption-gates.json` and
`evidence/verify-post-adoption.log`. Handoff: `evidence/HANDOFF-proof.md`.
The committed original patch is `evidence/original-proof.patch.log`; its target
is the proof payload, relative to the original assignment base, restricted to
the four owned paths. Metadata added by this seal is separately committed.
`evidence/SHA256SUMS` is the current canonical file manifest;
`evidence/SHA256SUMS-inventory` preserves the historical source-only manifest
(which applies to its historical committed snapshot, not the revised files).
The final seal head is recorded in the result report and generated artifact
receipt; the handoff records the exact proof and adoption heads.

## Published dependency adoption, 2026-11-05T1422Z

Adopted publication `8bf8321873befa3f35ca31e97e5339a1baee93e6` via merge
`f24960a1fafc195e7d5320ad7bb6060fd5d6f429`, preserving the original lane
and separate Exp packet. Five precompile modules and all 75 input pins are
unchanged. Independent read-only finder/skeptic adoption reviews PASS, no
findings or Lean/server/build use. Fresh scope/kernel-evidence checker and
roots pass. Central axiom inventory remains EXIT1: zero errors and 164
unrecorded changes; coordinator-owned registration and full local validation
remain pending. No original obligation or whole-lane completion follows.
Exact commands/results: `evidence/adoption-8bf.json`; handoff and current
adoption manifest: `evidence/HANDOFF-adoption-8bf.md` and
`evidence/SHA256SUMS-adoption-8bf`. Historical proof seals are preserved.

## Published dependency adoption, 2026-11-05T1608Z

Adopted `3ad22f66d8fc6431378c22e71823436c79dede7f` via merge
`e2c6faef3edce821b636ec01c42ccc518bcbe172`, preserving the previous lane head
and separate Exp packet. All five precompile modules and 75 pins are unchanged.
Independent read-only finder and skeptic adoption reviews PASS without findings
or Lean/server/build use. Fresh bounded scope/kernel-evidence and roots checks
pass. Central axiom inventory remains EXIT1: 8279 pins, zero errors and 164
unrecorded changes. Coordinator-owned registration and full local validation
remain pending. No whole-goal or runtime-gate completion is inferred.
Exact commands/timings/results: `evidence/adoption-3ad.json`; handoff and
checksums: `evidence/HANDOFF-adoption-3ad.md` and
`evidence/SHA256SUMS-adoption-3ad`. Previous proof seals and raw failures remain
preserved. No new composition, shared registry write or ship-cache.sh run.

## Requested rebase onto e6849d3b, 2026-11-05

Rebased onto `e6849d3bdf516099d20c33d3581d523449764018` without conflicts,
producing payload `00582aeac545d9708994deae0ed096d6abaeef2d`. Backup branch
`codex/solidity-sol-20261103/precompile-agreement-before-e684` preserves
`e809a8b9b3202bb8f025de9c805aba0bcab5b03c` and original history. All owned
payload files and 75 pins are unchanged. Separate read-only finder/skeptic
reviews PASS, no findings or Lean/server/build use. Scope/kernel evidence and
roots pass. Central axiom inventory EXIT1: 8763 pins, zero errors and 643
unrecorded changes; these are not all attributed to this lane. Original final
registration/validation obligations remain pending. Exp remains separate.
Exact commands/results: `evidence/rebase-e684.json`; handoff and checksums:
`evidence/HANDOFF-rebase-e684.md` and `evidence/SHA256SUMS-rebase-e684`.
No whole-goal/runtime completion or cache freshness is claimed.

## H70 DEP-BRIDGE-435 environment receipt, 2026-11-06

The external audit-precompiles owner relay at
`13ae4273bad4123baea9347dfa724ded432dfd57` (not reachable in this checkout)
requests Bridge dependency evidence. On the unchanged frozen v4.24 setup,
all 11 installed git packages match the Bridge manifest. The Mathlib Log
artifact exists. Owned `H70BridgeProbe.lean` imports it, the actual vendored
precompiles and existing IDENTITY proof; the bounded serial import/elaboration probe
passes in 4.744s. This proves neither installation in the requester worktree
nor v4.35 compatibility. Migration, RAW/BLS prerequisites and G43/V14's separate
compiler-success theorem remain with their respective owners. No frozen
configuration/interface/vendor/Source edit or re-pin was made.
Both independent read-only finder/skeptic receipt reviews PASS, no findings.
Receipt and handoff: `evidence/H70-bridge-receipt.json` and
`evidence/HANDOFF-H70-bridge.md`; exact command/output:
`evidence/H70-bridge-probe.log`; checksums: `evidence/SHA256SUMS-H70-bridge`.
Original whole-lane and validation obligations remain open; no goal reset or
completion, cache shipment or host relay is claimed.

## H44 reviewable evidence split, 2026-11-06

The five new raw log captures relative to held integration base
`b7c3cc5110b1ebee1eab45e8b1b9894ecada7237` are no longer tracked. Their original
absolute VM paths and all bytes remain intact. The logs total495449bytes; the
archive is30700bytes. Exact paths, individual sizes/hashes and archive location
are recorded in [H44-bulk-manifest.json](../../Bridge/tests/precompile-agreement/evidence/H44-bulk-manifest.json).
Only that small manifest is committed for the bulk. Existing Lean declarations,
proofs, deterministic generators, gates, budgets and small reviewable handoffs
are unchanged. Restore the archive at repository root when a fresh checkout
needs saved evidence; no gate is weakened to accommodate missing captures.
Historical evidence already present at the held base is unchanged. No full
build, cache shipment, scope expansion or goal transition occurs in this split.
The41ready core audit cases remain queued under the same original goal.
