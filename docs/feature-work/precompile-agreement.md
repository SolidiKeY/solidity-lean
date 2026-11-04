# SOL-PC: optional B16 precompile agreement

Status: **blocked at cache setup; source inventory checkpoint only**. No B16,
G51, G47 or RUNTIME_GATE_PASS claim. Base
`b6ba0696102a7a038afe2ed333c09dff397cc5b2`; assigned branch
`codex/solidity-sol-20261103/precompile-agreement` in
`/workspace/solidity-lean`. The initial checkout was clean at the base, which
is an ancestor of the local published `origin/master` at `82e75b10`.

## Queue and coverage

| Work item | Status | Evidence / remaining work |
|---|---|---|
| 18-address source inventory | Reviewed source inventory recorded | `Bridge/tests/precompile-agreement/inventory.json`: address, core gas, length/framing, malformed behavior, actual vendor definition, external boundary, planned controls, explicit empty proof mapping. |
| Arbitrary-length IDENTITY output and charged gas | Pending, cache blocked | Must import actual `Ξ_ID`, bridge List UInt8/ByteArray exactly, prove success and insufficient-gas branches including account/substate frame and gas arithmetic without extra equality premises. |
| All common algebraic rows | Pending, cache blocked | Candidates: 1–4, 6–8, 10; row 9 header formula only where four bytes are present. Prove actual branch formulas, rounding, inhabited controls and malformed/insufficient-gas cases. |
| Scope-complete acceptance, kernel/trust/axiom gates | Pending | Default checker intentionally exits 1. No theorem acceptance gate implemented yet. |
| Authorized backfill | Source mismatch evidence recorded | MODEXP fork schedule/bounds, BLAKE2F short header and subprocess/opaque boundaries. No producer changes requested or made. |
| Final full validation and committed handoff | Pending | This is a blocked checkpoint, not completion of the work queue. |

Every row has `proof_status=pending` and `proofs=[]`. Control lists are **planned
classes**, not executed EVM fixtures. The Python mutation tests only test the
source inventory checker. It verifies coverage against `Precompile.address`,
vendor dispatcher addresses and definition names, and exact source hashes.
It does not prove formula text or behavioral descriptions. Those are reading-based
observations awaiting the required kernel proofs and independent review.

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

## Setup blocker and exact cache request

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
