# SOL-PC bounded proof handoff

Status: PARTIAL overall; bounded implementation and local acceptance complete.
Central registration and full repository/Bridge gates remain required.
No full B16/G51/G47 or RUNTIME_GATE_PASS claim.

Repository: /workspace/solidity-lean
Branch: codex/solidity-sol-20261103/precompile-agreement
Original base: b6ba0696102a7a038afe2ed333c09dff397cc5b2
Proof payload head: b25eb32497033bac6c4085872df21e8de9c4baa1
Adopted publication: f77cf60d3cea8f7f1db8db29cc027532b0cd3fce
Full committed adoption head (seal parent): 8c93d6ed6e9270aa19d965b857559c37c08fb3d8
The metadata seal head appears in the CLOUDVM result and generated artifact receipt.

## Queue

1. Complete 18-address inventory: DONE, 75 input hashes pinned to original base.
2. Arbitrary-input IDENTITY/full frame/charged gas/all boundaries: DONE.
3. All common algebraic gas rows and common BLAKE header domains: DONE.
4. Scope checker/fixtures/trust/reviews/local acceptance: DONE. Central root,
   map and axiom registrations/full repository confirmation: PENDING.
Backfill: MODEXP minimum/bound/input-conversion and BLAKE short-header
counterexamples DONE; native output equality remains OPEN, not assumed.
SignedMod helper 584d34226053a12ae8e7cf82f58da44c177b54c5: DONE/preserved separately, clean; only its
three selected modules were previously integrated, no whole V09 completion.

## Proof and fixture coverage

Five new modules, 69 public theorems, 82 exact public axiom pins; all 204
private/generated/public declarations audited against only propext,
Classical.choice, Quot.sound. No new axiom, sorry, premise/exclusion weakening
or maxHeartbeats/maxRecDepth increase. No H16 Source/Core ExtCall/vendor edit.
The exact row/file/theorem/fixture map is inventory.json and required-coverage.json.
Acceptance.lean checks all public names. 143 pinned core #guards executed in
the fresh 45-input build; 27 additional computed core boundary #guards pass.
PointEval valid/invalid proof and versioned-hash classes map to its pinned
source vectors; these computed vectors are not kernel crypto equality proofs.
All 18 addresses are covered; vendor arms exist only for 1–10.

Gas proofs import actual vendor definitions. IDENTITY is arbitrary-length,
full-tuple and nonzero-byte inhabited. Crypto rows preserve actual success/
error charging; no malformed call is assigned a successful price unconditionally.
BLAKE header padding is proved at every length, gas on size>=4 or zero header;
malformed-size and flag-2 error laws are explicit. Unsupported 11–17/256 and
MODEXP fork remain open. No CALL/RETURNDATA/full adequacy claim.
Native subprocess/opaque crypto output correspondence is unproved. Logical
stub success is explicitly distinguished by ffi_logical_mismatch.

Both MODEXP native attempts fail missing ffi.ByteArray.zeroes/memset_zero.
The historical BoundaryVectors failure has a subsequent printed marker but
EXIT=1, so is not a pass. The isolated NativeModexpProbe also actually fails.
The passing suite excludes that open probe. Kernel modexp_base_truncation
proves exactly the source result and input conversion, not vendor output.
Raw failed direct-output reductions and all original cache failures remain.

## Commands and decisive outcomes

Actual Lean: Lean (version 4.24.0, x86_64-unknown-linux-gnu, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Release)
Actual Lake: Lake version 5.0.0-src+797c613 (Lean version 4.24.0)
LEAN_NUM_THREADS=1; every kernel check -j1 -M11264 --tstack=131072, serial,
<=12 GiB RSS / zero swap / >=4 GiB available reserve. MCP final worker
arguments also explicitly carry -j1/-M11264; no systemd-run/swap used.

- python3 Bridge/tests/precompile-agreement/build-inputs.py: PASS 45/45,
  raw pinned-input-build.log contains exact commands/source hashes/timings.
  Mathlib archives extracted, never rebuilt/re-pinned. Missing Log blocker cleared.
- python3 Bridge/tests/precompile-agreement/verify.py: PASS post-adoption;
  all five modules and importing consumer/vector/pin/audit files EXIT=0.
  See verify-post-adoption.log and exact per-file *-kernel.log commands/timings.
- python3 Bridge/tests/precompile-agreement/test_inventory.py: PASS 32 tests,
  9.308 s post-adoption. Omission/duplicate/wrong CWD/log-swap/footer controls included.
- python3 scripts/check-precompile-agreement.py: PASS 18 rows, exact-source-bound evidence.
- bash scripts/check-trust.sh: PASS 3938 sources, 287 inventoried sites, 0 findings.
- lean -j1 -M11264 --tstack=131072 Solidity/KeySort.lean (via lake env):
  PASS EXIT=0, 1.109 s, peak RSS 45613056 bytes.
- sha256sum --check vendor/EvmYul/SHA256SUMS (cwd Bridge): PASS, unchanged pin.
- ./scripts/check-doc-paths.sh: PASS all references resolve; existing
  ambiguous basenames are warnings, not a strict-mode pass claim.
- sha256sum --check evidence/SHA256SUMS: PASS final file manifest;
  checksum-check.log and generated artifact output record verification.
- git apply --cached --check original-proof.patch.log against an isolated base
  index: PASS; checkout and real index unchanged.
- ./run-lean.sh --bridge: EXIT=1 / HELD, five missing generated root imports;
  its build and final native/runtime gates were not reached.
- python3 scripts/coord-tools/module-map.py f77cf60d3cea8f7f1db8db29cc027532b0cd3fce: EXIT=1 / HELD, five rows.
- node scripts/check-axiom-pins.mjs: EXIT=1 / HELD, 0 errors / 82 unrecorded pins.
  Proposed exact entries/imports/rows are in registration-proposal.json.

See post-adoption-gates.json for every checkpoint command, timing, exit and
absolute evidence path. Do not reinterpret the three central holds as passes.

## Reviews and outstanding work

Separate read-only finder/skeptic proof, acceptance, doc and adoption reviews
PASS after fixes, without Lean/server use. Exact fixes/verdicts are recorded
in proof-reviews.md and adoption-reviews.md. No remaining confirmed finding.

Coordinator integration must register five root imports/five area rows/82
axiom entries, then run the full repository/Bridge gates. Exclusive writes
prohibit lane edits to these shared files; concrete proposal is complete.
No fresh global cache claim follows from coordinator notices or this packet.
get_goal is unavailable; no goal created/reset/completed or competing continuation.
No push/PR/default-branch merge performed.

## Saved artifacts

Original owned patch, base -> proof payload: /workspace/solidity-lean/Bridge/tests/precompile-agreement/evidence/original-proof.patch.log
Committed handoff: /workspace/solidity-lean/Bridge/tests/precompile-agreement/evidence/HANDOFF-proof.md
Evidence directory: /workspace/solidity-lean/Bridge/tests/precompile-agreement/evidence
Canonical checksums: /workspace/solidity-lean/Bridge/tests/precompile-agreement/evidence/SHA256SUMS
Generated archive/receipt after metadata seal: /workspace/solidity-lean/Bridge/tests/precompile-agreement/artifacts
Historical source-only manifest: /workspace/solidity-lean/Bridge/tests/precompile-agreement/evidence/SHA256SUMS-inventory

The exact raw Git patch is named .patch.log because it contains captured
compiler output; the existing documentation checker excludes .log captures.
No scanner rule or raw failure text was changed.
