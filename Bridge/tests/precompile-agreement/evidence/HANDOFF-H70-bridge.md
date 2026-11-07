# H70 DEP-BRIDGE-435 owner receipt

Request: audit-precompiles head13ae4273bad4123baea9347dfa724ded432dfd57.
Evidence source head70845978ab616a63b13d0dee8b31b28893ccf591, same original VM.
Frozen core/Bridge Lean4.24.0; Lake5.0.0-src+797c613. All11 installed git
packages match the frozen Bridge manifest; exact paths/heads/hashes in
H70-bridge-receipt.json. Previously missing Mathlib/Data/Nat/Log.olean exists.

Actual import probe imports Mathlib.Data.Nat.Log, vendor PrecompiledContracts
and the existing IDENTITY proof. It checks identity_run and identity_charged:
EXIT0,4.744s,peakRSS1562865664bytes,no resource stop. Actual command/log:
H70-bridge-probe.log; source ../H70BridgeProbe.lean. Serial Lean-j1,
LEAN_NUM_THREADS1,-M11264,zero swap,12GiB aggregate cap and4GiB reserve.
No Lean MCP diagnostic tool is available in this turn. The transient writer
lock directory was absent after resume; initial flock failed before edits;
the same documented lock path was restored before the actual run.

This establishes the installed v4.24 closure on this VM only. The requester
worktree installation and v4.35 import/migration compatibility are NOT proved.
No v4.35 toolchain is installed under this VM's configured tools directory.
Frozen pins, interfaces, vendor and Source files were not edited or re-pinned.
No dependency rebuilding, network/cache transfer, ship-cache.sh or host relay.
Migration toolchain/dependency delivery remains with migrate-bridge and the
coordinator. This receipt may support retrieval of the existing pinned setup;
v4.24 artifacts must not be relabelled as v4.35 artifacts.

OBL-SUCCESS remains with G43/V14; this receipt supplies no compiler-success
or Stipend theorem. DEP-RAW-435 and DEP-BLS-435 remain producer-owned. Original
whole-lane/central registration/full-validation holds and proof boundaries
remain unchanged. No goal created/reset/completed; get_goal unavailable.

Files for coordinator retrieval: this handoff, H70-bridge-receipt.json,
H70-bridge-probe.log, ../H70BridgeProbe.lean, and SHA256SUMS-H70-bridge.

Separate read-only finder and skeptic reviews PASS, no findings. Both
verified package heads/hashes and exact probe outcome against stated limits;
neither ran Lean/server/builds or edits. Final commit head is in CLOUDVM-RESULT.
