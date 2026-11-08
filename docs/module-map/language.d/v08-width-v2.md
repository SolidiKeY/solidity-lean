| `tests/h62/item4/generic-v08/IntrinsicWidthsV2.lean` | Explicit-mapFree fixed-bytes width consumers; isolated checker `scripts/h62/item4/generic-v08/check-width-v2.sh`. Frozen v1 headers remain unresolved; this test proves no historical correspondence or execution adequacy. |

Run the v2 checker with `--toolchain TOOLCHAIN_ROOT --output FRESH_ABSOLUTE_DIR`
outside the checkout. It explicitly requires master Lean4.24.0 commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`; ambient Lake is not used. The frozen
v1 `reproduce-width.py` keeps its separate Lean4.35.0/archive pin unchanged.
The existing `bounded.py` runs every local import and the v2 test with `-j1`,
H232 cloud-VM isolation, a12GiB host reserve,
plus the existing address-space and sampled-RSS diagnostics, and a shared
300second execution deadline. No pass is accepted after the observed deadline;
monitor sampling is0.25seconds and failed-check termination has up to5seconds
grace. Runtime monitor exceptions/signals fail closed and clean the child
process group. Before/after hashes bind dependencies, target and helper scripts. Aggregate sampling is opt-in for v2; v1 defaults
remain unchanged. Existing output directories are refused to preserve receipts.
Its explicit `mapFree` consumers neither import nor certify the frozen original
module. Predicate independence compares two current-signature calls only.
The five original headers remain unresolved. Missing dirty work and unrecovered
historical validation remain UNVERIFIABLE under H151.

The driver forwards handled termination and waits for monitor cleanup while
holding the writer lock. The monitor also inherits the lock descriptor and
retains the original driver PID; parent loss stops the worker before ownership
is released. It never substitutes a new parent in resource measurements.
Kernel parent-ID discovery and live-owned status reads fail closed; missing
data is ignored only when process exit is confirmed. The guard regressions
use lightweight process fixtures and do not establish any Lean theorem.

Handled interruption is deferred across process creation until the child handle
is owned. Aggregate-mode workers inherit the writer lease and use a Linux
parent-death SIGKILL guard, including the parent-loss-before-registration race;
monitor SIGKILL therefore cannot leave an unowned worker running. Lifecycle
regressions separately cover the fork-to-assignment window and monitor death.
If required host-memory/no-swap observations are unavailable, those lifecycle tests report
NOT VALIDATED/skipped; that is not successful cleanup evidence. The public
checker itself still refuses unavailable resource observations.

Only on the authorized cloud VM, explicitly add `--cloud-vm-h232` to select
H232 admission. It is propagated explicitly to each monitor; absent that flag,
the driver and monitor require the strict12GiB/no-swap hard scope. No ambient
variable or ordinary-host fallback selects the cloud exception. Both modes
record actual unified cgroup membership and fail on observed migration.
H232 authorizes serial execution without a systemd scope: no systemd scope on
the cloud VM (H232). The VM is the isolation; the host pre-gate separately
enforces its16GiB/no-swap merge cap. Local checks retain one Lean process,
12GiB address-space and sampled aggregate-RSS bounds, no swap, the existing
host reserve and deadline. Local success does not certify the host pre-gate.
The separate strict scope verifier remains regression-tested and is the default admission route. Frozen v1 defaults remain unchanged.
