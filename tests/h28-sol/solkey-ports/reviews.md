# Independent read-only reviews

Finder `/root/finder`: reviewed exact pins and initial proof module without
Lean server/compiler. Both full source hashes match snapshot.json. Found
published arbitrary expression-spine and strip-write typing results, and
published nested mirror theorem. Required exact absence certificate and
copied-origin separation across arbitrary suffixes. Fixed by
`fresh_iff_absent`, `copy_then_witness`, and `copies_ordered`.

Skeptic `/root/skeptic`: independently reviewed statements, premises, controls,
and passing selected logs without Lean server/compiler. No semantic defect
or forbidden premise found. Required negative sequence controls and a
nonempty reference shadow fixture. Fixed by `writes_cannot_allocate`,
`operations_cannot_shrink`, and `shadow_not_allocated`; final MCP check passes.
The syntactic copy equality versus additive allocating interpretation must
remain explicit. Final selected re-review: both reviewers pass at implementation commit
`96780494a943f45035d3d8164321bff6c30d3be7`. Finder checked all 15 theorem
signatures/axioms and 46 controls, all 18 main / 83 control declarations,
exact source pins and local registration. Skeptic independently confirmed
coverage, source hashes, negative controls, and the exact root delta.
The requested documentation correction distinguishes final acceptance runs
from the stopped initial setup attempt.

Finder required capturing external compiler wrapper bytes/hashes; these are
saved under `runtime/` and `evidence/toolchain-sha256.json`. Periodic read-only
resource audits found no failed build or OOM. OpenLoops passed in 523 seconds;
the cgroup reached its cap and reclaimed memory (`max=1448`, `oom=0`,
`oom_kill=0`). Full build passed all 3673 jobs.

Skeptic also reviewed the existing corpus procedure without running Lean:
six Lake coordinators can coexist, but every actual probe compiler inherits
the global compiler flock and explicit `-j1`, keeping heavy Lean work serial.
Generation uses scratch output and leaves frozen source untouched.


Final metadata closure: finder and skeptic independently verified every one of
the 61 ledger entries against declarations and actual compiler logs (including
all hashes and axiom sets), all five frozen-input identities, fetched-base
ancestry, successful broad/selected exits, and accurate resource accounting.
Both returned pass with no mandatory fix. Neither ran Lean, server, build or
probe. Exact-head receipts and seal are the remaining mechanical delivery gates.

## e6849d3b rebase review (2026-11-05)

Independent read-only finder and skeptic: PASS, no findings. Neither invoked
Lean/server/build tools. Both verified four owned Lean files and five frozen
inputs match the backup, all 67 restored private files exactly match the backup,
and the only metadata adaptation adds the fixed approved ancestor and documents
the rebase/H41 policy. Both original and published bases remain ancestors.

VM handoff: serial owned build, actual axiom ledger, 46 controls, selected
acceptance and KeySort runtime passed. Exact final-head rerun receipts and
verified H41 cache pack are sealed under `artifacts/rebase-e6849d3b/`. No
whole-tree/Bridge rerun, global cache freshness or coordinator transfer is claimed.
