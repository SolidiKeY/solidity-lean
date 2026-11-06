# H62 item 2: v10-storage empty-statement audit

Status: blocked on pinned-toolchain migration dependencies; full assignment unfinished.
Owner: solidity-h62-2-20261106/audit-v10-storage.
Branch: codex/solidity-h62-2-20261106/audit-v10-storage.
Frozen base: c6f550e281a7e5affa9a99bc2cdaed556dec00e4.
Repository: /workspace/solidity-lean.

## Scope and inventory

The initially clean work branch was 6cf853aea0417155aca29ddb91f1767d3f3a3cc4.
Fetched origin/master and the exact published base, verified base ancestry in
origin/master, and created only the assigned isolated branch at that base.
No pushes, PRs, merges, pre-gates, owner-file edits or H55 work were performed.
Coordinator inputs under /workspace/h62-coordinator-inputs matched all five supplied
SHA256 entries. get_goal is unavailable; the coordinator explicitly states that its
absence is optional and no goal was created or reset.

The deterministic generator is scripts/h62/item2/audit-v10-storage/census.py.
It unions 118 explicit module-map paths with 230 backend wildcard paths, deduplicating
to 322 files. Wildcards come from the frozen Git tree. Every input's bytes must equal
its BASE blob. It records 3281 theorem/lemma source signatures exactly once by stable
path/line/name ID, hashes signatures and source context, and records V10 area ownership.
It conservatively includes controls and private helpers. This is a lexical inventory,
not an elaborated interface-theorem census. Fully qualified names, semantic hypothesis
classification, simultaneous witnesses and statement-fidelity proofs remain pending.
Every row is explicitly uncovered. Bulk JSON stays outside Git; the generator is tracked.

## Checkpoint obligations

| Checkpoint | Status | Remaining |
|---|---|---|
| 1. Exact signatures/owners/premise classification | partial | Elaborated names/types, interface selection and global/per-input classification |
| 2. Simultaneous hypothesis witnesses | blocked | All statements; zero new verified witnesses |
| 3. Supported success/totality and trivial-compiler negatives | blocked | All new theorems/controls and failure/gas/fork boundary validation |
| 4. Witness/fidelity census | blocked | All semantic verification; source census reports every row uncovered |

No frozen theorem was weakened, no premise invented and no statement repair attempted.
No weakened/vacuous theorem has been established by this preliminary work; this is not
an assurance that there are none. Typed dependency tickets and next steps are in
[the blocker queue](../../tests/h62/item2/audit-v10-storage/BLOCKERS.md).

## Verification and resource evidence

Actual official binary: Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc;
Lake 5.0.0-src+eb6cafb (Lean 4.35.0). Archive SHA256 matches toolchain-pin.json.
Pinned KeySort check passed with explicit -j1 and --tstack=131072; guarded reproduction
elapsed 1.617805099 s, observed peak group RSS 507736064 bytes. No RUNTIME_GATE_PASS is
claimed because required dependency checks fail. Initial v4.24 version inspection was
setup discovery; its KeySort attempt did not run because /usr/bin/time was absent.
It supplies neither a proof nor a migration baseline.

Five source-scanner regression tests pass, covering nested comments, misleading strings,
nested default assignments, equation-style proofs, let conclusions and match branches.
Two final census runs are byte-identical. Each input matches the frozen base.
Pinned dependency build and resource-guarded reproduction both exited 1 in unchanged
Syntax.Raw, Hash.CollisionBound and Source.Ctor. Reproduction took 54.7867672 s with
1608388608 bytes observed peak group RSS. Owners are migrate-syntax, migrate-hash and
migrate-source. No dependency fix is within this lane's write scope.

Validation uses validate.sh (writer lock), validate.py (12 GiB per-process address-space
cap and aggregate RSS guard, 4 GiB available reserve, zero host swap), and an isolated
TOML with explicit Lean -j1, disabled artifact cache and dedicated v4.35 build directory.
Inspected traces use only the pinned build path. One Lean child was observed. Guard
cleanup is bounded and only kills the runner's own process group. No systemd-run was used.
Full affected validation/acceptance/run-lean gates and before/after proof timing comparison
remain pending behind the failed dependency gate. No proof refactor or slowdown claim exists.

## Independent reviews

Read-only finder and skeptic, neither using a Lean server, reviewed the census and runner.
They found and drove fixes for swallowed equation bodies, truncated let/match conclusions,
unvalidated frozen inputs, working-tree wildcard omissions, unbounded TERM cleanup,
misleading raw resource-stop exit records, relative runner cwd and lock documentation.
After fixes, both found no further concrete census defect in the current corpus. Both
explicitly limit acceptance to lexical scanning and preserve all semantic/proof gaps.
Runner closure review and detailed evidence are exported off Git with the handoff.

## Handoff boundaries

Zero new Lean declarations/helpers, axioms, sorry, trust shortcuts or heartbeat overrides.
No generated roots, module maps, axiom pins, library imports or interfaces changed.
No registration fragment is needed until additive proof modules actually exist.
All four checkpoints and the original persistent goal remain unfinished. Owner migration
resolution is required before proof-bearing imports can check. The saved tickets are
for coordinator retrieval; no relay delivery or external message is claimed.

Final runner regression: a process ignoring SIGTERM was killed by the resource guard
in 2.608168363 s, child/effective exit -9, stopped=resource guard. Final locked-wrapper
KeySort passed in 1.814585664 s, observed peak RSS 518316032 bytes. Relative to the
previous guarded 1.617805099 s sample this is +12.163%, so further Lean runs stopped
under the >10% timing rule. These are repeat prerequisite samples with runner changes,
not a validated before/after proof-refactor comparison; no cause is inferred. Comparable
proof/build timing remains outstanding. The failed dependency JSON predates the final
runner cleanup and child_exit-field fixes; its command/exit/timing provenance is retained.

Final static boundary checks passed: layers (857 core modules, zero frontend/parser
reaches), register.sh --check and fragments.sh --check. Independent final finder and
skeptic reviews found no concrete handoff status/scope mismatch. No full gate was run
past the known failed dependency boundary.
