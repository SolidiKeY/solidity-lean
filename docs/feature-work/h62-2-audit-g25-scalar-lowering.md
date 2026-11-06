# H62 item 2: G25 scalar lowering empty-statement audit

Status: **blocked; assignment incomplete**. This is a substantive preparation
checkpoint, not completion of any proof or final gate.

## Frozen scope and ownership

Batch `solidity-h62-2-20261106`, owner
`solidity-h62-2-20261106/audit-g25-scalar-lowering`, branch
`codex/solidity-h62-2-20261106/audit-g25-scalar-lowering`, repository
`/workspace/solidity-lean`, base
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
The checkout was initially clean on `work` at
`6cf853aea0417155aca29ddb91f1767d3f3a3cc4`. Fetching `origin master`
established that the exact base is an ancestor of published
`821e3e8f4c7a5ac3a51dc5cba8be813bb173e310`; the assigned branch was created
at that base without resetting or discarding work. No push, merge, PR,
pre-gate, deployment, producer edit, root registration, or central pin edit.

Coordinator inputs in `/workspace/h62-coordinator-inputs` match every supplied
SHA256. Its ownership snapshot assigns both G25 and G31 to V09. The module-map
file includes its G31 preparation table; this audit retains those rows.
H55-G49 files are untouched. No owner approval for an existing-file edit is
needed or implied: all changes are new paths within this audit's sole scope.
No `get_goal` tool is exposed; coordinator explicitly confirmed this does not
block work or authorize creating/resetting a goal.

## Checkpoint census

| Checkpoint | State and remaining work |
|---|---|
| 1. Frozen inventory and premise classes | Source inventory complete; elaborated types and theorem-by-theorem premise classification pending. |
| 2. Simultaneous hypothesis witnesses | 15 draft Slice witnesses; **zero verified**. All 311 public statements remain uncovered. |
| 3. Meaningful totality and negative controls | Nine draft controls against real frozen interfaces; validation blocked and broader supported-program coverage still required. |
| 4. Witness and statement-fidelity verification | Source-fidelity census passes; kernel fidelity, witness checking, final gates and final reviews remain pending. |

The area map contains 48 modules. G25: 37 modules, 185 public named theorems,
54 private named helpers. G31: 11 modules, 126 public named theorems, two
private named helpers. Totals: 311 public and 56 private declarations.
Public names occur exactly once. Private entries use namespace-qualified
**source labels**, not Lean's generated private internal names. `example`
commands do not export named interface theorems and receive no theorem credit.
No public statement is excluded because it lacks a binder named `h`.

`source-census.json` preserves the exact source signature before `:=`, line,
module, owner, section-variable source text, and signature/file hashes. The
scanner compares every module and the map to `git show BASE:path` and rejects
unsupported namespace, section, identifier and variable layouts. This is a
limited source scanner, not Lean's elaborator: auto-implicit arguments,
transitive structure fields, propositions behind aliases, and hypotheses in
returned `forall` types require the pending kernel census. It never promotes a
row to verified. `coverage-ledger.json` accounts for all 311 public statements
exactly once, retaining 311 uncovered rows, 15 candidate links, and 296 rows
without a draft. Both bulk files stay off git under H44.

### Premise distinctions to retain in the kernel audit

* `UnaryCertificate` and `BinaryCertificate` carry correctness for **all** typed
  operands and tails. `CheckedCertificate` and `CheckedUnaryCertificate` carry
  uniform checked-operation laws. A sample successful target run does not
  construct any of these global premise structures.
* `ClosedCertificate e` includes source success for **every** typed state plus
  target success for all tails, for one fixed intrinsic expression. Its global
  uniformity must be witnessed with an actual constructor; it cannot be replaced
  by a single-state source equation.
* `BinaryInvocation`, `CheckedInvocation`, and `ClosedInvocation` are per-input
  capacity evidence indexed by their particular certificate, operands and tail.
  In prefix theorems, decomposition and prefix-success equalities must hold for
  that same invocation. Independently inhabited structures do not suffice.
* Environment `Represents`, `HashInput`, and `ValueCertificate` relate particular
  frames/states, heaps/paths, bytes or programs. Their coupled fields must be
  satisfied simultaneously. `Stable` relates two concrete frames. Arithmetic
  laws such as `signedBitwise_read`'s universally quantified function bound
  also require genuine global witnesses.
* Equalities, bounds, nonzero/exclusion tests, and run/source-success hypotheses
  remain per-input obligations. Every full binder telescope, including implicit
  typed data, must be included in each eventual simultaneous assignment.

These are structural distinctions, **not** theorem-by-theorem proof credit.

## Draft additive modules

`tests/h62/item2/audit-g25-scalar-lowering/SliceWitnesses.lean` has one marker
for each of the 15 public Slice theorems. Each existential binds all statement
inputs, conjoins all original premises on one assignment, then includes the
unchanged theorem's instantiated conclusion. Nonempty stacks/tails and actual
instructions distinguish these from independent `Nonempty` assumptions.
The original `run_comp` witnesses share the intermediate stack.

`tests/h62/item2/audit-g25-scalar-lowering/SuccessControls.lean` uses the actual
`UnaryCertificate`, `BinaryCertificate`, `CheckedCertificate`, `run`, `guarded`
and `stackBound`. It drafts totality for Boolean not/and, checked addition at
zero, reject-all/always-revert contradictions, observable zero-division panic
versus raw EVM zero, distinct panic classes, and the 1024-word stack boundary.
This does **not** cover all supported programs. GAS/BASEFEE/CLZ controls show
only local refusal. These evaluators have no gas or fork parameter; fetched
EVM success, gas adequacy and cross-fork agreement remain unproved boundaries.
There is no new source IR, surrogate compiler contract or invented premise.
No new `sorry`, `axiom`, `native_decide`, trust shortcut, or heartbeat override.
Drafts are explicitly unverified, with no axiom-set claim.

## Validation and typed dependency tickets

Toolchain archive: official `lean-4.35.0-linux.tar.zst`, SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Actual Lean: 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
Actual Lake: `5.0.0-src+eb6cafb` (Lean 4.35.0).
Initial discovered installation was 4.24.0/Lake `5.0.0-src+797c613`;
a preliminary command failed before invoking Lean because `/usr/bin/time`
was absent. Automatic approval review then rejected the 4.24 rerun as contrary
to the latest toolchain pin. No 4.24 validation or cache reuse followed.

Each actual Lean run holds the repository writer lock, uses
`LEAN_NUM_THREADS=1`, explicit `-j1 --tstack=131072`, an isolated 4.35 cache,
a 12 GiB address-space cap and a live 4 GiB host/cgroup headroom guard.
The VM has a 16 GiB cgroup cap and zero system swap; the runner rejects
nonzero cgroup swap and terminates/reaps its own child on guard exceptions or
interruption. No systemd job, other worker termination, or raised proof budget.
`bounded_lean.py` records normal command completions and resource-stop outcomes,
including source hash, exit, time and log. Guard exceptions/interruptions clean
up the child but do not append a result row;
this per-file runner does not replace `./run-lean.sh`.

* KeySort prerequisite: PASS, exit 0, 2.003 seconds, empty error log under
  `keysort-v435`. This alone is not `RUNTIME_GATE_PASS` or a final gate.
* **DEP-MIGRATION-G25**: unchanged scalar closure passes Opcode (5.004 s),
  Jumpdest (2.002 s), Assembler (3.002 s), then fails Slice (2.002 s), exit 1.
  `Solidity/Backend/Scalar/Slice.lean:303` expects `ternary` to have no axioms;
  official 4.35 reports `[propext]`. Source SHA256
  `69e2138972d979cbad32d299178a7fc53887ac81c9cb5d7c0595815c15e9b0a9`.
  Producer V09; migration owner
  `solidity-h62-6-20261106/migrate-backend`. Frozen guard left unchanged.
* **DEP-MIGRATION-G31**: independent environment closure passes Opcode,
  KeySort, AST and SpecSyntax, then fails `Solidity/Syntax/Raw.lean` (5.005 s),
  exit 1. Errors at 597/650/665/682/684 include String.Slice versus String,
  missing Slice.toList and String.dropRight. Source SHA256
  `7c137f7e8e4c70f4868dc41a437687ab42e2d63e887cdde3ba3ccd1ea764b76f`.
  Migration owner `solidity-h62-6-20261106/migrate-syntax`.
* Direct draft diagnostics fail at missing unbuilt imports; neither draft
  has elaborated. These failures confer no partial proof credit.
* Before/after checking-time delta: **unavailable**. No source refactor was
  performed, and a matching passing affected baseline is blocked. The >10%
  slowdown stop condition cannot be adjudicated from these short failing runs.
* `./run-lean.sh`, full affected validation, runtime acceptance, statement-fidelity
  kernel census, witness axiom inspection and final timing comparison: PENDING.
  No final gate or full assignment completion claimed.

Owner tickets request a coordinator-supplied, signature-preserving migration
handoff/overlay and its authorized replay procedure for this exact frozen audit.
Do not update an axiom pin, change a producer statement, cherry-pick into live
owned files, downgrade the required toolchain, or claim a frozen witness using
an unreviewed migrated interface. No `relay.sh` or coordinator messaging tool
is present; these self-contained tickets are saved for coordinator retrieval,
**not falsely reported as delivered**. The ownership snapshot already identifies
the migration owners; no human approval of a premise/exclusion is requested.
No weakened/vacuous theorem was established, so there is no such theorem finding.

ESCALATE: audit-g25-scalar-lowering validation toolchain; Q-TOOLCHAIN-01: frozen checkout pins 4.24 and coordinator says “Migration ONLY,” but automatic approval rejected the 4.24 audit rerun; official 4.35 fails unchanged Slice/Raw imports. Options: (1) explicitly authorize frozen 4.24 validation for this non-migration audit, leaving migration gates on 4.35; (2) keep this audit on 4.35 and wait for owner-approved compatible migration inputs. No option weakens a theorem or premise.

This self-contained question was presented to the user with both options and no
recommended choice; a reply is required before any rejected 4.24 action can be
retried. Until clarification, the successful official toolchain checks and failed
imports above remain the only actual validation evidence.

## Independent read-only reviews

Finder and skeptic ran as separate agents because AGENTS and the assignment
explicitly require independent milestone reviews. Neither used Lean/server or
edited files. Both independently confirmed the 48/311/56 source counts and
all 15 Slice witness links. Initial tooling findings were fixed: frozen-byte
verification, declaration-boundary/namespace/variable/identifier fail-closed
checks, and unconditional Lean child cleanup. Re-review found no remaining
material issue in the current limited source census. Eight adversarial census
tests and a real subprocess exceptional-cleanup test pass. The evidence collector
also includes untracked paths in its scope check and recursively checks Lean
helpers, following skeptic review.

Both reviewers found no omitted/weakened Slice premise or surrogate success
contract by inspection. Skeptic noted potential implicit-inference ambiguity;
program/stack arguments were made explicit. Both retain all validation and
coverage limitations above. These reviews do not replace final proof reviews
once every statement and gate is covered.

## Reproduction and handoff

Run from `/workspace/solidity-lean` (hold the writer lock for writes/Lean):

```sh
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item2/audit-g25-scalar-lowering/census_tests.py
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item2/audit-g25-scalar-lowering/runner_tests.py
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item2/audit-g25-scalar-lowering/census.py --ownership /workspace/h62-coordinator-inputs/ownership.json --output /workspace/h62-audit-g25-artifacts/evidence/source-census.json
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item2/audit-g25-scalar-lowering/verify_census.py --ownership /workspace/h62-coordinator-inputs/ownership.json --census /workspace/h62-audit-g25-artifacts/evidence/source-census.json --output /workspace/h62-audit-g25-artifacts/evidence/coverage-ledger.json
```

Non-Lean acceptance: all ten commands pass (the two Python test runners,
census generation, ledger reproduction, diff whitespace, base ancestry, core
layer check, generated roots, fragments, and documentation paths). The layer
check reports 857 core modules with zero elaborator/checked-parser reachability.
Documentation paths resolve; 115 existing ambiguous-basename references are
reported by the non-strict checker. No runtime or Lean proof conclusion follows.
Scope violations and new forbidden Lean trust/budget tokens: zero. Full actual
commands, exits, elapsed times and log hashes are in `acceptance-results.json`.

The corresponding `bounded_lean.py` commands and decisive output are retained
in each off-git `results.json` and log under `/workspace/h62-audit-g25-artifacts`.
The exported handoff records the full committed head. Original patch,
checksum manifest, command outcomes, review records and owner tickets remain
at absolute paths in that handoff. Bulk census/ledger/logs are off git; their
deterministic generators and a small evidence manifest are committed.
The large toolchain archive/cache need not be imported into the repository.

Resume the same goal/VM/branch after the owners resolve the two migration
imports. First revalidate the authorized unchanged interfaces and affected
baseline. Then kernel-check/correct the drafts, classify every full elaborated
telescope, construct the remaining 296 draft witnesses, broaden totality and
negative controls to every supported case, inspect axiom sets, run full required
gates and same-resource timings, and repeat independent final reviews. Keep all
311 rows uncovered until their actual checks succeed. If the coordinator needs
a fresh thread after 3–5 completed items, transfer this exact original goal and
state; never self-create a replacement goal. This checkpoint is not completion
of that work queue.
