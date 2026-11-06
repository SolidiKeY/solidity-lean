# H62 item 6: Solkey migration overlay

Owner: `solidity-h62-6-20261106/migrate-solkey`.
Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Branch: `codex/solidity-h62-6-20261106/migrate-solkey`.
Checkout: `/workspace/migrate-solkey`; original clean checkout preserved at
`/workspace/solidity-lean` on `work`.

## Scope and current status

All four checkpoints remain binding. This is an isolated migration overlay,
not a transfer of live producer ownership. No push, merge, generated root,
module registry, axiom pin or tracked toolchain edit is authorized here.
The five assigned original files remain byte-identical to the pinned base.
There is no proof refactor, new axiom, `sorry`, `native_decide`, or raised budget.

1. Census implemented; clean old source-closure measurement in progress.
2. Exact official new toolchain downloaded and identity verified; compatibility
   elaboration pending the serial baseline.
3. Complete new build and comparable timings pending. Any regression escalates;
   a wall-time or RSS increase above 10% stops acceptance.
4. Kernel-interface inventory fixture and source/fixture hashing implemented;
   successful execution on both compilers, exact comparison and final gates
   remain pending. A final bundle must not claim these are complete.

## Reproduction and evidence

Bulk evidence stays off Git at `/workspace/migrate-solkey-evidence`.
The scripts under `scripts/h62/item6/migrate-solkey` are deterministic generators.

```
python3 scripts/h62/item6/migrate-solkey/census.py
python3 tests/h62/item6/migrate-solkey/test_census.py
python3 tests/h62/item6/migrate-solkey/test_compare.py
python3 scripts/h62/item6/migrate-solkey/measure.py --root /workspace/migrate-solkey --toolchain /workspace/.setup/tools/lean-4.24.0-linux --out /workspace/migrate-solkey-evidence/old-clean-1
```

The initial measurement process loaded the runner before review hardening.
It uses serial standalone `lean -j1 --tstack=131072`, fresh `.olean` output,
no Lake artifact cache, no configured swap, a 12 GiB per-process address-space
limit, and a 4 GiB cgroup reserve guard. Its original termination wait is
unbounded after TERM; the revised runner fixes this and checks host reserve
before starting each child. Preserve the original measurement as a pilot;
use the final revised runner identically for the accepted old/new comparison.

The runner checks the complete topologically ordered assigned source-import
closure. This narrow gate is distinct from the repository-required final
`./run-lean.sh` and affected validation. Each module's command, exit, wall time,
and aggregate maximum child RSS are recorded. The 250 ms polling loop adds
measurement overhead; fresh outputs do not imply a cold OS page cache. Do not
interpret a borderline timing ratio without repeat measurement.

The census covers five assigned modules, seven distinct direct imports,
280 local dependency modules and 16 standard-library imports. It records eleven
fixture-import occurrences, including the intentional stale-hash import,
three explicit theorems, two private definitions, commands and their locations.
Full source and fixture SHA256 values preserve every frozen expected-message
block. They are lexical evidence, not elaborated interface equivalence.

`tests/h62/item6/migrate-solkey/FrozenInterfaces.lean` inventories all constants
owned by the five modules, including private and command-generated constants,
with declaration kind, universe parameters, kernel type expressions and definition,
proof and opaque value expressions. It requires entries for
every module and all three named theorems. It also prints the three theorem
axiom sets. Output belongs off Git. This helper has not yet been elaborated;
no successful semantic interface or axiom audit is claimed.

## Toolchain identity

Coordinator inputs at `/workspace/h62-coordinator-inputs` passed their complete
`sha256.json` manifest. `toolchain-pin.json` requires:

- `leanprover/lean4:v4.35.0`, official `lean-4.35.0-linux.tar.zst`.
- Archive SHA256: `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
- Lean: `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release.
- Lake: `5.0.0-src+eb6cafb (Lean version 4.35.0)`.
- Old Lean: `4.24.0`, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, Release.
- Old Lake: `5.0.0-src+797c613 (Lean version 4.24.0)`.

Archive and versions are recorded in off-Git `toolchain.json`. No per-master
v4.24 artifact cache is used. No RUNTIME_GATE_PASS is asserted.

## Cross-directory dependencies and coordination

Direct imports: `Solidity.Frontend.Import`, `Solidity.Frontend.Problems`,
`Solidity.Tools.Run`, `Solidity.Calculus.Close`, `Solidity.Calculus.Closers`,
`Solidity.Calculus.Deploy`, and `Solidity.Calculus.Surface`.
Every dependency outside `Solidity/Solkey/` is read-only to this lane. The
source census includes the full closure and its hashes for migrate-root-gate.

Typed coordination blocker `OWNER_RELAY_UNAVAILABLE`: the required `relay.sh`
is absent from the actual checkout and workspace. No owner reply or permission
is inferred. No assigned original has been edited. Once an elaboration failure
identifies a specific external dependency, record its exact file and error as
an owner migration request; never repair that dependency here.

The additive test inventory is deliberately absent from generated library roots.
Suggested registration for the root migration owner: run the fixture explicitly
against each clean build's `LEAN_PATH`; no production-module registration is
needed unless the owner chooses a maintained integration location.

## Independent reviews and controls

The finder and skeptic worked independently, read-only, without Lean or a server.
Finder found incomplete legal import parsing and missing host-memory/prelaunch
checks plus unbounded stop cleanup. Skeptic found incorrect command locations,
unbounded cleanup, polling overhead and the distinction between source and
semantic interface hashes. Confirmed defects were repaired; both reviewers
confirmed the repairs by inspection. Finder additionally requested fail-closed
checks for module/theorem omissions in the interface fixture; these were added.

Five scanner controls pass: module-system import modifiers, nested comments/string delimiters, exact five-file
and eleven-import census, command locations, and source/fixture/dependency
mutations. Four acceptance controls pass: finite positive metrics, incomplete/failed runs, resource or
input drift, and wall/RSS regression thresholds. These are external Python tests,
not Lean theorem proofs. Final fixture elaboration, Lean gates and measured
acceptance remain outstanding.

## Static validation evidence

`node scripts/check-layers.mjs`: exit 0; 857 core modules, zero reaching
either elaborators or checked parser adapters. Generated-root and fragment
checks: exit 0. Census comparison: exit 0, all source/fixture/dependency hashes
unchanged. `bash scripts/check-testsuite.sh --solkey
tests/migration/solkey/keyext.solidity.examples`: exit 0; trust clean across
54 modules and 564 public functions = 552 derived + 11 refuted + 1 excluded,
zero pending, plus 2 skips. This checks pinned rows, not new Lean elaboration.
The initially attempted default and setup-snapshot paths failed; the explicit
repository-pinned snapshot resolves those setup failures without source edits.

`bash scripts/check-doc-paths.sh`: exit 1 for a pre-existing missing reference
in `docs/feature-work/after-roadmap-va1.md` to the optional Bridge Mathlib
checkout. The new handoff introduces no missing Lean path. No fix outside the
assigned scope is attempted. Logs are under off-Git `static-gates/`.

## Corrected physical-memory measurement bounds

The initial old pilot failed at `Solidity.Calculus.TermSize` with exit -6:
`libc++abi: terminating due to uncaught exception of type lean::exception:
failed to create thread`. It ran for 1462.017 s before stopping; maximum child
RSS was 3,296,560 KiB. This is a failed partial pilot, not an accepted baseline.
The extra RLIMIT_AS cap incorrectly limited virtual stack reservations. The
repository explicitly distinguishes these reservations from RSS.

A diagnostic recheck without that extra virtual-address limit passed TermSize
in 29.830 s under the actual VM cgroup. A live sample showed 13,404,156 KiB
virtual size versus 1,051,480 KiB RSS. No cgroup OOM event was recorded. The first
diagnostic attempt failed because the new output root shadowed the supplied
import root; the runner now places the existing import root first. Both failed
attempts are retained as evidence, without theorem/source changes.

Accepted measurements use the existing physical cgroup cap of 17,179,869,184
bytes (16 GiB), no configured swap, a 4 GiB reserve checked against both host
availability and cgroup headroom before launch and during each job, serial
explicit `-j1`, bounded TERM/KILL cleanup, and no artificial virtual-address
limit. Old and new comparisons require identical runner/census hashes, resource
settings, module order and source/fixture hashes. Per-file and inventory modes
cannot count as clean-build acceptance.

Every completed module records its output OLean SHA256. Inventory mode requires
a complete assigned-closure report, matching source identity and Lean/Lake
versions, and verifies every imported OLean hash. Diagnostic per-file mode is
explicitly separate and can use a partial closure to reproduce provisioning
failures. Five scanner, five acceptance, and five interface controls currently
pass; these Python controls do not replace Lean elaboration.

## External prerequisite migration request

The exact official 4.35.0 attempt passes KeySort, AST and SpecSyntax, then fails
`Solidity/Syntax/Raw.lean` with five errors at lines 597, 650, 665, 682 and 684.
`String.drop` now yields `String.Slice`; direct String consumers and Slice.toList
fail, String.dropRight is unavailable, and passing endsWith without eta expansion
fails overloaded-pattern inference. Warnings also report deprecated String.mk
and Slice.dropRight. This dependency is outside this lane's write scope.

Typed blocker: `EXTERNAL_DEPENDENCY_MIGRATION`. Recipient: Syntax migration
owner through migrate-root-gate. Request an owner-approved compatible prerequisite
overlay/artifacts on the coordinator's official pin, preserving exact types,
semantics and budgets. No edit to Raw is made here, and no reply is inferred.
The complete diagnostic and shortest dependency chains for all five assigned
modules are saved in off-Git `dependency-blockers.json`. Every assigned module
reaches Raw, so none can currently complete on the new compiler.

`StringApiControls.lean` adds eight isolated case controls for the reported API
boundaries, including Unicode, hash-name prefix stripping, function/return
spelling, positive and negative location suffixes. These are finite case proofs,
not a proof of Raw's parser correctness or a dependency migration. They are
awaiting serial per-file checks on both toolchains. No original statement,
premise, exclusion, observation or budget is changed.
