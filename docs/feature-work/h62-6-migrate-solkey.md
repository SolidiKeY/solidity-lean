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
with universe parameters and kernel type expressions. It requires entries for
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

Four scanner controls pass: nested comments/string delimiters, exact five-file
and eleven-import census, command locations, and source/fixture/dependency
mutations. Three acceptance controls pass: incomplete/failed runs, resource or
input drift, and wall/RSS regression thresholds. These are external Python tests,
not Lean theorem proofs. Final fixture elaboration, Lean gates and measured
acceptance remain outstanding.
