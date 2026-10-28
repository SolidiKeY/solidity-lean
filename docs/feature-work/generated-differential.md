# Generated real-solc differential harness: bounded increment

Starting point: SolidiKeY/solidity-lean `origin/master`
`f4dee4a29c2e208b36db4a4161a4723c735cd775`, clean attached clone
`/workspace/solidity-lean`, branch `codex/generated-differential`, 2026-10-28.
On this commit the documented D/E harness had neither a `solcases` target nor
a typed Stmt-to-Solidity printer. Existing `#difftest` uses the internal compiler;
fixed EthereumJS replay vectors are separate. No existing group or semantics
was changed. Step 14 has no individual language-manifest row; no source feature
status is promoted by this differential evidence.

## Executable scope

`Solidity/Tools/SolCases.lean` constructs actual intrinsic `Stmt`/`Prog` values
for one contract with two uint256 roots, x and y. The root CLI enumerates ten
program families over all sixteen initial pairs from {0,1,2,2^256-1}: checked
addition, subtraction, multiplication, division, remainder; a write then require;
a write then assert; a write then revert; a conditional add/delete; and typed
literal-only 5/2. The guard after the write reads x=7, not initial x. There are
160 cases, each independently compiled/executed in all four legacy/viaIR ×
optimizer off/on configurations. Seeds rotate the boundary pool; there are four
distinct orders, not a claim of random coverage. Index and seed replay a case.

The printer reads typed syntax directly and preserves literal types using
uint256/int256 casts, avoiding Solidity rational-constant folding. Unsupported
constructors fail with named refusals. setup is itself a typed program printed
as setUp(); the actual interpreter runs the same setup and then Prog.run with
the existing withPanics transformation. No internal EVM compiler supplies the
oracle. Failure observations use the initial transaction storage and exact
panic/revert bytes; unknown model halts block. Concrete parser/printer equality,
literal division and refusal facts are kernel checked in the example module.
These are not a universal printer-correctness theorem.

The optional runner reuses the pinned compiler and EthereumJS package outside
Lake. It executes deployment, setup, run and observation transactions, comparing
exact output/revert bytes, decoded getter values and every declared root through
solc's checked storageLayout. Raw uint256 words cross-check the getter. Failed
transactions must preserve both initial roots. Unhandled layouts, logs and
exceptions block. Gas/steps/max-stack are retained observations, not claims
against a gas-free model. Source, compiler input, creation/runtime bytecode,
actual deployment hash, toolchain versions, generator source/binary, runner,
replay adapter and dependency lock provenance are retained. Reports never replace
historical upstream results. Mismatches retain reproducers; shrinking reexecutes
same-template boundary operands in the failing pipeline, preserving any mismatch,
not necessarily its cause. No semantic mismatch is relabelled as agreement.

## Reproduction and validation

Use the commands in `scripts/evm-reference/README.md`. Install only that optional
package with its existing exact npm lock. The compiler is Solidity
0.8.38+commit.1835d247.Emscripten.clang, SHA-256
6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390.
Actual runtime: Lean 4.24.0 (797c613), Lake 5.0.0-src+797c613.
The locked KeySort smoke build passed in 0.190 seconds.

The attached VM has no systemd user bus. The first native build under a 4 GiB
address-space bound failed to create a Lean thread; it is failed evidence.
A direct check against stale parser artifacts exited 139; it is not passing
evidence either. Current dependencies were rebuilt before successful checking.
Remaining heavy checks run sequentially in an offline Docker container on the
same VM, binding this exact checkout/toolchain, with cgroup MemoryMax=12 GiB,
no swap, one CPU, LEAN_NUM_THREADS=1 and an alternate untracked Lake TOML adding
explicit -j1. The writer lock is held. No Lean server is used. The alternate
TOML is removed before handoff; no tracked resource/search limit is raised.

Successful narrow checks:

- lake build solcases and the example import closure; per-file lean -j1
  --tstack=131072 diagnostics for both new modules and the CLI.
- roundTrip_exact and refuse_assumption axioms: [propext].
- literal_division_exact axioms: [propext, Classical.choice, Quot.sound].
- Seven generated Node tests passed in 4.911 seconds, including all four
  compiler configurations, deterministic seeds, malformed CLI input, literal
  division, wrong raw storage/getter/return bytes, unhandled layout and actual
  shrinking of a deliberately corrupted expectation.

Combined run on implementation commit
016184b5564044d22d1d387dfb88d1209d8ea190 (clean tracked implementation):
[complete observations](../../tests/generated/seed-0.json) and
[exact per-case table](../../tests/generated/seed-0.tsv).
All 160 cases agreed under every configuration: 640 agree, 0 mismatch, 0 blocked.
The report records 36.909 seconds for generated execution; process wall time
including compiler load/generation was 38.381 seconds. `lake -q exe solcases 0`
emitted 160 records in 0.354 seconds. Seed 1/index 9 was independently replayed with four agreements;
its full report is tests/generated/replay-seed-1-index-9.json.
The reused reference-replay suite passed
14/14 tests in 2.523 seconds. Successful final kernel example target checking
took 1.596 seconds; cold parser dependency refresh took 2m36.695s and ended in
a local test type error that was fixed, so that failed attempt is not a pass.
Native executable/import checks also passed; the first successful native build
was not timed. Peak aggregate memory across bounded checks was 1,160,622,080
bytes (1.081 GiB); cgroup max/oom/oom_kill counters were all zero.

| Kind | Generated cases | Typed reverts | Agreements (four variants) |
|---|---:|---:|---:|
| checked add | 16 | 5 | 64 |
| checked subtract | 16 | 6 | 64 |
| checked multiply | 16 | 3 | 64 |
| checked divide | 16 | 4 | 64 |
| checked remainder | 16 | 4 | 64 |
| write then require | 16 | 12 | 64 |
| write then assert | 16 | 12 | 64 |
| write then revert | 16 | 16 | 64 |
| conditional add/delete | 16 | 2 | 64 |
| typed literal divide | 16 | 0 | 64 |

Structural gates: 152 core modules, zero forbidden printer/elaborator paths;
702 reachable modules, zero orphans; trust audit 717 sources, 240 inventoried
sites, zero findings; automatic gate 491 automatic, 61 budgeted, 11 refuted,
zero manual/pending. Inventory regeneration reports 212 features / 783
classified upstream symbols, with generated files unchanged. No manifest
status/evidence change is justified for this validation-only increment.
The documentation-path gate remains failed on 20 pre-existing missing references
in Eqns, historical group03/group10 reports; those citing files are unchanged
from the starting commit and this branch deletes no target files. None of its
reported missing paths is introduced here. The trust script is invoked with
`bash` because its saved mode is not executable. No core semantics was edited,
so the core-change `./run-lean.sh` gate was not invoked; the new executable,
example import closure and each edited Lean file were checked explicitly.

Shared files edited: Solidity.lean, lakefile.toml, scripts/check-layers.mjs,
scripts/evm-reference/README.md, docs/README.md, docs/module-map.md,
docs/coverage-plan.md, docs/parallelism.md and docs/solc-validation.md.
No existing frontend, interpreter, rule or compiler module was changed.

## Independent reviews

Read-only finder and skeptic reviews used no Lean server. Confirmed findings
were fixed: typed casts replace bare numeric literals; malformed/extra seeds
are rejected; the enumeration driver is hashed; shrink scope admits different
mismatch causes; concrete parser/printer checks were added. The layout-negative
control adds a third root so compiler type rejection cannot mask the layout
refusal. Both reviewers found no direct false-agreement path in this fragment.
Their coverage caveats are retained here. Final independent reviews verified all
640 observations and source/code/deployment/tool/binary hashes without new findings. Literal-only division was also added
to all four real-EVM pipelines, not just the kernel regression.

## Remaining work and refusals

This is a coherent executable increment, not completion of all harness D/E.
The enumerated grammar has ten families, not arbitrary bounded-depth program
composition. Signed/bool state, structs, arrays, mappings and retained tails,
constructibility-based setup for composite storage, aliases, locals, memory,
loops, calls, payments and effectful operand-order/hoist/capture cases are not
generated. Val's unsupported forms refuse as solcases.value.unsupported;
unsupported operators as solcases.value.operator; numeric bool literals as
solcases.value.numericBool. Other statements refuse as
solcases.statement.unsupported; unknown kind/literal range/model halt refuse
by their named range/type/halt errors. Only the precise two-uint256 storage
layout is adapted. There is no coverage claim for every taclet, both modalities,
solc helper names or path-directed inputs. The full D verdict taxonomy and
cause-preserving structural shrinking remain future work. Environment fields,
observable logs, delegatecall, assembly, gas and physical-layout policy are
unchanged. Differential agreement is compiler/EVM evidence; kernel facts above
have only their stated concrete meanings. No profile decision D1/D2 was taken.
