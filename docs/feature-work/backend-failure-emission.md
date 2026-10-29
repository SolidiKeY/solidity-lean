# G38: failure and return emission

Assigned base: `50658f41061b366d6e503d1e8a3a324a281e9fca`.
Branch: `codex/solidity-independent5-20261029/failure-emission`.
Checkout: `/workspace/scratch/failure-emission-assigned`.
The original clean checkout on branch `work` at
`dedb3aee5743025aeb6d8f7219c9b6b9c1e00e5d` is preserved untouched.
This lane imports no other new lane and edits no reserved implementation.

This is an exact instruction-slice component, not a source-to-bytecode,
whole pinned-EVM, full ABI-shape, catch-dispatch or whole-world rollback proof.
G37/G42/G47 and the source/backend composition obligations remain with their
owners. Gas exhaustion, memory expansion, the calling convention and code
placement still require integration. Existing observations, exclusions,
refusals, target predicates and approved profile are unchanged.

## Source and feature anchors

Manifest IDs are `assertBuiltin`, `requireBuiltin`, `revertBuiltin`,
`errorDeclarations`, `returnStatement`, `tryStatement` and `catchClauses`.
There is no `tryCatch` ID at this base. Local evidence points to
`Syntax/Elab.lean`, `Syntax/Scoped.lean` and the error-declaration frontend
files; this component does not change their partial verdicts.

The current intrinsic `RevPart` constructors are `bytes`, `sel`, `word`
and `mem`; `RevPart.evalT` and `TRun.revertData` in
`Solidity/Semantics/Run.lean` evaluate and concatenate their bytes.
`Stmt.revertData`, assert lowering in `Solidity/Syntax/Elab/Arms.lean`,
`Semantics.encodePanic`, `encodeError` and `selectorBytes` in
`Solidity/RevertBytes.lean` remain the read-only source of payload bytes.
`Roadmap.Outcome.success` and `.revert` carry exact byte observations.
G04 R04/R29 and the current payload-free `Evm.Machine` revert remain parent
composition obligations. Nothing here revisits source failure semantics.

## Queue and checkpoint 1 handoff

| Item | State |
|---|---|
| 1: typed input and opcode emission | Done: focused gates and independent reviews passed |
| 2: independent byte memory, stack tails, terminal slices | Pending |
| 3: intrinsic observations and discriminating controls | Pending |
| 4: local checkpoint/unwind and nested failure | Pending |
| A: arbitrary payload chunking, tails and address bounds | Chunk decomposition implemented; memory proof pending |
| B: concatenation, distinction, input preservation, external vectors | Internal exact byte vectors implemented; remaining proofs/tests pending |

`Input` distinguishes empty failure, panic (bounded machine code), Error
reason bytes, already encoded custom-error bytes and ordinary return bytes.
Its `bytes` function reuses the existing ABI functions. Custom bytes include
the already evaluated selector and arguments: this is not a declaration or
ABI encoder. `digits` is only a machine-immediate encoder.

`writes` emits PUSH1 byte, PUSH32 address, MSTORE8 per byte, in increasing
address order. The final instructions are PUSH32 length, PUSH32 offset,
RETURN or REVERT. `writes_decompose` pins each selected byte and address
after exactly three instructions per preceding byte (`writes_length`).
`writes_append` proves arbitrary chunk concatenation and offset advancement;
`emit_length`, `panic_length` and `reason_length` pin lengths without a small
payload cap. `Fits` records machine-word/half-open-address bounds for the
later execution theorem. MSTORE8 deliberately introduces no padding writes;
the unused final word bytes must retain their initial values.

`Gap.lean` was checked against only pre-existing modules before payload
emission: Panic(1) has 36 bytes, crosses a word boundary, ends `[0,0,0,1]`,
and differs from Panic(0); bare backend REVERT encodes only `fd`.
`EmissionChecks` adds empty/custom exact byte vectors (custom at offset 5),
panic selector/tail, a 33-byte crossing at nonzero address, Error length,
return, wrong endian/offset/order/terminal and concatenation controls.
These are kernel proofs, not external-EVM agreement tests.

Independent read-only finder and skeptic reviews used no Lean server.
Both confirmed operand order and existing ABI reuse. They identified missing
emitter controls, exact byte vectors and handoff/registrations. Finder also
identified the unfinished offset arithmetic proof and requested an exact
per-byte decomposition theorem. Those findings have been addressed; follow-up
read-only finder and skeptic reviews both cleared checkpoint 1. A concrete Error-length reduction hit the default recursion
budget; it was replaced by `reason_length`, without raising any budget.

## Runtime and evidence

Read AGENTS, intrinsic Gate G0, parallelism/contributing, the local
lean-verify skill, current G01/G04/G06/G02, the actual scope decisions and
roadmap impact document. No Lean MCP or get_goal tool is exposed, so per-file
checks use actual Lean CLI with `--tstack=131072 -j1`.

Actual tools: Lean 4.24.0, commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`; Lake 5.0.0-src+797c613.
The VM enclosing cgroup is 16 GiB; host swap is zero. systemd scopes are
unavailable and direct child-cgroup creation is denied. An offline Debian
container enforces `memory.max=12884901888`, `memory.swap.max=0`, one CPU,
`LEAN_NUM_THREADS=1`, with only assigned source and the read-only toolchain
mounted. The broad initial mount was rejected by automatic review; the
narrow offline alternative was accepted. Repository writer lock is held by
the runner throughout each check. The original work checkout is not mounted.

`lake -f .failure-emission.lakefile.toml build Solidity.KeySort` passed:
`Build completed successfully (2 jobs).`, exit 0, elapsed 1 second,
cgroup peak 25,534,464 bytes (warm repeat with explicit `-j1`).
The cold preceding KeySort run reported `Built Solidity.KeySort (1.0s)`
and `Build completed successfully (2 jobs).`, peak 158,109,696 bytes.
RUNTIME_GATE_PASS applies only to this actual toolchain/runtime check.

Exact logs and the capped runner are saved under
`/workspace/scratch/failure-emission-evidence`.
The alternate lakefile changes only weak Lean arguments to add `-j1`, and
is not a tracked package/configuration change. Full closure gates, final artifacts and later checkpoint commit IDs will be recorded as they run.
No inherited failure is waived by historical results.

Checkpoint 1 gate record (2026-10-29):

| Command | Actual result / evidence |
|---|---|
| `lake -f .failure-emission.lakefile.toml build Solidity.Backend.Failure.EmissionChecks` | Pass, 11 jobs, exit 0, 5s, cgroup peak 300,802,048 B; `cp1-build.log` |
| `lake ... env lean -j1 --tstack=131072 Solidity/Backend/Failure/EmissionChecks.lean` | Clean, exit 0, 3s; sampled aggregate RSS 431,192 KiB, cgroup peak 253,952,000 B; `cp1-rss-check.log`. Summed RSS includes shared mappings. |
| `node scripts/check-layers.mjs` | Pass: 168 core modules, 0 reach the elaborator; `cp1-layers.log` |
| `node scripts/check-orphans.mjs` | Pass: 770 reachable, 0 orphaned, 0 not allowed; `cp1-orphans.log` |
| `bash scripts/check-trust.sh` | Pass: 785 sources, 241 inventoried sites, 0 findings; `cp1-trust.log` |
| `bash scripts/check-doc-paths.sh` | Fail: 46 missing references; `cp1-doc-paths.log`; identical output from untouched exact base in `base-doc-paths.log` (diff exit 0). No new findings; inherited failure is not called passed. |

Headline axiom sets are pinned with `#guard_msgs`: only `propext` and
`Quot.sound`; no new axiom, recovery hook or proof-budget override.
The final CLI checks supplement the focused module build because no MCP exists.
Independent review summaries are saved in `cp1-reviews.md` in the evidence
directory. Checkpoints 2–4 and final closure validation remain outstanding.
