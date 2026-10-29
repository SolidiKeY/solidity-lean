# Fresh memory struct witness lane

Branch: `codex/next10-memory-struct-witness`; baseline:
`f4dee4a29c2e208b36db4a4161a4723c735cd775`.

The original `gapMemStruct` formula and target certificate are unchanged.
The implementation adds finite typed child-first allocation plans, heap
preservation, sharing and root freshness proofs, and an exact scalar field
cut. Per-state exactness retains `Nonempty (MObj H (.struct s))`; global
scalar exactness constructs children. The returned countermodel is the
adopted child heap **before** the parent allocation performed by `allocAll`.

The decision addition recognizes one outer map-free struct binder with a
reflexive equation or a direct primitive field read equated to a literal on
the right. It does not claim general struct decision completeness, nested
reference/alias formula coverage, reversed equations or connective bodies.
`Fml.inTarget`, exclusions, Waivers and DecisionTheorem are unchanged.
There are no source/compiler/EVM support claims: these are calculus/kernel
fixtures, with compiled verdict and full ordered heap-observation controls.

The independent read-only finder and skeptic reviewed the construction,
classifier, returned state and original pin. Neither used a Lean server.
They found no semantic defect. The skeptic identified missing Account
balance/token observations in the new controls; those were added without
removing any existing observation. Broader decision scope remains explicit.

## Evidence

The recovered baseline container completed 310 jobs, including the original
DecisionMemory pins, exit 0, from 2026-10-28 13:03:17 UTC to 13:59:48 UTC.
Its cgroup peak was 8,929,996,800 bytes, capped at 12,884,901,888 bytes with
zero swap. The executor became unavailable during the run; its retained
container output was recovered from the same VM. KeySort passed before
editing. Lean is 4.24.0; Lake is 5.0.0-src+797c613.

Per-file MCP diagnostics pass for both new core files and the integrated
Decision module. Actual axiom reports show only `propext`, `Classical.choice`
and `Quot.sound`; the scalar cut itself uses only `propext`.

The original gap is closed: its verdict changes from `unknown` to `refuted`
with kernel-checked coverage and countermodel proofs. All mandatory gates
below passed. No resource stop or incomplete diagnostic is counted as a pass.
Full command logs and machine-readable resource/fixture records are under
`/workspace/next10-memory-struct-evidence` (`summary.json`).

All heavy groups used `LEAN_NUM_THREADS=1`, explicit Lean `-j1` through a
private temporary Lake configuration, and the repository writer lock.
Docker verified `memory.max=12884901888` and `memory.swap.max=0`; the outer
VM cgroup is 17179869184 bytes, leaving 4 GiB outside the build group.
The first full run reached the cgroup cap (including charged page cache)
but exited 0, with `OOMKilled=false`; no limit was increased. The final
warm confirmation peaked at 410,619,904 bytes. Actual shell/toolchain and
available-memory observations are in `environment-final.log`.

| Command/check | Exit | Elapsed | Aggregate cgroup peak |
|---|---:|---:|---:|
| Baseline `lake build Solidity.Examples.DecisionMemory` (310 jobs) | 0 | 3391 s | 8,929,996,800 B |
| Integrated core build (247 jobs) | 0 | 33 s | 462,790,656 B |
| Fixture dependency build (312 jobs) | 0 | 865 s | 7,418,314,752 B |
| `./run-lean.sh`, kernel trust audit, final static gates | 0 | 5799 s | 12,884,901,888 B |
| Final confirmation of the same pipeline | 0 | 154 s | 410,619,904 B |

`./run-lean.sh` passed the full 688-job library and 259-job SolkeyTestSuite.
The frozen SolKey check parsed 377 taclets and covered all 131 read-bearing
annotations. `lake env lean --tstack=131072 -j1 TrustAudit.lean` verified
529 headline theorems use only the standard axioms. The new scalar cuts use
only `propext`; the decision soundness/refutation and original countermodel
reports use only `propext`, `Classical.choice`, `Quot.sound`.
`lean_verify` on `fieldEq_refutes` reported those same three axioms and no
warnings. All five edited/new proof-bearing files received successful,
nonpartial per-file MCP diagnostics; DecisionMemory was checked again after
the review's final wording correction (`memory-mcp-final.log`).

Strict gates passed: `check-orphans` (703 reachable, 0 orphans),
`check-layers` (152 core, 0 violations), `check-automatic --strict`
(491 automatic, 61 budgeted, 0 manual, 11 refuted, 0 pending), and
`bash scripts/check-trust.sh` (717 sources, 240 inventoried sites,
0 findings). `solidity-feature-audit.py` regenerated/checked the inventory:
212 features and 783 symbols, no generated changes or inflated support.
`git diff --check` passed. No repository scripts were changed.

## Fixture observations and exact scope

| Fixture | Baseline | Final |
|---|---|---|
| Original `gapMemStruct` | unknown | refuted |
| Original negative-block / hidden-binder pins | unknown / unknown | unknown / unknown |
| Reflexive fresh field | new control | proved |
| Unsigned five / Boolean / fixed-child / signed-child | new controls | refuted each |
| Mapping-bearing / reversed equation / buried literal | new controls | unknown each |

The full ordered observations are kernel proved and compiled-evaluation
pinned: shared graph `[4,1,1,7,11,12,9,0]`; distinct-child graph
`[6,1,3,7,8,11,12,9,0,10,2]`. These cover actual heap size, every field,
child identity, sentinels and independent parent ages. The actual returned
countermodel reports `[some 2,some 0,some 0,some 0]`: child count,
Token.value, Account.balance, Account.token. Empty-heap vacuity is separately
kernel proved; an empty heap is not misreported as a countermodel.
`verdict` tests the public goal pipeline; returned-state observations and
coverage/exactness certificates test the leaf pipeline. No compiler/EVM
execution is claimed for these calculus fixtures.

## Recovery and review

The original saved executor and branch were recovered, without another VM,
clone or branch replacement. A host polling handle disconnected during the
full build; the existing container continued, and its actual complete output
was recovered. No checks/edits overlapped that interval. A detached lock
holder restored the writer lock; final confirmation used a lock held inside
the container so it survives transport loss. Initial unsupported Lake flag,
missing container Node path and non-executable trust-script invocations were
repaired by the private Lean configuration, saved Node path and explicit
Bash invocation, respectively. Raw failed attempts remain in the evidence;
they are not passing gates. MCP teardown warnings are distinct from its
successful nonpartial Lean results.

Finder and skeptic independently reviewed the witness/cut, classifier,
Decision integration, unchanged original statements/certificates, alias and
freshness controls, returned pre-parent heap and documentation. Neither ran
a Lean server or wrote files. Confirmed observation and historical wording
findings were fixed; the final decider wording was corrected and rechecked.
No semantic review findings or mandatory validation blockers remain.
General struct bodies and nested reference/alias formulas remain outside
this scalar schema; the witness construction does not assert a general
DecisionTheorem completeness result.

Shared edits: `Solidity.lean`, `Solidity/Calculus/Decision.lean`,
`Solidity/Examples/DecisionMemory.lean`, `docs/module-map.md`, `docs/automation.md`,
`docs/lean-key-rule-map.md`.
The witness/cut module pair, graph controls and this document are lane-owned.

Integration note: other memory lanes may also extend the `mxTop = none`
fallback. Compose their certified answers with `decideStruct`; do not
overwrite either certificate or the established array cut. No push or merge
was performed. The external handoff records the final commit and patch hash.
