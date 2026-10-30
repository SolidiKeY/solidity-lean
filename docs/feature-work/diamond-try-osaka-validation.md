# Compatible Osaka validation after M1

Human authorization call_773eaf24f18747868cab51e9a9fed612 item0 allows the existing
compatible modern Osaka checks, in legacy and viaIR, after the preserved M1
combined-driver rejection. The rejected driver was neither modified nor launched.
This checkpoint changes documentation/evidence only: no source admission, D3,
target, callback/default semantics, producer, P4/P5b/P8, expected observation,
compiler flag, proof/gas/step/fuel/node/process budget or dependency lock changed.
It is not original-assignment completion or an integration delivery.

The [pre-execution plan](diamond-try-osaka-validation/plan.md) records exact commands,
transitive execution paths and exclusions. Both read-only reviewers checked
actual prepare/CLI/import/test paths before execution. Native prepare parses
fixture settings then rejects incompatible EVMVersion before compile-input/jobs.
The exact original paths
`test/libsolidity/semanticTests/tryCatch/assert_pre_byzantium.sol` and
`test/libsolidity/semanticTests/tryCatch/require_pre_byzantium.sol` remain in the
20-row catalog, each with EVMVersion:<byzantium, literal gas:8000 and both original
expected observations. Neither was compiled or executed in this increment, under
a historical fork or Osaka. Snapshot hashing/extraction is not execution. No
historical backend was acquired, built, loaded, executed or instrumented.

| Requested group | Actual result | Scope/limit |
|---|---|---|
| Source admission | HELD, not run | Existing script explicitly selects Cancun compiler+engine; Osaka-only authorization preserves its settings |
| Script fixtures | Exit 0, 146/146 tests, 6 s | Explicit five test files, serial test concurrency1; actual Osaka replay controls in both pipelines plus static parser/AST/linker controls |
| EVM exception vectors88 | HELD, not run | Existing script explicitly selects Cancun compiler+engine; no reinterpretation to Osaka |
| Original native tryCatch catalog | **Exit 1**, 12 working / 8 blocked / 0 broken, 78 s | Full original20 rows retained; 24 replay jobs for12 admitted rows; both required modes completed on each working row |
| Original malformed_panic reference | Exit 0, 4 observations per pipeline / 8 total, 4 s | Exact single original source, actual deployment/call, Osaka legacy+viaIR, full bytes/flags/order retained |

The8blocked native rows remain assert_pre_byzantium, require_pre_byzantium,
invalid_error_encoding, malformed_error, malformed_panic, malformed_panic_2,
malformed_panic_3 and malformed_panic_4. Those six physical/reference source rows
are not admitted by M1, decoder controls or this validation. Policy-blocked ABI
and other-owner work remain untouched. Native malformed_panic is still blocked
while its independent bytecode reference works; no source-correspondence claim.

All66 fresh completed native observations match retained reference and frozen
expectations in exact order, including signature, failure flag and complete
return/revert bytes. Their entire native observation objects also equal the
previous decoder checkpoint. All8 fresh malformed_panic reference observations
match frozen bytes; entire pipeline variants (including provenance, deployment,
gas/step/stack observations and actual raw data) equal the previous reference
checkpoint. These are finite observations, not universal kernel proofs or P4.
No fresh18-row reference family replay or fresh140-count reference/frozen claim:
those wider reports are retained historical evidence. Fresh reference family
coverage here is precisely one original row in two required pipelines.

Pins: original Solidity commit1835d247de183f23e7b0e2bc4a50732af525b77c,
archive SHA2569200f2a26b08be5b77faf877c44f5cfbf5ea95f1bccc45dae559d2fbc7cefb2d,
compiler0.8.38+commit.1835d247.Emscripten.clang SHA256
6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390.
Modern EVM10.1.3/common10.1.2/util10.1.2 are the actual checked-in lock versions;
all20 package metadata versions match the existing conditional/reference tree.
The universal/reference tree has different common/util versions and was NOT used.
Existing dependency source hashes are retained separately. Nothing was installed,
fetched or built as an EVM backend. Node24.19.0, Lean4.24.0, Lake5.0.0-src+797c613
were actually observed. Source/compiler/pipeline IDs and complete original
settings/observations remain unchanged; source hash for malformed_panic is
522bfa3512517476f4f06cef823b176afe52978eb52393b25783e30d10ccc311.

Each invocation used the existing bounded/job/check helper chain, writer lock,
LEAN_NUM_THREADS=1, whole-group memory.max=12,884,901,888 and swap.max=0, with no
max/OOM events. Native used evidence-local temporary Lake configuration with
explicit Lean-j1; tracked/user configuration was untouched. Largest cgroup peak
496,521,216 bytes; largest sampled aggregate RSS1,182,136 KiB. Gas100M, steps5M,
reference process120s and native replay120000ms/loopfuel1000/batch16 are unchanged.
The existing one-time cached tool-build deadline300000ms was not increased.
Disk had22GiB free, host MemAvailable exceeded16GiB; no competing build/MCP ran.

Two preflight failures are preserved: existing empty node_modules directory
instead of absent path, and Lake selector rejecting --version after -f. Neither
reached tests/compiler/fixtures. The exact empty directory was renamed temporarily
and restored, and actual pinned Lake binary used only for version reporting.
Finally removed the temporary config and restored the original dependency path.
The successful source checks were not repeated. No new automatic approval
rejection occurred; the original M1 rejection and deferred logs remain immutable.

Static accounting passed exit0 (1s): full ordered comparisons, current source
hashes, unchanged inspected scripts, immutable M1/post-M1 evidence manifests,
and runtime cleanup. Retained M1 full/library/TestSuite/Corpus/strict/trust/MCP
and axiom audits are not fresh passes from this documentation-only increment.
Strict docs comparison/independent final review are recorded below after checks.

Delivery records the direct user authorization and actual execution-tool chunks.
No worker-visible coordinator journaled-resume/receipt helper exists; the
coordinator's receipt/turn reconciliation remains explicitly deferred, not
fabricated or re-dispatched. See [delivery](diamond-try-osaka-validation/delivery.json).

Evidence: /workspace/next10-diamond-try-evidence/osaka-validation, including exact
commands/logs, complete native/reference receipts, source/dependency hashes,
preflight failures and [machine-readable results](diamond-try-osaka-validation/results.json).

Final read-only finder/skeptic review confirmed actual scope/counts against raw
logs and static accounting. Finder corrected one JSON label to explicitly say
“not compiled or executed THIS INCREMENT,” preserving the earlier authorized
static compiler investigation in task history. No current-run historical
execution was found. Review scope excludes new execution or coordinator-receipt
certification; [review record](diamond-try-osaka-validation/reviews.txt).

Strict documentation paths retained actual exit1 (20 missing references and
unchanged ambiguity notices). The complete pre-resource-footer output is
byte-identical to post-M1 baseline; zero new findings. [Comparison](diamond-try-osaka-validation/documentation-comparison.json).
