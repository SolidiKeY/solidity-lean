# Revert-power handoff

Branch: `codex/revert-payload-settings`; starting master `f4dee4a29c2e208b36db4a4161a4723c735cd775`.

Default checked unsigned powers now preserve Panic(0x11) bytes in self-call frames, including nested, conditional and index paths. No new panic code or revertStrings setting is admitted.

- Kernel: 40 completed execution theorems, 34 returns and six specific assertion panics, in both pipelines. All use only propext, Classical.choice and Quot.sound.
- Compiler/EVM: 82 exact-byte observations. SelfPowerData: 29 per pipeline; original tryCatch/panic.sol: eight per pipeline; original revertStrings/empty_v2.sol: four per pipeline. The debug setting is compiler-only evidence.
- Final normal run-lean: **BLOCKED**, exit 124 at 680/686 library jobs, 1800 seconds, 8.01 GiB cgroup peak. 5 total 1800-second attempts remain blocked, not passing evidence. The single authorized continuation advanced from 607 to 680 jobs, then timed out with unchanged Solidity.Examples.Decision active. No further full retry was run. At that checkpoint, default library completion, SolkeyTestSuite build and sort check were missing assigned validation. The independent continuation below subsequently passed TestSuite and frozen sorts; default library completion remains blocked.
- Node: 23/23 pass. Static trust, layer, orphan, automation, generated inventory and frozen TestSuite parity checks pass. Static parity is separate from the actual TestSuite build recorded below. Public TrustAudit passes (529 headline theorems).
- Original model harness: panic fixture blocked by the unchanged host adapter; debug fixture blocked by revertStrings=debug. Neither is model agreement.
- Documentation audit: 20 missing references and six ambiguous names, all in files unchanged from starting master; historical reports preserved.

Final static command setup failures (script execute permission and setup SolKey pin path) are retained; invoking through bash and explicitly selecting the repository frozen inputs passed without file mode or configuration changes.

Exact commands, per-fixture results, source/runner/compiler hashes, theorem axioms, elapsed times, peak memory, shared files, reviews and remaining scope are in validation.json and logs/. Runtime wrapper/config snapshots are in runtime/; they use the same attached checkout and toolchain under a 12 GiB, no-swap Docker cgroup, one CPU and serial Lean flags.

Before/after probes and historical initial compiler observations are retained. No expected observation, proof premise, heartbeat, recursion, fuel or search limit was weakened or raised. Existing error transport and checked multiplication/cutoff proofs are reused; there is no universal source/compiler or loop-equivalence claim.

Remaining: signed magnitude-overflow bytes, allocation 0x41 and explicit revertStrings settings; explicit checking modes and all environment/log/layout/delegate policies remain unchanged. Full coverage-plan step 4 remains partial, and the combined validation gate remains blocked.

## Independent final gates (2026-10-28)

TestSuite and frozen sorts do not transitively import `Solidity.Examples.Decision`. Before running, TestSuite had 257 local modules with 238 cached oleans; sorts had five with all five cached. Finder independently recomputed both graphs. Cache presence was not counted as success.

- `lake build SolkeyTestSuite`: **passed**, 259 jobs, exit 0, 1470 seconds, 11,986,788,352-byte cgroup peak. Actual Report and Suggestions compilation completed.
- Existing `scripts/check-solkey.sh --key` with the exact frozen repository `solidityProgramRules.key` file: **passed**, exit 0, 377 taclets, 131 read-bearing and all 131 covered; 379,518,976-byte cgroup peak. The runner's one-second clock reported 0 elapsed seconds for this cached gate. The explicit file was checked and hashed; no absent-checkout skip was accepted.
- Static layer/orphan/automatic/trust/generated-inventory/frozen-parity checks passed again. These gates ran sequentially, with the same 1800-second limit, 12 GiB hard cap, zero swap and serial Lean flags.

The default library gate still has no terminal success: its preserved 1800-second timeout at 680/686 remains blocked. No full/default retry, proof-evaluation change or general closer repair was attempted. No implementation, fixture, expectation, refusal or supported-setting change occurred. Step 4 remains partial, including the signed-overflow/allocation/revertStrings gaps listed above.

`independent-gates.json` records exact commands, log/config/closure/rules hashes, resources and reviews. The original `validation.json` is preserved unchanged as the earlier checkpoint; all its 44 log hashes and 15 implementation hashes still match.
