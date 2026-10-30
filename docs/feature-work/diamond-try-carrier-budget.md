# Closed carrier proofs and bounded modern Cancun validation

Component/tooling checkpoint from79eaf89143318665c03743f94994d0caabcb8992 on the
same original diamond-try branch/executor. The combined user recovery records
receipt4e20b800 reconciled_not_accepted117pages/5804items; no accepted prior turn
was replayed. [Delivery](diamond-try-carrier-budget/delivery.json) names the actual
M1 mechanical scope and later runner approval call_0f9867a06fbb4d3b9eea8999fb34e047
item0. That later approval supersedes only the old runner hold. No journal
receipt/turnID was fabricated or coordinator state changed.

## Kernel component: constructed calls only

New core module `Solidity/Evm/TryPanicCarrier.lean` uses existing intrinsic Prog,
litBytes, block, Args, CallRet.enterT and call/catch operations; no semantic
constructor, axiom, dependency or profile is added. `Solidity/Examples/Tactics/TryPanicCarrier.lean`
holds nonvacuity/negative controls. Both are registered in Solidity.lean.

* carrier36_halt proves the actual closed Prog halts with M1 computed36: existing
  litBytes allocation, actual fresh-object readback/raw revert, then block/error
  transport. No desired hcall is a premise or certificate field.
* litBytesT_alloc's map(.st) equality is inverted ONLY for an error constructor.
  It never supplies a normal Out/heap-extension equality.
* args36_eval derives the actual literal36 input; empty_entry proves empty f
  returns enter the real parameter state without a return-default allocation.
  call_halt follows from those and the closed Prog theorem for arbitrary live H.
* catch_halt uses actual self receiver/nonzero condition and self=true without
  an external oracle; data_transport reuses existing catchData allocation/scope/
  Ext law with the derived call halt.
* normal_return proves a selected constructed Panic handler's EXACT normal Out:
  original caller state with its typed result slot set67 and prefixrefl; callee
  ghost heap rolled back and catch scope dropped. Arbitrary caller slot/context
  and live two-alias nonempty-H controls are explicit; sender/value fields are
  not normalized. Both pipeline tags quantify provenance only.
* call_at_halt and other_argument deliberately show this CONSTANT constructed
  body also emits36 for another scalar argument6. Missing size36/source-identity
  evidence is NOT a semantic revert or proof execution is impossible. Actual
  zero receiver and self=false/empty-oracle failures remain distinct; wrong-byte
  controls refuse an incorrect observation, not a source shape operationally.

No original generic f(uint) replacement, CheckedOriginalAt36, original-source
callee transport, emitted-byte/compiler/path/resource adequacy or source early
return theorem is claimed. P4 actual byte/resource correspondence, P5b original
whole-declaration/body/callsite construction and P8 source admission/default
adoption remain gated. The original callback/source counterexamples and all six
gap/target certificates remain unchanged. M1's physical computed image and ghost
materialization remain distinct from original source execution and EVM bytes.

## Modern runner facility: exact pinned derived CommonJS artifact

The approved facility is explicit tracked code, not a preload/monkeypatch, opcode
override or a new evaluator. Existing universal/reference dependencies are
vm/evm/common/util10.1.3 and ethers6.17.0. conditional/reference lacks VM/ethers
and is not substituted. The original dependency tree is immutable and its full
manifest is rechecked. A NEW separate copy has exactly four changed CJS/API files
through scripts/evm-reference/attempt-budget-engine.patch and exact original/new
source hashes in attempt-budget-pins.json. Other files are byte-identical. ESM
is unmodified and NOT supported by this API. Stale JS sourceMappingURL references
are removed for patched JS files; original inert map files are not a new source
map claim. No npm install, package-version upgrade or backend build occurred.

`derive-attempt-budget.py ORIGINAL_NODE_MODULES NEW_NODE_MODULES` rejects an
existing destination or destination inside original tree, validates the complete
original tree/patch hashes, copies then applies the fixed patch, checks every
original/new file and re-enumerates the original tree. It never modifies the
original installation. The current derived artifact is
/workspace/next10-diamond-try-evidence/carrier-budget/patched-v1/node_modules;
its exact mapping/provenance is patched-v1/attempt-budget-derivation.json.
The failed initial artifact and all failed logs remain retained.

The engine API beginAttemptBudget/endAttemptBudget attaches ONE explicit budget
object to the EVM. Its interpreter consumes BEFORE opcode lookup/jump analysis,
dynamic gas preparation or effects, once per entered instruction attempt. Nested
CALL/STATICCALL/DELEGATECALL/create interpreters use the SAME EVM/object and never
reset it. With used=N, consume rejects before starting N+1; STOP/REVERT/invalid/
static- and dynamic-OOG attempts count once, independently of tracing events.

The small tracked attempt-budget.mjs helper creates AttemptBudget(limit5M,used,
aborted) at each original root runCode/runCall. Normal completion detaches it
for the next original root while preserving VM state; host stop poisons it and
leaves it attached permanently. Both future begin and direct root entry reject
the same poisoned machine, even empty-code roots. A distinct non-EVM AttemptLimit
escapes nested async execution; it is never returned as an EVM exception result,
expected Solidity FAILURE, completed revert or target observation. Other host
exceptions also poison/discard the machine. No journal rollback/finalization
theorem is inferred after host abort. Group stops, prefix audit survives.

Native precompile/compiler/WASM/setup work is zero interpreted attempts, not
invented instruction coverage. Existing tool-job120s process/descendant cap,
gas30M and whole-group12GiB/swap0 remain. No Node timer is relied on to interrupt
synchronous native work. Successful logs retain raw return/revert bytes, failure
status, used count/depth and gas separately; no budget change is hidden in env.

Only the TWO previously approved Cancun scripts explicitly call artifact
verification BEFORE backend require and wrap their ORIGINAL runCode/runCall roots.
Removing those exact wiring edits reproduces the prior scripts byte-for-byte;
[pre-fixture audit](diamond-try-carrier-budget/pre-fixture-plan.json). Their
Cancun/Hardfork.Cancun, optimizer flags,30Mgas, actual source programs/inline
controls, ordered assertions/observations and both pipeline loops are unchanged.
The compiler remains0.8.38+commit.1835d247.Emscripten.clang SHA256
6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390.
No historical fork/backend or global runner/profile change is adopted.

## Actual controls and required group execution

Review preceded controls and original fixtures. Finder/skeptic found two initial
packaging defects (import before hashbang, malformed EOF diff). They were repaired
and pins regenerated before engine load. Derivation failed on the initial corrupt
patch; that failure/partial-copy evidence remains. They also found invalid
timeout child quoting and absence of a descendant check; repaired before controls.
First control execution was11/12: normal DELEGATECALL failed because the raw
control's root account was absent. Explicit root STOP account setup repaired the
fixture, preserving engine/caps/assertions. [Failure/repair](diamond-try-carrier-budget/control-repair.txt).
No failed command was rerun unchanged or relabeled a pass.

| Fresh check | Actual result | Limits/provenance |
|---|---|---|
| Budget controls | 12/12 pass, exit0,2s | ExactN/N+1, invalid/STOP/REVERT/static+dynamicOOG, pre-gas SSTORE warmth/storage refusal, nested shared CALL/STATICCALL/DELEGATECALL/CREATE, native/zero-code0steps, synchronous stop/no-reuse/noFAILURE, actual process+grandchild timeout |
| Ordered state controls | 7calls per legacy/viaIR,14total | Actual state increment/revert rollback/readback/selfcatch; complete expected return/Error bytes and flags, all budgeted; no unbudgeted baseline |
| Source-admission group | 22calls, exit0,2s | SourceLiterals/SourceIdentifiers, original6invalid/4rejected/3accepted compiler controls, maximum2590attempts/root |
| Exception group | 88vectors, exit0,4s | Original CallExceptions source/ordering/expected bytes, maximum3650attempts/root |

Both reviewers read actual successful controls/derived source/abort behavior/pins
before the two original groups executed. All110 original roots record limit5M,
statuscompleted, no blocked roots, exact legacy/viaIR order. Script assertions
remain active after wrapper returns. Passing is compiler/EVM evidence, not a
kernel compiler proof, target correspondence or original malformed-f source pass.
The old rejected combined driver was not modified/invoked/rerouted.

## Kernel/structural/full confirmation and original family

Owning per-file MCP for core, example and registration completed with successtrue,
partialfalse, no failed dependency and no errors/warnings. Initial elaboration
failures are retained; no sorry/axiom/native proof shortcut or bound increase.
Full ./run-lean.sh (including library/TestSuite/sort pin), Corpus, frozen complete
TestSuite audit, check-orphans, check-layers, check-automatic --strict, check-trust
and feature-inventory --check all pass. Full build replayed existing unrelated
linter warnings; owning new-file diagnostics are clean.

Actual kernel #print axioms audits cover310distinct names: the prior290 plus
20new public theorems, with only propext/Classical.choice/Quot.sound or no axioms.
The complete actual raw log/sets are external Axioms.lean/axioms.log/axiom-account.json;
[20new names](diamond-try-carrier-budget/new-axiom-names.json). No audit was inferred
from a connected MCP status or a successful script exit alone.

Original20-row native catalog was freshly replayed after these imports: **exit1**,
12working/8blocked/0broken, not a passing family gate. All66 completed ordered
native observations equal prior full objects and retained reference/frozen full
return/revert bytes, signatures and flags. Both <byzantium originals are rejected
BEFORE compilation/jobs and retain original gas8000/source/observations/rows.
No historical execution/reinterpretation. Six physical/reference source rows
remain blocked. Wider old18reference/140reference-frozen results are retained,
NOT fresh execution in this turn. P4/P5b/P8/source/profile/blocker statuses do not
improve from constructed proofs or these local compiler controls.

Core/script tests are serialized with writer lock, LEAN_NUM_THREADS1 and explicit
Lean-j1 through temporary evidence-local Lake config; no build/MCP overlap, disk
caches, measured headroom, memory.max12884901888/swap.max0/maxOOM0 retained.
Actual [gate commands/results](diamond-try-carrier-budget/code-gates.json) retain
native expectedexit1 with gatePassed=false. Native replay73s; no gas/step/proof/
process/fuel/node budget or frozen expectation changed. All2600 prior evidence
checksums verified, no historical failure/export discarded. Temporary config
was removed after the actual Lean checks; tracked/user config remains unchanged.

[Result account](diamond-try-carrier-budget/results.json) separates kernel, modern
compiler/EVM and original source status. [Independent reviews](diamond-try-carrier-budget/reviews.txt)
state their actual read-only scope, repairs and no reviewer test/server execution.
No push/merge, other-batch work, policy-blocked ABI, D3 relaxation, callback
judgment/default adoption or new VM/thread/timer/service. This is a reviewed
component/tooling checkpoint, NOT original-assignment completion or an eligible
standalone integration delivery. Controller alone integrates complete work.

Final read-only report/derivation review found no discrepancy; both reviewers
confirmed exact source-vs-constructed limits and actual result counts, with no
execution or cleanup/export certification of their own. Worker verified temporary
config removal and unchanged tracked config/toolchain/fixtures. Historical docs
exit1 is preserved by exact baseline comparison below.

Final strict documentation paths retain actual exit1 (3s): complete pre-footer
output identical to previous checkpoint,20missing/unchangedambiguities,new0.
[Exact comparison](diamond-try-carrier-budget/documentation-comparison.json).
[Fresh check/resource account](diamond-try-carrier-budget/validation.json) records
maximum cgrouppeak1129066496bytes and sampled aggregateRSS4960268KiB
with hard12GiB/swap0 and no max/OOM events; native/docs exit1 stay explicit.

The final hardened derivation recipe was also executed on a fresh separate
artifact; every derived file equals the tested artifact. A negative inside-base
destination is refused before any write. No engine/fixture rerun was used for
these provenance controls. [Actual derivation controls](diamond-try-carrier-budget/derivation-controls.json).
