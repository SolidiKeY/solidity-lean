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

## H70 candidate classification while Lean is held

The coordinator acknowledged accepted migration-owner relays and explicitly held all
further Lean runs pending Syntax/Raw, Hash/CollisionBound, Source/Ctor and root-gate's
KeySort timing disposition. No Lean/Lake/MCP, build, runtime gate or timing check was
run for this continuation. No repair was fetched or original-file permission inferred.

The five candidate bundles are recorded in
[candidate-bundles.json](../../tests/h62/item2/audit-v10-storage/candidate-bundles.json).
Their complete frozen source signatures and hashes are attached by the deterministic
classify_candidates.py generator to off-Git evidence. Shared inputs are a single tuple
per theorem, with binder order retained; existing fixture definitions are referenced
without editing or replacing them. Exact names come from explicit frozen namespaces,
not a new Lean elaboration. All five signatures have zero global premise-structure
arguments: Env, functions and machine/state values are data parameters, while the
listed hypotheses are per-input observations or execution feasibility.

| Exact namespace suffix | Joint hypotheses on the same inputs | Contract role |
|---|---|---|
| LoopLaws.turn_step | nonzero, cond and step for the same rc/rb/machine/result/flag | Conditional single-turn adapter |
| LoopLaws.turn_exit | cond on the same rc/rb/machine; rb remains unrestricted | Zero-guard exit; no body-success premise |
| LoopLaws.run_single_loop | finished on the same cond/body/machine/result | Assumes whole-loop success; no independent termination claim |
| SourceWordRead.read_total | ordinary on the same E/context/frame/path/locals/state | Total outcome equation, retaining missing-cell failure |
| SourceWordRead.complete | ordinary, present and coherent on one shared dependent tuple | Source/fixed-readCode success derived from raw input observations |

LoopLaws means Solidity.Backend.StorageOps.LoopLaws; SourceWordRead means
Solidity.Lowering.StorageOps.SourceWordRead. The loop candidates use frozen populated
controls: turn_step uses yes/body/initial/after and flag 1; turn_exit and run_single_loop
use no/pending/initial. The latter loop exits without executing its faulting body.
The read candidates use the same frozen environment, frame, left path, nil locals and
initial state. complete adds read value 11, the frozen machine and root slot 0.
SourceWordWriteControls.value is 53 and must not be substituted for that read value.
Negative candidates record exactly which input premise would fail after such changes;
these are unproved case plans, not executed controls or results.

No compiler parameter/selection contract, gas cost or EVM fork appears in these five
signatures. Their classification does not finish checkpoint 3: supported compiler
success, reject-all/always-revert negatives and observable failure/gas/fork boundaries
still need the originally required separate proofs and controls. Conditional adapters
are not classified as vacuous merely because they assume successful executions.

All 3281 original census rows remain uncovered and all four checkpoints unfinished.
This source-only classification adds zero Lean declarations, proofs, axioms or sorry.
The original failed dependency and timing holds are unchanged. Finder/skeptic review
and deterministic consistency evidence for this continuation are exported separately.

H70 review closure: independent read-only finder and skeptic confirmed all five binder
orders, joint input assignments, source roles and zero-promotion status. The finder
identified an older combined resume sentence that wrongly attributed complete-only
binders/premises to read_total; it was split into the exact two bundles above, and the
resume command now explicitly requires coordinator hold release. The skeptic found
no status/scope/path mismatch. Neither reviewer used Lean or edited files. Generator
consistency and two byte-identical outputs passed; no witness satisfiability was checked.

## H70 requester continuation: all-row static classification

Starting head: 2d53437157aeb2385aeaaab7b7bb891e92566058. The requester directs
continued static work across all 3281 uncovered rows, retaining zero verified
witnesses and waiting on migrate-syntax Raw, migrate-hash CollisionBound and
migrate-backend producer repairs. Earlier Source/Ctor and root-gate timing holds
have not been explicitly released. This continuation runs no Lean, MCP, Lake,
build, timing or runtime gate; no original file or toolchain is edited.

surface_classification.py adds a deterministic off-Git ledger with exactly one row
per original census ID. Each retains its exact source signature/hash/context hash,
owner and uncovered status. It extracts grouped declaration binders with source
offsets/types, leading forall source text, the complete result text, and occurrences
of selected representation/endpoint markers. Bare or unsupported syntax is retained
as unresolved. Section dependencies remain unresolved explicitly; in particular,
PublishedOps.lean has source variable declarations, so a no-declaration-binders
label must not be interpreted as a closed theorem or absence of logical premises.

| Static syntax class | Rows |
|---|---:|
| declaration-binders | 1247 |
| declaration-binders plus leading-forall | 40 |
| no-declaration-binders | 1672 |
| no-declaration-binders plus leading-forall | 322 |
| Total, all still uncovered | 3281 |

Signature-marker occurrences: FiniteRun: 275, Represented: 592, Transport: 410,
PathSupported: 28. Counts overlap and include conclusions, so they are not counts
of hypotheses, global structures or feasible inputs. No inference about semantic
premise class, statement vacuity or satisfiability is made from token occurrence.
No statement is excluded; semantic interface selection/verification remains pending.

Manual candidate metadata now has thirteen exact selected declarations: the original
five and TargetOperations.ofSlot_toSlot/toSlot_ofSlot/toSlot_injective/add_keysFit/
run_read/run_write/run_copy/run_copy_self (namespace Solidity.Backend.StorageOps).
Local bounds and equality in the conversion cases share the same root values.
The four run cases have data binders but no logical success hypotheses. Populated
read/write/nonself-copy plans observe stored11, write bool-true word1 over11, and copy
root 0 = 11 into root 1 = 0 respectively. All are fixed symbolic target-code contracts,
not arbitrary compiler selection or gas/fork correctness. Self-copy preserves the
machine, so empty code also meets that identity; it is not presented as a useful
reject-empty-code control. These are source plans only. Thirteen manual source
classifications leave 3268 rows without manual semantic analysis and all 3281 without
new checked witnesses. The existing five were not counted again as new work.

[Producer field inspection](../../tests/h62/item2/audit-v10-storage/producer-field-classification.md)
separates the three local endpoint structures from a universal compiler producer,
and retains FiniteRun.hash_bound over ALL preimages. It is not a checked structure
inhabitant or an added theorem row. No backend repair diff was supplied or applied.

External consistency checks: five static-extractor regressions pass; candidate and
all-row outputs each generated twice and compared byte-identical; all frozen input
bytes matched BASE; no row was lost, duplicated or promoted. Independent read-only
finder and skeptic reviews found no concrete mismatch in extraction or the eight
new shared-input plans and preserved all semantic/proof limitations. Neither used
Lean/server or edited files. Detailed review and generated bulk evidence are off Git.
All four checkpoints and the original goal remain unfinished; no new Lean helper,
axiom, sorry, heartbeat override, root registration or interface change was made.

Final static review closure: both reviewers checked producer field fidelity, including
the universal hash bound and the same after state, and found no concrete mismatch.
Source-only counts and the new backend wait are accurate; old holds stay unreleased.
The ledger explicitly defines binder offsets relative to the signature suffix after
the declaration name. No semantic or proof coverage is promoted by successful parsing.
