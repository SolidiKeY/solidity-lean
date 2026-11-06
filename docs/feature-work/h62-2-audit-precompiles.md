# H62 item 2: precompile empty-statement audit

Status: blocked; this is a committed partial audit, not completion of the four-checkpoint queue.
Owner: solidity-h62-2-20261106/audit-precompiles. Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Branch: `codex/solidity-h62-2-20261106/audit-precompiles`.
Actual worktree: `/workspace/solidity-h62-audit-precompiles`.
The existing clean `/workspace/solidity-lean` checkout was preserved. The required base was fetched,
verified as an ancestor of published origin/master, and used directly for this branch.
No push, merge, deployment, central registration, axiom-pin edit, or frozen-interface edit occurred.

## Checkpoint accounting

| Checkpoint | Saved result | Remaining obligations |
|---|---|---|
| 1. Frozen inventory and owners | 17 module-map files, 138 source theorem declarations (134 public, four private), complete source signatures/context/owners and classification for all 138; 24 public types kernel checked | Remaining kernel signatures, four private constant names, and feasibility proofs |
| 2. Simultaneous witnesses | Seven implication statements have joint proof-premise witnesses; 17 unconditional statements have concrete data-domain samples | 114 remain: 30 joint proof-premise cases, 56 data-domain cases, 28 closed fidelity checks; no case is silently excluded |
| 3. Success and trivial implementations | IDENTITY exact output/total success, reject-all and constant-empty negative controls; basic/P256 totality; MODEXP success/gas and BLAKE2F valid-size success/failure | Actual compiler success contract, executable stipend control, full gas/fork and Bridge boundaries |
| 4. Fidelity and verification | Exactly-once partial ledger, frozen source/scope guards, eight scanner regression tests, independent reviews | Full statement-fidelity acceptance, all remaining witnesses, full affected validation, complete queue handoff |

The deterministic source census rejects any module-map or source-byte change from BASE.
Its `preceding_variable_commands` field is lexical history, **not** a list of actual premises:
closed namespace variables can appear there. The new inventory tracks active source scopes separately and retains the effective implicit
Contract binder in all 12 Stipend declarations; full kernel verification is still pending for 114 types.
Private keys are source identifiers, not a claim about Lean's private mangled names.
`Solidity.Stipend`'s implicit `{C : Contract}` is retained in the source context.
All 138 candidates appear exactly once in the off-git statement ledger, including pending rows.

The seven checked originals are `Solidity.Precompiles.words_mono`,
`Solidity.Precompiles.sha256Gas_mono`, `Solidity.Precompiles.ripemd160Gas_mono`,
`Solidity.Precompiles.identityGas_mono`, `Solidity.Precompiles.Modexp.modexp_length`,
`Solidity.Precompiles.Modexp.gas_ge`, and `Solidity.Precompiles.Blake2f.blake2f_length`.
Each witness binds all relevant inputs together with every proof hypothesis and instantiates
that exact unchanged theorem. A successful call's input and output are the same pair throughout.
No independently inhabited premises are substituted for a joint witness.

`BasicWitnesses` and `CoreWitnesses` contain 17 checked named declarations: seven premise
witnesses plus success/control helpers. `DataWitnesses` adds 17 checked named declarations for
unconditional data domains, not extra proof-premise cases. `TypeFidelity` checks 24 anonymous
full-type assignments directly against the frozen constants. `JointPremiseFixture` adds two checked named declarations (one private helper and one joint
numeric fixture), bringing checked named audit declarations to 36. It imports Field only,
so original-statement coverage stays 24. `StipendControl` retains two **unchecked** proposals. No source `sorry`, new axiom, native_decide, or increased proof limit.
Failed elaboration logs can print `sorryAx`; those failures are retained and never accepted.
Accepted new declarations use only the recorded standard propext/Classical.choice/Quot.sound sets.

## Global structures and input feasibility

The stipend obligation takes global gas/failure functions. These are distinct from a feasible
execution on a particular admitted source input. Its Fitted component bounds reported gas;
it does not assert execution success. The proposed negative control sets gas to zero and failure
to True, then uses the already admitted empty body to rule out an empty source-body domain.
This is an abstract contract assignment, not an implemented always-revert compiler.
The control is blocked from kernel checking by the unchanged import closure.

The BLS generic gas theorems need a **single** table with both its length and monotonicity proof,
plus the same k/l relation for msmGas_mono. An isolated kernel fixture now supplies one zero table, cap and k/l pair satisfying all three
constraints together, including the table/cap boundary. It is not an imported BLS theorem
witness: BLS type instantiation and original statement coverage remain pending. No separately
inhabited assumptions are substituted for this joint tuple. Osaka gas_mono likewise needs one p with
LengthPriced p and one related input pair. Its witness remains pending behind BLS.

## Typed owner blockers and decision

Concrete tickets, evidence, repair choices and delivery state are in
[owner-tickets.json](../../tests/h62/item2/audit-precompiles/owner-tickets.json).

* OBL-SUCCESS: **decision resolved; theorem pending**. The coordinator answered H62 item 2:
  “the totality obligation is met by a SEPARATE compiler-success theorem proved for the owner's
  compiler (it does not reject everything / always revert on the stated inputs); do not change
  any frozen interface statement.” G43/V14 (`v12-v17/v14-payments-bytecode`) must supply that
  theorem for its actual compiler and stated supported success inputs. Its qualified name,
  source path, compiler identity and commit remain pending in
  [compiler-success-pending.json](../../tests/h62/item2/audit-precompiles/compiler-success-pending.json).
  The audit will check it alongside the original obligation. Existing precompile totality and
  data-domain samples do not discharge this owner-compiler obligation. No frozen repair is requested.
* DEP-RAW-435: pinned Lean rejects frozen Syntax/Raw String APIs, preventing Stipend imports.
  The migration Syntax/Source owner must supply a compatible overlay; this lane cannot edit it.
* DEP-BLS-435: frozen Bls12381 discount length proofs at 171/172 hit the existing recursion budget.
  The assigned migrate-precompiles producer owns the fix, without raised proof budgets.
* DEP-BRIDGE-435: the frozen optional Bridge pins v4.24 dependencies, and no compatible packages
  are installed in this worktree. Migration/Bridge and live SOL-PC producer coordination remains required.

relay.sh is **host-only**. H70 records the five recipient lanes in
[h70-waits.json](../../tests/h62/item2/audit-precompiles/h70-waits.json). No local relay call is
needed or attempted. The recipient plan is not a producer receipt and grants no original-file
edit permission. Await the V14/G43 theorem, migrate-syntax Raw, migrate-precompiles BLS and
migrate-bridge dependency receipts, coordinated with the live precompile-agreement owner.
The scope decision is resolved; the actual theorem/receipts remain pending.
H55-G49 work is untouched. None of these blockers is an exclusion or a weakened statement.

## Toolchain, gates, timings and evidence

The coordinator's five input hashes verified. Official Lean archive SHA256:
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Lean: 4.35.0, release eb6cafb7290e8bd5f2937522d8d804f58f02bafc.
Lake: 5.0.0-src+eb6cafb, Lean 4.35.0. No v4.24 per-master cache was reused.
The owned alternate config disables artifact caches and passes explicit -j1.
The original core and Bridge toolchain files were preserved.

Current evidence directory: `/workspace/h62-audit-precompiles-evidence-3`.
The H70 readable per-declaration inventory is `hypothesis-inventory.md`; machine-readable
rows, all binders, package/import/open context and full source types are in `hypothesis-inventory.json`. Both are generated
by committed inventory.py; bulk output remains off git. Source classification is complete,
not the kernel witness/fidelity audit. Previous evidence-2 and delivery-2 are preserved.
The original evidence archive and SHA256 manifest at `/workspace/h62-audit-precompiles-delivery`
are preserved and still verify. Its old census record remains historical, not the current corrected census.
Every bounded receipt contains its full actual command, cwd, exit, wall time and resource fields.
Final proof receipts also bind the exact source import closure and config hashes and reject edits
through the run. The ledger verifies every recorded proof/config/import-source binding before marking seven proof-premise witnesses and 17 data-input samples.

| Evidence stem / command purpose | Outcome |
|---|---|
| census-tests-continuation / python3 scripts/h62/item2/audit-precompiles/test_census.py | Eight tests pass, including frozen scope/source mutation rejection |
| frozen-census / census.py --check | 17 files, 138 declarations, exact frozen bytes |
| basic-final / bounded lake env lean BasicWitnesses | Exit 0; seven declarations, four simultaneous witnesses |
| core-final / bounded lake env lean CoreWitnesses | Exit 0; ten declarations, three simultaneous witnesses |
| data-final / bounded lake env lean DataWitnesses | Exit 0; 17 unconditional concrete-domain samples |
| type-fidelity-final / bounded lake env lean TypeFidelity | Exit 0; 24 direct full-frozen-type assignments, retaining every binder |
| core-signatures / bounded lake env lean CoreSignatures | Exit 0; 24 public type checks with pp.all |
| coverage-mutations-continuation / test_coverage.py | Six tests pass: valid partial input, failed exit, wrong cwd, stale import, failed axiom log, missing data receipt |
| doc-paths / bash scripts/check-doc-paths.sh | Exit 1: existing archived after-roadmap-va1.md reference to absent optional MathlibTest/SplitIfs.lean; owned handoff link resolves |
| h70-inventory / inventory.py | All 138 source signatures/binders classified; 114 kernel obligations remain |
| h70-inventory-tests / test_inventory.py | 14 tests pass, including member-vs-data classification, active C, scope endings, closed/private status, failed type receipt and no fixture promotion |
| joint-fixture / bounded lake env lean JointPremiseFixture | Exit 0; one joint table/cap/k/l fixture and private helper, propext only; no original BLS coverage increment |
| coverage-check-continuation / coverage.py | Partial ledger: 138 statements, 7 proof-premise + 17 data-input witnesses, 114 pending; never full acceptance |
| keysort-control-a, keysort-control-b / bounded lean -j1 Solidity/KeySort.lean | Both exit 0, 1.505269 s and 1.509260 s |
| import-prerequisite / bounded lake build Basic and Stipend imports | Exit 1; Raw String API errors at 597/650/665/682/684 |
| osaka-imports / bounded lake build Osaka import | Exit 1; frozen BLS discount proofs hit max recursion depth |
| stipend-blocked / bounded lean StipendControl | Exit 1; missing Rule.olean after failed producer build |
| full-run-lean-fixed / bounded bash ./run-lean.sh using owned lake wrapper | Layer/roots/fragments passed; frozen proof/API failures; stopped only its own group after decisive errors, signal 15 (shell 241), 185.393 s; NOT a passing full gate |

Full-run errors include frozen Hash/CollisionBound, Backend/AbiEntry/RawFreeTransport,
Source/Ctor and Yul/ReservedNames failures. The log preserves all decisive diagnostics.
Earlier failed setup attempts are retained: missing GNU time, quoting error, Node path correction,
and an initial BLAKE witness reduction failure fixed with symbolic list lemmas, without budget changes.

The VM has a 16 GiB cgroup cap and no enabled swap. Owned checks hold the writer lock,
set LEAN_NUM_THREADS=1, and use a per-process 12 GiB address-space cap. The final runner samples
aggregate process-group RSS, 4 GiB available reserve and single Lean worker count every 0.25 s,
stopping its own group on a breach. These are sampled guards, not a separate hard RSS cgroup.
The full-gate sampled peak was about 3.30 GiB, with at least 13.89 GiB available memory.
Older receipts before monitoring was added retain only their original resource fields.

KeySort's same-source/same-runner control delta is +0.265%; no slowdown above 10% was measured.
This is a stability control, not a compiler speedup or a completed migration before/after comparison.
No production refactor or original-source change occurred. Basic/Core/TypeFidelity checks take about 0.50 s each; DataWitnesses took 2.34 s. The H70 isolated joint fixture took 0.51 s.
No RUNTIME_GATE_PASS, full sort-check pass, external EVM test, or cryptographic agreement is claimed.

## Corrected signature census and resolved owner approach

The continuation's full-type checks exposed one audit-parser defect: top-level `let x :=`
inside a theorem conclusion was mistaken for the proof delimiter. The old recorded signature
for Solidity.Precompiles.Bn254.decodeG1_eq_none_iff stopped before its full conclusion.
The scanner now tracks pending top-level let assignments; the regression includes two
successive lets. The regenerated census contains both lets and the polynomial condition.
Only that signature record changed (`census-correction.json`); no frozen source byte changed.
The initial generated full-type file failed before correction; its failure receipt is retained.
The corrected generated file passes all 24 assignments without removed binders or raised budgets.
Local unused-variable lint is disabled solely for these exact-type examples so original unused
proof-binder names can be retained. This does not alter any theorem or proof limit.

## H70 full source classification and receipt waits

The complete source inventory accounts for every declaration exactly once:

| Source category | All declarations | Kernel checked | Still pending |
|---|---:|---:|---:|
| Explicit proof hypotheses | 37 | 7 | 30 |
| Data/type parameters without proof hypotheses | 73 | 17 | 56 |
| Closed statements without input or hypothesis binders | 28 | 0 | 28 |
| Total | 138 | 24 | 114 |

The 37 proof-bearing statements contain 47 top-level proof-hypothesis binders: seven configuration constraints
(BLS hlen/htab in two statements, Osaka hp, Stipend pow h/hq) and 40 per-input conditions. Nested quantifiers remain inside their exact predicate types.
This is a source classification, not proof that any pending tuple is inhabited.
There is no quantified global premise-record binder in these 138 source types. Implementation
FieldOps/NeZero instances, the Osaka.fixed data object and the global Stipend.Obligation
predicate are context, not replacements for per-input validity or actual compiler success.
C : Contract is data and must be the same C used by every dependent typed input.

The full inventory explicitly handles Controls.blake_malformed_lengths.member as a membership
proof; compress_size.h as array data; all 12 implicit Contract binders; both BN254 let
bindings; and all four unresolved private constant IDs. Dependent Loc/Val/Prog/Body domains
have a same-contract caution. identity_unaffordable requires a logical versus feasible-allocation
distinction; pointEval_result needs one real successful KZG input/output pair, not a computed
#guard treated as a kernel hypothesis witness. These cases remain pending.

Closed statements receive no artificial exists-True witness: after receipts they need whole
frozen-statement and axiom fidelity checks. All 30 remaining proof-premise cases must prove
one joint data/configuration tuple; all 56 data-domain cases need faithful input instantiation.
H70 routing is recorded for migrate-bridge, migrate-precompiles, migrate-syntax, live SOL-PC
precompile-agreement, and solidity-v12-v17-20261031/v14-payments-bytecode. No receipt has
been substituted by the routing plan. New source classification and isolated-fixture work
introduce no original-file changes and do not discharge the V14 compiler-success obligation.

## Reviews and continuation handoff

Independent finder and skeptic reviews were read-only, used no Lean server/build, and confirmed
seven statement-faithful proof-premise witnesses, 17 unconditional data-domain samples,
24 direct full-type checks, and the narrow negative-control interpretation. Their findings
were fixed: mutual block namespace handling; comment offsets; section-variable overclaim; frozen
module-map/source guards; resource evidence wording and sampled monitoring. The scanner regression
line-number typo was corrected. Continuation reviews independently confirmed the let-signature
fix, separate witness counts, and the coordinator-resolved separate owner theorem requirement. H70 finder/skeptic reviews independently checked all 138 source signatures and every remaining
114 row; both confirmed the 30/56/28 split, proof-role counts and isolated-fixture limit.
The sole caution improvement (Val C in pow_not_fits) was added and regression-tested.
Their final review text is saved off git in reviews.md.

Continue the existing goal only; never create/reset a replacement. Original prompt digest:
39585f8ffb6629c51fc8d1e0fca1808807d9cb06983d0c558dcdc019112450f3.
Original VM/environment:
ccarenv_b64_Y2NhcmVudl83YjM2Yzc3YzA3Njg4MTkxODg3Yjc3MTBhZWVkNzdhMg.
get_goal is not exposed; the goal objective in this thread is authoritative.
Ask the coordinator for a fresh thread on this same VM/branch/goal after this saved handoff.
Do not self-launch another goal. Resume with the migration overlays and the pending G43/V14 compiler-success theorem, then
finish 30 joint proof-premise cases, 56 data-domain cases and 28 closed fidelity checks,
complete exact kernel types/private names,
Bridge/gas/fork/compiler boundaries, independent milestone reviews and all final passing gates.
The assignment remains blocked, not complete; the 8-10 hour useful queue has not been exhausted.
