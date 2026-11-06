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
| 1. Frozen inventory and owners | 17 module-map files, 138 source theorem declarations (134 public, four private), exact source headers, hashes, owner records; 24 public types elaborated | Full elaborated signatures, private constant mapping, complete hypothesis and input-feasibility classification |
| 2. Simultaneous witnesses | Seven original implication statements have checked joint witnesses | 131 candidates remain pending; data-only declarations are retained, not silently excluded |
| 3. Success and trivial implementations | IDENTITY exact output/total success, reject-all and constant-empty negative controls; basic/P256 totality; MODEXP success/gas and BLAKE2F valid-size success/failure | Actual compiler success contract, executable stipend control, full gas/fork and Bridge boundaries |
| 4. Fidelity and verification | Exactly-once partial ledger, frozen source/scope guards, seven scanner regression tests, independent reviews | Full statement-fidelity acceptance, all remaining witnesses, full affected validation, complete queue handoff |

The deterministic source census rejects any module-map or source-byte change from BASE.
Its `preceding_variable_commands` field is lexical history, **not** a list of actual premises:
closed namespace variables can appear there. Elaboration must decide effective implicit binders.
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

`BasicWitnesses` and `CoreWitnesses` contain 17 checked declarations total: seven premise
witnesses plus success/control helpers. `StipendControl` contains two additional **unchecked**
proposed declarations. No source `sorry`, new axiom, native_decide, or increased proof limit.
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
plus the same k/l relation for msmGas_mono. Those joint witnesses remain pending; the audit
makes no claim from separately inhabited tables. Osaka gas_mono likewise needs one p with
LengthPriced p and one related input pair. Its witness remains pending behind BLS.

## Typed owner blockers and decision

Concrete tickets, evidence, repair choices and delivery state are in
[owner-tickets.json](../../tests/h62/item2/audit-precompiles/owner-tickets.json).

* OBL-SUCCESS: master source owner and G43/V14 must resolve the missing execution-success link
  in Solidity.Stipend.Obligation. Either link the actual compiled run to successful source inputs
  in the obligation, or publish a separate public compiled-success theorem required alongside
  this gas-only obligation. Do not demand success for source programs that intentionally revert.
* DEP-RAW-435: pinned Lean rejects frozen Syntax/Raw String APIs, preventing Stipend imports.
  The migration Syntax/Source owner must supply a compatible overlay; this lane cannot edit it.
* DEP-BLS-435: frozen Bls12381 discount length proofs at 171/172 hit the existing recursion budget.
  The assigned migrate-precompiles producer owns the fix, without raised proof budgets.
* DEP-BRIDGE-435: the frozen optional Bridge pins v4.24 dependencies, and no compatible packages
  are installed in this worktree. Migration/Bridge and live SOL-PC producer coordination remains required.

relay.sh is absent in this checkout. Tickets are saved for the local coordinator's authorized
retrieval; no relay delivery or owner reply is claimed. No frozen repair is authorized by silence.
H55-G49 work is untouched. None of these blockers is an exclusion or a weakened statement.

## Toolchain, gates, timings and evidence

The coordinator's five input hashes verified. Official Lean archive SHA256:
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Lean: 4.35.0, release eb6cafb7290e8bd5f2937522d8d804f58f02bafc.
Lake: 5.0.0-src+eb6cafb, Lean 4.35.0. No v4.24 per-master cache was reused.
The owned alternate config disables artifact caches and passes explicit -j1.
The original core and Bridge toolchain files were preserved.

Absolute evidence directory: `/workspace/h62-audit-precompiles-evidence`.
Every bounded receipt contains its full actual command, cwd, exit, wall time and resource fields.
Final proof receipts also bind the exact source import closure and config hashes and reject edits
through the run. The ledger verifies every recorded proof/config/import-source binding before marking seven witnesses.

| Evidence stem / command purpose | Outcome |
|---|---|
| census-tests-final / python3 scripts/h62/item2/audit-precompiles/test_census.py | Seven tests pass, including frozen scope/source mutation rejection |
| frozen-census / census.py --check | 17 files, 138 declarations, exact frozen bytes |
| basic-final / bounded lake env lean BasicWitnesses | Exit 0; seven declarations, four simultaneous witnesses |
| core-final / bounded lake env lean CoreWitnesses | Exit 0; ten declarations, three simultaneous witnesses |
| core-signatures / bounded lake env lean CoreSignatures | Exit 0; 24 public type checks with pp.all |
| coverage-mutations / test_coverage.py | Five receipt mutation tests pass: valid partial input, failed exit, wrong cwd, stale import, and failed axiom log |
| doc-paths / bash scripts/check-doc-paths.sh | Exit 1: existing archived after-roadmap-va1.md reference to absent optional MathlibTest/SplitIfs.lean; owned handoff link resolves |
| coverage-check / coverage.py | Partial ledger: 138 statements, seven witnesses, 131 pending; never full acceptance |
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
No production refactor or original-source change occurred. New audit file checks take about 0.50 s each.
No RUNTIME_GATE_PASS, full sort-check pass, external EVM test, or cryptographic agreement is claimed.

## Reviews and continuation handoff

Independent finder and skeptic reviews were read-only, used no Lean server/build, and confirmed
seven statement-faithful witnesses and the narrow negative-control interpretation. Their findings
were fixed: mutual block namespace handling; comment offsets; section-variable overclaim; frozen
module-map/source guards; resource evidence wording and sampled monitoring. The scanner regression
line-number typo was corrected. Their final review text is saved off git in reviews.md.

Continue the existing goal only; never create/reset a replacement. Original prompt digest:
39585f8ffb6629c51fc8d1e0fca1808807d9cb06983d0c558dcdc019112450f3.
Original VM/environment:
ccarenv_b64_Y2NhcmVudl83YjM2Yzc3YzA3Njg4MTkxODg3Yjc3MTBhZWVkNzdhMg.
get_goal is not exposed; the goal objective in this thread is authoritative.
Ask the coordinator for a fresh thread on this same VM/branch/goal after this saved handoff.
Do not self-launch another goal. Resume with the migration overlays and owner decision, then
finish all 131 pending candidate applicability witnesses, complete exact elaborated types,
Bridge/gas/fork/compiler boundaries, independent milestone reviews and all final passing gates.
The assignment remains blocked, not complete; the 8-10 hour useful queue has not been exhausted.
