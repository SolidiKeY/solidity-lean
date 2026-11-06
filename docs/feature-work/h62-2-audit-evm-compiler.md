# H62 item 2: frozen EVM compiler hypothesis audit

Status: **active, partial**. The coordinator explicitly authorized resuming and
merging origin/master after the retirement checkpoint. The original goal/VM and
branch are preserved; no reset or replacement goal. The historical retirement
instruction and preservation files remain under the assigned tests handoff
folder. The latest resume instruction supersedes its stopped-state directions.

## Checkout, scope and frozen interfaces

Original base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Branch: `codex/solidity-h62-2-20261106/audit-evm-compiler`.
Repository: `/workspace/audit-evm-compiler`; old clean checkout
`/workspace/solidity-lean` preserved.
Authorized origin/master merge fast-forwarded to
`d96f2406d352de7e0b72ba6ac4ab29dc457582c6`, containing retirement head
`eaaaee17fe61e71ac3b5052839c0cf146eae3072` and coordinator checkpoint
`20e492ee9`. All 160 original mapped files and their module map remain identical
to the frozen base. All 321 files in the original core dependency closure are
also unchanged. Other master changes arrived through the authorized merge;
this lane's new writes remain in its tests/scripts/document scope.

H82 permits statement-preserving edits without exact-file agreement; changing
existing statements, dependent definitions, signatures, budgets, axiom sets or
exclusions still needs owner authorization. No such change was made. No push,
master mutation, generated-root/map/axiom-pin edit or new goal was performed.

## Four-checkpoint ledger

1. Inventory remains partial: 1,830 authored theorem declarations in 160 mapped
   modules, including private and no-premise declarations. All 1,830 types
   in 160 modules now have exact kernel Expr/universe/axiom captures, including
   1,721 core declarations and 109 optional Bridge declarations. The four new
   Bridge counts are 25, 7, 61 and 16; no source/kernel rows are unmatched. Generated
   recursors/equations, standard instances and 224 anonymous examples are separate
   from the authored census; the read-only custom theorem-macro sweep found none.
   The scanner's 48 corrected let/match/tuple signatures preserve every identity
   and kernel expression. Producer owner master is established for 37 Opcode/
   Jumpdest records by G45.05 and their headers; 1,793 owners remain unresolved.
   The 570 snapshot write-owner candidates and migration overlays are separate.
2. Joint hypotheses remain partial: 65 unique exact-signature links comprise
   40 joint witnesses, 23 H69 intentional impossibilities and two closed Opcode
   statements. The remaining 1,765 rows await classification or witnesses.
   JumpdestAudit adds exactly one full-telescope witness for each of its 19
   authored declarations. Boundary, lookup and size proof hypotheses use coherent
   actual inputs. No global producer structure is required by these statements.
   Headline witnesses retain one shared nonempty setAge program/state/machine.
3. Success/totality remains partial. setAge admits, writes slot 13 from zero to
   ten and finishes with zero pending jumps. Reject-all, REVERT, empty-code and
   trailing-jump controls fail that observation; overflow reverts exactly. The
   conditional generic non-paying source-success transfer has all its premises
   jointly inhabited. Opcode encoding is total with round trips and rejects
   none/empty/constant-REVERT encoders. Jumpdest controls reject PUSH immediate
   data and truncated PUSH32 data while accepting the following genuine boundary;
   scanning every byte for 0x5b fails the public predicate. These are byte-level
   boundaries, not execution-gas or historical-fork equivalence. Broader supported
   source totality, all public contracts and gas/fork checks remain unfinished.
4. Fidelity and final gates remain partial. The ledger checks frozen names,
   source IDs and signature hashes exactly once. Reconciliation is bookkeeping;
   separate Lean checks and read-only reviews establish proof meanings. Full
   affected-library and run-lean.sh gates have not been claimed complete here.

## Witness tools and H69

JointWitness elaborates a supplied witness against the entire original dependent
forall telescope, packaged as nested Exists ending True. Data, typeclass
certificates and proof hypotheses are all included. The original conclusion
never manufactures a premise. Closed-expression, kernel addDecl and standard
axiom guards are mandatory. A checked negative regression tries to use ambient
contradictory arguments and is rejected by the free-variable guard.

JointImpossible uses the same complete telescope to prove its joint package
impossible only when the original terminal proposition is explicitly False.
H69 accepts these proofs for intentional negative controls, separation lemmas
and refutations. All 23 cases retain exact names, reasons and checked proofs in
the ledger and audit sources. Ordinary statements still require joint witnesses.
SCOPE1 and TC1 are resolved; no premise, exclusion or statement was weakened.
Syntactic is_prop_binder never establishes feasibility by itself.

There are now 89 checked additive theorem declarations: the previous 63, 25
Jumpdest declarations (19 generated witnesses, two scan helpers, four controls)
and one intentional tool-regression fixture. Printed axiom sets use only
propext, Classical.choice and Quot.sound as applicable. No authored sorry, new
axiom, native_decide, trust shortcut or raised maxHeartbeats. Failed initial
elaboration receipts are historical and distinct from passing replacements.

## Versions, resources and gates

Actual Lean 4.24.0, release commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`; Lake `5.0.0-src+797c613`.
The merge keeps v4.24.0. No v4.35 overlay/install. KeySort passed again on the
merged checkout before the new checks. No Lean MCP is exposed, so per-file
checks use bounded Lake env lean, explicit -j1, LEAN_NUM_THREADS=1, writer lock,
no swap and four GiB reserve. One heavy Lean job, no systemd-run or proof-budget
change. No RUNTIME_GATE_PASS is claimed.

Core build evidence retains 321 dependencies: 260 built, 61 existing, zero
failures; separate successful Lake --no-build trace validation establishes
freshness for all 156 mapped core targets. Default metadata budgets reset per
declaration rather than raising proof budgets. The new helper and full Jumpdest
file pass, including the ambient-assumption rejection regression. Initial
concrete decide failures were repaired by using existing well-founded scan
equations, preserving all statements and budgets.

Optional Bridge uses exact frozen manifest Git pins, private serial configs and
v4.24. Public Mathlib cache CONNECT403 is preserved; source builds used
bounded 300-second batches with completed artifacts retained. Two resumed
batches timed out; the third passed in 93.20 seconds, completing all 1,240 jobs.
All four mapped Bridge modules then passed separate bounded type captures.
Reconciliation accounts for every one of the 1,830 declarations exactly once,
with zero pending types and only the three standard axioms in their union. External cache/build diagnostics and
static tests are evidence outside the Lean proof statements. Ten separately
checked EthereumJS 10.1.3 fixtures cover exact/insufficient gas, PUSH0 and CLZ
fork activation, empty reversion, valid jumps and runtime truncated-PUSH zero
extension. The optional engine/common packages are copied from the frozen
repository lock and installed outside Git with lifecycle scripts disabled.
These observations do not prove source-compiler gas/fork equivalence.

Historical matched unchanged Layout timing was -0.65% on the same tree/cache/
resources; this is not a whole-build or post-merge performance claim. No original
proof refactor or reversal of speed changes was performed in this milestone.

## Reviews, artifacts and continuation

Independent read-only finder and skeptic use no Lean server, heavy calls or
edits. They checked merge fidelity, all 19 exact Jumpdest input tuples, tool
closure and controls, the Bridge capture/join tooling and all ten external
reference fixtures. The suggested ambient-assumption regression was added.
Final receipts and current census live under
`/workspace/audit-evm-compiler-evidence/resume-merged`; older directories are
historical. The current ledger is the small reviewed coverage.json in tests;
bulk census, kernel expressions and logs stay off Git with SHA256 manifests.
Registration suggestions remain additive fragments under tests, not root edits.

Preserved original prompt, complete work/backfill queue and exact 160-file scope
remain authenticated in the committed tests handoff files. Continue this same
original assignment: 1,765 witness/classification rows,
1,793 producer owners, general success/totality and gas/fork boundaries, then
full witness fidelity/reviews/final gates. Signature/type capture is complete;
producer ownership, premise meaning and joint feasibility remain partial. Backfill remains within-scope census, negative
controls, isolated fixtures and deterministic acceptance/reproduction/timing.
A fresh-thread handoff after 3–5 completed items never completes the full goal.

## Checkpoint gates and outstanding validation

All eight audit modules pass on the merged tree; all 89 printed theorem axiom
sets contain no sorryAx. Freshness checks for all 156 mapped core targets and
four mapped Bridge targets pass with Lake --no-build, separately from extraction.
Dependency layers pass (859 core modules, zero elaborator/parser reachability),
generated fragments pass, and scanner acceptance passes.

The global documentation-path check fails on five references in four files:
external artifact StringApiWitness.original-unproved in the migration-theory
report; a synthetic Backend/A fixture in the ABI-world census test; proposed
PanicBytes in the packet-panic candidate; and two proposed GenericMapped module
paths in the structured-flow registration fragment. These files are byte-identical
to the authorized integration base d96f2406d. No missing reference belongs to
this lane's changed files. The global gate is reported FAIL, not waived or
counted as a pass. Resolving it remains an outstanding repository validation
item, alongside full-library/root checks and the incomplete proof/owner queue.

This checkpoint's committed scope contains only additive audit tooling, proofs,
fixtures, ledger and documentation. The external handoff records the complete
committed head, original base and integration base, exact gate commands/output,
independent reviews, incremental and cumulative owned patches, bundle and hashes.
The original assignment remains active and unfinished; no goal completion or
replacement continuation is authorized by a passing subset of these checks.
