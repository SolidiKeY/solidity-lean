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
`ac9d8db2ad2b29d4f04ed2391d78b5f19b4c97a6`, containing the reviewed audit head
`b299b15d79815ec00ebb81cb74e4ca57acc207c9` and retirement head
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
2. Joint hypotheses remain partial: 300 unique exact-signature links comprise
   40 joint witnesses, 23 H69 intentional impossibilities and 237 closed equality
   statements. The remaining 1,530 rows await classification or witnesses. The
   committed 65-link manual ledger is combined with a separately manifested
   235-link closed-equality ledger; both require exact-once reconciliation.
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
forall telescope, including inputs hidden behind definitions and Not,
packaged as nested Exists ending True. Data, typeclass
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

There are now 92 checked additive theorem declarations: the previous 63, 25
Jumpdest declarations (19 generated witnesses, two scan helpers, four controls)
and four closure/alias regression declarations. The closed-equality classifier
adds zero theorem declarations and retains each unchanged original proof. Printed axiom sets use only
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

Matched Jumpdest audit checking around the definition-aware tool change used
the same core tree, cache and resources: median 5.35364 s before, 5.07186 s
after, delta -5.26%, within the 10% threshold. This measures audit-command
checking, not compiler execution or whole-build performance. Git history showed
no earlier speed change to undo; no original proof source was refactored.

## Reviews, artifacts and continuation

Independent read-only finder and skeptic use no Lean server, heavy calls or
edits. They checked merge fidelity, all 19 exact Jumpdest input tuples, tool
closure and controls, the Bridge capture/join tooling and all ten external
reference fixtures. The suggested ambient-assumption regression was added.
Final receipts and current census live under
the externally supplied evidence archive. The repository-relative verifier
and manifest described below replace reliance on VM-only artifact paths; older
VM directories remain historical snapshots. The current ledger is the small reviewed coverage.json in tests;
bulk census, kernel expressions and logs stay off Git with SHA256 manifests.
Registration suggestions remain additive fragments under tests, not root edits.

Preserved original prompt, complete work/backfill queue and exact 160-file scope
remain authenticated in the committed tests handoff files. Continue this same
original assignment: 1,530 witness/classification rows,
1,793 producer owners, general success/totality and gas/fork boundaries, then
full witness fidelity/reviews/final gates. Signature/type capture is complete;
producer ownership, premise meaning and joint feasibility remain partial. Backfill remains within-scope census, negative
controls, isolated fixtures and deterministic acceptance/reproduction/timing.
A fresh-thread handoff after 3–5 completed items never completes the full goal.

## Checkpoint gates and outstanding validation

All eight audit modules pass on the merged tree; all 92 printed theorem axiom
sets contain no sorryAx. Freshness checks for all 156 mapped core targets and
four mapped Bridge targets pass with Lake --no-build, separately from extraction.
Dependency layers pass (859 core modules, zero elaborator/parser reachability),
generated fragments pass, and scanner acceptance passes.

The global documentation-path check fails on five references in four files:
external artifact StringApiWitness.original-unproved in the migration-theory
report; a synthetic Backend/A fixture in the ABI-world census test; proposed
PanicBytes in the packet-panic candidate; and two proposed GenericMapped module
paths in the structured-flow registration fragment. These files are byte-identical
to the latest authorized integration base ac9d8db2a. No missing reference belongs to
this lane's changed files. The global gate is reported FAIL, not waived or
counted as a pass. Resolving it remains an outstanding repository validation
item, alongside full-library/root checks and the incomplete proof/owner queue.

This checkpoint's committed scope contains only additive audit tooling, proofs,
fixtures, ledger and documentation. The external handoff records the complete
committed head, original base and integration base, exact gate commands/output,
independent reviews, incremental and cumulative owned patches, bundle and hashes.
The original assignment remains active and unfinished; no goal completion or
replacement continuation is authorized by a passing subset of these checks.

## Closed-equality census and portable evidence

The 555 pending records with zero explicit binders were only candidates. Each
actual original theorem was loaded from its defining module in a separate
bounded Lean process. All 36 module checks passed. Exactly 235 candidates are
literal equality propositions with no inputs after definition-aware telescope
expansion and standard axiom sets. Their canonical identities, source names,
frozen signatures and full raw kernel types match the original census. The
other 320 candidates remain pending; zero explicit binders alone is insufficient.

The classifier generates no replacement True lemmas. Each new closed record
retains the original compiled proof. Closed-input accounting establishes neither
semantic nonvacuity nor source-compiler totality; ordinary interface hypotheses
still need simultaneous witnesses. Hidden negative and positive aliases test
the tool's rejection and complete dependent packaging.

Reviewer artifact portability feedback is addressed by the committed
[verification instructions](../../tests/h62/item2/audit-evm-compiler/evidence.md),
a compact committed path/size/SHA256 index. Expanded repository-relative
source pins, archive-relative data pins and all generated evidence remain
outside Git under H44. The verifier authenticates a downloaded archive and
its embedded full manifest before applying the unchanged source/data checks.
Corruption controls cover artifact and source changes, duplicate tar members
and escaping paths. Hash verification does not replay Lean or prove provenance.
Bulk records stay outside Git and are regenerated with the committed classifier
and manifest tools. The original 65-link ledger remains unchanged; an actual
duplicate additional ledger is rejected before output.

The current result is 300 accounted statements and 1,530 pending, with producer
ownership still 37 known and 1,793 unknown. All four original checkpoints remain
partial. The original full goal is preserved, not reset or declared complete.

## H44 packaging split

The held increment's 1,199-line expanded manifest has moved off Git. Only the
compact file/archive index is committed. The expanded 181-source/113-artifact
pins and all corresponding data remain on this VM, with absolute paths, sizes
and SHA256 hashes in that index. All Lean source blobs, theorem statements,
proof gates and budgets are byte-identical to the held checkpoint. No new
audit cases or proof implementation are included in this split.

The unmerged held head is preserved in an external Git bundle before amending
the review increment. The original bulk archive and evidence directories are
retained. Archive verification retains every prior source/artifact check and
adds authentication of the transported full manifest. Source-only verification
now needs the external full manifest, explicitly reflecting H44 storage policy.
The original full assignment remains partial with the same outstanding queue.
