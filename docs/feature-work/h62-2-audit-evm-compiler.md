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
Authorized origin/master fast-forward: `d7a1cbdf597826add5af3533fdaf6b8d91e28f66`,
containing the saved checkpoint `17ba931f5e6edb86955b7bd1cc6514631a695a02`.
The original branch, VM and history are preserved. The original 160 source files
and 321-file dependency closure remain unchanged since the preceding integration.
Original/live captures remain separate, with three pending raw-type differences
from the original base. No original source definition was edited.

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
2. Joint hypotheses remain partial: 345 unique exact-signature links comprise
   56 joint witnesses, 52 H69 intentional impossibilities and 237 closed equality
   statements. The remaining 1,485 rows await classification or witnesses. The
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

At the preceding checkpoint there were 92 checked additive theorem declarations: the previous 63, 25
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

At that checkpoint all eight audit modules passed; all 92 printed theorem axiom
sets contain no sorryAx. Freshness checks for all 156 mapped core targets and
four mapped Bridge targets pass with Lake --no-build, separately from extraction.
Dependency layers pass (859 core modules, zero elaborator/parser reachability),
generated fragments pass, and scanner acceptance passes.

The global documentation-path check fails on five references in four files:
external artifact StringApiWitness.original-unproved in the migration-theory
report; a synthetic Backend/A fixture in the ABI-world census test; proposed
PanicBytes in the packet-panic candidate; and two proposed GenericMapped module
paths in the structured-flow registration fragment. These files are byte-identical
to that checkpoint integration base ac9d8db2a. No missing reference belongs to
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
other 320 candidates remained pending at that checkpoint; zero explicit binders alone is insufficient.

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

The closed-equality checkpoint result was 300 accounted statements and 1,530 pending, with producer
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

## Joint refutations and unified entry witness

The new RefutationAudit module classifies 29 original negative controls and
observation-separation statements under H69. Every command is preceded by its
exact source location and intentional reason. JointRefutation reduces the
entire original telescope, including hypotheses hidden by Not, and proves the
full existential input package impossible using the unchanged original proof.
Its positive/negative guards reject ordinary non-refutations. In particular,
calleeFailure_not_panic separates empty revert from Panic(1); it does not imply
that its successful input certificate is impossible.

EntryAudit witnesses the complete input package of Compilation.correct using
the existing closed mutation_input certificate. The fixture allocates an array
and performs an internal call. JointFromCertificate matches only the final
original proof input to that closed certificate, requires every data and proof
argument to become closed, then kernel-checks the complete nested existential.
No original conclusion supplies an assumption. Conditional certificates and
undetermined extra data are rejected by checked regression controls.

The enrollment generator reproduces exactly 30 new links from these reviewable
commands and successful final receipts. Combined with the original 65 links and
235 closed equalities, this yields 330 unique records: 41 joint, 52 intentional
impossibilities and 237 closed statements. The remaining 1,500 records, producer
owner gaps (1,793 unknown), general supported-source success/totality, complete
negative compiler controls and failure/gas/fork coverage remain unfinished.
This checkpoint adds 35 checked declarations including helper regressions;
all 127 additive declarations pass with only the standard three axioms, no
sorry, new axiom, native_decide or increased proof budget. All twelve modules
were checked serially after refreshing the merged dependency tree.

Finder and skeptic independently accepted the new proof methods, full tuple
construction, classifications and duplicate-free counts. Both required the
three dependency-sensitive type changes to remain explicit and pending.
The external owner ticket records evalE_selected, evalE_operand and evalE_two
with original/current expressions and versioned-pair or isolated-dependency
repair options. No statement repair or scope decision is inferred here.

Lean is 4.24.0 (797c613eb9b6d4ec95db23e3e00af9ac6657f24b), Lake
5.0.0-src+797c613. The bounded KeySort prerequisite passes. The refreshed core
build took 181.09 seconds, peak sampled group RSS 1.67 GB, with at least
12.47 GB available. These are observations on changed dependencies, not a
same-tree before/after speed comparison; no timing improvement claim is made.
No RUNTIME_GATE_PASS or full assignment completion is declared.

At the preceding checkpoint, global static gates were reported independently from proof checks.
The layer gate fails on twelve newly unallowed core-to-non-core edges already
present in integration cc1; its 901 core modules still reach neither elaborators
nor checked parser adapters. This lane changes no original core module, root,
central map or layer allowance. Scanner/corruption controls and fragment checks
pass. Full run-lean/root gates and resolution of the inherited layer gate
failure remain outstanding. No failure is waived or relabeled as a pass.

The current documentation-path gate passes: every backticked Lean reference
resolves, with 132 ambiguity warnings. Earlier documentation-path failures above
are historical and have been resolved on the authorized integration baseline.

## Previous checkpoint handoff (cc1 integration)

The next worker retains the original goal, branch and VM. The cumulative patch,
integration patch, branch bundle, exact committed head and checksum manifest are
exported under /workspace/audit-evm-compiler-evidence/continuation-3-handoff/.
The authenticated compact index points to the full bulk archive and manifest;
expanded data remains off Git. The original rendered assignment, entire
work/backfill queue and exact scope manifest remain in the committed handoff
folder and cumulative patch/bundle. Their historical hashes are retained.

All four original checkpoints remain partial: reconcile producer ownership and
three dependency-sensitive frozen types; jointly witness or classify 1,500
remaining statements; finish supported-program totality, trivial compiler
controls and observable failure/gas/fork boundaries; then complete the full
statement-fidelity census and required final repository gates. The baseline
layer failure requires coordinator integration repair. Independent scanner,
additional witnesses, isolated fixtures, acceptance and timing backfill remain
available within the assigned scope; no new queue or replacement goal is made.

This checkpoint has no original statement/dependent-definition edits, new
axioms, sorry, trust shortcuts, proof-budget changes, push or master mutation.
It does not mark the persistent assignment complete or paused. A fresh-thread
handoff goes through the coordinator after this bounded group of work items.

## Five backend selector joint witnesses

[SelectorAudit](../../tests/h62/item2/audit-evm-compiler/SelectorAudit.lean)
checks the ordinary memory_input, referenceArray_input, object_input,
construction_input and memoryCalls_input interfaces in Compiler.Compilation.
Each witness supplies every actual telescope input together, including the
backend-selector proof, one correlated result/program, contexts, resource
values, state and machine. These originals are equivalences; their Input
expression is on the conclusion side and is not an extra assumed premise.
This establishes feasibility of each selector interface, not compiler totality.

[InputFixture](../../tests/h62/item2/audit-evm-compiler/InputFixture.lean)
recovers all twelve arguments and the existing proof from an exact closed
public Input certificate. It rejects conditional certificates and other closed
propositions. The resulting safe definition is kernel-checked and carries only
standard axioms. Five populated fixtures cover legacy memory, separated reference
arrays, populated objects, object construction and an internal allocation/call.
No defaults, invented assumptions or original statement changes are used.

The enrollment script's selectors-only mode checks exactly five joint records
and their final receipt markers. The prior thirty-case mode retains exactly its
old output. Reconciliation preserves all prior 330 entries and accounts for
335 original statements: 46 joint witnesses, 52 intentional impossibilities,
237 closed equalities, with 1,495 still pending. New helpers add six printed
theorem declarations, for 133 total across fourteen audit modules. Generated
record projections/recursors and five fixture definitions are not counted as
new original authored theorem coverage.

Finder and skeptic independently accepted the fixture method and each exact
selector mapping. The full four-checkpoint queue and all previously recorded
scope, owner, totality, failure/gas/fork and fidelity obligations remain open.
The three frozen-type owner tickets remain pending. New module-map additions
are unassigned registry candidates, not additions to this lane's scope.

The current checkpoint handoff retains the original VM/branch/goal, original
rendered prompt, full work/backfill queue and exact scope manifest. Its external
export directory is continuation-4-handoff under the evidence root. The compact
committed index authenticates all bulk data; new scripts resolve repository
paths from their own location and receive evidence paths as command arguments.
No push, replacement goal, pause or completion is performed.

At the preceding checkpoint, the unchanged strict census command failed its
whole-map byte-identity check after seven coordinator-added rows. That failure is retained in the
gate report. The separate original-scope rescan does not waive it: it verifies
original map preservation, all 160 source blobs against the frozen Git base,
and exactly re-parses the original 1,830 records. Sequence edit validation
rejects non-row insertions, removals, changes and duplicate module paths. A
finder-discovered duplicate-line gap was fixed and covered by regression checks.

On integration 4f0a2d6ab the current layer gate passes: 901 core modules,
no elaborator/parser reachability and zero unallowed edges (107 allowances).
The earlier twelve-edge wait is resolved by coordinator integration. The current
documentation-path gate passes with 135 ambiguity warnings. Strict historical
map identity still fails as recorded above; original-scope verification and all
fourteen per-file proof checks pass. Full root/library gates remain pending.

## Copy selectors and output-equivalence premises

[CopySelectorAudit](../../tests/h62/item2/audit-evm-compiler/CopySelectorAudit.lean)
adds exact joint input packages for memory_copy_input, fixed_input,
copyConstruction_input, memory_copy_free_input and object_rep in
Compiler.Compilation. These are premise-satisfiability results for unchanged
original equivalences. They establish neither conclusion-side representation
truth nor source execution success. The output-equivalence witness instantiates
both entry and output data; it does not assert that the program leaves its
entry state unchanged.

The copy-free witness explicitly supplies the defaulted hasArrayCopy=false
hypothesis together with its backend guard. Its existing closed Input
certificate admits a real destination-check failure, so the source reverts.
This is an ordinary jointly inhabited input, not a contradictory H69 package
or an always-success claim. The other fixtures exercise populated fixed memory,
copying and construction. Three supporting example modules are read-only imports
outside the frozen module-map census; none of their declarations is enrolled.

The enrollment mode for these five cases is mutually exclusive with the old
modes and requires exactly five joint records. Prior thirty-case and five-case
outputs remain byte-identical. All previous 335 records remain accounted exactly
once. The current result is 340 accounted statements (51 joint, 52 intentional
impossibilities, 237 closed equalities), with 1,490 pending. Fifteen audit modules
check 138 printed theorem declarations with standard axioms only. Five additional
fixture definitions remain separate from theorem and original-census counts.

The original full four-checkpoint queue remains partial. Unknown producer owners,
three frozen-type owner tickets, general supported-program totality, complete
negative compiler controls, failure/gas/fork boundaries and final root/library
gates remain open. No Source adequacy or success theorem is claimed by this
increment. Finder and skeptic reviewed the complete tuples, explicit defaulted
guard and semantic boundaries independently without using Lean/server.

The checkpoint handoff retains the original VM, branch and persistent goal,
original rendered assignment, whole work/backfill queue and exact scope manifest.
Its external export directory is continuation-5-handoff under the evidence root.
The committed compact index authenticates a portable archive: downloaded-archive
verification does not require the original VM paths. New code derives repository
paths from its own location and accepts evidence paths as arguments. No push,
master mutation, goal reset, replacement, pause or completion is performed.

The current rescan retains exactly 160 original modules and 1,830 declarations;
eight coordinator-added map rows remain unassigned and unenrolled. Strict map
identity still fails, with the unchanged gate retained. At that checkpoint the fragment gate also failed because the combined
documentation index was out of order relative to its fragments; coordinator
integration subsequently repaired the generated index. Synthetic scope-test paths were replaced with real repository
paths so their map snippets remain meaningful and the documentation-path check
can resolve every quoted Lean filename. No original proof or statement changed.

After the owned fixture-path fix, the final scope controls pass (six tests) and
the documentation-path gate passes with 137 ambiguity warnings. Layer checks
pass with zero unallowed edges. Fragment synchronization and strict map identity
remain failed separately; neither is waived by the passing proof checks.

## All original Compiler interfaces have joint premise packages

[LoopSelectorAudit](../../tests/h62/item2/audit-evm-compiler/LoopSelectorAudit.lean)
finishes the five remaining original Compiler statements: memoryLoops_input_of,
memoryLoops_input, memoryLoopScopes_input_of, memoryLoopScopes_input and
construction_rep. Its nonempty loop and scoped-loop fixtures use populated,
typed source data and actual certificates returned by unchanged lower compilers.
Backend-selector proofs are supplied where present. Input and Room occur only
in the equivalence conclusions and are not asserted by these witnesses.

The construction-output state is explicit typed logical data with empty heap
and unset memory locals. It is not asserted to be an actual execution result
or to satisfy Rep. Its noncomputable annotation reflects that the existing
logical fixture has no generated executable code; the value is still checked
by the kernel with the standard axiom guard. Fully qualified fixture names
avoid accidental capture of original theorem telescope variables. An initial
scope-capture rejection was corrected before any ledger promotion.

All sixteen authored statements in the unchanged Compiler file now have exactly
one joint premise package. This is a completed file-level census, not a
statement of general compiler success or Source adequacy. Across the complete
frozen area, 345 statements are accounted for: 56 joint, 52 intentional
impossibilities and 237 closed equalities; 1,485 remain pending. The new module
adds five checked theorems and eight audit-data definitions; sixteen audit
modules check 143 printed theorem declarations. Prior enrollment outputs remain
byte-identical and duplicate additional records are rejected.

The work/backfill queue remains the original four-checkpoint assignment. Owner
reconciliation, remaining witnesses/classifications, meaningful totality and
compiler controls, failure/gas/fork coverage, the three type-drift tickets and
full root/library gates remain unfinished. All original scope and observation
boundaries stay in force. No new axiom, sorry, trust shortcut, proof budget,
exclusion or frozen-statement change is used. Independent read-only finder and
skeptic reviews accept the full tuples and the limited feasibility claims.

The current export directory is continuation-6-handoff under the evidence root.
It retains the original rendered assignment, entire work/backfill queue, exact
scope manifest, cumulative owned patch and named branch bundle. The compact
committed index authenticates portable bulk evidence; original VM paths are
retrieval metadata, not a requirement for downloaded-archive verification.
The original goal remains unfinished and unchanged; no push, master mutation,
pause, replacement goal or completion is performed.

On the current e0f4251ff integration, layers and fragment synchronization pass.
The documentation-path gate passes with 139 ambiguity warnings. Strict original
whole-map identity remains failed after eight coordinator additions; the
separate original-scope rescan passes without enrolling those additions. The
previous fragment wait is resolved. Full root/library gates and the three
frozen-type owner tickets remain pending; no RUNTIME_GATE_PASS is issued.

## Review clarification and actual checked-entry observation

The five LoopSelectorAudit packages establish binder-level satisfiability only.
They instantiate all original arguments together. They do not show that Input,
Room or Rep is satisfiable: those predicates occur in equivalence conclusions.
The updated classification text makes this boundary explicit without changing
any proof, original statement, signature, coverage status or exclusion.

The index archive_member continuation-2/evidence-manifest.json is intentional.
An authenticated check finds exactly one regular archive member at that path;
its bytes, size and SHA256 match the index, and its archive_root is continuation-2.
It is the compatibility transport prefix, not a checkpoint identifier. The
archive filename and integration metadata identify each checkpoint.

[CheckedEntryAudit](../../tests/h62/item2/audit-evm-compiler/CheckedEntryAudit.lean)
connects the actual Compiler.compile result to the existing nonempty setAge
observation. The closed admission certificate and the owner's read-only
compile_core_some theorem select the core result; its code executes normally
with zero pending jumps and writes 10 at storage slot 13. This result concerns
the actual checked entry rather than a manually supplied Some code candidate.

Four negative controls show that this actual output differs from rejection,
revert-only code, empty code and code with the correct write followed by an
unresolved jump. All use the unchanged WritesAge observation. They cover one
supported intrinsic-model fixture; they establish no general totality, Source
adequacy or external EVM gas/fork result. Owner modules are imported read-only
and their new declarations are not enrolled in the original census.

The increment adds five checked theorems and one code-observation definition.
Seventeen audit modules check 148 printed theorem declarations. Original census
accounting stays 345 (56 joint, 52 intentional impossibilities, 237 closed),
with 1,485 pending and 1,793 producer owners unresolved. All four original
checkpoints remain partial. The three frozen-type tickets, broader success and
failure coverage and full root/library gates remain open.

The current handoff directory is continuation-7-handoff under the evidence root.
It preserves the original rendered assignment, full work/backfill queue, exact
scope manifest, cumulative owned patch and named branch bundle. No original
statement, budget, axiom set or observation changed. No push, master mutation,
new goal, reset, pause or completion is performed.

Current layer, fragment and documentation-path checks pass; the latter reports
140 ambiguity warnings. Strict whole-map identity remains failed after eight
coordinator additions. The original-scope rescan and all seventeen per-file
checks pass. Full root/library gates and type-owner tickets remain unfinished.

## General supported-core success contract

[CoreContractAudit](../../tests/h62/item2/audit-evm-compiler/CoreContractAudit.lean)
defines a contract over arbitrary code-producing candidates with the existing
checked compiler's input shape. Admits requires code for every original inFragP
certificate, independently of source execution outcome. Succeeds retains exactly
the existing fragment, Sim, resource-room and successful source-run premises;
it requires actual admission, normal execution with zero pending jumps, stack
equality and the original final Sim relation. Their conjunction is the contract.
No new support predicate, success oracle or restriction is introduced.

The actual Compiler.compile entry, mapped to its code, satisfies both parts for
all supported core programs. The proof reuses the owner's read-only
compile_core_some and compile_core_success results without changing their
statements or premises. This covers the intrinsic core fragment; it does not
establish Source adequacy, general memory-backend totality or gas/fork behavior.

Four candidate compilers fail this general contract: rejection, unconditional
revert, empty code and actual code followed by an unresolved jump. The existing
joint source_success_joint fixture supplies every success premise together.
The empty-code control uses a typed live storage path and two representation
lemmas to force the source's observed write to equal unchanged storage, giving
0 = 10. The jump control forces one pending jump where the contract requires
zero. Thus normal termination alone cannot satisfy the contract, and the
negative controls do not rely on an empty premise domain.

The increment adds five public contract theorems and two private representation
helpers, all checked with standard axioms. Ten definitions/abbreviations describe
the contract, candidates and typed reference. Eighteen audit modules check 155
printed theorem declarations. Original census accounting stays 345 with 1,485
pending; all earlier enrollment bytes, signatures, statuses and proof links are
unchanged. The three type-drift tickets and 1,793 unknown producer owners remain
open. All four original checkpoints remain partial.

The current export directory is continuation-8-handoff under the evidence root.
It preserves the complete original assignment, full work/backfill queue, exact
scope manifest, cumulative owned patch and named branch bundle. Bulk evidence
remains outside Git with an authenticated compact index. No original statement,
axiom, budget, exclusion or observation changed. The original goal remains
unfinished and unchanged; no push, reset, replacement, pause or completion is
performed.

Current layers, fragments and documentation paths pass; documentation reports
140 ambiguity warnings. Strict whole-map identity remains failed after eight
coordinator additions. The original-scope rescan and all eighteen proof checks
pass. Full root/library checks and the three owner type tickets remain pending.
