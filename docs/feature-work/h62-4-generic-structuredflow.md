# H62 item 4: generic StructuredFlow controls

Owner: `solidity-h62-4-20261106/generic-structuredflow`. Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. Branch: `codex/solidity-h62-4-20261106/generic-structuredflow`. Checkout: `/workspace/solidity-lean`.

## Checkpoint 1 — frozen census complete

All 46 original modules, including all 23 Controls modules, are inventoried. The inventory contains 358 named declarations: 241 theorems, 115 definitions and two abbreviations. Controls contain 179 theorems, 90 definitions and two abbreviations. Two `#guard_msgs` and two `#eval` commands are separate inventory records; they are not four extra semantic cases. Every original file remains byte-identical to the pinned base. No frozen statement, premise, observation, refusal, budget, root or axiom pin was edited.

`scripts/h62/item4/generic-structuredflow/census.py` regenerates the complete declarations, exact source signatures and SHA256s off git. `tests/h62/item4/generic-structuredflow/frozen.json` is the compact seal. Canonical census SHA256: `badb6ddbb9776a6c0d265d779932501da1c5b71fddfd54b2edb8f9a1e2d2d1db`. Full inventory: `/workspace/h62-generic-evidence/census.json`. The scanner is lexical and scoped to the frozen grammar; these hashes are not elaborated Lean type/axiom metadata. All 241 theorem boundaries were independently checked against their actual proof assignment.

Audit 9: all nine For/While/DoWhile × Continue/Return/Break compiler/control pairs are retained; their Source outcomes, fuel, scope, entry and capture obligations remain distinct. Several observations already share MappedCondition/ForBreak facts; this census does not claim all their proofs are duplicate. Audit 11: no listed cons-revert, pushes_zero, allocationCostProg, sourceReverted, HRef/Loc.data or HeapRepr/AllocatorRepr fixture copies were found in this family. Audit 16: only typed mapped-observation fixture consolidation is proposed; Yul Raw/vector generators remain H55-owned and are neither copied nor regenerated here.

### Original module inventory

| Module under `Solidity/Backend/StructuredFlow/` | Theorems | Definitions/abbreviations | Commands |
|---|---:|---:|---:|
| `AssignmentBlocksCompiler.lean` | 1 | 1 | 0 |
| `AssignmentBlocksCompilerControls.lean` | 10 | 4 | 0 |
| `BranchControls.lean` | 9 | 5 | 4 |
| `BranchSelector.lean` | 8 | 1 | 0 |
| `ConditionalContinuationCompiler.lean` | 1 | 1 | 0 |
| `ConditionalContinuationCompilerControls.lean` | 8 | 3 | 0 |
| `ConditionalReturnCompiler.lean` | 1 | 1 | 0 |
| `ConditionalReturnCompilerControls.lean` | 8 | 3 | 0 |
| `ConditionalSequenceCompiler.lean` | 3 | 1 | 0 |
| `ConditionalSequenceCompilerControls.lean` | 10 | 5 | 0 |
| `ConditionalSourceCompiler.lean` | 2 | 1 | 0 |
| `ConditionalSourceCompilerControls.lean` | 12 | 16 | 0 |
| `CoreScopeControls.lean` | 13 | 8 | 0 |
| `CoreScopes.lean` | 6 | 2 | 0 |
| `CoreSequence.lean` | 2 | 1 | 0 |
| `CoreSequenceControls.lean` | 10 | 11 | 0 |
| `DoWhileBreakCompiler.lean` | 1 | 0 | 0 |
| `DoWhileBreakCompilerControls.lean` | 4 | 0 | 0 |
| `DoWhileContinueCompiler.lean` | 1 | 0 | 0 |
| `DoWhileContinueCompilerControls.lean` | 4 | 0 | 0 |
| `DoWhileReturnCompiler.lean` | 1 | 1 | 0 |
| `DoWhileReturnCompilerControls.lean` | 4 | 3 | 0 |
| `ExitControls.lean` | 9 | 0 | 0 |
| `ExitSelector.lean` | 3 | 1 | 0 |
| `ForBreakCompiler.lean` | 3 | 2 | 0 |
| `ForBreakCompilerControls.lean` | 6 | 0 | 0 |
| `ForContinueCompiler.lean` | 2 | 1 | 0 |
| `ForContinueCompilerControls.lean` | 7 | 0 | 0 |
| `ForReturnCompiler.lean` | 2 | 1 | 0 |
| `ForReturnCompilerControls.lean` | 7 | 0 | 0 |
| `MappedBranch.lean` | 7 | 3 | 0 |
| `MappedBranchControls.lean` | 10 | 6 | 0 |
| `MappedCondition.lean` | 5 | 2 | 0 |
| `MappedConditionControls.lean` | 7 | 9 | 0 |
| `ReturnPairCompiler.lean` | 1 | 1 | 0 |
| `ReturnPairCompilerControls.lean` | 6 | 2 | 0 |
| `ReturnTailCompiler.lean` | 2 | 1 | 0 |
| `ReturnTailCompilerControls.lean` | 7 | 7 | 0 |
| `ScopedMappedSequence.lean` | 4 | 2 | 0 |
| `ScopedMappedSequenceControls.lean` | 8 | 8 | 0 |
| `WhileBreakCompiler.lean` | 1 | 0 | 0 |
| `WhileBreakCompilerControls.lean` | 6 | 0 | 0 |
| `WhileContinueCompiler.lean` | 4 | 1 | 0 |
| `WhileContinueCompilerControls.lean` | 7 | 2 | 0 |
| `WhileReturnCompiler.lean` | 1 | 0 | 0 |
| `WhileReturnCompilerControls.lean` | 7 | 0 | 0 |

### Reproduction, review and handoff

Commands (from this checkout):

```sh
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item4/generic-structuredflow/census.py --output /workspace/h62-generic-evidence/census.json
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item4/generic-structuredflow/test_census.py
```

Both exit 0; eight regression/mutation tests pass. They cover all original records, all 241 theorem boundaries, the eight type-level-let conclusions, equation-style signatures, nested comments/strings, declaration/statement/file deletion, CRLF byte drift, nested additions and unhandled declaration refusal. Evidence: `/workspace/h62-generic-evidence/census-tests.log`. Python/source acceptance does not prove Lean correspondence.

Independent read-only finder `census_finder` and skeptic `census_skeptic` used no Lean server or Lean jobs. Both found the initial type-level-let truncation. Finder also identified inconsistent equation-definition signatures; skeptic identified universal-newline normalization and recursive-scan asymmetry. All confirmed findings were fixed and regression-tested. Both re-reviews passed the frozen-family extraction and independently counted the full inventory. The initial rejected seal is retained off git.

## Remaining checkpoints and typed blockers

Checkpoint 2 (parameterized lemma/table), checkpoint 3 (kernel correspondence, negative coverage, deterministic acceptance), and checkpoint 4 (paired performance/full affected validation) are unfinished. Additive drafts and an UNAPPLIED owner patch may be prepared within scope, but they are not checked-proof claims.

`MIGRATION_DEPENDENCY`: official pinned Lean v4.35.0 archive SHA256 `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d` was verified. Actual Lean is 4.35.0, release commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake is 5.0.0-src+eb6cafb. KeySort passes with explicit `-j1`, LEAN_NUM_THREADS=1, 12 GiB cgroup cap and zero swap; its isolated run peak was 93,880,320 bytes. No RUNTIME_GATE_PASS is claimed for the family.

The serial fresh-output MappedCondition import closure exits 1 at read-only `Solidity/Syntax/Raw.lean`, with v4.35.0 String API errors at lines 597, 650, 665, 682 and 684. KeySort, AST and SpecSyntax passed first. No v4.24 per-master cache was used. Evidence and exact commands: `/workspace/h62-generic-evidence/baseline-mapped/{receipt.json,check.sh,gate.log,modules.tsv,memory.peak}`. Failure occurs before the family or additive lemma is checked. This requires the responsible migration owner; it does not authorize this lane to edit Syntax.Raw.

`OWNER_RELAY_REQUIRED`: no exact-file owner agreement has been received. Existing family files remain read-only. No relay.sh or relay connector exists in the supplied workspace/tool list; the saved handoff is for coordinator retrieval as instructed. Any proposed original-file migration and module-map/root registration must be applied by the owner after agreement and measured acceptance.

`PERFORMANCE_UNMEASURED`: the failed dependency check is not a before/after performance result. No speedup or slowdown is asserted. Stop adoption if a valid same-condition measurement exceeds 10% slowdown. A full affected gate, actual new axiom sets, final run-lean.sh gate and owner-approved patch validation remain required.

All coordinator input hashes were verified against `/workspace/h62-coordinator-inputs/sha256.json`. The optional get_goal tool is unavailable; the existing persistent goal was neither reset nor replaced. No pushes, merges, PRs, pre-gates, publishing or generated-root edits occurred.

## Blocked backfill handoff

`GenericMapped.lean` is additive unvalidated source: typed `Fixture`, intrinsic
`program`, proposed `compiled_execution`, distinct-donor `copyFixture` and
same-slot `selfFixture`, typed `fixtures` data table, proposed `fixtures_execute`.
It imports the existing mapped compiler/semantics and introduces no external
dependency, untyped intermediate or semantic outcome reclassification. Source
contains zero sorry/axiom/native_decide/ofReduceBool/maxHeartbeats tokens; actual
new theorem axiom sets remain UNMEASURED because imports do not compile.

`propose.py` exports an UNVALIDATED_UNAPPLIED patch with ten positive proof
replacements in six exact owner files. SHA256:
`2d6f682dc9da8d0991de9e20c0267bf25c60656296cd42a1605f18a8806ad3dd`.
All34 original declarations/statements in those files remain; other24 bodies,
including every refusal, are unchanged. `registration.md` supplies the exact-file
relay request and owner-only relocation/module-map fragment. Its temporary test
module import is unregistered: the proposal is NOT APPLY-READY. No owner agreement
has been received and no original file was edited or overlay applied.

`accept.py --output /workspace/h62-generic-evidence/acceptance-final` exits0:
eight census regressions, three synthetic timing threshold/refusal tests,
deterministic proposal regeneration, textual `git apply --check`, zero forbidden
helper proof tokens and a fresh byte-identical original-family census. This is
source/tooling acceptance only. It explicitly emits semantic/performance PENDING.
`measure.py` requires successful distinct runs of all six affected targets,
identical conditions/tree/pin, unchanged unrelated dependencies, complete module
records and fresh outputs; it stops strictly above10% using integer nanoseconds.
No real paired timing result exists; KeySort-only timings are not family evidence.

The final bounded affected-closure command is recorded verbatim in
`/workspace/h62-generic-evidence/affected-closure/receipt.json`: helper plus all six
Controls targets requested, fresh private objects, LEAN_NUM_THREADS=1, explicit
-j1, one CPU, 12GiB/no-swap, effective4GiB headroom guard, 300s module timeout.
Exit1 in20.456950836s, no resource guard stop, peak774029312bytes. KeySort exits0
in1.894318423s, AST exits0, SpecSyntax exits0; Syntax.Raw exits1 with the same five
v4.35 String API errors. Both source hashes and Git status before/after match.
The helper and affected controls are not reached. No RUNTIME_GATE_PASS follows.

Final independent finder and skeptic re-reviews report all source/tooling
findings fixed; detailed findings, corrections and explicit limits are saved in
`/workspace/h62-generic-evidence/REVIEWS.md`. Neither used Lean. Frozen originals,
all179 Controls theorems and all241 family theorems remain accounted for.

Next coordinator action: relay the Syntax.Raw migration repair from its owner;
obtain V17 exact-file agreement and finalize helper registration; validate helper
axioms, all exact instances and refusals; run matched baseline/candidate timings
and stop above10%; complete full affected and repository run-lean.sh final gates
serially. No full build/correspondence/axiom/timing gate has passed. Persistent
goal must remain blocked, not complete. No replacement goal/thread was launched.

Artifacts for retrieval: `/workspace/h62-generic-export/original.patch`,
`/workspace/h62-generic-export/HANDOFF.md`, `/workspace/h62-generic-evidence/`,
`/workspace/h62-generic-export/SHA256SUMS`. Full committed head is recorded in the
exported handoff and result, avoiding self-referential commit metadata here.

## Successor live-toolchain helper check

The staged GenericMapped helper now passes cache-aware `lake lean` on the actual Lean4.24.0 closure. Its two theorem reports contain only propext/Classical.choice/Quot.sound. Prior direct `lake env lean` failures were missing fetched artifact paths; H88's `lake lean` resolves them without rebuilding or changing semantics. The real MappedCondition dependency build passed106jobs in538.881seconds; helper check2.399seconds. Replayed dependency warnings are retained, not relabelled clean diagnostics.

Only the intrinsic universal compiler execution lemma and its two typed fixture instances are checked. Full original-control correspondence, negative/refusal execution, all-declaration trust audit, paired timings and final affected gates remain unfinished. No4.35migration or whole-family completion is inferred.

## General snapshot correspondence follow-up

`GenericMapped.copy_snapshot` now proves the complete four-memory-cell plus saved-stack snapshot at every natural base. `emitted_snapshot` binds this result to the exact original emitter and mapping expression; base0/base128 are instances. The theorem does not replace the stronger whole-machine equation, which remains `compiled_execution`/`MappedCondition.after`. Natural memory indices do not wrap in this model. Production control declarations and refusal proofs remain unchanged.

Cache-aware bounded check generic-mapped-emitted-1107-02 exits0 in3.267seconds. Both new theorem axiom outputs contain only propext/Classical.choice/Quot.sound. Failed elaboration and recursion attempts remain retained; no budget was raised. Separate independent read-only finder and skeptic found no soundness issue and confirmed the exact snapshot/whole-machine distinction. Finder noted unused simp arguments; dependency and local warnings remain visible. No Lean server/build was used by reviewers.

The inherited `gate.py`/`measure.py` protocol requires a pinned4.35 runtime and matched fresh-private-output receipts across all six original modules. Current successful checks use live4.24 and cannot be substituted into that comparison. No timing acceptance or STOP release is claimed. Exact ten-control correspondence, unchanged refusal coverage, complete declaration audit and final affected gates remain open.

## Ten original positive propositions checked

One off-Git `ExactInstances.lean` combines the checked helper with the original import/namespace contexts and ten exact extracted proposition headers from the six proposed control files. Each proof uses `emitted_snapshot` at its original base0/base128. `bindings.json` records each original declaration name and statement SHA256. Production controls were not modified.

The actual cache-aware bounded check generic-mapped-instances-1107-01 exits0 in112.261seconds, including changed import-closure compilation. This is an importing-consumer check, not a per-module timing or paired performance result. Replayed dependency and unused-simp warnings remain retained. Printed helper theorem axiom sets are standard-only; a complete per-instance/declaration axiom comparison remains open.

This closes only the ten positive proposition-instance check. Full refusal preservation/audit, deterministic committed reproduction of this new test input, independent review, all-declaration trust and matched before/after timing remain required. P7 nonempty-payload rollback and unified event/world/frame coupling remain separate original producer obligations for MIC and G52 consumers; no instance-test result is promoted to those semantics.
