# H71 CheckedMul helper candidate — not validated

Upstream now registers the canonical `Solidity/Backend/PrimitivePackets/PanicBytes.lean` module and the test-scoped path is a compatibility import. Earlier staged/unregistered notes below are historical; see the final rebase reconciliation. Independent Lean validation and the remaining gates are still pending.

The coordinator relayed MIC's agreement to review and eventually apply an owner-only patch after the shared helper is publicly available and reviewed. This does not transfer `Solidity/Backend/PrimitivePackets/CheckedMul/Controls.lean` or authorize editing it here. The reply path `/workspace/solidity-compiler10-h70-replies1106/checkedmul-owner.md` is absent in this VM, so the quoted SHA-256 cannot be independently checked; the coordinator message itself supplied the reply text. At that earlier handoff MRS separately reported a 4.35 consumer import-closure blocker at `Solidity/Roadmap/Contracts.lean:1104` without a local source log; a later isolated overlay probe independently reproduced that guard mismatch as recorded below.

## Staged declarations

At the original staging point, `PanicBytes.lean` in this directory imported `Solidity.Source.Observe` and staged these names, each with the exact Source proposition shown; Q1 later authorized including the third proof in the MIC review-only proposal:

```lean
Solidity.Backend.PrimitivePackets.PanicBytes.exact_panic_bytes :
  Source.panicData .arithmetic = [0x4e,0x48,0x7b,0x71] ++ List.replicate 31 0 ++ [0x11]
Solidity.Backend.PrimitivePackets.PanicBytes.panic_not_truncated :
  Source.panicData .arithmetic ≠ [0x4e,0x48,0x7b,0x71,0x11]
Solidity.Backend.PrimitivePackets.PanicBytes.panic_not_empty :
  Source.panicData .arithmetic ≠ []
```

`CheckedMulEquivalence.lean` stages three proof-term equality checks against the unchanged originals using `rfl`. Even if checked, Lean proof irrelevance makes those checks statement compatibility, not equality of axiom sets, execution behavior, case accounting or timing. The quoted test-module import and these checks have not elaborated. The helper's `decide` proofs and printed axiom sets have not been kernel-checked in this environment.

## Registration and unapplied owner proposal

The Q1 review-only patches `/workspace/h62-packet-panic-evidence/checkedmul-proposal-q1.patch` and `/workspace/h62-packet-panic-evidence/checkedsub-proposal-q1.patch` import `Solidity.Backend.PrimitivePackets.PanicBytes` and replace only the proofs of `exact_panic_bytes`, `panic_not_truncated`, and `panic_not_empty`, retaining their exact signatures. All fixture declarations and `#print axioms` lines remain untouched. Earlier non-Q1 patch artifacts are historical. `git apply --check` passes against the reviewed base, which is only a context check. At the original proposal point, the production import did not exist and the source was staged under this test directory. Upstream later registered `Solidity.Backend.PrimitivePackets.PanicBytes`; independent application and validation remain pending. H82 grants standing agreement for additive and proof-only work; the explicit G25 exclusion and restriction on generated roots, central maps and pins still require coordinator handling rather than a repeated owner-permission request for proof-only changes. The original proposal did not itself register or publish the module or modify roots and maps. A final proposal must be regenerated and reviewed against the owner's current file and the actual registered module.

The original audit assigns the two named helpers. The coordinator subsequently relayed Q1 YES for including the third `panic_not_empty` proof-only replacement in the MIC proposal; MRS explicitly requested a review-only three-control CheckedSub candidate. These proposals do not change either producer file, transfer ownership, relax the G25 exclusion, or waive integration gates. No owner application is requested before the proof, original-case, trust, resource, before/after timing and review gates pass. In particular, Source panic bytes establish no target revert payload.

## Actual checks and limits

Pinned archive SHA-256: `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`. Actual versions: Lean `4.35.0`, Lake `5.0.0-src+eb6cafb`. A serialized Lean MCP `Solidity/KeySort.lean` diagnostic returned success with no Lean diagnostics (`keysort-mcp.log`); Python emitted an event-loop shutdown traceback after the result. The staged helper no-build MCP diagnostic returned exit 1 and `Imports are out of date and must be rebuilt` (`panic-helper-mcp.log`). The reproducible `scripts/h62/item1/packet-panic/run_mcp_diagnostic.sh` takes the writer lock, prints toolchain versions and sets the per-process address-space limit. The harness deliberately disables leanclient's automatic dependency rebuild; it did not establish whether a bounded build of the pinned closure would pass. It checks cgroup headroom at 250 ms intervals and applies an address-space limit to each inherited process, but the watcher is not a hard aggregate 12 GiB cap. No full runtime gate or before/after timing was run. Automatic retry, stale imports, warnings and partial results are not treated as proof passes.

Textual `test_mul_proposal.py` and `test_sub_proposal.py` each check all three literal propositions against the corresponding original, patch context, and that their review-only proposal changes only three proof bodies and an import. These are external Python/Git checks, not Lean proofs. The independent read-only finder and skeptic used no Lean; they confirmed the initial statement shapes and caught the unregistered module and extra third edit. The initial proposal was narrowed to the two assigned declarations; after Q1 YES the current review-only proposals include the third as described below. Full affected validation, exact axiom checks, proof-resource/timing comparison, independent final proof review, unchanged full case/refusal/frame/tail/timeout observations, and all original checkpoints remain open.

Both MCP logs contain an event-loop cleanup exception. A subsequent process snapshot showed no live Lean/Lake processes but eight defunct Lean processes adopted by PID 1; this does not establish that all watchdog or timeout paths clean up descendants. The sampled reserve guard is not a hard aggregate cap and the tests above do not qualify as a full runtime gate.

## Isolated byte fixture backfill

`PanicBytesFixture.lean` imports only `Init`. It defines a local copy of the byte recurrence, a fixture selector and modulo-2^256 encoding, and proves eight fixture theorems: the local arithmetic encoding, distinct fixture arithmetic/division codes, canonical length, nontruncation, nonemptiness, and those three conclusions from a supplied equality to the canonical list. The pinned Lean MCP diagnostic completed with `success: true`, no error/warning Lean diagnostics, and `#print axioms` reported no axioms for all eight (`panic-fixture-mcp.log`). The log retains the Python event-loop cleanup traceback and the sampled-memory/defunct-process limitations above.

`test_fixture_source_shape.py` pins the reviewed `Solidity/Source/Observe.lean` and fixture file SHA-256 values and compares the copied recurrence text, selector, modulo, word encoding and panic-code literals. That is a textual drift check only. The fixture has no imported definition or kernel theorem connecting its local encoding to `Solidity.Source.panicData`, original CheckedMul controls, execution or target revert. It is not a substitute for the failed helper diagnostic, equivalence proof, same-condition timing or any original gate. Two independent read-only reviewers checked the fixture and log without Lean; both confirmed this boundary.

The cited isolated migration overlay commit `2a18afcdba00a85645b0b3079704f78ffcd78860` was not present as a local Git object; a remote branch search for the H62 migration names returned no branch. This does not disprove the relayed overlay and is not a migration-gate result.

The independent reviewers noted that substring checks alone do not identify Lean syntax or prove the fixture expression has the claimed semantic role; the reviewed fixture bytes are now pinned as well. The check still is not Lean parsing or a kernel correspondence proof.

The fixture's checked SHA-256 is `60c0c6e2c1747b48384421bba6009ba1360a9f40387012b74864e004681f94f0`; the diagnostic log did not itself record a hash at invocation. A later read-only reviewer snapshot found twelve defunct Lean processes under PID 1 and no live Lean process; the earlier count above is historical. These snapshots do not demonstrate cleanup under all cancellation paths.

## Post-merge Q1 continuation

At the coordinator's explicit request the assigned branch was fast-forwarded to published master `5f14596531efea2be64f1a5e7a83afa5e151e865`; the previous lane head `f3943ea6d0c1f2e9f603e759237c348fe81d1044` is an ancestor, merged upstream at `5ca6d3315e3d76a7da28ed0831f69a8383a51efb`. No source producer was edited. The two current Q1 generators preserve the three proposition strings and alter only the import and those proof bodies; `test_mul_proposal.py`, `test_sub_proposal.py` and `git apply --check` pass as textual checks. An independent read-only finder and skeptic confirmed these limits and used no Lean. At that point, the test-scoped helper and equality fixtures had not elaborated and the production helper module was unregistered; the canonical module was registered later upstream. No axiom, case, runtime or timing gate is established by these proposals.

## Restricted proposal-check follow-up

The Mul/Sub review-only tests now reject several malformed cross-declaration and comment-boundary examples and pin the independently inspected helper bytes by SHA-256. The original producer bytes remain pinned by their patch generators. Independent read-only finder and skeptic reviewed the changes without Lean. The extractor is not a Lean parser; in general it does not determine whether a theorem-shaped header occurs inside a preceding block comment. The pins and manual inspection bound the current inputs, but textual statement equality and unapplied patch checks do not prove theorem equivalence, axiom sets, target behavior or timing; upstream registration is a separate fact.

## Registered helper rebase reconciliation

At upstream `3c2734000413fb142b186e93387306bbb01fd181`, the canonical module is `Solidity/Backend/PrimitivePackets/PanicBytes.lean`, and the former test-scoped module is a compatibility import. The historical notes above describing it as unregistered predate this upstream change. Mul/Sub textual proposal tests now pin the canonical helper bytes at SHA-256 `c1d3eeb8f7c23308ee1b0b33fb7be331e7792f7bf8e646812517453db7428246` while retaining their restricted extractor and negative controls. This rebase does not independently validate the canonical module, its axioms, producer equivalence, affected/full gates or timing; candidate patches remain review-only and G25 originals remain untouched.

## Isolated Hash-overlay consumer result

The registered helper was copied byte-for-byte into a fresh test project in detached upstream overlay `2a18afcdba00a85645b0b3079704f78ffcd78860`. The Lean 4.35 MCP build reported `Solidity.Hash.CollisionBound` built, then failed at `Solidity/Roadmap/Contracts.lean:1104`: its `PublicCorrectness.transfer` guard expected no axioms, while Lean reported `[propext, Classical.choice, Quot.sound]`. The helper `.olean` was absent, so its per-file diagnostic was not reached. Source.Const and Source.Types also emitted deprecation warnings. This independently reproduces the Roadmap mismatch only on the older overlay tree; it does not validate the current-master closure, helper, consumer equivalence or runtime gate. The raw output is `overlay-consumer-attempt1.log` in the off-Git evidence directory. Independent read-only finder and skeptic reviewed the log without Lean. No guard or axiom pin was changed.

## Current-source dependency result

A fresh current-source Lean 4.35 MCP build at diagnostic commit `7ca224b4f7976aa26da556c10cbd4c95aabe6cd8` reached the same `Solidity/Roadmap/Contracts.lean:1104` guard mismatch: expected no axioms for `PublicCorrectness.transfer`, observed `[propext, Classical.choice, Quot.sound]`. `CollisionBound` built with warnings, but the copied registered helper did not produce an `.olean` and its per-file diagnostic was not reached. Independent read-only finder and skeptic reviewed the log without Lean. This is a failed dependency build, not proof of the helper, consumer equivalence, target behavior, axioms or timing. No guard or pin was changed.
