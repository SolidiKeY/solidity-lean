# H71 CheckedMul helper candidate — not validated

The coordinator relayed MIC's agreement to review and eventually apply an owner-only patch after the shared helper is publicly available and reviewed. This does not transfer `Solidity/Backend/PrimitivePackets/CheckedMul/Controls.lean` or authorize editing it here. The reply path `/workspace/solidity-compiler10-h70-replies1106/checkedmul-owner.md` is absent in this VM, so the quoted SHA-256 cannot be independently checked; the coordinator message itself supplied the reply text. MRS separately reports the current 4.35 consumer import-closure blocker at `Solidity/Roadmap/Contracts.lean:1104`, but its source log is absent here and this report is not independently reproduced.

## Staged declarations

`PanicBytes.lean` in this directory imports `Solidity.Source.Observe` and stages these names, each with the exact Source proposition shown (the third is an additive observation, not a proposed producer-file edit):

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

The hypothetical owner patch `/workspace/h62-packet-panic-evidence/checkedmul-proposal.patch` imports `Solidity.Backend.PrimitivePackets.PanicBytes` and replaces only the proofs of `exact_panic_bytes` and `panic_not_truncated`, retaining their exact signatures. The old `panic_not_empty` proof and all fixture declarations and `#print axioms` lines remain untouched. `git apply --check` passes against the reviewed base, which is only a context check. The production import does not exist: the source is currently staged under this test directory. Before any application, the responsible owner/coordinator must approve placement at `Solidity/Backend/PrimitivePackets/PanicBytes.lean`, register the module and appropriate module-map fragment under repository policy, and make it available to the consumer. This is a registration proposal, not a registration or publication; the roots and map were not modified. A final proposal must be regenerated and reviewed against the owner's current file and the actual registered module.

The original audit assigns the two named helpers. MIC asked for a third proposed edit to `panic_not_empty`; it is intentionally absent from the owner patch while Q1 waits on lane `solidity-compiler10-20261028/memory-internal-calls`, item `Q1 panic_not_empty proof`, as routed by the coordinator. No owner application is requested before the proof, original-case, trust, resource, before/after timing and review gates pass. In particular, Source panic bytes establish no target revert payload.

## Actual checks and limits

Pinned archive SHA-256: `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`. Actual versions: Lean `4.35.0`, Lake `5.0.0-src+eb6cafb`. A serialized Lean MCP `Solidity/KeySort.lean` diagnostic returned success with no Lean diagnostics (`keysort-mcp.log`); Python emitted an event-loop shutdown traceback after the result. The staged helper no-build MCP diagnostic returned exit 1 and `Imports are out of date and must be rebuilt` (`panic-helper-mcp.log`). The reproducible `scripts/h62/item1/packet-panic/run_mcp_diagnostic.sh` takes the writer lock, prints toolchain versions and sets the per-process address-space limit. The harness deliberately disables leanclient's automatic dependency rebuild; it did not establish whether a bounded build of the pinned closure would pass. It checks cgroup headroom at 250 ms intervals and applies an address-space limit to each inherited process, but the watcher is not a hard aggregate 12 GiB cap. No full runtime gate or before/after timing was run. Automatic retry, stale imports, warnings and partial results are not treated as proof passes.

Textual `test_mul_proposal.py` checks all three literal propositions against the original, checks patch context and ensures the third proof is not changed. These are external Python/Git checks, not Lean proofs. The independent read-only finder and skeptic used no Lean; they confirmed the initial statement shapes and caught the unregistered module and extra third edit. The proposal was narrowed to the two assigned declarations. Full affected validation, exact axiom checks, proof-resource/timing comparison, independent final proof review, unchanged full case/refusal/frame/tail/timeout observations, and all original checkpoints remain open.

Both MCP logs contain an event-loop cleanup exception. A subsequent process snapshot showed no live Lean/Lake processes but eight defunct Lean processes adopted by PID 1; this does not establish that all watchdog or timeout paths clean up descendants. The sampled reserve guard is not a hard aggregate cap and the tests above do not qualify as a full runtime gate.

## Isolated byte fixture backfill

`PanicBytesFixture.lean` imports only `Init`. It defines a local copy of the byte recurrence, a fixture selector and modulo-2^256 encoding, and proves eight fixture theorems: the local arithmetic encoding, distinct fixture arithmetic/division codes, canonical length, nontruncation, nonemptiness, and those three conclusions from a supplied equality to the canonical list. The pinned Lean MCP diagnostic completed with `success: true`, no error/warning Lean diagnostics, and `#print axioms` reported no axioms for all eight (`panic-fixture-mcp.log`). The log retains the Python event-loop cleanup traceback and the sampled-memory/defunct-process limitations above.

`test_fixture_source_shape.py` pins the reviewed `Solidity/Source/Observe.lean` and fixture file SHA-256 values and compares the copied recurrence text, selector, modulo, word encoding and panic-code literals. That is a textual drift check only. The fixture has no imported definition or kernel theorem connecting its local encoding to `Solidity.Source.panicData`, original CheckedMul controls, execution or target revert. It is not a substitute for the failed helper diagnostic, equivalence proof, same-condition timing or any original gate. Two independent read-only reviewers checked the fixture and log without Lean; both confirmed this boundary.

The cited isolated migration overlay commit `2a18afcdba00a85645b0b3079704f78ffcd78860` was not present as a local Git object; a remote branch search for the H62 migration names returned no branch. This does not disprove the relayed overlay and is not a migration-gate result.

The independent reviewers noted that substring checks alone do not identify Lean syntax or prove the fixture expression has the claimed semantic role; the reviewed fixture bytes are now pinned as well. The check still is not Lean parsing or a kernel correspondence proof.

The fixture's checked SHA-256 is `60c0c6e2c1747b48384421bba6009ba1360a9f40387012b74864e004681f94f0`; the diagnostic log did not itself record a hash at invocation. A later read-only reviewer snapshot found twelve defunct Lean processes under PID 1 and no live Lean process; the earlier count above is historical. These snapshots do not demonstrate cleanup under all cancellation paths.
