# V16 compiler correctness, transactions and specification transfer

Status: partial backfill; full lane blocked on unpublished concrete prerequisites.
Base: `2fe1f8932f96be15b00df03ba2cde46f64a87758`.
Branch: `codex/solidity-v12-v17-20261031/v16-correctness-transfer`.
Repository: `/workspace/solidity-lean`.

No final G48–G51 contract is proved. No existing reserved implementation is
changed. The only shared changes are append-only module/document registration.
The [G01 contracts](roadmap-g01-interfaces.md), [G03 ledger](roadmap-g03-ledger.md),
[G04 restrictions](roadmap-g04-restrictions.md) and
[scope decisions](../solidity-scope.md) remain binding and unchanged.

## Work and backfill accounting

| Item | State and remaining obligation |
|---|---|
| G48 | Blocked: actual independent SourceSpec/admission/lowering instances and full-profile progress are not published; source handoff explicitly leaves SourceSpec open. No new premise is counted as discharged. |
| G49.01 | Open: compose actual expression/statement/call/pass certificates over every approved intrinsic constructor, without residual fragments. No backend implementation changed here. |
| G49.02 | Blocked: final source lowering and integrated V12–V15 runtime byte/pinned-EVM prerequisites are required. No Bridge application added. |
| G49.03 | Open: full-profile coverage, failure preservation, resource progress, traces and non-vacuity. Toy controls below do not establish compiler coverage. |
| G50.01 | Blocked: actual V14/V15 constructor/creation/runtime-installation composition. |
| G50.02 | Blocked: actual deployment, call, rollback and reachable adversarial transaction composition. The decoded invariant below is only a conditional consequence. |
| G51.01 | Open: calculus rule consumers with exact SolKey correspondence and unchanged Fml.inTarget/verdicts. No reserved rule or closer repaired. |
| G51.02 | Blocked: concrete box/diamond/callback/loop/spec consumers of G49/G50, with matching SolKey correspondence. |
| Backfill A | Partial: finite-prefix stability, observation/resource and decoded-world invariant transport proved. Actual transaction induction, additional relational composition controls and full inhabited divergence/failure/event controls remain open. |
| Backfill B | Partial: scoped axiom pins, inhabited success/revert, no-failure loop and negative failure-bound controls, and two-pass identity-certificate combination control. Full constructor/feature accounting and box/diamond/callback/loop transfer witnesses remain open. |

Exact prerequisite evidence: [source-s05.md](source-s05.md), sections
"Well-formedness and progress interfaces" and "Handoff", explicitly leaves
SourceSpec, failure points and full progress open. Concrete fields needed include
independent Parses/Resolves/WellFormed/InProfile, recorded hash preimages,
compiler-independent stipend/failure readings and admission/lowering certificates.
These are requests to their existing owners, not assigned repairs in V16.
No unmerged branches were fetched, imported or cherry-picked.

All reserved Source/lowering/compiler-pass/storage/memory/copy components,
Backend/Scalar, Storage/Hash, Backend/Environment, Backend/Failure,
Backend/Creation, Opcode/Jumpdest/Assembler/Control/Checks/EvmVectors,
Precompiles/Stipend/FixedPoint, external EVM workers, calculus/closer and
frontend/generated-differential/SolKey/TestSuite owners remain read only.
V11→V12→V13→V14→V15→V16→V17 serial integration obligations remain open.
Component completion is distinct from parent closure. Proposed G03 reconciliation:
record these lemmas only as conditional backfill for G49.03, G50.02 and G51.02;
mark no feature or combination discharged.

## Theorems and exact premises

The new [transport module](../../Solidity/Roadmap/V16/Transport.lean) defines no
source, intrinsic or EVM semantics. All names below have prefix
`Solidity.Roadmap.V16`.

| Name | Premises and consequence |
|---|---|
| completed_stable | A consistent existing prefix family, an ordered pair of bounds and a completed source prefix; the larger prefix is equal. |
| completion_at_need | Actual Cert, pass domain, allowed target environment, source admissibility, Forward, Guard and completion; exact events/outcome and target admissibility at that certificate's supplied need bound. |
| event_at_need | Same certificate/domain/environment/resource/Forward/Guard premises and source event membership; target event membership at need. Completion is not required. |
| event_invariant | Actual Cert/domain/allowed environment, source event invariant at every admissible bound, target admissibility and target Guard; target event invariant. Source failure bounds remain included. |
| decoded_invariant | Full PublicCorrectness, source admission/well-formedness/profile, successful compilation, allowed target environment, admissible target resource and target Guard; an invariant over every admissible intrinsic reached-world list transports to successfully decoded target worlds. |

`decoded_invariant` assumes public correctness and therefore cannot establish
it. The supplied `Cert.need` may itself use choice; these lemmas introduce no
new choice, but final bound computability still needs a concrete audit.
The first four theorems have no axioms. `decoded_invariant` uses only
`propext` and `Quot.sound`. No new axioms, sorry, native_decide,
implemented_by or proof-budget increases are introduced.

[Checks](../../Solidity/Roadmap/V16/TransportControls.lean) reuse the existing G07 semantics
and actual identity certificate. Singleton-hash success and exact revert data
are inhabited; success/revert identification and revert-data erasure are refuted.
A loop at every non-exhausted bound has no completion, but an admissible
exhausted bound reverts. The negative control rejects promoting this to
unconditional divergence over all admissible bounds. The two-pass control checks
the actual composed certificate's need and success observation. These controls
are not external EVM tests or compiler constructor coverage.

## Runtime and validation

Lean: 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`.
Lake: 5.0.0-src+797c613 (Lean 4.24.0).
The clean checkout initially used branch `work`; the assigned branch was created
from the exact base under the repository writer lock. No unexpected work reset.

The VM has a 16 GiB cgroup limit and currently no swap. Both systemd scope
probes failed (no user bus and PID 1 is tail). Those raw failures are retained;
they are superseded for bounded execution by the managed Docker route:
`ubuntu:24.04`, digest
`sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852`,
`--memory=12g --memory-swap=12g`, with observed memory.max=12884901888 and
memory.swap.max=0. Builds use LEAN_NUM_THREADS=1, Lean -j1 via a temporary
alternate TOML, no concurrent LSP/build, and the repository writer lock.
Remaining memory is available to the OS. One existing build/cache tree is reused.

RUNTIME_GATE_PASS: `lake -f lakefile.v16-runtime.toml build Solidity.KeySort`
passed: "Build completed successfully (2 jobs)." Cgroup peak: 25,186,304 bytes.
Transport focused/import closure passed (6 jobs), peak 311,463,936 bytes.
Initial controls check failed due to supplying both conjuncts of toy_forward
where Forward alone was expected; raw failure retained. The corrected controls
check passed (8 jobs), peak 114,647,040 bytes. Final post-pin/two-pass and renamed-module checks passed (8 jobs); the final
log is controls-renamed-final.log in the evidence directory. No per-file Lean MCP diagnostics tool was available;
focused serial Lake checks are used. Cgroup peaks are memory evidence, not
aggregate process RSS measurements. The final controls check sampled aggregate
process RSS every 50 ms: peak sampled RSS 283,764 KiB (including shared mapped
pages); final cgroup peak was 115,216,384 bytes. Whole-lane RSS validation
remains pending.
Disk probe before builds: about 30 GiB free on a 32 GiB overlay; no caches deleted.

Exact-base full doc-path checker fails with 46 missing references; raw output is
retained. The separate no-new-findings comparison is recorded in the handoff.
Layer check passed (174 core modules, none reach elaborators), orphan check
passed (998 reachable, zero orphaned), and staged diff whitespace check passed.
Full bounded run-lean, broader trust gates, external EVM tests and whole-lane validation
remain pending; no missing required gate is counted as passing.

## Independent review

Separate read-only finder and skeptic reviews inspected Transport's actual
statements and proofs without Lean servers/builds. Both found a documentation
overclaim about computability of arbitrary Cert.need. It was fixed to describe
the certificate-supplied bound and retain the concrete computability obligation.
Both found no mathematical mismatch in the five transport proofs and confirmed
they do not establish compiler coverage. Final follow-up finder and skeptic reviews found no new logical or ownership
defect in controls and append-only registration. They required the final
handoff/checksums and post-pin check evidence before any artifact claims.
The docs comparison subsequently found a new Checks basename ambiguity; renaming
the owned module to TransportControls fixed it without editing its existing
owner. Unresolved full-lane requirements stay open.

## Handoff

Evidence directory: `/workspace/scratch/v16-correctness-transfer-evidence`.
The external handoff records final base/head, exact command lines, raw failures,
review follow-ups, patch/bundle paths and SHA-256 checksums. This is a partial
reviewable checkpoint, not a completion of G48, G49, G50, G51 or either backfill.
