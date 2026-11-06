# H55 source-relations

Base: `4d3790eadb8a5212233bc7d5e345817476b2f590`. Repository: `/workspace/solidity-lean`. Branch: `codex/solidity-h55-sol-20261106/source-relations`.

The coordinator lease correction makes all seven listed existing source paths migration inputs, not write leases. No existing producer/consumer source has been edited. Production migrations await an actual owner notice, accepted handoff, and exact transferred files. New work is confined to this document and `tests/h55/source-relations/`, `scripts/h55/source-relations/`. This is not full assignment completion.

## Runtime and boundaries

Actual Lean 4.24.0, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b; Lake 5.0.0-src+797c613. A local Docker source check of `Solidity/KeySort.lean` printed KEYSORT_PASS under 12 GiB memory and equal memory+swap limits (no swap), one CPU, `LEAN_NUM_THREADS=1`, explicit `-j1`. The reproducible bounded runner saves command, output, exit, elapsed time and enforced runtime bounds outside git. A pass of this prerequisite alone is not a proof-suite or acceptance pass.

The original checkout was clean on `work`, at 8bf83218. `git ls-remote origin refs/heads/master` returned the exact assigned base. Fetch advanced origin/master to that base; the task branch was created there after ancestry checking under the repository writer lock. No reset, push, merge or PR occurred. The goal tools expose stop_goal but not get_goal in this session. No replacement goal was created.

## Queue status

1. Shared inferencer implementation and exact adapters: production edits blocked by the lease correction. Read-only design and standalone backfill proceed. Both fuel and choice order of the Option interface, and exact list Res including auxiliary receiver/slot/call-option results and InferComplete statements, must survive. Selecting the head of the exhaustive list is not an established adapter.
2. Unified value relation and locals/context-map equivalences: production edits blocked by the same correction. Existing primitive correspondence supports exactly bool, uint256 and int256; IntValueRel also supports narrower integer widths with intrinsic range evidence. Backend.Scalar.ValueRel observes ABI words, a different codomain. It must retain signed two’s-complement and full word observation. P12NextInterface.ValueRelation is world-indexed and supports reference relations; replacing it by a scalar-only relation would lose its contract.
3. Consumer requests and controls: read-only census and standalone acceptance are in progress. Owner identity/transfer requests go to the coordinator, not inferred from retired notices.

H58 HOLD remains in force: no Outcome/Word edits, git-ref relays, single-state-file rewrite, generated axiom audit, or outcome-folding work. No theorem weakening, premise/exclusion changes, heartbeat increase, sorry or new axiom is authorized.

## Standalone backfill delivered

`tests/h55/source-relations/InferAcceptance.lean` proves exact equality of the three copied helpers, type membership of successful Option results, exhaustive expression-refusal equivalence, and propagation of exhaustive refusal to every Option fuel. The inhabited boolean control distinguishes zero-fuel refusal from underivability. The success-membership theorem deliberately does not claim derivation identity or selected-list order.

`tests/h55/source-relations/RelationRoundtrip.lean` proves the exact PrimitiveRel and LocalsRel producer graph laws, primitive target uniqueness, ofModel injectivity, total and unique primitive source correspondence, total locals correspondence, and the IntValueRel producer iff for every valid source width/sign with its original range premise. Integer inversion reuses the unchanged `integer_relation_target` in `Solidity/Lowering/V07/DoubleAssignment.lean`.

`tests/h55/source-relations/ContextMapAcceptance.lean` lifts arbitrary heterogeneous pointwise relation equivalence through ContextMap.Related, proves equality of fully world-indexed value/world predicates and equivalence of Aligned, and transports each complete Condition, MemoryCapture and StorageCapture record. It proves exact roundtrips and operand/code preservation. These generic adapters require full universal relation equivalence; the new concrete production relation and that equivalence are still absent. They do not provide inhabited compiler producers or an execution simulation.

All 25 explicitly printed theorem axiom reports in the final suite contain no project axiom or sorryAx: helper equalities use no axioms; the others use subsets of propext, Classical.choice and Quot.sound. This is direct per-theorem reporting, not the H58-held generated axiom audit. No existing source or contract changed.

## Shared-inference design constraints

A shared implementation must remain intrinsic in context, category, syntax and derivation type, depend only on Source typing prerequisites, and leave Source independent of Frontend. A policy over shared rule construction must encode committed refusal and observation order explicitly. A simple replacement of Option.orElse with List.append is insufficient:

- Source implicit assignment commits to assign; a failed assignRefused test does not fall through to copying. The list implementation independently enumerates assignment and copying.
- Source call selection is conversion, struct, builtin, internal call, committing to recognized conversion/struct branches even on later failure. List callIdentRes appends conversion, internal, builtin, struct.
- Source prioritizes constant comparison; list binRes appends constant comparison after operand-pair results.
- Every inferN fuel step matters, including empty argument and slot lists. Public wrappers retain nodes.length + 1.
- abi.decode reads its type-expression argument through decodeTys without requiring an ordinary TypedArgs derivation first.
- Res auxiliary nilList, slot, slotL, pos, recv, named and withValue results are observable. Receiver results are not expression typings.

Before implementation acceptance, prove exact equalities for all four inferN interfaces over every fuel/context/input, all four public wrappers, every indexed Res adapter with both roundtrips, and the entire list after transport over every category. Preserve list order, multiplicity, derivation data and all projection helpers. Reuse unchanged InferComplete theorem statements. Type membership or resolved-meaning uniqueness alone does not discharge these equalities. Proposed shared-module names and their registration fragments must await an accepted owner handoff; this checkpoint adds no production module.

## Exact consumer requests for coordinator routing

Owner identities are deliberately pending the coordinator's current notice. The saved census identifies actual importers plus textual candidates; it does not treat a token match as resolved name use. No message was sent to other owners from this VM.

| Consumer/request | Contract to retain and requested gate |
|---|---|
| Source/Elaborate and Source statement inference owners | Preserve four Option inferN signatures, exact fuel/choice/refusal behaviour and size-bounded wrappers; validate elaboration and statements against exact adapter laws. |
| Frontend/Static/InferComplete, InferStmt, InferStmtComplete, InferExamples owners | Preserve all Res constructors and projections, exact lists, typed_complete/lval_complete/args_complete/slots_complete/hasType_iff statements and controls; no derivation or result-category erasure. |
| Source/Agreement/Primitive and NormalStatement plus Agreement clients | Use proved primitive/local iff adapters while preserving constructor inversion, both intrinsic ranges, all bindings/order and locals-only StateLocalsRel boundary. |
| V07/DoubleAssignment, SourceReads, Conversions, DeclarationGraph and integer users | Preserve every source integer width/sign, range premise, numeric inversion and integerValue observation; retain integer_relation_target clients. |
| V07/ContextMapWrite and ReferenceCapture owners | Preserve heterogeneous slots, position preservation/reflection, write framing and separate alias clauses; use generic Related congruence only after full pointwise equivalence. |
| P12 condition/capture consumers and Backend/Passes/P12ConditionExecution, P12MemoryCapture, P12StorageCapture | Transport full reached-world alignment and complete records, retaining success/revert, nonemptiness, map-free/location, memory HRef.id and storage SRef alias conditions. No scalar specialization of generic contracts. |
| Backend/Scalar certificates and downstream Bridge consumers | Keep ValueRel's exact ABI-word observation, canonical booleans, signed two's-complement and injectivity. A word relation is a separate encoding layer, not a substitute for the Source/model relation. |
| Central registration/documentation owner | No library-root/map/pin edit is supplied. Integrate accepted production module registration and documentation fragments only after the actual migration handoff. |

## Gate ledger

Evidence root: `/workspace/source-relations-evidence`. Hardened runtime directories (infer-acceptance-01 onward) store exact command JSON, raw output, exit/wall result, source snapshots, runtime limits and samples. Later runs also store direct external-script hashes. Initial keysort-01 and infer-baseline-01 predate source manifests, saved sample records, independent process checks and enforced wall deadlines; their completed elapsed times do not establish enforced deadlines. Original failed records are retained.

| Gate/command | Outcome and decisive evidence |
|---|---|
| lean --version; lake --version; lean -j1 --tstack=131072 Solidity/KeySort.lean | PASS, initial keysort-01/output.log prints actual versions and KEYSORT_PASS; keysort-final-01 repeats the prerequisite with the hardened runner and external process timeout. |
| bash /workspace/source-relations-evidence/infer-closure.sh | PASS, infer-baseline-01: 10 unchanged source modules, H55_CLOSURE_PASS, 242.843 s. This initial runner did not independently sample process seriality or input hashes; the emitted commands are serial and explicit -j1. Not a before/after refactor result. |
| lean -j1 --tstack=131072 tests/h55/source-relations/InferAcceptance.lean | PASS, infer-acceptance-01, 2.321 s, exact raw theorem axiom output. |
| bash /workspace/source-relations-evidence/value-chunks/NN.sh (NN 01 through 11) | PASS on all chunks after correcting the monitor's process-exit sample. Original value-prereqs-03 has exit125 (monitor stop), not a proof pass; value-prereqs-03-retry1 passes the identical emitted shell. Each shell contains the exact per-module source command. |
| lean -j1 --tstack=131072 tests/h55/source-relations/RelationRoundtrip.lean | First attempt FAIL, retained relation-roundtrip-01: dependent elimination, inferred witness and unavailable unique-existence notation. Fixed via observation injectivity, explicit intrinsic witnesses and explicit uniqueness formula. relation-roundtrip-02 PASS, 2.706 s; theorem statements retain their full intended contracts. |
| bash /workspace/source-relations-evidence/p12-extra.sh | PASS, p12-prereqs-01, five additional unchanged producer modules, H55_P12_PREREQUISITES_PASS. |
| lean -j1 --tstack=131072 tests/h55/source-relations/ContextMapAcceptance.lean | PASS, contextmap-acceptance-01, 3.526 s. |
| bounded.py standalone-final-01, serial timeout300 lean -j1 --tstack=131072 -o proof-object for each of the three tests | PASS, H55_STANDALONE_PASS, 5.108 s, identical before/after snapshots, proof objects and final theorem reports. Reviewers verified current proof hashes match this run. |
| python3 tests/h55/source-relations/tooling.py | PASS, nested comments, actual Units prose, adjacent comment tokens, prelude and multi-import regressions. |
| git diff --check; git diff --exit-code BASE -- Solidity Solidity.lean SolidityExamples.lean Bridge | PASS, static-01; existing production inputs unchanged. |
| bash scripts/check-trust.sh | PASS, static-01/trust.log: 6277 sources, 289 inventoried implementation/recovery sites, 0 findings. |
| node scripts/check-layers.mjs; register.sh --check; fragments.sh --check | PASS, static-01; no new core dependency or shared-root/fragment edit. |
| bash scripts/check-doc-paths.sh | PASS, static-01: all backticked Lean paths resolve. Existing 115 ambiguous references reported, none missing. |

Every heavy invocation was attached to this VM, serial, with LEAN_NUM_THREADS=1 and explicit -j1. Docker enforces 12 GiB memory and equal memory+swap limits, one CPU, no network; the monitor stops below a 4 GiB available reserve. Hardened proof/source invocations have an external 300-second process timeout and a 600-second wrapper maximum wall. Initial keysort-01 and infer-baseline-01 had no enforced wall/process deadline; they completed in 2.353 s and 242.843 s respectively. keysort-final-01 repeats KeySort under the hardened deadline policy. No heartbeat, cap, swap or effort increase, systemd-run, or Lean server was used. Initial KeySort and initial baseline limitations are stated above.

The production migrations, full affected-module build/proof/control gates, run-lean.sh/full gate, TestSuite/corpus/strict external tests, exact shared-adapter proofs and full-scope Terra acceptance have NOT passed here. No solc/EVM/compiler preservation, reference producer or whole-world agreement follows from these proofs. No matched production before/after measurement exists because production source was not changed; the >10% slowdown stop criterion remains binding for later migration.

## Reviews and repairs

Independent finder and skeptic reviews ran read-only, without Lean/server/builds. Their final reports and source hashes are in evidence/reviews/. Confirmed scanner, runner, external-input identity and census-boundary findings were fixed; the generic P12 comment was made precise and the final suite rerun. A process-exit monitoring stop and first proof-elaboration failure remain in raw evidence. Final reviewers confirmed complete P12 record transport, preserved primitive ranges, exact proof hash agreement, and accurately limited acceptance claims.

## Remaining typed dependencies

- DEP-H55-LEASE: coordinator notice naming current owners, accepted handoffs and exact transferred files. All seven original existing paths remain inputs only. This is a production-work blocker, not an H58 pause.
- DEP-H55-INFER: shared intrinsic implementation plus exact Option/list/Res/projection equalities, with unchanged complete-checker statements and owner-run consumer gates.
- DEP-H55-VALUES: actual canonical relation beside the P12 interface, with concrete PrimitiveRel/IntValueRel/locals/context-map equivalences and full reference/world contracts. Generic extensional transport does not establish that producer's equivalence.
- DEP-H55-CONSUMERS: coordinator-routed owner acknowledgements and actual migrations for the exact requests above, followed by complete scope acceptance and matched checking-speed gates.

The persistent original goal is unfinished. No push, merge, PR, duplicate/reset goal, HOLD work or production lease expansion occurred.

## Saved artifacts

The cache pack is `/workspace/source-relations-artifacts/cache-pack.tar.gz`, SHA256 `24bea0ac9d952c7805841612d363d7b7925f6c7ececcfcbda66394f3b998ac17`. It contains 94 freshly source-checked dependency objects and all three final proof objects, with source/object identities and actual tool hashes. It is a source-check olean pack, not a drop-in Lake trace/native artifact cache; no ship-cache.sh was run. Bulk evidence and object data stay off git.

The committed checksum inventory is `scripts/h55/source-relations/evidence.sha256`. Final source patch, bundle, handoff and aggregate checksums are exported under `/workspace/source-relations-artifacts/`; their exact head/base and paths are in the final CLOUDVM-RESULT and exported handoff. Full pending production gates are not represented as passing artifacts.
