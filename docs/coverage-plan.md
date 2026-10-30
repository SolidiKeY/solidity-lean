# Full compiler and proof roadmap

The endpoint is a complete compiler for the pinned Solidity language **except
features the user explicitly excluded**, with kernel-checked proofs from source
through executable EVM bytecode. Source-model coverage, a restricted compiler
simulation, passing fixtures, or a list of named proof gaps does not meet this
endpoint. This roadmap replaces the former 19-step feature-coverage plan.
Existing integrated work is reused after checking its exact theorem and input
coverage; the groups below are remaining obligations, not claims of missing code.

## Scope contract

The versioned starting point is [solidity-scope.md](solidity-scope.md), the
[feature manifest](solidity-features.json) and the
[upstream ledger](solidity-upstream-inventory.json). G00 records the precise
user-approved exclusions and their evidence. A manifest exclusion without that
evidence is a scope question to resolve, not permission to drop work. Until that
reconciliation, preserve the recorded profile; never enlarge its exclusions.

The recorded excluded families include general assembly/Yul, gas observations
and exact machine-resource behavior, raw calldata and arbitrary low-level calls,
`delegatecall`/low-level `staticcall`, selfdestruct, salted creation, raw code
observations/execution, physical storage/transient layout and raw memory
observations, observable logs, and listed extra chain/transaction fields. Use the
exact feature IDs and exceptions in the scope document, not this summary, for
admission. The old D1/D2 recommendations to add environment fields and logs are
not approvals. Any such extension is conditional on an explicit user decision.

An implementation refusal, recursive type, signature, combination of features,
proof timeout, difficult theorem, finite test universe or backend limitation is
**not an exclusion**. Neither source admission nor compiler correctness may be
made complete by narrowing the profile, adding an oracle, assuming the desired
result, or treating unsupported input as a successful compilation.

Physical layout being unobservable does not remove the obligation to implement
and prove the compiler's internal storage/memory representation. The compiler
may choose its own representation; matching solc's packing is not required when
excluded observations cannot distinguish it. The abstraction from EVM execution
must still be proved. Hash collisions cannot be dismissed by assuming global
injectivity. Existing cryptographic/environment premises must be stated exactly;
new premises require approval and cannot conceal a representation defect.

## Final proof obligations

These are required artifacts, not existing theorem names. G01 fixes their
intrinsic types and relations; S00–S05 implement the independent source
definitions before preservation proofs begin. Definitions must not make
correctness true merely by running the compiler to define source semantics.

1. **Source admission and parsing:** an independent, pinned source grammar,
   static semantics and operational meaning; a checked parser/resolver, or a
   proof-producing frontend whose certificate is checked in Lean. Prove
   soundness and completeness of acceptance for well-formed in-profile source,
   across compilation units and supported settings. A solc JSON AST, matching
   digest or `ScopeScan.within` alone does not prove source correspondence.
2. **Lowering:** every such source unit lowers to intrinsic programs and a
   contract world, with preserved typing, evaluation order, observable outcomes
   and execution behavior. Prove admission coverage, not just preservation for
   whichever inputs the importer happens to accept.
3. **Compilation:** every lowered in-profile program/contract has executable
   output. Prove each lowering/backend pass, calls, deployment, runtime dispatch
   and linking. Fragment predicates may organize intermediate proofs but cannot
   remain additional restrictions of the final public theorem.
4. **EVM execution:** prove assembly, byte encoding, jumps and the relation to
   a pinned EVM semantics. Cover returns, revert bytes/panic, rollback, payments,
   storage, memory, calldata, transient state and typed external interactions
   wherever in scope. A symbolic-slot or word-memory machine alone is insufficient.
5. **Composition:** one public source-to-bytecode correctness theorem, including
   deployment and transaction sequences, plus coverage/compilability and
   specification-transfer corollaries. State behavior refinement/equivalence and
   nondeterministic environment quantification precisely. Preserve success and
   failure observations; do not permit a compiler that always reverts. Include
   termination/divergence or matching finite-prefix behavior; arbitrary fixed
   fuel cannot stand in for source semantics. Excluded gas/resource observations
   permit an explicit resource abstraction, not silent loss of functional behavior.
   G01/G06 must define it before backend work: for each finite source execution
   prefix, prove a corresponding EVM prefix with sufficient gas/memory/stack/code
   resources under the approved profile; conversely, each target functional step
   must match source behavior. State resource adequacy constructively or by a
   proved bound, never by assuming execution already has the desired result.
   Model unbounded behavior by a consistent family of resourced finite prefixes,
   not a claim that one finite-gas EVM transaction diverges. If an actual fixed
   EVM limit prevents that theorem, record and resolve the conflict with the
   approved profile; do not erase the source program or silently idealize the EVM.
6. **Verification and trust:** soundness of all added calculus rules and their
   connection to compiled executions, audited assumptions, no `sorry` or new
   axioms, and a reproducible kernel check of all public results. Automatic
   theorem search need not decide arbitrary specifications; its approved target
   and exclusions remain unchanged. Incomplete search is distinct from an
   incomplete compiler proof.

This proves this repository's compiler, not the correctness of solc's optimizer
or every solc release. solc remains an external compatibility oracle unless its
output is independently certified by the checked pipeline. An optional external
EVM integration stays in `Bridge/`; the core stays dependency-free.

## VM execution contract

The schedule is **18 lanes** (see [VM assignments](#vm-assignments-revised-2026-10-29)),
each on an isolated **16 GiB VM** for **eight to ten hours including
validation**, with one branch/worktree and a reviewable patch per
checkpoint. The 115 proof work packages below are checkpoints within
those assignments, **not 115 separate VM launches**. An assignment performs
its checkpoints sequentially, reusing the environment, caches and context.

These are unmeasured allocation estimates, not a guarantee that an open research
proof finishes within ten hours. G02 calibrates costs before the implementation
launches; the first batches' measurements are in the sizing rules below. Rebalance checkpoints between assignments when measurements support it;
add a continuation assignment only for actual unfinished work. Keep all theorem
obligations open until integrated. Splitting a proof into smaller lemmas does
not automatically allocate another VM. Never replace an unfinished deliverable
with a refusal, a new exclusion or a promise of a later proof.

- Start with `LEAN_NUM_THREADS=1`, explicit `-j1`, a process-group
  `MemoryMax=12G` and `MemorySwapMax=0`; leave the remaining RAM for the OS.
  Use disk-backed private caches, monitor aggregate RSS and available memory,
  and stop before exhausting the VM. Run Lean MCP or a build, not both.
- A cold build is a prerequisite to measure, not a free operation hidden in
  every estimate. Publish a reproducible dependency cache with source/toolchain
  identities; if clean validation exceeds one timebox, split validation targets
  into VM groups and check their final joint import closure.
- Use [module-map.md](module-map.md), the feature's `localEvidence` and current
  source before editing. Reproduce current behavior and audit existing proofs;
  do not rebuild integrated foundations. Follow [intrinsic.md](intrinsic.md),
  [parallelism.md](parallelism.md) and the matching repository conventions.
- Freeze shared interfaces in G01. Same-wave groups may run concurrently only
  where their writes and proof interfaces are independent. Record ownership of
  shared files; serialize shared edits and integration. A local shared checkout
  also requires the [writer lock](refactoring-progress.md#resource-bounds-and-resuming-work).
- Every group delivers its specified artifact, checks and updated
  coverage/proof ledger. Implementation groups additionally deliver code,
  kernel-checked proofs, inhabited nontrivial witnesses, relevant negative
  controls and feature-combination regressions; audit/measurement groups deliver
  reproducible evidence rather than invented implementation theorems. No `maxHeartbeats` rescue, new axioms, weakened
  observations, changed expected verdicts or extra profile restrictions.
- Handoff: base/patch revision, feature IDs/source constructors, new theorem
  names and exact premises, dependencies, before/after fixtures, checks, audit
  results, elapsed time/peak RSS, and every remaining child obligation. Resource
  stops and timeouts remain open work.
- After each milestone, perform separate read-only finder and skeptic reviews,
  neither using the Lean server. Record and fix confirmed findings in the
  owning feature document. Rebase dependent work on integrated prerequisites;
  the coordinator validates the combined imports and proofs before pushing.

## Groups and dependencies

All rows are planned obligations. No row is marked complete by this documentation
change. The seven waves are dependency phases, not seven simultaneous launches.
Every wave depends on the preceding wave (with the explicit G36.03 deferred-check edge below); within each wave, the additional
prerequisites below define subwaves. Unlisted rows may run together only with
independent writes and the frozen proof interfaces. Work may prepare against an
interface, but cannot pass its final check until actual prerequisites merge.

| Wave | Additional prerequisites within the wave |
|---|---|
| 0 | G03 and G05/G06 follow G00/G01; G07 follows G02–G06 and closes with current-fragment/checker controls only; G49.03 owns future whole-pipeline controls. |
| 1 | G11 follows G08–G10; G15 follows G11–G14. |
| 2 | G23's whole-source composition follows G16–G22. |
| 3 | G25–G31 follow G24; G28 follows G27; G29/G30 follow G28. |
| 4 | G33/G34/G38/G39 follow G32; G35 follows G33/G34; G36's call cases follow G37. |
| 5 | G42 follows G40/G41; G43/G44 follow G42; G47 follows G42–G46. |
| 6 | G49 follows G48; G50 follows G49; G51 follows G50; G54 follows G48–G53; G55 follows G54. G52/G53 can start at the phase boundary. |

G03 owns the detailed module/lemma dependency ledger and must add any newly
found dependency before scheduling. Split cyclic proof interfaces into mutual
induction or shared foundation child groups; do not claim independence by
assuming each other's unproved conclusions.

### Wave 0 — scope, interfaces and measured baseline (G00–G07)

| Group | Deliverable and completion evidence |
|---|---|
| G00 | Freeze the exact approved profile, Solidity/fork/settings pins and exclusion evidence. Reconcile every manifest row and upstream source constructor, including feature combinations; assign every in-profile obligation an owner below. Unconfirmed exclusions remain unresolved work. |
| G01 | Specify intrinsic source/typed/bytecode interfaces, observations, state/world relations and all six final theorem contracts. Specify compositional pass certificates and the frontend, backend and EVM proof boundaries without circular semantics. |
| G02 | Measure cold/warm per-target checking on 16 GiB; publish bounded build/cache reproduction and split any oversized target. Preserve current baseline evidence and identify stale artifacts. |
| G03 | Build the source-constructor/feature → admission → lowering → backend → EVM → theorem ledger, including combinations. Check missing owners/cases mechanically; do not change generated feature statuses without evidence. |
| G04 | Audit current compiler theorems and all fragment/input restrictions: core/memory split, capacities, loops, copies, payment asymmetry, hashes, alias liveness and divergence. Map each restriction to its discharging group. |
| G05 | Audit current frontend/provenance/unsafe elaborator paths and define checked certificate interfaces for raw source, parsed syntax and resolved metadata. Digests prove identity only. |
| G06 | Establish reproducible pinned EVM semantics/observation interfaces and a dependency-free core certificate boundary, with external adapters in Bridge. Inventory every existing machine disagreement and required bridge lemma. |
| G07 | Establish proof/trust regression gates, axiom inventories and inhabited source-to-machine controls; record existing failures separately. Check that malformed source, altered bytecode and always-revert output cannot satisfy the planned contracts. |

G00 status (2026-10-29): pins, exclusion evidence, reconciliation and owners in [feature-work/roadmap-g00-scope.md](feature-work/roadmap-g00-scope.md); its questions Q1–Q6 are answered in [solidity-scope.md](solidity-scope.md#user-decisions-2026-10-29), which confirms all 30 exclusions.

G00 manifest status (2026-10-29): the manifest cites the decisions (30 exclusions tier A, G00 Q2 outcomes on the 23 abstract rows) and `fixedPoint` is in profile (model/missing, owners S00–S02, G08–G47); pin work left for G05/G06 is in [feature-work/roadmap-g00-scope.md](feature-work/roadmap-g00-scope.md#pin-decisions-2026-10-29).

G01 status (2026-10-29): contracts and pass certificates specified in [roadmap-g01-interfaces.md](feature-work/roadmap-g01-interfaces.md) and `Solidity/Roadmap/Contracts.lean` (statements only); its questions Q1–Q8 are answered in [solidity-scope.md](solidity-scope.md#user-decisions-2026-10-29), which lists the contract revisions they require before G01 counts as frozen.

G02 status (2026-10-29): cold/warm/cache-restore measurements on the 16 GiB VM in [roadmap-g02-measure.md](feature-work/roadmap-g02-measure.md): cold `./run-lean.sh` 58 min with `TestSuite/Derived17` OOM-killed beside its siblings (11.5 GiB peak alone), warm 2 s, cache restore 3 s, Bridge 17 min with `Arith/Widths` failing at the base; splits recommended there, not made.

G03 status (2026-10-29): constructor-to-theorem, combination, decision-row and module/lemma dependency ledger in [roadmap-g03-ledger.md](feature-work/roadmap-g03-ledger.md), checked by `scripts/roadmap-g03-ledger.py --check`; no obligation closed, no feature status changed.

G04 status (2026-10-29): base-revision audit in [roadmap-g04-restrictions.md](feature-work/roadmap-g04-restrictions.md) (theorem inventory, restriction ledger and owners); no obligation closed; its questions Q1–Q3 are answered in [solidity-scope.md](solidity-scope.md#user-decisions-2026-10-29).

G06 Osaka re-pin (2026-10-29): the hand-written `scripts/check-*.mjs` EVM vectors pass 16/16 on Cancun and on Osaka; they exercise no Osaka-specific behaviour beyond the EIP-7825 transaction cap, and the frame trace behind "no differing vector" is not committed. The pin commit `0f92a28a` switches their pins ([roadmap-g06-osaka.md](feature-work/roadmap-g06-osaka.md)); the bridge `TargetSchedule` and the Cancun AST fixtures remain G06 obligations.

G01 revision (2026-10-29): `Solidity/Roadmap/Contracts.lean` and [roadmap-g01-interfaces.md](feature-work/roadmap-g01-interfaces.md#decisions-applied) implement the G01 follow-up of both decision rounds, G06's findings F1–F8 and the integration reviews (the hash premise on source-determined preimages, `Fixed.Sane`, the unified hash premises); statements only, pending integration review.

G05 status (2026-10-29): base-revision audit and certificate interfaces in [roadmap-g05-frontend.md](feature-work/roadmap-g05-frontend.md) and `Solidity/Roadmap/Frontend.lean` (statements only); G00 disagreement 6 resolved (link maps recorded, only the empty map admitted; settings are solc's two pipelines); no frontend code changed and no instance exists.

G06 status (2026-10-29): machine inventory (23 disagreements with pinned Osaka), the pinned semantics and observation interfaces, the core/Bridge certificate boundary and bridge lemmas B01–B28 with owners in [roadmap-g06-evm.md](feature-work/roadmap-g06-evm.md) and `Solidity/Roadmap/Evm.lean` (statements only); no obligation closed; its questions Q1–Q3 are answered (second round, 2026-10-29) and encoded.

G07 status (2026-10-29): controls and gates in [roadmap-g07-gates.md](feature-work/roadmap-g07-gates.md): a toy source, EVM and compiler meet `PublicCorrectness` (`Solidity/Roadmap/Controls.lean`), and always-reverting, byte-altering, data-erasing and malformed-source-accepting compilers are refuted; `node scripts/check-g07.mjs` runs the non-circularity, axiom-pin and trust gates and reports base failures (46 doc paths, `Derived17` memory, 37 SolKey mismatches; the G03 ledger baseline is 0 errors) apart from new ones.

Fixed-point status (2026-10-29): reference semantics for G00 Q6 in [fixed-point-semantics.md](feature-work/fixed-point-semantics.md) and `Solidity/Language/FixedPoint.lean` (values, operations and laws; not wired into the frontend or compiler); its scope questions Q1–Q8 are answered and encoded; owners (S00–S02, S04.02, G08–G53) are listed in its §4.

Decision impact (2026-10-29): [roadmap-decisions-impact.md](feature-work/roadmap-decisions-impact.md) maps every user decision to the definitions, theorems, rules, tests, scripts, documents and Codex lanes it affects, with owners; G04 R32–R36 now carry the decided premises; no obligation closed.

Integration notes (2026-10-29):

- **G01 revision held back (second time, 2026-10-29).** Its rework fixed both
  defects below, but `refines` is still unmeetable through `Collided`, which
  requires the source to be failure-free (a real collision after any gas
  failure has no source match).
- **Original hold-back.** Integration review found that its
  `PublicCorrectness.refines` cannot be met for long sessions (the
  2^128-hash bound restricts only the target) and that unconstrained
  `Fixed.regionLen`/`rootSlots` can make the hash premise false on every
  hashing run, letting an always-reverting compiler through. It returns to
  its session; the contracts on master are still the first G01 version.
- **Pending on the G01 revision:** G06's findings F1–F8
  ([roadmap-g06-evm.md](feature-work/roadmap-g06-evm.md)), G05's C1 adapter,
  and one correspondence between G01's and G06's `Fixed`, precompile
  predicates and `keccakWord`, and the hash premises in
  `Solidity/Hash/CollisionBound.lean`.
- **G03 checker follow-ups** (review of the merge): `FROZEN` also silences
  parallel shared writes; `ACK_MODULES` silences findings by module whatever
  their kind; refusal anchors count as stage coverage; some definition
  anchors are tagged `theorem`; proposed G24 children are labelled
  `roadmap`. The discharge parser now reads only the G04 restriction table.
- **Decision-impact follow-ups:** `Storage.full`'s verdict should cite G04
  R24 (solc's `Panic(0x41)` past 2^64 elements); the Lean docstrings of
  `StmtOut.refused`/`compile_correct` still describe the stale payment
  disjunct as live.

G06 status (2026-10-29): machine inventory (23 disagreements with pinned Osaka), the pinned semantics and observation interfaces, the core/Bridge certificate boundary and bridge lemmas B01–B28 with owners in [roadmap-g06-evm.md](feature-work/roadmap-g06-evm.md) and `Solidity/Roadmap/Evm.lean` (statements only); no obligation closed; its questions Q1–Q3 are answered (second round, 2026-10-29) and encoded.

Precompiles lane (2026-10-29, `lane-precompiles`): all 18 Osaka precompiles are computed core definitions with Osaka gas, checked by vectors from Osaka's execution specification; `Precompiles.Osaka.fixed` instantiates G06's `Fixed`, with failure exactly on malformed input (`run_eq_none_iff`) and length-monotonic gas (`gas_mono`) ([precompiles.md](feature-work/precompiles.md)). The stipend cost rule (G06 Q3; backfill item 5) is `Stipend.rule` with the G43 obligation `Stipend.Obligation` ([stipend-cost-rule.md](feature-work/stipend-cost-rule.md)). Bridge agreement (B16) is blocked: the Bridge's Mathlib cache hosts are unreachable from the lane's VM, and the vendored crypto outputs are Python/FFI calls; the agreement table is recorded by reading.

### Independent source definitions — after G00–G07, before wave 1

These six source-definition workstreams implement the source side of G01's interfaces. They
must define semantics from the pinned language specification and reviewed source
rules, independently of the lowering/compiler. Reusing an intrinsic datatype
requires proving its correspondence, not defining the source by compiled output.
S00 precedes S01 and the state/value definitions S04.01–S04.03. S02 follows
S01 and those three definitions. S03.01–S03.03 follow S02; S03.04 composes
them. S04.04 then composes transactions/observations, and S05 follows all
S-groups. Wave 1 follows S05. S03/S04 are parent milestones with proof
checkpoints below, not individual VM launches.

| Group | Deliverable and completion evidence |
|---|---|
| S00 | Implement the pinned source grammar/typed declaration graph and constructor index, with an explicit mapping from upstream syntax. Include syntax outside the profile for precise rejection; preserve intrinsic contexts. |
| S01 | Implement source static typing, resolution judgments and compile-time constant/conversion semantics; prove their well-formedness and constructor coverage. |
| S02 | Implement independent scalar/reference expression semantics, effect ordering, values, aliases and failures; cover every admitted expression constructor. |
| S03 | Implement independent statement/control/call/modifier/constructor operational semantics, including finite traces and divergence, without fixed inlining/fuel limits. |
| S04 | Implement independent aggregate/storage/memory/calldata/world/environment/ABI observations and transaction semantics under approved abstractions. Give inhabited models of the relations. |
| S05 | Compose S00–S04, check the full source-constructor ledger against G00, prove source well-formedness/progress interfaces and independent nontrivial behavior controls. Missing semantic cases block frontend/backend preservation work. |

S00/S01 status (2026-10-29): [source-s00-s01.md](feature-work/source-s00-s01.md). S00: the pinned solc 0.8.38 grammar as intrinsic syntax over `Solidity/Source/` (112 constructors indexed by category and loop/`unchecked` context), its complete constructor index, precise rejection of the six syntax-level exclusions, the checked mapping from all 119 grammar rules and labels and the manifest's syntax features, and the declaration graph. S01: constants, conversions (fixed point per the second round), C3 resolution with builtin profile status, expression and statement typing as derivations elaborated into the intrinsic resolved layer `RExpr`/`RStmt` (every expression and statement constructor classified, 23 of 29 expression constructors typed, the rest deferred with stages), settings over the two pipelines and well-formedness of every body kind; typing is a relation, a checker and derivation uniqueness are open.

S04.01–S04.03 status (2026-10-29): [source-s04-state.md](feature-work/source-s04-state.md). The source state over S01's types and a declaration layout: values with intrinsic ranges, enum bounds and reference locations; recursive aggregates with content-keyed mappings; typed memory with copy and aliasing laws; read-only calldata; storage typed by its layout; ABI words, selectors and Panic/Error revert data under G01 Q5; instance accounts, transient storage, transaction configuration, and a journal whose rollback undoes any operations since a call's entry (`rollback_run`, nested calls, transfers). Aggregate storage copies, calldata decoding, the frame stack and its depth limit, static-call enforcement and logs remain for S04.04.

S02 status (2026-10-29, lane V04; partial): [source-s02.md](feature-work/source-s02.md). Literal typing follows solc (Q1) and uniqueness of meaning is proved for every expression, statement and body (`Typed.unique`, `StmtD.unique`, `RBody.ofDerivation_unique`); type inference computes derivations and `elaborate` builds the program from a resolution, every part tied to its syntax and a derivation (item 1b); the expression semantics on `RExpr` has an arm for every constructor (some `stuck` on unmodelled inputs). Dynamic ABI arguments (`bytes`, `string`, dynamic value-type arrays) are decoded. Open: calldata references, `abi.decode`, `new`, slices, inline arrays, `try`, tuple declarations; ABI decoding of static arrays, structs and external function types (user-defined value types decoded since V04b); immutables assigned in a constructor (such contracts do not elaborate, [source-s02.md](feature-work/source-s02.md)); progress, failure points and `SourceSpec` (V04b, [source-soundness.md](feature-work/source-soundness.md)).

S03 status (2026-10-29, lane V04; partial): [source-s03.md](feature-work/source-s03.md). Statements, modifiers, constructors and call frames as before; public value-type getters, `emit` reverting in static frames and value to non-payable constructors are modelled; horizon independence is proved (`runTx_stable`, `firstDone_runTx`). Open: gas/resource failure points, the stipend rule, Panic 0x41 (allocation too large), `fallback` with parameters, getters of non-value types.

S04.04 status (2026-10-29, lane V04; partial): [source-s04-state.md](feature-work/source-s04-state.md#s0404-transactions). Deployment, transactions, the frame stack, static guards, logs, transient reset and the projection to G01 events, with kernel-checked rollback and reentrancy controls. Open: sender-funds validity is not checked; a call with value from a static frame fails the call instead of halting the frame (EIP-214), fixed by V04b ([source-s04-state.md](feature-work/source-s04-state.md)).

S05 status (2026-10-29, lane V04): [source-s05.md](feature-work/source-s05.md). The composition has the type of G01's `Lang Event Outcome` with consistent sessions, now also showing the events of unfinished transactions and deployments (`sourceLangEvents`, from `runTx_events_mono`, `deploy_approx`); horizon independence is proved, and a stuck transaction is told apart from a divergent one by `txFate` (`stuck_not_diverges`), not in G01's `Prefix`; a callback from depth 1024, or with value from a static frame, fails; the ledger and nontrivial controls as before. `SourceSpec`, failure points and a progress theorem (for a modelled fragment: unmodelled features are `stuck`) remain.

### Wave 1 — source syntax and checked admission (G08–G15)

| Group | Deliverable and completion evidence |
|---|---|
| G08 | Checked lexical analysis of comments, escapes, identifiers, number/unit/string/hex literals and source ranges; prove token/source correspondence and coverage of the pinned lexical classes. |
| G09 | Checked type/declaration syntax, data locations, structs/enums/UDVTs and recursive declaration references; parsing and printing/source certificates with soundness and acceptance coverage. |
| G10 | Checked expression syntax, precedence, associativity, tuple/slice syntax, calls and options; prove parse correspondence for all in-profile expression forms. |
| G11 | Checked statement/function/contract syntax, loops, try/catch, modifiers, inheritance and compilation-unit syntax; prove parse correspondence and assemble whole-source parsing from G08–G10 interfaces. |
| G12 | Resolve imports, remappings, source-unit identities, namespaces and overload signatures; prove declaration identity and resolution correctness/coverage across units. |
| G13 | Check type inference, conversions, constants, UDVT operators and overload selection; certify static semantics and discharge compiler-provided type metadata trust. |
| G14 | Check inheritance linearization, overrides, modifier binding, constructor order, library/using-for resolution and callable identities; prove resolution against the independent source definitions. |
| G15 | Complete admission extraction over all execution roots and observations; prove exact profile classification and coverage. Prove the existing solc-JSON import agrees with certified source, or route the public compiler through the checked frontend. |

G12 status (2026-10-29, lane-static): [frontend-static.md](feature-work/frontend-static.md#g12-imports-identities-scopes-and-overloads). Multi-unit programs over S00 syntax with solc's path resolution and remappings, declaration identities, the file-level scope across imports as a least fixpoint (`Sees`), the judgment `UnitsOK` (imports and imported symbols found, no clash) decided by a resolver proved sound and complete (`globals_sound`, `globals_complete`, `unitsOK_iff`) and conservative over S01's lookup; overload sets across bases (`InheritedFn`, `mem_inheritedFns`) and overload selection. Typing across units and S01's use of the merged overloads are handoffs to lane-semantics.

G13 status (2026-10-29, lane-static): [frontend-static.md](feature-work/frontend-static.md#g13-type-inference-constants-user-defined-value-types). Type inference returning S01's own derivations (sound by construction) and complete for every `Typed`/`LVal`/`StmtD`/`ItemsD` rule (`typed_complete`, `stmt_complete`, `hasType_iff`); S01's `WellFormed` decided (`wellFormed_iff`), the typing component of G05's metadata stage (`metadataChecker`); new relations with checkers for compile-time constant initializers, solc's typed constant evaluation with named array lengths, acyclic constants and user-defined value type operators. S01's per-typing overload uniqueness was a deviation from solc, removed on 2026-10-30 (below); S01's reading of the new relations is a handoff to lane-semantics.

G13 status (2026-10-30, lane-soundness checkpoint 1): [source-soundness.md](feature-work/source-soundness.md#checkpoint-1-integration). The checker follows S02's typing changes (solc literal typing `hexConst`, `shiftTy`, the new `const`/`expr`/`retTuple`/`rethrow` premises) and has arms for `member`, `structNew`, `extCall`, `extCallValue`, `transfer`, `send`, `abiEncode`, `assignCopy` and `LVal.member`; `hasType_iff`, `stmtOK_iff`, `itemsOK_iff` and `wellFormed_iff` hold. With solc's literal typing the overload deviation is gone: `f(0x01)` with `f(uint8)`/`f(bytes1)` is refused, as by solc (`hexCall_typed`).

G14 status (2026-10-29, lane-static): [frontend-static.md](feature-work/frontend-static.md#g14-inheritance-overrides-constructors-modifiers-using-for). New relations `InheritanceOK` (linearization, overrides, required overrides, implementations, `virtual` declarations, base-constructor arguments, modifier invocation resolution, `using L for`) each naming solc's error, decided by checkers (`inheritance_iff`, G05's `inheritanceChecker`); a declarative C3-consistency relation met by S01's `Env.linearize` (`linearize_sound`); constructor order and callable identity (`callable_unique`). Cross-checked on 26 transcribed solc syntax tests; solc's override-graph pruning for 6480, getters, fallback/receive, modifier overriding and several units are recorded gaps.

G11 may link against G08–G10 certificate interfaces during parallel development;
its integrated whole-parser check runs after their implementations merge. The
same rule applies to later composition groups: an interface is not a completed
proof, and their final checks must use the actual implementations.

G08 status (2026-10-29): [frontend-parse.md](feature-work/frontend-parse.md#g08-checked-lexical-analysis). A checked lexer over source bytes (`Solidity/Frontend/Checked/Lexer.lean`): every lexer rule of the pinned `SolidityLexer.g4` classified with a sample (`lexRules_classified`), maximal munch with modes, solc's scanner rules where they differ from the grammar, and the certificate proved for every accepted source: its pieces re-print it (`lex_reprint`), each token's range re-locates it (`lex_locate`), refusals are located (`lex_error_pos`); the string-escape decoder is proved against an inductive grammar (`strBody_sound`).

G09 status (2026-10-29): [frontend-parse.md](feature-work/frontend-parse.md#g09-type-and-declaration-syntax). The token yield of S00's syntax under layouts (attribute orders, string fragments) as the grammar derivation; an untrusted fuel-structural parser to `Syn` checked against it (`parse_sound`, `parse_derives`, `parseType_derives`: translation validation); a canonical printer with round trips; recursive and mutual declaration references; every type and declaration constructor covered (`declCtors_covered`). Unambiguity and completeness of the parse are open.

G10 status (2026-10-29): [frontend-parse.md](feature-work/frontend-parse.md#g10-expressions). Expressions by solc's precedence climbing, the selected tree fixed by `Syn.prec` (levels and associativity of the grammar, refusal where the grammar and solc disagree); level lemmas for every binary constructor (`binary_levels`), every operator parsed (`every_operator`), every expression constructor covered (`exprCtors_covered`), `>>>`/`years` rejected precisely (`expr_out_of_profile`). Translation validated; unambiguity is open.

G11 status (2026-10-29): [frontend-parse.md](feature-work/frontend-parse.md#g11-statements-definitions-and-whole-units). Whole-source parsing to `Syn .unit` from G08–G10 (`parse_sound`, translation validation; completeness and uniqueness open), syntax-level admission (`parseInProfile`), every one of S00's 112 constructors produced by an accepted program (`allCtors_covered`; in-profile ones by admitted programs, `profileCtors_covered`), G05's parse-stage checker (`parseChecker`, `checkUnits_sound`, `produce_accepted`), and the corpus regression over solc 0.8.38's 3542 syntax tests and the repository's `.sol` files (`scripts/parse-corpus.mjs`, baseline `tests/parse-corpus/baseline.json`: 3126 of 3208 expected-accepted tests accepted, 289 of 334 expected-refused refused, every disagreement with its reason; print/parse round trip without failure).

### Wave 2 — lowering and complete source semantics (G16–G23)

| Group | Deliverable and completion evidence |
|---|---|
| G16 | Prove scalar expression lowering for every width/sign, enums, addresses, UDVTs, constants and conversions; exact checked/wrapping arithmetic and operand order. |
| G17 | Prove effectful expression lowering: short-circuit/conditional, tuple targets/captures, references, assignments and update expressions; include aliasing and mixed locations. |
| G18 | Prove aggregate/recursive type admission and lowering: arbitrary in-profile nesting, mappings, structs, arrays, bytes/strings and location conversions; preserve identity, copy/delete and lifetime semantics. Split by type constructor if necessary. |
| G19 | Prove control-flow and modifier lowering: every loop, break/continue/return, repeated placeholders and constructor/initializer composition; no unrolling limit as a source restriction. |
| G20 | Prove callable lowering: getters, receive/fallback within scope, internal/external function values, overloads, inherited/library functions and all parameter/result signatures. |
| G21 | Prove ABI/calldata and exception lowering: nested dynamic/reference values, slices, custom errors, revert reasons and every in-profile panic/catch case; preserve payloads and decoding failures. |
| G22 | Complete ordinary source-world semantics/lowering for typed calls, callbacks, creation/try-new and linked libraries. Include payment entry, balance changes, rollback and source-order failures without bounded call expansion as a semantic restriction. |
| G23 | Prove source lowering for transient lifetime/reset/rollback, allowed environment inputs, cryptographic builtins and event argument effects; maintain recorded excluded observations. Compose source-unit lowering coverage from G16–G22 contracts. |

### Wave 3 — compiler values and persistent representation (G24–G31)

| Group | Deliverable and completion evidence |
|---|---|
| G24 | Unify core/memory compiler entry and state relations with typed pass certificates; compositional sequencing must support mixed programs instead of selecting a restrictive whole-program fragment. |
| G25 | Compile all primitive widths/signs, constants, casts, comparisons, bit operations and checked/wrapping arithmetic; prove machine value agreement and exceptional guards. |
| G26 | Compile scalar/control expressions, captures and effect ordering with a proved stack/frame discipline; preserve short-circuit, tuples and conditional references. |
| G27 | Prove persistent storage representation for structs, all mapping keys, nested fixed/dynamic arrays and recursive paths; internal addressing and hash interpretation must respect the approved abstraction. |
| G28 | Compile storage reads/writes and all lvalue update forms with alias/path commutation; preserve reference identity and live/dangling behavior under the selected source semantics. |
| G29 | Compile runtime-length aggregate storage copies across aliases, preserving mappings and clearing only the correct tails; prove traversal invariant, termination where applicable and rollback. |
| G30 | Compile storage allocation/push/pop/delete and reuse for aggregate elements; replace current fragment length/liveness restrictions with semantic checks and proved representation preservation. |
| G31 | Compile permitted environment, balances, cryptographic builtins and source metadata; expose exact oracle assumptions and prove the target observation bridge, including argument effects of erased emits. |

### Wave 4 — compiler memory, flow and internal execution (G32–G39)

| Group | Deliverable and completion evidence |
|---|---|
| G32 | Prove byte-addressed memory/frame/heap representation and separation, including nested/reference-containing structs and arrays; connect it to the actual target memory model. |
| G33 | Compile allocation/default construction and allocator extension for all in-profile memory types. Emit and prove required allocation/size failures; remove unchecked capacity premises that hide in-profile behavior. |
| G34 | Compile memory paths, aliases, reference writes/rebinding, slices and deletion; prove identity and disjointness properties without a primitive-only restriction. |
| G35 | Compile arbitrary in-profile storage↔memory↔calldata and memory↔memory copies, including dynamic/recursive aggregates; prove snapshot/alias semantics and runtime traversal. |
| G36 | Compile branches, blocks and unbounded loops with general bodies: pushes, payments, shrink, memory, break/continue/returns. Prove iteration/prefix simulation and termination/divergence correspondence under the resource abstraction. |
| G37 | Compile internal calls and internal function values using runtime frames/returns, including recursion and reference results; no finite inlining/call-depth cutoff in the final semantics. |
| G38 | Compile all revert/assert/require/custom-error/panic paths and return payloads; prove exact failure classes, bytes, local unwind and persistent/transient rollback. |
| G39 | Compile transient state, transaction reset, sharing through self-calls/callbacks and rollback, mixed with persistent/memory operations; preserve distinct logical roots. |

### Wave 5 — ABI, world and executable bytecode (G40–G47)

| Group | Deliverable and completion evidence |
|---|---|
| G40 | Compile ABI input decoding and runtime selector/receive/fallback dispatch for every in-profile entry signature; prove validation and decoding-failure behavior without dropping noncanonical accepted cases. |
| G41 | Compile ABI output/error encoding and cross-call decoding for every in-profile aggregate signature; prove offsets, lengths, byte observations and catch dispatch. |
| G42 | Compile typed external/self calls, libraries and function values; prove world relation, arbitrary permitted callees, callbacks, static restrictions and reentrancy across runtime frames. |
| G43 | Compile payments/send/transfer, balance checks and failure propagation with a joint world/payment relation; discharge the current source-success/machine-revert asymmetry rather than exporting a one-way success-only substitute. |
| G44 | Compile constructor/initcode/runtime artifacts, inheritance initialization, deployment/new and try-new, address/world installation and linking; prove fresh instance identity and constructor rollback. |
| G45 | Implement and prove instruction selection/expansion to actual EVM operations, stack manipulation, labels/jumps, assembly and byte encoding/decoding. Structured LOOP/relative jumps must have checked executable realizations. |
| G46 | Prove primitive instruction/byte-memory/storage/environment correspondence with the pinned EVM semantics. Discharge symbolic-slot, word-addressing, truncation and hash-model obstructions or identify an unresolved approved-premise obligation; unresolved means incomplete. |
| G47 | Prove EVM call/create/return/revert and transaction correspondence, including excluded-resource abstraction and finite/infinite traces; actual account execution replaces a payment-acceptance boolean where typed code is in scope. |

G46.05/G27.05 hash premise status (2026-10-29): the approved per-run premises `CollisionFree` and `RegionsDisjoint` and their non-adaptive bounds (q²/2²⁵⁷ and about (q²L + qRL)/2²⁵⁶ for keccak) are proved in `Solidity/Hash/CollisionBound.lean`, and for adaptive runs (eager sampling, repeated queries, early stopping, regions) in `Solidity/Hash/Adaptive.lean` (random-oracle model; `q` counts every oracle query of the run and of whoever chose its inputs); bounded slot offsets are proved for the model's terms (`STy.locate_bounded`); only their tie to compiled code is open ([feature-work/hash-collision-bound.md](feature-work/hash-collision-bound.md)).

G27.05/G46.05 hashed layout status (lane-hashing, 2026-10-29): `Solidity/Storage/HashedLayout.lean` models the storage layout as slot terms read through a hash parameter, proves offsets stay inside their regions for every access path (`STy.locate_bounded`) and that distinct bounded slot terms of one run denote distinct words under the region premise (`Loc.word_inj`, `located_word_inj`); `Solidity/Storage/HashedLayoutEvm.lean` relates the terms to `Evm.Slot` read-only; `Solidity/Storage/HashedKeccak.lean` instantiates the hash with keccak-256 over the injective ABI preimage encoding (`keccak_word_inj`) and `#guard`s solc's slot formula; `Solidity/Storage/HashedSeparation.lean` proves the G27.01–G27.03 separation statements (struct members, mapping keys, array elements and header occupy disjoint slot terms, and distinct words under the region premise); value representation (G27.01–03 read/write agreement), widths and packing, `string`/`bytes` keys and headers remain. The relation to `Evm/Layout.lean` and to compiled code remains G27.05 ([feature-work/storage-hashed-layout.md](feature-work/storage-hashed-layout.md)).

**G45 lane status (assembler, 2026-10-29).** G45.05 byte encoding: the
Osaka instruction datatype, `decode_encode`, `encode_injective` and the
jump-destination theorems are proved in `Solidity/Backend/`. G45.04: the
assembler with labels, relocation, per-label push widths by a terminating
fixpoint and library placeholders, with `assemble_pushTag` (every resolved
jump reaches its label's `JUMPDEST`) and `link_patch`. Decoder agreement
(partial): generated `#guard` vectors against EthereumJS at Osaka and the
vendored EVMYulLean tables; a Bridge module running the vendored decoder
waits on a reachable Mathlib cache. G45.03 preparation: structured
branch/loop expansion into labelled items with unique, defined labels and a
loop layout theorem; the expanded code's execution meaning remains G45.03.
Handoffs per checkpoint are in
[backend-assembler.md](feature-work/backend-assembler.md).

### Wave 6 — whole pipeline, verification transfer and release (G48–G55)

| Group | Deliverable and completion evidence |
|---|---|
| G48 | Compose frontend acceptance/lowering proofs and prove every well-formed in-profile compilation unit reaches the backend. Close all unowned feature combinations and certificate holes from G03. |
| G49 | Compose backend and EVM bridges into runtime source-to-bytecode correctness plus compiler coverage. Prove non-vacuity, observable failure preservation and matching progress/traces with no residual fragment predicates. |
| G50 | Compose deployment and transaction-sequence correctness, reachable-state invariants and adversarial interaction quantification; connect runtime and creation artifacts rather than proving isolated function bodies only. |
| G51 | Complete soundness/coverage of affected calculus rules, box/diamond/callback/spec/loop machinery and specification transfer to G49/G50. Preserve SolKey correspondence, approved automation target and verdicts; proof-search incompleteness cannot restrict compiler coverage. |
| G52 | Complete generated differential testing across source combinations, pipeline/settings variants, deployment, ABI, calls and rollback, with shrinking and retained observations; tests supplement, never replace, G48–G51. |
| G53 | Re-pin SolKey and rerun strict correspondence, corpus and TestSuite proof gates; resolve actual discrepancies without weakening assertions or adding undocumented exclusions. |
| G54 | Reproduce the whole proof closure and axiom/trust audit on bounded 16 GiB validation VMs; verify caches against a clean build, executable artifacts and the public API. Split build targets into child VMs as needed; all must pass on the same revision. |
| G55 | Independent final finder/skeptic audit of the profile ledger, compiler coverage, every theorem/premise and public claims; close all child groups and publish the final evidence. Missing proofs or resource-blocked gates prevent completion. |

## Proof work-package manifest

There are **115 proof work packages**: unsplit S/G rows plus child rows
replacing split S/G parent milestones. These packages preserve the detailed
coverage/proof checklist; the VM assignment table below schedules them in
batches. Parent milestones are not additional work packages or VM launches.
Within a G-parent, checkpoints run in listed order unless G03 records proved
independence; S-parent dependencies are specified above. Composition waits for
all actual prerequisite proofs. G03 refines any oversized checkpoint into
lemmas without changing its obligation or automatically adding a VM.

| Work package | Narrow artifact and proof |
|---|---|
| S03.01 — Structured statements | Implement independent block/branch/loop/break/continue/return transitions and local well-formedness lemmas. |
| S03.02 — Modifiers and constructors | Implement independent modifier placeholder/initializer/constructor transitions with pinned order. |
| S03.03 — Call semantics | Implement independent internal/external/callback/library call-frame transitions using source world/value definitions. |
| S03.04 — Statement composition | Compose statement/call semantics and finite-prefix/divergence judgments, with complete constructor checks and nontrivial controls. |
| S04.01 — State definitions | Implement independent storage/heap/calldata/recursive aggregate state definitions and identity/copy interfaces. |
| S04.02 — Values and observations | Implement source value/ABI/error/environment/cryptographic observation definitions under approved interpretations. |
| S04.03 — World definitions | Implement account/world/transaction configuration, persistent/transient state and frame/rollback relations. |
| S04.04 — Transaction semantics | After S03.04, compose independent deployment/transaction transitions, reset/rollback and observable trace projection. |
| G18.01 — Declaration graph | Certify recursive type graph admission, inline-layout ranks and typed graph-to-source correspondence. |
| G18.02 — Storage aggregates | Prove lowering for structs, mappings and fixed/dynamic storage paths against the source relation. |
| G18.03 — Memory aggregates | Prove lowering for nested/reference-valued memory construction, aliases and updates. |
| G18.04 — Calldata aggregates | Prove lowering for nested calldata, bytes/strings and reference-element slices. |
| G18.05 — Conversions and copies | Prove source location conversions, copy/delete and recursive-copy policy against the agreed semantics. |
| G18.06 — Aggregate composition | Compose these five certificates and close aggregate combinations in G03. |
| G22.01 — Typed source calls | Prove ordinary typed external/self call lowering and source-order failure/return transport. |
| G22.02 — Source callbacks | Prove callback/reentrancy lowering and arbitrary permitted environment execution. |
| G22.03 — Source creation | Prove new/try-new, constructor world installation and rollback lowering. |
| G22.04 — Source libraries | Prove linked library and function-value world-context lowering. |
| G22.05 — World composition | Compose the four lowering relations, including funded entry and nonzero-payment controls. |
| G27.01 — Struct representation | Prove internal storage struct member representation, separation and widths. |
| G27.02 — Mapping representation | Prove representation for all in-profile mapping key types and nested mapping paths. |
| G27.03 — Array representation | Prove fixed/dynamic array headers, elements and nested array paths. |
| G27.04 — Recursive representation | Prove recursive graph paths and observation agreement under the source copy policy. |
| G27.05 — Storage composition | Compose storage representation families and approved hash/address premises without global injectivity. |
| G29.01 — Copy traversal | Implement runtime storage-copy traversal and prove its index/path invariant. |
| G29.02 — Clear and alias | Prove stale-tail clearing, preserved mapping leaves and overlapping-source behavior. |
| G29.03 — Copy composition | Compose runtime storage copy correctness, termination obligations and rollback. |
| G35.01 — Storage to memory | Compile/prove deep storage-to-memory copying with fresh identity and dynamic lengths. |
| G35.02 — Memory to storage | Compile/prove memory-to-storage copying with correct tail clearing and mapping treatment. |
| G35.03 — Calldata copies | Compile/prove calldata-to-memory/storage copies and slices with exact bounds behavior. |
| G35.04 — Memory copies | Compile/prove memory-to-memory alias versus deep-copy cases, including overlap. |
| G35.05 — Recursive traversal | Prove generic typed traversal/copy obligations for recursive and nested graphs; reject no approved source shape. |
| G35.06 — Copy composition | Compose the five location/traversal certificates and mixed-location regression witnesses. |
| G36.01 — Structured flow | Compile/prove blocks, branches, break/continue and early return with frame preservation. |
| G36.02 — General loops | Prove loop simulation for mixed heap/storage mutation, shrinking and iteration allocation. |
| G36.03 — Effectful loop traces | Prove payment/call loops and finite-prefix/divergence correspondence using G37 and G43 interfaces; final check follows G43. |
| G37.01 — Call frames | Implement/prove internal runtime argument, local, result and reference frame transport. |
| G37.02 — Recursive execution | Prove internal recursive call return/prefix simulation without inlining or depth admission limits. |
| G37.03 — Function dispatch | Compile/prove internal function values and full signature dispatch against the frame theorem. |
| G42.01 — Self calls | Compile/prove typed self-call execution with ABI and persistent/transient world sharing. |
| G42.02 — External calls | Compile/prove arbitrary permitted typed callees and return/exception world transport. |
| G42.03 — Callbacks | Prove reentrant callback execution and restored caller frames/invariants. |
| G42.04 — Libraries | Compile/prove linked caller-storage library execution and aggregate arguments/results. |
| G42.05 — External function values | Compile/prove runtime address/selector function values and all in-profile signatures/static restrictions. |
| G42.06 — Call composition | Compose call-mode proofs with rollback, ABI decoding and resource-indexed traces. |
| G44.01 — Constructor code | Compile/prove inheritance initializers and constructor execution, arguments and failures. |
| G44.02 — Creation artifacts | Assemble/prove initcode, installed runtime code, link references and instance identity. |
| G44.03 — Create execution | Prove new/try-new account installation, payments, fresh state and failed-creation rollback. |
| G45.01 — Instruction selection | Prove scalar instruction expansion and target opcode selection. |
| G45.02 — Stack lowering | Prove stack/frame manipulation expansion and instruction stack invariants. |
| G45.03 — Labels and loops | Prove label layout, jump destinations, structured branch/LOOP expansion and backedges. |
| G45.04 — Assembler | Implement/prove assembled instruction offsets, relocation and linked code layout. |
| G45.05 — Byte encoding | Implement/prove opcode/immediate byte encoding and decoder agreement, including PUSH data. |
| G45.06 — Assembly composition | Compose selection/stack/control/assembly/encoding certificates against executable bytes. |
| G46.01 — Numeric EVM bridge | Prove opcode arithmetic, signedness, truncation and control primitive correspondence. |
| G46.02 — Memory EVM bridge | Prove byte-addressed EVM memory and calldata access against compiler representation. |
| G46.03 — Storage EVM bridge | Prove persistent/transient EVM storage accesses against symbolic compiler paths. |
| G46.04 — Environment EVM bridge | Prove approved environment/metadata/balance instruction correspondence. |
| G46.05 — Hash EVM bridge | Prove hash and cryptographic observation bridge under exactly approved interpretations; resolve address collisions without added injectivity assumptions. |
| G46.06 — Machine composition | Compose primitive bridges against the pinned EVM transition relation with exact resource adequacy obligations. |
| G49.01 — Backend composition | Compose expression/statement/call/backend passes for every covered intrinsic constructor. |
| G49.02 — Runtime theorem | Compose byte encoding/EVM bridges with source lowering and prove runtime behavior correspondence. |
| G49.03 — Coverage and progress | Prove compiler coverage and non-vacuity, failure preservation and resource-indexed progress; no residual fragment admission restriction. |
| G50.01 — Deployment theorem | Compose source-to-initcode/runtime installation correctness with constructor failure observations. |
| G50.02 — Transactions theorem | Lift runtime/deployment simulation to reachable transaction sequences and adversarial interactions. |
| G51.01 — Rule soundness | Complete affected rule/soundness bridges for new source/target operations, preserving SolKey correspondence. |
| G51.02 — Specification transfer | Prove box/diamond/callback/loop/spec transfer through runtime/deployment/transaction theorems; keep approved search target unchanged. |
| G54.01 — Clean proof targets | Reproduce clean default/compiler/frontend proof targets under the measured 16 GiB VM cap. |
| G54.02 — Suite proof targets | Reproduce TestSuite/corpus and remaining kernel targets on the same revision under the cap. |
| G54.03 — Trust and closure | Audit axioms/trust inventories, joint public import closure, executable artifacts and clean-cache equivalence after the other validation leaves pass. |

G36.03 is checked after G43, so wave 4 exports its loop interface and
completed G36.01/G36.02 first; the wave-5 barrier excludes only that
deferred check, which remains mandatory before wave 6. G43 cannot assume
G36.03: its payment relation must be proved independently of loop composition.

## VM assignments (revised 2026-10-29)

This is a scheduling proposal calibrated by the first three cloud batches. Each row is a **lane**: one 16 GiB VM
working through an ordered queue of checkpoints on one branch. A parent ID
includes all its child checkpoints. The rows cover all work packages exactly
once. Prerequisites are integrated revisions, not other lanes' unproved
interfaces.

### What the batches showed

- **Wave-0 batches** (`roadmap-w0-20261029`, `roadmap-w1-20261029`): 13 audit,
  specification and measurement assignments each took **15–60 minutes** of
  agent work; the only long step was one ~50-minute cold build.
- **First lanes** (`roadmap-l1-20261029`): five lanes sized for four to ten
  hours finished their whole queues in **about 1.5–3 hours** (fixed point
  1 h 25 min, assembler 1 h 30 min, hashing 1 h 45 min, source 2 h 25 min,
  precompiles about 3 h including a stalled turn), each with per-checkpoint
  finder/skeptic reviews. Cost was about $8–41 per lane.

So a checkpoint list that looks like ten hours is about three, and lanes
must hold roughly three times more work than estimated.

### Sizing rules

- **Fill eight to ten hours.** A lane holds enough checkpoints for eight to
  ten hours of work, including validation — in practice three or four of the
  old roadmap groups, a whole dependency chain rather than one link of it.
  Every lane contains implementation checkpoints with kernel-checked proofs.
- **No lone audits.** An audit, specification or measurement never gets its
  own VM. It becomes the first checkpoint of the lane that consumes its
  result.
- **Keep going.** When a checkpoint is finished (gates pass, finder/skeptic
  reviews applied, pushed to the lane branch), the VM starts the next
  checkpoint in its queue on the same branch, reusing the build cache. It
  stops only when:
  - the queue and the backfill queue are empty;
  - every remaining item needs an unmerged prerequisite from another lane;
  - about ten hours are spent;
  - or a resource limit stops it.
- **Backfill before stopping.** A blocked or empty lane takes the next ready
  item from the [backfill queue](#backfill-queue) before it stops.
- **One cold build per lane.** The cold build is paid once. Later
  checkpoints use per-file Lean server diagnostics and warm rebuilds.
- **Handoff per checkpoint.** Each checkpoint records its own handoff
  (revision, theorems, premises, checks, remaining obligations) in its
  feature document, so the coordinator can integrate a lane in parts.
- **Fewer, longer lanes.** Prefer one lane that runs a dependency chain end
  to end over several lanes that wait on each other; parallel lanes are for
  independent chains.

### Lanes

Wave 0 is complete apart from merges. The remaining work is grouped into 14
lanes (V04–V17) instead of the former 28; each is a dependency chain of
three or four groups. Earlier preparatory lanes already delivered parts of
several groups (noted per row); a lane starts by reading those results.

| Lane | Checkpoints, in order | Starts after | Status (2026-10-29) |
|---|---|---|---|
| V00 | G00, G01 | — | Integrated; the G01 contract revision is in a fifth review round. |
| V01 | G02, G04 | V00 | Integrated. |
| V02 | G03, G05, G06 | V00, V01 | Integrated (with the G06 Osaka re-pin). |
| V03 | G07, S00, S01, S04.01–S04.03 | V02 | Done on `cloud/roadmap-l1-20261029/lane-source`; merges after the G01 revision. |
| V04 | S02, S03, S04.04, S05 | V03 | Partial on `cloud/roadmap-l2-20261029/lane-semantics`: semantics, controls, G01 `Lang` instance, uniqueness of meaning, elaborator, horizon independence and unfinished transactions' events done. Open: calldata references, `abi.decode`, `new`, slices, inline arrays, `try`, tuple declarations; `fallback` with parameters, UDVT decoding (closed by V04b), getters of non-value types; Panic 0x41, the stipend rule, sender funds; immutables assigned in a constructor (contracts fail to elaborate); progress, failure points, `SourceSpec`. V04b (`cloud/roadmap-l3-20261030/lane-soundness`, [source-soundness.md](feature-work/source-soundness.md)): checkpoint 1 (integration with G13's checker) done; checkpoint 2 (preservation of the heap typing) and 3 (gap-relative progress: the value fragment with `return (a, b)`, internal calls (also inside expressions) to modifier-free fragment bodies under a whole-program hypothesis, with the frame derived for elaborated programs up to the override's return types and the dispatched declaration's membership in the unit (`hdec`), the stuck census, three typing gaps closed) partial; checkpoint 4 partial (UDVT argument decoding); checkpoint 5 (`Failures`, `SourceSpec`) not started. |
| V05 | G08, G09, G10, G11 | V04 | Partial (lane `roadmap-l2-20261029/lane-parse`, integrated 2026-10-30): checked lexer and parser, translation-validated against the lane's own transcriptions (`classify`, `Syn.yield`, `Syn.prec`); parse completeness and uniqueness open, so G05's `Checked.complete` and G01's `SourceSpec.Unambiguous` are not met; `-x++`, `~x++` and `a ? b : c = d`, which solc compiles, are refused (G10). Round-trip backfill done. |
| V06 | G12, G13, G14, G15 | V05 | Fixed-point admission rules are prepared (`Solidity/Language/FixedPoint/Literals.lean`). Partial (lane `roadmap-l2-20261029/lane-static`, integrated 2026-10-30): G12 for file-level scopes (typing across units and `N.x` namespaces open); G13 decides S01's `Typed`/`WellFormed`, but the type-metadata trust is not yet removed and UDVT operators do not compose; G14's `InheritanceOK` is stated over the checker's own helpers and accepts programs solc refuses (fallback/receive overrides, getters, modifier overriding); G15 not started. Backfill item 5 (fixed-point mobile constants) done. |
| V07 | G16, G17, G18, G19 | V06 | — |
| V08 | G20, G21, G22, G23 | V07 | — |
| V09 | G24, G25, G26, G31 | V08 | G24's foundation children come from G03; G31's precompile and stipend parts are prepared (`Solidity/Precompiles/`, `Solidity/Stipend/Rule.lean`). |
| V10 | G27, G28, G29, G30 | V09 | G27.01–G27.03 separation and the hashed layout are prepared (`Solidity/Storage/Hashed*.lean`); the representation halves and G27.04/G27.05 remain. |
| V11 | G32, G33, G34, G35 | V10 | — |
| V12 | G37, G36.01, G36.02, G38, G39 | V11 | — |
| V13 | G40, G41, G42 | V12 | — |
| V14 | G43, G36.03, G44, G45 | V13 | G45.05, G45.04 and the G45.03 expansion are prepared (`Solidity/Backend/`). |
| V15 | G46, G47 | V14 | Needs the Mathlib cache hosts for its Bridge adapters (backfill). |
| V16 | G48, G49, G50, G51 | V15 | — |
| V17 | G52, G53, G54, G55 | V16 | — |

The remaining dependencies (G03's ledger) make the lanes one chain: each
starts when the previous one is merged. Lanes run in parallel only through
backfill and prepare-against-interface work, never through a final check. G02's measurements apply per lane: one cold build
of about an hour, then warm rebuilds of minutes; a lane whose edits touch a
low module such as `AST.lean` pays about an hour per full rebuild. G03's
shared-foundation child packages under G24 (decision G03 Q1) are not yet in
the manifest: G03's ledger lists them under "Integration steps" and its
checker applies them through `PROPOSED_PACKAGES` until they land. A lane
that still finishes early takes backfill items or the next ready lane's
first group, and the coordinator merges the lane in parts.

### Backfill queue

These items are ready now, are independent of the lane order, and are owned
as listed. A lane takes them in this order when it is blocked or its queue
is empty, unless the item touches files an open Codex lane owns
(`Solidity/Evm/**`, the Bridge Widths files, TestSuite `Derived*`).

1. **Hash regions** — done (lane-hashing, 2026-10-29). (G27.05/G46.05 preparation): the region predicate and its
   counting bound next to `Solidity.Hash.CollisionFree`, if the hash-bound
   task leaves it as a child obligation.
2. **Fixed-point reference semantics** (S01/S02 preparation): complete the
   fixed-point module of the fixed-point-semantics task for the second-round
   decisions and prove the remaining laws.
3. **Osaka residue** (G06): the Bridge `TargetSchedule`, the hash-pinned
   Cancun AST fixtures and the core machine's fork, after the Codex
   evm-* lanes merge.
4. **Stale payment disjunct** (G04 R32, G43 preparation): a statement-only
   change that drops the never-constructed `refused` case of `StmtOut`. It
   waits for the Codex memory/evm lanes, because it edits
   `Solidity/Evm/**`.
5. **Fixed-point mobile constants** — done (lane-static, 2026-10-29). (S01): encode the decision that a
   standalone fractional constant takes solc's mobile type with truncation,
   also as an ABI argument, in `Solidity/Language/FixedPoint/Literals.lean`
   (the merged model still refuses `abi.encode(0.1)` as solc does).
6. **Source cost rule for stipend payments** (decision G06 Q3, S02/G43
   preparation): define the compiler-independent rule and its examples.
7. **Bridge decoder agreement** (G45.05, decision 2026-10-29): once the Lean
   environment allows the Mathlib cache hosts (`lakecache.blob.core.windows.net`,
   `mathlib4.lean-cache.cloud`), add a `Bridge/` adapter that runs the vendored
   EVMYulLean `decode`/`D_J` against `Solidity/Backend`; until then agreement
   rests on the generated vectors in `Solidity/Backend/EvmVectors.lean`.
   The same applies to the precompiles (lane decision, 2026-10-29): the Bridge
   adapter checks `Solidity/Precompiles/` against the vendored EVMYulLean gas
   rows and `IDENTITY` by proof; MODEXP and 0x0b–0x11/0x100 are B01 re-pin
   obligations; until then the record is the reading-based table in
   [precompiles.md](feature-work/precompiles.md).

## Done when

Completion requires **all** of the following on one integrated revision:

- Every approved in-profile source form and feature combination is accepted and
  compilable, with no implementation/proof gap disguised as an exclusion. Every
  `model` row is `present`; every `abstract` row is implemented under its stated,
  approved environment. An inventory status alone is not proof.
- G48–G50 expose kernel-checked public source-to-executable-bytecode theorems,
  coverage proofs and nontrivial witnesses for the full profile, with only
  approved environment/resource/cryptographic premises. Parsing, resolution,
  lowering, assembly and the actual EVM bridge are included.
- No residual `inFrag`/memory-only/static-copy/signature/finite-fuel restriction
  narrows the public theorem. No premise assumes the source safety/correctness
  property being claimed, and success/failure observations cannot be erased.
- Every new rule is sound and G51 transfers verified source specifications to
  compiled contract executions. Approved proof-search exclusions do not become
  compiler exclusions or excuses for missing preservation proofs.
- All integrated kernel/trust/build gates pass, the TestSuite has zero pending,
  and the upstream corpus has zero unexplained broken or blocked in-profile
  rows. Every excluded, invalid-upstream or resource-observation-only row has an
  exact ledger justification; finite oracle agreement is never a theorem.
- All child groups, review findings and scope questions are closed, with the
  revision, commands, theorem names, assumptions and measured resource costs
  published. A timeout or an unfinished proof keeps the roadmap open.

## Relationship to existing work

The old 19 groups addressed source/model gaps, automation and tests. They are
absorbed into G00–G07 (baseline/hooks), G12–G23 (source gaps), G27–G44 (backend
work), and G51–G54 (rules, tests and SolKey). The former final rerun is now part
of G54/G55, not a weaker alternative completion condition.

The ten earlier cloud snapshots and the
[2026-10-28 integration](feature-work/cloud-integration-20261028.md) are inputs
to the initial audit, not evidence that the corresponding full-profile theorem
already exists. [compiler-verification.md](compiler-verification.md) records the
current fragment theorem; [assurance.md](assurance.md) records its trust and
representation premises; [solc-validation.md](solc-validation.md) distinguishes
external compiler tests from proofs.

## Historical baseline (2026-10-28)

Preserved evidence from the earlier coverage plan; not a fresh measurement of
the current checkout and not a completion verdict for this roadmap.

The fresh baseline starts at `f4dee4a29c2e208b36db4a4161a4723c735cd775`.
All ten collected cloud snapshots are ancestors; unmerged work is excluded.
The combined 9,660-fixture report has **4,135 working, 196 broken, 5,329 blocked**.
Its 1,662 Lean-runtime fixtures have **657 working, 196 broken, 809 blocked**.
The 3,478 pinned-solc diagnostic agreements are reference evidence, not Lean
coverage. Every input, required source mode, completed observation and resource
block is retained in the [new evidence](../tests/upstream/baseline-20261028/README.md).
The immutable bulk report and 22 isolated follower reports remain separate.

The inventory currently has 212 rows: 13 present, 160 partial, one missing,
38 not applicable. The new diagnostic index provides reviewed boundaries for
76 partial rows and explicitly leaves 84 needing feature-specific attribution.
It does not promote statuses or infer completeness from absent fixtures. The
manifest/schema is unchanged; generated inventory files remain reproducible.

The cold `./run-lean.sh` attempt reached its initial 90-minute wall bound
(exit 124) at 546/685 default targets, with `FunctionTypes.lean` active.
Kernel cgroup peak was 8,195,923,968 bytes (7.633 GiB), with zero OOM events.
The default/TestSuite/frozen-sort combined gate remains blocked; warm timing
was not run because cold completion was not established. Partial cold
artifacts and the restored original cache remain on this VM. This baseline
is diagnostic evidence, not a universal semantics or lowering-equivalence proof.

The [feature-attribution follow-up](../tests/upstream/baseline-20261028/attribution/README.md)
now assesses all 84 IDs left unresolved by that checkpoint: 59 have explicit
source/documented limits, and 25 retain feature-specific missing-evidence
questions. Ten rows link directly to exact fresh fixture/variant gaps. The
original 76/84 index remains historical evidence, and the supplement does not
claim universal semantic attribution or change any manifest status. The cold
stop and unrun warm measurement above remain unchanged.

The [bounded discriminator matrix](../tests/upstream/baseline-20261028/probes/README.md)
adds actual pinned-compiler/provenance/source-reader controls for those40 questions.
It preserves the original corpus and distinguishes source emission from native
typed admission/proofs/replay, which remain blocked after a single bounded API
refresh stopped124. No feature status or profile decision changed.

The [native diagnostic follow-up](../tests/upstream/baseline-20261028/native-cache/README.md)
now establishes production typed-import/replay observations through the reusable
narrow adapter, without another build. The old combined preflight conflated it
with the stale proof-search branch. Named refusals and existing proof/model
limits remain separate from finite successful controls; the inventory is not
promoted. The precise remaining native capability is nonzero-payment entry
validation; the old cold stop and warm-unrun remain unchanged.

## Roadmap documentation review (2026-10-28)

Separate read-only finder and skeptic reviews, without the Lean server,
identified and corrected: oversized parent tasks (split into proof checkpoints and batched VM assignments), missing implementation ownership for independent source semantics,
within-wave dependency cycles, the source-state/semantics ordering, an
unqualified per-group proof requirement for audit VMs, and ambiguity in the
resource-prefix theorem. The dated baseline is preserved as historical evidence.

Documentation validation checks group IDs/counts, prerequisite references,
relative paths and heading anchors. The whole-repository `check-doc-paths.sh`
baseline reports 46 existing missing references in external/vendor citations
and archived generated validation records; these are separate from this
roadmap's Markdown links. This is a documentation change: no compiler or proof
has been implemented or newly verified by it, and no VM has been launched.
