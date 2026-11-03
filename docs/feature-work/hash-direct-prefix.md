# Direct EVM hash-query prefix receipts (G46.05)

The optional `Bridge/SolidityBridge/HashBridge/` interface records byte inputs
of successful **explicit** pinned evaluator steps. It reuses the exact owned
`Queries`, `Step`, and `Layout` sources from checkpoint `998ffef7`, rechecked
against current master; those three files are reused work, not new proofs.

`Prefix.directQueries` computes a direct KECCAK256 input from actual memory
and stack operands. `ExplicitPrefix` is a proof-only indexed receipt whose
edges contain equalities to the existing `EvmYul.EVM.step`; it is not an
evaluator, source judgment or an arbitrary hash-output oracle. A pure extractor
on a fuel-zero input does not prove hashing occurred. `recorded_keccak` derives
a nonempty receipt, the actual opaque digest and all supplied operation frame
fields without assuming a successful reply or selected next state.

`PrefixControls.repeated_query_prefix` derives two hash steps and an intervening
POP. Memory preservation proves the two full symbolic query byte arrays agree;
the receipt retains both occurrences. Its collision-premise control correctly
allows repeated preimages. `no_zero_fuel_edge` prevents a failed step from
supplying a successful edge. These are kernel explicit-step controls, not
original source/native fixtures. Cost zero in a control is a supplied evaluator
cost, never an affordability or EVM gas-cost claim.

The per-run `CollisionFree` / `RegionsDisjoint` and adaptive bounds remain those
of `Solidity/Hash/{CollisionBound,Adaptive}.lean`. Layout separation still needs
actual encoded-preimage inclusion and the approved per-run region premise.
`NativeAgreesOn` is an explicit missing compatibility obligation, not an axiom
or proof that the fixed native function was sampled uniformly. Global hash
injectivity is neither asserted nor needed. Actual byte queries are bounded
UInt8 values; arbitrary Nat inputs to `queryBytes` truncate and are not injective.

## Exact limits and next edges

The explicit-step receipt alone has no fetch, X guard, memory-expansion/base
affordability, shared fuel or installed-code claim. It observes direct KECCAK instructions only:
queries inside child calls/native providers, and adversary/offline queries,
are not automatically included. It cannot justify the full-run probability
bound until that query-completeness obligation is supplied.

Current master retains opaque padding/scanner definitions. No vendor, pin,
extern or provider is changed here. The old H7-dependent `Controls` source is
retained verbatim as evidence but is not imported under this master snapshot.
No canonical memory/padding/native equality is assumed by the new controls.
The human's prior H7 authorization is not represented as an unanswered question;
this implementation does not duplicate or silently adopt another vendor patch.

## Fetched/charged first-edge consumer

`ChargedGuard.lean` now specialises the exact existing X check API to KECCAK:
memory expansion is charged first, then actual `C'` (`30 + 6*ceil(size/32)`),
then underflow/capacity checks. This does not reorder the pinned model's `!`
operand indexing before underflow. Logical malformed-stack controls therefore
DO NOT establish native panic safety.

`Charged.lean` derives `CheckedHashEdge`: actual successful checks and evaluator
step, the same byte-query receipt, exact stack/world/memory/activeWords/gas/PC/
execLength/response fields, and equality to the unchanged residual X. The
public `hash_driver_outcome` supplies the exhaustive first-edge account from
actual fetch/operand facts without a passed guard or chosen result premise.
Fuel0 skips checks. Fuel1 checks first, then exhausts in step0 when checks pass.
Larger fuel derives the actual checked successor; it does not prove the residual
program succeeds. Arbitrary destination arrays are retained; no membership is
needed for this non-jump instruction.

`ChargedControls.lean` checks memory/base-gas failure, affordable underflow,
capacity, fuel ordering and a real one-byte KECCAK/static-mode control with
remaining gas2 and PC1. Its actual zero-size read remains symbolic, never
canonical-empty hash input. These are kernel controls, not original fixtures.
The generic X observation API is exact reused owned `OutcomeDriver` from
`3d4f8d7f`, rechecked, not a second driver implementation.

## Recursive checked frame-query account

`Frame.lean` refines the existing `Classifies` proofs, rather than defining a
new driver/stage policy. `ClassifiedQueries` is an indexed Prop: failed checks
or evaluators emit no successful direct hash; successful steps record the actual
charged-input extractor; the nonterminal case continues at the original smaller
fuel. No runtime matching/erasure of this proof datatype is introduced.
`DriverQueryReceipt` hides only the stage proof, not an arbitrary selected result.

`FrameSound.lean` proves existence for every actual bounded X computation and
erasure soundness to that SAME operational result. It retains exception versus
raw REVERT versus success via the original classifier. Revert receipts may
contain internal step state, but the public result remains only its actual gas
and bytes; no public error state or rollback is invented.

`FrameHash.lean` consumes the actual charged KECCAK edge and derives the rest
of the queries from its SAME residual X. The public all-fuel client has no passed
guard, desired reply, or independent terminal certificate premise. `FrameControls`
shows why an error cannot erase earlier successful hashes: identical input has
no query at fuel0 and one real recorded hash before its later fuel2 error. Its
query bytes stay symbolic, regardless of whether the byte array is empty.

These are DIRECT frame queries only. Global/nested-call or adversary query
completeness is not proved. Different initial fuel values are not asserted to
have prefix-related query lists: child-call behavior can depend on fuel.

## Fixed-run query uniqueness

`QueryShape.lean` derives a one-cut Prop view from existing classified receipts:
it references the SAME checks, evaluator and terminal-data computations. It is
not a new driver or output oracle. `QueryUnique.lean` compares two such views
and recurses only on the same actual successor at smaller fuel. Thus receipt
proofs and even different result indices cannot select different query lists
for the same initial state, destination array and fuel. `driver_queries_unique`
combines this with actual receipt existence; it does not define/adopt a source
or default observation function.

`QueryControls.lean` imports the actual checked hash-then-error witness and
proves every valid receipt has its singleton query list. An empty log cannot
be substituted just because the result is an error. The BYTE contents of that
query remain symbolic; no zero-padding or empty-input hash identity is assumed.
This uniqueness is not hash-output injectivity, native-provider determinism,
query completeness across calls, or a comparison of different starting fuels.
Per-run collision/region premises still have to be established on the actual
list; uniqueness only makes them independent of which valid receipt proves it.

## Checked cuts in the same run

`QueryCut.lean` indexes cuts by existing classified query receipts. Only actual
checked nonterminal tail edges advance a cut. `CutSound.lean` proves the query
split, equality of residual X computations, and a cursor receipt retaining the
original result index. It asserts neither whole-state equality nor a relation
between independently started fuel runs.

`HashCuts.lean` derives this cut from the actual checked KECCAK edge, including
zero/one fuel and failed guards. `CutControls.lean` witnesses a real query followed
by an error: its internal cursor has gas 2 and PC 1, and its remaining query list
is empty. That cursor is not a public error poststate.

## Composition of related cuts

`CutComposition.lean` grafts a later checked cut at the exact earlier cursor,
remaining fuel, query suffix and original result. Induction rebuilds only the
existing nonterminal receipt edges. It does not identify arbitrary cursors from
an equal terminal result or compare independently initialized fuel runs.

`TwoHashCuts.lean` imports two supplied actual checked KECCAK edges and derives
the remaining receipt from X. It records their queries in order and retains the
original X result at the second cursor. This is a conditional local component:
its edge premises remain explicit in that theorem. `PairControls` below
discharges them for fixed bytecode, without supplying a source invocation or
destination scanner law. Symbolic memory bytes remain so.

## Concrete two-hash producer

`PairControls.lean` discharges both checked-edge premises for the fixed bytecode
`20 20`, gas64, and stack `[0,0,0]`. The first hash leaves gas34 and its actual
digest atop the remaining zero. That digest becomes the second offset; its size
is zero, so expansion is zero independently of the digest. The second edge
leaves gas4 at PC2. The composed receipt records both actual symbolic byte
queries in order, with empty remaining query suffix and the same later error.
The cursor is internal checked-prefix evidence, not a public error poststate.

This is a kernel control, not a native fixture or an original Solidity invocation.
Neither zero-size byte expression is identified with canonical empty bytes; no
KEC result or padding/serialization supplier law is assumed. The existing X1
classification retains its real checks-before-exhaustion alternatives.

## Public invocation receipts

`XiQueries.lean` lifts direct-frame receipts through the pinned public `Ξ`
constructor and result projection. Its Prop-only `XiQueryReceipt` retains the
actual initialized state, original opaque destination scanner, smaller X fuel,
and real error/revert/success projection. All-fuel existence derives the X
result internally; soundness and uniqueness preclude selecting a different
public result or query list for the same invocation. No returned world is
silently replaced by an input world.

`XiControls.lean` uses the public constructor itself. A bare KECCAK at gas30
has no inherited operands: its fresh stack is empty, its actual checks reject
underflow, and no query is executed. Account map and transaction snapshot are
arbitrary distinct inputs, not desired reached states. This kernel control is
not native indexing/panic safety or a source/installed-code witness.

The constructor/projection expressions observe the existing definition, not a
second initialization semantics. Prior original-require invocation adapters on
the archival branch remain unchanged; their source-specific import closure is
not copied into this generic hash interface.

## Public CODE-message policy

`ThetaQueries.lean` carries the actual initialized child-frame query receipt
through public `Θ`'s CODE branch. `ThetaCodeQueryReceipt` is Prop-only: its lets
retain the exact recipient-credit then sender-debit expressions and environment,
including independent transfer/context values. Soundness checks against pinned
`Θ`; all-fuel production derives the actual child reply, rather than requiring
successful checks, a desired world or a caller-supplied terminal result.

OutOfFuel propagates. Ordinary child faults restore the pre-message map and
substate with zero refund and empty response; genuine REVERT retains actual gas
and bytes with that checkpoint. Success retains actual child created accounts,
world, gas, substate and data, including the original empty-map fallback to the
pre-message map/substate. Nothing rolls back to `snapshot` by assumption.
Fixed-argument/fuel uniqueness reuses the initialized child receipt.

`ThetaControls.bare_code_handled` derives actual initialized-child underflow
and the handled message tuple for arbitrary transfer value and independent
world/snapshot. Both preparation updates remain symbolic even when sender and
recipient coincide. This does not prove caller-funds/depth admission, a child
source installation, canonical bytes or native indexing/allocation safety.
The original zero-value STATICCALL CODE-policy adapters remain unchanged; this
new interface observes public arbitrary-value CODE calls and their queries.

## Actual call-operation composition

`CallQueries.lean` carries the CODE child-frame queries through the existing
`call` operation, rather than leaving its message reply as a user premise.
Soundness retains explicit actual `toExecute = Code code`; all-fuel production
derives the message reply internally. Funds/depth rejection records no child
query and keeps the actual handled result. An admitted call uses the original
smaller Θ fuel, so OutOfFuel and handled error paths remain distinct.

The receipt preserves pre-debit `Ccallgas`, the actual cost debit, warmed
account checkpoint, exact calldata read and child result. Installation uses the
original UInt256 minimum for the output copy while full response bytes become
returnData. Actual refund, two memory-range expansions, caller bit tests, world,
created accounts and substate remain in the exact returned-state expression.
No whole-world equality, canonical bytes or nonwrap/disjoint-memory law is added.

`CallControls.low_fuel_and_depth` distinguishes call0 exhaustion, admitted call1
exhaustion in Θ0, and call1 depth1024 handling with bit0/no child query. Its
actual returned account map remains separate from the arbitrary transaction
snapshot. The computed output-memory write is not normalized to empty memory.

This is the call OPERATION layer: its cost argument is not an affordability
proof, and it does not establish fetched/checked STATICCALL, parent-frame query
ordering or all nested/global queries. Precompiled/native code selection remains
outside the CODE receipt. Existing archival zero-value call-preparation helpers
are unchanged; no replacement evaluator or source/callback model is installed.

## Checked STATICCALL boundary

`StaticQueries.lean` consumes the actual fetched STATICCALL, full six physical
operands/tail and actual CODE selection. Its all-fuel producer retains zero fuel,
checks before evaluator exhaustion, every memory/opcode/stack-capacity guard,
the smaller call fuel, actual effectful call reply and real caller continuation.
No successful check, sufficient gas/fuel, chosen reply or terminal receipt is a
headline premise. Invalid destinations in the remaining caller execution remain
actual faults; no original scanner membership is asserted.

`StaticCodeQueryReceipt` keeps child CODE-frame queries and later caller-frame
queries as separate indices. Soundness derives the SAME original X result.
The continuation starts with `staticPost` of the actual returned state, bit and
saved physical tail; its receipt preserves actual terminal/error provenance.
The effectful call is not treated as a pure world-preserving prefix, and SLOAD
warming in the continuation is not erased by a whole-state equality.

`StaticQueryControls.fuel_and_check_order` gives concrete fetch/stack/CODE
controls: X0 exhausts, X1 can fail its gas check, and X2 reaches call0/exhausts
before handled-depth policy even at depth1024. This is not a positive original
Solidity-source/native run or canonical byte realization.

Six existing owned driver files were reused from committed `3d4f8d7f…`, with
exact original seals retained. Five remain byte-identical; StaticcallDriver only
loses one unused `and_false` simp argument (types unchanged). Import preparation
first hit two aggregate60s stops, both retained. The unchanged master Dispatch
closure was then prepared separately (144s), as allowed for unchanged inputs;
restored owning stages still used60s, with RequireLocalCut52s. The initial
scratch import map missed a lazy cached module; the corrected setup comes from
Lake's full import map. The repository-tactic fallback reported an unknown tactic in this
narrow import; primitive tactics did not close the soundness goal.

Next owned hard edge: a concrete successful call/continuation split or repeated
call-boundary composition. Separate lists do not certify a flattened nested or
global trace. Source/native adequacy, canonical input realization and native hash
compatibility remain open.
Generic receipt append/split/count and guard projection glue remain open
routine obligations. Original source/compiler/native/heap/call/catch
correspondence and G45.03 whole structured simulation remain open.

Focused owning diagnostics, exact public types/axioms and source/evidence
reviews are in the accompanying sealed handoff. The first plain-lean attempt
failed on lazy artifact-cache setup; corrected checks use Lake-generated import
maps. No full optional/root/TestSuite/docs/strict lane gate was run under H12,
and mixed cached/fetched importing closures are not cold timing evidence.
