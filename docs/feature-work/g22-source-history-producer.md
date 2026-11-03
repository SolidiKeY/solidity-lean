# Source callback history producer

These components prove facts about the existing Source evaluator. Source files,
profiles, observations and limits are unchanged. StaticJournal.History remains
an algebraic certificate; its linkage to actual execution requires a producer.
These proofs preserve persistent storage under static histories, not every
world, balance, ledger, heap or event observation.

HistoryRollback extracts operation ancestry and rewinds exactly the live
checkpoint, retaining earlier caller effects. CallbackFrame.enter_history
combines smaller-bound actual dispatch history with the live pre-credit prefix.
Success and non-revert halts retain reached state; completed revert rewinds its
own descendant journal entries and preserves its outcome bytes. callbacks derives
the bounded CallbackHistories predicate from smaller dispatch components. This
is an induction step, not general callback closure.

SourceHistory.At is generated from the published evaluator signature inventory
by scripts/o1-source-history-interface.py. It has seventeen actual mode-indexed
run-effect components and specializes child entry to live-checkpoint ancestry;
it is not byte-identical GrowAt extraction or a producer theorem.
SourceHistoryBase.at_zero proves the exhausted base. The positive-bound
expression/conversion/statement helpers and evaluator/call induction remain
owned, unfinished work.

UnknownSourceCall.history links actual unknown zero-value call execution to its
environment history for success, revert and all halts. evaluated_frame pairs the
computed pre-decoder outcome/state with its static frame, still requiring bounded
Source callback histories. Neither favorable return bytes nor a desired final
frame is assumed.

EffectRules composes effects at the live reached bind state, preserves reached
states through subframes and caught halts, and forgets requested static mode only
toward its parent. Catching a halt does not imply rollback. Pure/local operations
preserve the journal; there is no generic arbitrary-state overwrite rule.
MachineEffects proves actual allocation and checked heap replacement preserve
the journal in either mode, including refused replacement. ReadEffects supplies
nine read/reference/guarded-write histories without heap-validity or successful
read premises. Writes use the actual frame's static flag.

The helper mutual inductions are closed at every horizon:

- DeleteEffects.delete_histories covers deleteStor/deleteRange/deleteFields,
  retaining mapping no-op, static write refusal, partial effects and exhaustion.
- ZeroEffects.zero_histories covers zeroData/zeroVal/zeroElems/zeroFields in
  either mode, retaining allocation, missing-default/location refusal and timeout.
- LoadEffects.load_histories covers loadMem/loadElem/loadElems/loadFields/loadBytes
  in either mode, retaining allocations, mapping refusal, read failures and timeout.
- StoreEffects.store_histories covers storeData/storeVal/storeElems/storeFields/
  storeBytes under the real F.static. The constructor/reference cuts are
  discharged by this induction. Mismatch, mapping-copy refusal, partial shrink
  effects and same-path reference no-op remain. It does not prove copy-value
  correctness, layout admission, successful completion or implicit rollback.

Memory mutation remains permitted in static mode. The bounded recursive copying
and initialization helpers exhaust at zero, including empty range/list cases
whose positive-bound calls can succeed. Other location helpers keep their own
bound behavior; no blanket timeout policy is imposed.
Not every static deletion or assignment refuses: actual no-op branches remain.

Controls include actual ordinary child writes/revert, inherited-static refusal,
and live versus stale checkpoints under both Source pipelines. The child journal
growth before rollback is two ordinarily and zero statically. The unknown-call
credit/revert control retains a supplied prior caller write; its nil arguments
do not witness an argument write. Other controls distinguish caught-halt heap
retention, type refusal, ordinary deletion, initialization allocation and timeout.
These use populated Source examples and toyFixed, not native compiler evidence.

CopyControls uses a typed two-bytes-field environment with kernel-checked path
types and seven successful seeding writes. Its checkpoint is AFTER seeding,
not a deployment or constructor provenance witness. A static loading run returns
a real allocated reference to bytes[7,9] without a journal change. Ordinary copy
shrinks destination length3 to2, clears the old tail and adds four writes.
Static copy refuses and preserves the seeded state; static same-path copy is a
permitted no-op. Type mismatch and exhaustion remain distinct. All-mode/all-bound
loader/store clients use the closed producers, and the ordinary-change negative
retains the counterexample to false preservation.

Validation uses automation-first candidates and shared per-file kernel gates.
The latest fourteen-declaration signature/axiom audit passed in3.230s with
aggregate peak161718272bytes under hard12GiB/no-swap, CPU1, thread1/-j1 and the
unchanged proof/time limits. Only propext, Classical.choice and Quot.sound or
none occur. Broad aggregate-copy search exhausted200000 heartbeats and triggered
a subsequent Lean diagnostic panic; it remains a failed/blocked experiment.
Explicit typed constructor cuts repaired the proof without relaxing any statement,
premise or budget. Raw successful/failed receipts and earlier audit measurements
remain in immutable handoffs. Finder and skeptic independently cleared the
recursive producers and final inhabited controls.

No full/global/native gate or original O1 completion is claimed here.
General positive-bound At and CallbackHistories remain owned proof obligations.
P1 profile provenance stays an explicit hprof hypothesis; published P1 bare-revert
production does not supply Source callback histories or payload/rollback linkage.
P10 actual CALL/RETURNDATA execution and Source/target correspondence remain
separate compiler-side obligations. These Source-only laws do not close them.


EvalEffectsBase adds actual lifted-result/state-read effects and permits modSt
only under exact ex preservation. LocationEffects now covers memory element
read/write, readLoc/writeLoc/deleteLoc, lengthOf and indexLoc. Reads and
memory/local operations may use either history mode; storage writes/deletes use
the actual F.static and the closed copying/deletion histories. Calldata writes,
type mismatch and bounds panic remain refusals. No arbitrary state overwrite
rule or heap/local immutability claim is introduced.

LocationControls executes25 concrete observations, including successful static
memory-byte/array/local changes, ordinary scalar storage mutation, static storage
refusal, calldata refusal, bounds/type failures and local deletion exhaustion.
Deletion preserves zeroVal-before-write ordering. Two inhabited effect clients
and an ordinary-storage-change negative retain these distinctions. The final
fourteen-declaration signature/axiom audit passed in3.224s with aggregate
peak167170048bytes under unchanged hard12GiB/no-swap/serial limits. Only standard
axioms occur. Independent finder/skeptic review cleared the source branches and
final stored controls. General evaluator/callback closure remains open.


LocalInitializationEffects closes zeroVals and zeroInner effects for all modes,
bounds and separately indexed caller/result local contexts. Empty/skipped work
keeps its actual success behavior at zero bound. The19 stored initialization
observations show a fresh memory reference in the returned slots with unchanged
caller locals and retained outer slot; later default refusal keeps earlier raw
heap allocation. No implicit rollback is inferred. Its all-mode/bound client is
inhabited. Finder and skeptic independently cleared these exact distinctions.

The combined eighteen-declaration signature/axiom audit passed in3.828s with
aggregate peak164491264bytes under the unchanged hard limits and only standard
axioms. Source code, profiles, expected verdicts and runtime observations are
unchanged; these are proof-only helper additions. Remaining expression/statement/
dispatch helpers and the positive-bound seventeen-way evaluator/callback
induction are still owned work. Compiler/native and full-lane obligations remain
open as described above.

CallSupportEffects closes actual instance lookup, event observation, live mark
and outcome re-raising effects. It does not grant permission for Solidity LOG
under STATICCALL: emitEvent records Source observation events. It does not give
an unconditional rollback rule. CollectionEffects closes map/mapM, getV and
indexNat effects; a later failure retains the reached state.

ReferenceEffects closes bytesOfRV, cdToMem, convRV and convExplicitRV journal
effects for every bound and either mode. Existing conversion identities,
storage reads, allocation and refusals remain intact. TupleCopyEffects closes
pushVals with separate caller/result contexts, and copyInto under the actual
F.static. These are effects of existing algorithms, not ABI decoding correctness,
successful input admission, layout validity or value-copy correctness.

HelperControls contributes32 populated run observations and an explicit negative
to event rollback after a later mapM failure. They cover known/unknown instance
lookup, arbitrary success/revert bytes, a live seven-entry mark, storage-to-memory
allocation, explicit fixed bytes, memory-to-value refusal, timeout, calldata
conversion/refusal, and tuple conversion with retained allocation before an
arity failure. Discarding a slot succeeds at bound0 without allocating.

The final eighteen-declaration signature/axiom audit and changed-module kernel
check passed in31.128s with aggregate peak707883008bytes. Checks used hard
memory.max12884901888, memory.swap.max0, CPU1, serial Lean-j1 and a4GiB available
host reserve. Only propext, Classical.choice and Quot.sound or none occur.
Automation was attempted first. Failed namespace resolution and dependent-match
candidates remain failed; explicit qualification and matching the missing
constructor repaired them without a changed statement, expectation or budget.
The conversion join-point search failures and original full-gate failures are
retained. Finder and skeptic independently cleared all five stored modules and
the32 controls without Lean server use. No Source file, fixture or runtime
profile changed, and no full/global/native gate was rerun or claimed passed.

Ready owned work remains: positive-bound expression/statement/dispatch and the
seventeen-component evaluator/callback induction. This checkpoint does not
supply a general CallbackHistories or source-to-target/native correspondence.

SourceSequenceEffects proves four successor steps for evalPair, evalArgs,
evalConvArgs and evalArgsRev. They use At G n for strictly smaller-bound actual
evaluations and conclude the corresponding effect at n+1, keeping the same
global, frame and real static flag. They do not construct full positive-bound At.
SourceSequenceControls stores15 observations for both pipelines: legacy operand
order returns(2,1), viaIR returns(2,2), forward/reverse argument order is retained,
static local mutation remains permitted, empty work succeeds and exhaustion
preserves its reached locals. An inhabited empty-list client uses the proved
At G0 base; it does not assume a positive-bound full At.

The combined25-declaration signature/axiom check passed in6.838s with aggregate
peak173338624bytes under the same hard limits. Its initial partial-import scratch
setup failed on a missing cached AST object; the actual combined-import audit
module gives Lake the complete graph and passes. That failure remains failed.
A scratch control namespace typo was corrected without changing an observation.
Finder and skeptic cleared the exact stored sequencing proofs and controls.
The remaining evaluator/callback induction, Source/target correspondence and
original O1 final gates are still open.

KeyStepEffects closes the journal effect of the existing key conversion helper,
including storage byte reads, literal/scalar keys, refusal and exhaustion.
SourceLvalueCallEffects adds evalLoc and pay successor components. Their At G n
premise is strictly smaller than the n+1 conclusion; they preserve actual F.static.
The existing payment call keeps its requested false flag and inherits parent
mode through Effect.parent. No stipend rule, callback exclusion or payment
semantics is added. Together with the four sequencing steps, six of the
seventeen successor components are now available; full At is not constructed.

SourceLvalueCallControls stores17 observations and a genuine At0 local client.
They distinguish storage/literal/bool keys, refused keys and exhausted reads,
a bound1 location from bound0 exhaustion, arbitrary zero-value success/revert
bytes, static nonzero-value caller halt from an ordinary unaffordable child
revert, and the respective absence of pre-call events. Its explicit negative
proves the caller halt and child revert differ. Direct normalization hit the
unchanged200000-heartbeat limit; rewriting the already proved actual outcomes
before constructor discrimination repairs that proof. The failed attempt remains
a blocked proof experiment, not a passing check.

SourcePayloadEffects and SourcePayloadDecodeEffects prove only journal effects
of existing payload helpers: tailBytes, encodeOne/Parts/Vals, decodeArg/Args,
abiDecodeData and extReturn. All types, refusals, partial state and list order
remain as implemented. Byte/string/array constructor cuts share the proof;
explicit array composition avoids the broad search's heartbeat failures.
The isolated array cut passed in2.430s after those failures. There is no ABI
value correctness, new input admission, enum/nominal certificate extension,
algorithm change or target/native correspondence claim.

SourcePayloadControls stores19 actual observations at the populated seven-write
checkpoint: memory allocation, earlier allocation retained after a later invalid
bool, valid/invalid bool arrays, existing packed encoding/refusal, canonical
primitive return, malformed successful return, callee-revert data and nil declared
returns. Nil declarations retain unused-byte acceptance; this does not validate
discarding a nonempty declaration before checking it. A parameterized draft word
constructor was made total using existing toWord, retaining tested values1/2
and every observation.

The combined eighteen-declaration signature/axiom audit passed in6.542s with
aggregate peak274239488bytes under the same hard12GiB/no-swap scope, CPU1,
thread1/-j1, stack, heartbeat and300s limits, and4GiB host reserve. Dependencies
are only propext, Classical.choice and Quot.sound or none. Finder and skeptic
independently cleared the exact stored helpers and36 observations without Lean
server use. Source files, fixtures, profiles, pins and expected verdicts are
unchanged. Full/global/native gates and original C5 were not rerun; helper work
consumes none of its remaining allowance. Remaining expression/builtin/statement/
call/dispatch induction and actual source-target/native correspondence are open.

SourceAggregateReadEffects now closes ret32, fieldsOf and getterPath journal
effects. Arity/type refusals, key decoding and bounds failures remain actual
outcomes. The getter helper uses strict type-size induction because STy is
nested; no getter entrypoint, ABI value or digest correctness is inferred.
SourceBuiltinEffects adds the builtin successor step from At G n, retaining
legacy/reverse argument order, every refusal and opaque precompile-result
handling without making a precompile/native correctness claim.

SourceExpressionEffects.evalE_succ proves the actual expression component at
n+1 from At G n for the same global, frame and real static flag. Its41 typed
constructor cuts retain every original guard and argument, including external
call signatures and ABI decoding restrictions. Their telescopes and exhaustive
assembly are generated by scripts/o1-source-expression-effects.py from actual
Resolved.lean declarations, with source hash/inventory in the adjacent JSON.
The generator is proof tooling, not replacement semantics. Nested Lean comments
are handled; fixing that review finding regenerated byte-identical checked cuts.
No Source file or representation is changed.

Broad delta-unfolding and early generated attempts reached the unchanged200000
heartbeat bound. The existing Source equation-rewrite strategy repairs the
proof: seven read/literal cuts passed in22.918s, the next seven in19.008s, and
the remaining27 serially in132.421s. No limit or premise was raised. Failed
prototypes and their source snapshots remain failed evidence. No unchanged
full-lane timed gate was rerun, and this repair is not a pass for those gates.

SourceReadBuiltinControls adds24 actual observations: a typed array environment
with three seeding writes, retained checkpoint, successful path/value read and
bounds panic; field count/type refusals and digest-shape refusal; assert/require
outcomes and raw reason data; named gas refusal and malformed builtin-result/
argument refusals. The arithmetic controls assert(7+5) mod3=0 under both pipelines,
not zero modulus. The helper's bound0 array-path success is retained; it is not
a full interpreter bound0 success. A genuine At0 Boolean-expression client and
explicit gas-refusal negative are kernel checked.

The combined49-declaration signature/axiom audit passed in19.290s with aggregate
peak182812672bytes under the unchanged hard12GiB/no-swap, CPU1, thread1/-j1,
stack, heartbeat,300s and4GiB host-reserve limits. Dependencies are standard
propext, Classical.choice and Quot.sound or none. Finder and skeptic independently
cleared the exact final proof tooling, typed cuts and controls without Lean use.

Thirteen successor components are now proved: four sequencing components, lvalue,
pay, builtin, expression, callInternal, execItems, runMods, forIter and dispatch.
execS, callAddr, enterInstance and envLoop, and hence general positive-bound
At/CallbackHistories, remain owned work. Source-target/native correspondence,
P1 profile hypotheses and P10 actual call execution retain their prior boundaries.
Original O1 and its mandatory final gates are incomplete; original C5 allowance
and every prior failed receipt/seal remain unchanged.


SourceBodyEffects adds actual callInternal, typed item sequencing and modifier
successor histories from strictly smaller At premises. Modifier arguments and
caught body execution retain their actual live state; saving/restoring fnLocals
preserves ex and introduces no rollback. Both checked=true internal bodies and
checked=false unchecked blocks retain inherited static mode. These are Source
journal effects, not a full context-restoration or call-adequacy theorem.

SourceBodyControls kernel-checks seven inhabited observations on the existing
modifier fixture: static legacy return2, static viaIR return1, single-placeholder
return1, nonzero local updates, both journals unchanged, and saved function
locals restored. The numeric observations use decide; state equalities use rfl
because the dependent/function-containing states have no Decidable equality.
The failed decide attempt is retained rather than treated as a gate pass.

The final body module, controls and ten-declaration signature/axiom audit passed
separately in3.030s,4.129s and3.134s, respectively. The modifier prototype passed
in37.460s. Hard memory.max12884901888 and memory.swap.max0 were read back for
each serial Docker workload; CPU1, Lean-j1, unchanged proof limits and4GiB host
reserve applied. No OOM or descendant process remained. Dependencies are only
propext, Classical.choice and Quot.sound (or none). Finder and skeptic separately
cleared the proofs and seven controls without Lean. Earlier bounded failed
prototypes, including compiler diagnostic panics and heartbeat failures, remain
failed evidence; no original timed/full gate was repeated. The original C5
remaining allowance is20.294037341996614s and helper work consumes none of it.


SourceLoopEffects.forIter_succ proves the actual optional-condition/body/post
step, including break, continue, return and exhaustion, from strictly smaller
At G n. SourceLoopControls has15 populated-state observations: break skips post,
false skips body, continue executes post before dirty timeout, static body/post
writes refuse with exact empty revert data, early return skips post, and the
0/1/2 bound distinctions remain observable. A timeout does not undo the
ordinary post-write; no transaction rollback or native result is inferred.

SourceDispatchEffects proves five selector leaves and exhaustive dispatch_succ:
selected nonempty functions, or getters/special functions after absent-function
or selected-but-empty fallthrough. Signature, payability, calldata length,
getter-type, missing-body and fallback-signature refusals remain intact.
SourceDispatchControls has13 actual observations/clients, including return12,
ordinary state changes, dirty callee revert, static refusal, short arguments,
absent special function, payability and exhaustion. The At0 selected-function
client is inhabited conditional history at bound1, not successful-call coverage.
The same inherited static frame is used throughout.

Full dispatch proof search and a duplicated getter proof reached the unchanged
200000 heartbeat limit. Sharing actual selector-case lemmas repaired that
checking cost; no Source definition, statement, premise or budget changed.
Failed attempts and recoverable split-tactic compiler diagnostics are retained.
The final four-module check passed in81.955s with aggregate peak254820352bytes.
An initially empty audit generated by an overescaped regex is rejected as axiom
evidence, despite its process exit0. The corrected asserted35-declaration audit
passed in8.454s with peak114524160bytes; it reports only propext, Classical.choice
and Quot.sound or none. All checks used the verified hard12GiB/swap0 Docker
scope, CPU1, serial Lean-j1, unchanged stack/heartbeat/300s guard and4GiB host
reserve. Finder and skeptic separately cleared all leaves, exhaustive assembly
and28 controls without Lean. Four source induction fields remain; full At,
CallbackHistories, source/target/native adequacy and original mandatory final
gates are still open. No original C5 time was consumed by this H10 helper work.
