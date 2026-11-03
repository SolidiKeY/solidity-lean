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

SourceHistory.At was generated from the published evaluator signature inventory
by a script that is not in this repository. It has seventeen actual mode-indexed
run-effect components and specializes child entry to live-checkpoint ancestry;
it is not byte-identical GrowAt extraction or a producer theorem.
SourceHistoryBase.at_zero proves the exhausted base. The positive-bound
successor components are listed below; the status section records which remain.

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
and an ordinary-storage-change negative retain these distinctions.

LocalInitializationEffects closes zeroVals and zeroInner effects for all modes,
bounds and separately indexed caller/result local contexts. Empty/skipped work
keeps its actual success behavior at zero bound. The19 stored initialization
observations show a fresh memory reference in the returned slots with unchanged
caller locals and retained outer slot; later default refusal keeps earlier raw
heap allocation. No implicit rollback is inferred. Its all-mode/bound client is
inhabited.

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

SourceSequenceEffects proves four successor steps for evalPair, evalArgs,
evalConvArgs and evalArgsRev. They use At G n for strictly smaller-bound actual
evaluations and conclude the corresponding effect at n+1, keeping the same
global, frame and real static flag. They do not construct full positive-bound At.
SourceSequenceControls stores15 observations for both pipelines: legacy operand
order returns(2,1), viaIR returns(2,2), forward/reverse argument order is retained,
static local mutation remains permitted, empty work succeeds and exhaustion
preserves its reached locals. An inhabited empty-list client uses the proved
At G0 base; it does not assume a positive-bound full At.

KeyStepEffects closes the journal effect of the existing key conversion helper,
including storage byte reads, literal/scalar keys, refusal and exhaustion.
SourceLvalueCallEffects adds evalLoc and pay successor components. Their At G n
premise is strictly smaller than the n+1 conclusion; they preserve actual F.static.
The existing payment call keeps its requested false flag and inherits parent
mode through Effect.parent. No stipend rule, callback exclusion or payment
semantics is added. Full At is not constructed.

SourceLvalueCallControls stores17 observations and a genuine At0 local client.
They distinguish storage/literal/bool keys, refused keys and exhausted reads,
a bound1 location from bound0 exhaustion, arbitrary zero-value success/revert
bytes, static nonzero-value caller halt from an ordinary unaffordable child
revert, and the respective absence of pre-call events. Its explicit negative
proves the caller halt and child revert differ.

SourcePayloadEffects and SourcePayloadDecodeEffects prove only journal effects
of existing payload helpers: tailBytes, encodeOne/Parts/Vals, decodeArg/Args,
abiDecodeData and extReturn. All types, refusals, partial state and list order
remain as implemented. Byte/string/array constructor cuts share the proof;
explicit array composition keeps the proof within the default budget. There is no ABI
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
assembly were generated from the actual Resolved.lean declarations by proof
tooling that is not in this repository; it is not replacement semantics. The
proofs use the existing Source equation-rewrite strategy. No Source file or
representation is changed.

SourceReadBuiltinControls adds24 actual observations: a typed array environment
with three seeding writes, retained checkpoint, successful path/value read and
bounds panic; field count/type refusals and digest-shape refusal; assert/require
outcomes and raw reason data; named gas refusal and malformed builtin-result/
argument refusals. The arithmetic controls assert(7+5) mod3=0 under both pipelines,
not zero modulus. The helper's bound0 array-path success is retained; it is not
a full interpreter bound0 success. A genuine At0 Boolean-expression client and
explicit gas-refusal negative are kernel checked.

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

Dispatch proofs share the actual selector-case lemmas; no Source definition,
statement, premise or budget changed.

## Status

Thirteen of the seventeen successor components are proved: four sequencing
components, lvalue, pay, builtin, expression, callInternal, execItems, runMods,
forIter and dispatch. The remaining four (execS, callAddr, enterInstance and
envLoop), and hence general positive-bound At and CallbackHistories, are open.
Source-target/native correspondence, P1 profile hypotheses and P10 actual call
execution keep the boundaries stated above. Checked declarations depend only on
propext, Classical.choice and Quot.sound, or on none; no proof limit was raised.
Independent finder and skeptic reviews cleared the producers and controls.
