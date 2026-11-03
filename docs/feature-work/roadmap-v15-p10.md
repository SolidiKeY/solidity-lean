# V15 P10: fetched-byte execution steps against EvmYul

Partial checkpoint of roadmap item V15 (EVM agreement), producer P10: single
fetched EVM steps over Backend-emitted code, checked against the pinned
EvmYul reference (`Bridge/vendor/EvmYul`). All modules live in
`Bridge/SolidityBridge/RoadmapV15/P10/`; nothing in the core changed. Checked registered producer and control theorems have no `sorry` or new axiom; their
printed axiom sets are subsets of `propext`, `Classical.choice`, `Quot.sound`.
Source-only control proposals, where explicitly identified below, remain
unverified and are not registered.

## Sites

`Site op` (`Interface.lean`) packages a seed `EVM.State`, a Backend program
prefix and suffix, and a bound that the prefix length fits a word. `Site.state`
overwrites the seed's code with `Backend.encode (before ++ op :: after)` and
its PC with the prefix length. So a `Site` is a state built to hold `op` at
the PC; it is not a reachable state of a compiled contract. Applying a site
fact to a given state needs `Site.recover` (`RoadmapV15/P10/Execution.lean`), i.e. literal
equality of that state's code with an encoded Backend program. That equality
is the compiler/source-origin fact P10 does not supply.

## Frozen interface (consumers V13, V14, V16, VY3, VY4)

`FrozenInterface.lean`, namespace `SolidityBridge.RoadmapV15.P10.FrozenV1`,
fixes 18 statements in three `Prop` structures, for CALL, RETURNDATASIZE,
RETURNDATACOPY, JUMP, JUMPI and JUMPDEST sites:

| Structure | Fields | Content |
|---|---|---|
| `Decode` | 6 | `EVM.decode` at the site PC returns the opcode with no immediate. |
| `ChargedStep` | 6 | `Assembly.driverSteps 1` equals the opcode's dispatch after `Assembly.driverGate`: CALL through `EVM.call` (unevaluated), return-data size/copy, jump targets and fall-through. |
| `Continuation` | 6 | `EVM.X (fuel+2)` is one driver step followed by `EVM.X (fuel+1)`. |

`API` bundles the three. `FrozenWitness.lean` proves `FrozenV1.api : API`
from the theorems of `Interface.lean` and `RoadmapV15/P10/Execution.lean`; it adds no new
fact, so a hypothesis `(h : API)` is always dischargeable and is not evidence
beyond those theorems. The decode fields are byte-table lookups (also covered
by `DecoderAgreement.decode_all`); the step and continuation fields are
unfoldings of `EVM.step` and `EVM.X`, with `driverGate` left folded and the
`EVM.call` result not evaluated. The signatures are frozen as version 1;
changes go to a new version.

## Consumer laws

Each consumer pairs a typed scalar or Backend reading with the fetched,
charged step and its `X` continuation, with explicit gas and stack bounds.
Each has a controls module (`…Controls.lean`) with populated states, boundary
and error-order negatives.

| Modules | Opcodes | Content |
|---|---|---|
| `Execution`, `ExecutionControls` | CALL, RETURNDATASIZE/COPY, JUMP/JUMPI/JUMPDEST | Charged steps and continuations above; funded, underfunded and static CALL controls. |
| `Modular`, `ModularControls` | ADDMOD, MULMOD | Full-precision scalar agreement. |
| `ExponentConsumer`, `PowerControls` | EXP | Reference modular power; local gas bound 1610. |
| `StackFamilyConsumer`, `StackFamilyControls` | DUP1–16, SWAP1–16 | Every legal depth. |
| `SignedDivisionConsumer`, `SignedDivisionControls` | SDIV, SMOD | Bounded signed transport; raw zero and minimum-wrap behaviour kept as EVM semantics. |
| `ArithmeticShiftConsumer`, `ArithmeticShiftControls` | SAR | `BitVec` agreement including saturation. |
| `StorageReadConsumer`, `StorageReadControls` | SLOAD, TLOAD | SLOAD 100 warm / 2100 cold, TLOAD 100; existing typed slot observations. |
| `StorageWarmTransport`, `StorageWarmControls`, `StorageIsolationControls` | SLOAD, TLOAD | Warm cost after any SLOAD update, distinct-key isolation, fetched resource frame (below). |
| `BalanceEnvironmentConsumer`, `BalanceEnvironmentControls` | BALANCE | Charged read; the frame's `funds` field is defined from the EVM account map, so the funds agreement holds by construction. |
| `DecoderAgreement`, `DecoderAgreementControls` | 117 non-immediate opcodes | Backend bytes against the reference decoder and fetched dispatch. |
| `PushDecoderAgreement`, `PushDecoderControls` | PUSH0–32 | Payload extraction against the reference reader. |
| `ReturnCopyBounds`, `ReturnCopyBoundsControls` | RETURNDATACOPY | The order of the gas, arity, natural source-endpoint and capacity checks. The charged state changes only gas. The gate classification unfolds `driverGate` directly. The out-of-range refusal (`InvalidMemoryAccess`) is lifted to `driverSteps` and `EVM.X` through `FrozenV1.api`. The physical copy, padding and read values are not proved, and errors carry no final state. |

## Known differences and open items

- The pinned EvmYul has no CLZ: byte `0x1e` decodes to INVALID
  (`clz_invalid`). This is recorded, not excluded or approved.
- The reference accepts the truncated raw PUSH2 `[0x61, 0x01]` (value 1),
  which `Backend.decode` refuses; the PUSH laws cover complete emitted payloads.
- `valid` (the jump-destination array) is an input, not a scanner certificate.
- RETURNDATACOPY uses the reference byte-memory operation. The published
  [padding interface](../../Bridge/SolidityBridge/ExternalEvm/PaddingInterface.lean)
  supplies `paddingCorrect_bounded` under explicit host-width bounds and
  `paddingCorrect32` for the H7 logical zeroes body. Native allocation/extern
  correctness remains separate; this is not a physical allocator witness.
- Open: compiler/source origin of sites, G45.03 execution meaning, Osaka
  agreement, resource abstraction, and source/ABI/world/account/transaction/
  trace closure; the full per-opcode rows remain open.

## Master integration review

Read-only finder and
skeptic reviews confirmed: no `sorry`/axiom/heartbeat changes, all imports and
module-map paths exist, core untouched. Fixed on merge: the producer's ten
per-step notes were replaced by this page; the frozen-interface docstring now says its fields are discharged by
`FrozenV1.api` from existing theorems; `api` is a `theorem`; module-map rows
for `Site`, BALANCE and the frozen modules were made precise. Noted, not
changed: per-opcode `opcode_at`
lemmas are duplicated across modules, and most `#print axioms` are unguarded,
as elsewhere in `Bridge/`.

## Machine observations

`MachineObservation.lean` proves `pc_agreement`, `gas_agreement` and
`msize_agreement` against actual Backend-emitted sites, the reference charged
gate, one fetched step and its `X` continuation. Every law requires gas at least
2 and input stack length plus one at most 1024. PC reads the current instruction
address before incrementing it. GAS reads gas after charging 2. MSIZE reads
`activeWords * 32` in the native word arithmetic, not resident byte-array length.
These opcodes are outside the existing Scalar numeric slice; no replacement
slice semantics or source environment key is introduced.

`MachineObservationControls.lean` has 15 populated controls, including a fetched
PC/GAS/MSIZE sequence. Its exact output stack is `[96,5,3,258,513]`, gas 3,
PC 6 and execution count 44 after starting with gas 9, PC 3 and count 41.
Complete native State equality preserves accounts, caller/context, code, memory,
return data and halt buffers. Current-PC, entry-gas and resident-length negatives
separate the observations. Input-capacity 1023 succeeds, 1024 refuses; gas/fuel
failures remain ordered. Zero and maximal active-word counts test raw native
word arithmetic only, without claiming a physically realizable allocator state.

The laws have no source/frame-origin or P1 realization premise. They establish
native primitive clauses only, not source resource abstraction, full Osaka
agreement or closure of the three full per-opcode obligations. The frozen P10
interface remains unchanged. Independent source/control review found no defect.

### Complete native code extent

`CodeExtent.lean` proves `codesize_agreement`: actual Backend emission and pinned
decoding lead through the charged gate to the full native State and `X`
continuation. The pushed word is the entire execution code buffer size modulo
2^256, including bytes after STOP, with gas at least 2 and input stack length
plus one at most 1024. The theorem preserves every other state component except
the actual charge, stack push, PC increment and execution count.

Nine populated controls distinguish full extent from remaining bytes, retain
the ordered code lists, preserve nonzero accounts/caller/memory/return buffers,
and check gas/fuel refusal and stack capacities 1023/1024. This native clause
does not admit CODESIZE to the G31 source environment profile, prove a source
emission path, execute suffix bytes, or discharge full Osaka/resource agreement.
The existing frozen P10 signatures are unchanged.

### SIGNEXTEND byte-index boundary transport

`SignExtensionConsumer.lean` derives the actual fetched binary SIGNEXTEND step
and `X` continuation for arbitrary intrinsic words and a mapped caller tail.
It requires gas at least 5 and input stack capacity at most 1024. The native
result is the existing reference `UInt256.signextend`, with the complete
charged state preserved outside stack, PC, gas and execution count.

`signextend_large_word`, `signextend_large_scalar` and
`signextend_large_agreement` prove actual cross-representation identity when
the byte index is at least 32. No desired execution, decoder, caller-frame
origin or future preservation theorem is assumed. Eighteen populated controls
cover zero, positive and negative byte values, narrow truncation, two-byte
selection, indices 31/32/maximum, ordered code, and fuel before gas before
stack failure. A concrete client exercises both Scalar and fetched results
of the large-index composition theorem. An admitted input stack of 1024
succeeds; a tail of 1024 produces 1025 output words and refuses.
Account/caller/memory/return-buffer observations use complete
State equality. The Scalar signed-code controls are finite kernel facts.

The all-index theorem below extends this boundary result to all in-range
values. Compiler-path/source/Osaka/resource composition and the full opcode
row remain open.
The frozen P10 interface and the admitted source profile remain unchanged.

Independent finder and skeptic reviews cleared the statements and controls.
The finder requested direct use of the large-index composition theorem and
stack-limit controls; the populated client and success/refusal tests above
address both findings without changing the theorem premises.

### Native external account-code extent

`ExternalCodeExtent.lean` proves five native clauses: `extcodesize_cost`,
`extcodesize_cost_bound`, `extcodesize_agreement`, `extcodesize_read_shape` and
`extcodesize_value`. Backend emission and the existing pinned decoder feed the
actual charged fetched step and `X` continuation. The charge is 100 for a warm
low160 address and 2600 otherwise. The value is that account's full code-buffer
size (zero for a missing account), converted to the native word; the actual
substate records the accessed address. Bounds require enough gas for that
precise charge and input stack length at most 1024.

Nineteen controls preserve complete account/storage/transient-storage/log/
caller/memory/return-buffer states while distinguishing external code length 3
from account balance 73 and fetched code length 5. Cold/warm, low160 alias,
missing/empty code, static (`perm=false`) and writable (`perm=true`) cases run
through the real gate. Input length 1024 succeeds and output length 1025
refuses; gas-before-arity is checked. Post-read cost probes distinguish warming
the requested address from the returned code-size word. These probes are not
a claimed second fetched execution or a PUSH proof.
Ordered fetched and external code bytes and gas/fuel negatives remain explicit.
The G31 source relation still refuses EXTCODESIZE, with a checked refusal
control; no environment key or source admission is added. This proves native
account observation only, not execution of that account, source-installed code
correspondence, physical allocator adequacy or full Osaka/resource closure.

Independent finder and skeptic reviews corrected the writable-permission
control label and requested stack/arity boundaries and post-read warming
coverage. The nineteen checked controls address these findings. A second
fetched instruction sequence remains a separate obligation.

### BYTE and the intrinsic word-byte observation

`ByteObservation.lean` proves seven clauses. `byte_fetched` derives actual
decoding, charge 3, binary stack update, whole State and `X` continuation.
`byte_nat` identifies the exact in-range value as the word divided by
`256^(31-index)`, modulo 256. `byte_image` and `byte_image_word` connect that
value to the existing intrinsic `TryByteImage.wordByte`; `byte_image_agreement`
transports it through actual fetched execution. No desired-simulation premise
is supplied. The original mapped tail remains, with gas at least 3 and input
stack length at most 1024.

`byte_large` proves zero for indices at least 32. The typed-image transport
requires `Fin 32`: the producer's natural-index arithmetic is not an
out-of-range BYTE specification. A boundary control distinguishes its byte at
index 32 from the native zero result. `byte_scalar_refusal` preserves the
existing Scalar slice's refusal of BYTE, with no new scalar opcode semantics
or admitted source path.

Twenty-one controls include a populated typed-image client, complete ordered
32-byte observation, distinct first/second/penultimate/last bytes, wrong-endian
and index-bound negatives, zero/maximum words and indices, admitted stack1024
and output1025 refusal, and fuel/gas/arity order. Complete State equality keeps
nonzero account/caller/memory/calldata/return-buffer observations. The intrinsic
byte image is a pure observation, not a physical allocator or padding witness.
Full compiler/source/Osaka/resource agreement and the full opcode row stay open;
the frozen P10 interface is unchanged.

Independent read-only finder and skeptic reviews cleared the actual equations,
inhabited controls and ownership. The bounded index requirement and lack of
physical/source/Osaka closure remain explicit.

### Source-input calldata extent at arbitrary emitted sites

A fixed-PC, fixed-gas predecessor is not on master.
[CalldataExtent.lean](../../Bridge/SolidityBridge/RoadmapV15/P10/CalldataExtent.lean)
extends the native clause to arbitrary Backend before/after programs, the
actual emitted instruction PC, and an explicit gas-at-least-2 bound.
`calldataSite` installs exactly the existing `Source.Calldata.input` list in
the target buffer; `calldataSite_bytes` preserves its ordered bytes.
`calldatasize_source_input` derives the fetched whole-State result and `X`
continuation from that installation, with input stack length plus one at most
1024. The observed word is the complete input-list length modulo 2^256.

Fourteen controls include a real nonzero-PC, non-exhausting-gas source-input
client, empty input, complete code/calldata lists, decoded-object-table
independence, code-versus-memory-versus-calldata size negatives and gas/fuel/
stack bounds. The fixture tables demonstrate only that input and objects are
separate fields; they do not assert ABI coherence. Neither a source expression
step nor the origin of an arbitrary native call frame follows from installing
its bytes. ABI decoding, physical memory/padding, compiler emission origin and
full source/Osaka/resource correspondence remain open.

Independent read-only finder and skeptic reviews cleared the extension over
the fixed-site predecessor, its inhabited clients and its explicit source/ABI
boundaries.

### Generated environment task signatures

`EnvironmentTasksV1.lean` was generated from a specification; the generator
and specification are not on master. It contains claim types only. `OriginClaim`, `GasPriceClaim` and `ChainIdClaim` describe
actual fetched whole-State and `X` producer goals, with explicit gas and stack
bounds. They have no proofs or instances. ORIGIN observes the pinned reference
`sender`, GASPRICE observes its transaction price, and CHAINID uses the existing
`State.chainId`; no source environment profile is extended.

Separate `OriginFactsClaim`, `GasPriceFactsClaim` and `ChainIdFactsClaim` describe
only cost2, zero-input/one-output arity and zero expansion.
`SourceRefusalsClaim` retains G31 refusal. These are routine glue tasks in
`PendingGlueBatch`, whose existence is unproved. Unconditional environment
execution and full source/compiler soundness remain separate obligations. The
module's successful type check proves no claim, discharges no opcode row, and
does not alter the existing frozen P10 interface.

Lane reviews checked the generated statements against that specification
and the producer-versus-routine-glue split. No supplied inhabitant of the pending glue structure is claimed.

### Native environment producer clauses from finite facts

`EnvironmentObservationProducer.lean` proves `origin_at`, `gasprice_at` and
`chainid_at` against the actual fetched relation. Each takes the exact
`EnvironmentTasksV1.LocalFacts` for that site: cost 2, zero inputs, one output
and zero memory expansion. These premises contain no execution, decoder,
frame-origin or desired-simulation claim. Actual decoding, charged gating,
native opcode evaluation and the `X` continuation are derived. Gas at least 2
and stack length plus one at most 1024 remain explicit.

`EnvironmentObservationWitness.lean` supplies three populated clients with
concrete local-fact proofs and complete State/continuation observations. The
origin client observes sender 19, distinct from caller source 11 and owner 7;
the price client observes transaction price 37. The fixtures start with gas
9, PC 3 and execution count 41; the clients state the next State through
`chargedPrepare … replaceStackAndIncrPC` rather than as numerals. The
original tail `[258,513]`, accounts and memory/calldata/return buffers remain
in the complete resulting State. Chain ID uses the reference's existing
constant. Gas/fuel refusals and the origin-versus-caller negative are checked.

These facts are state-independent for the constant-cost `W_base` opcodes, so
the producer is only nominally conditional; the universal fact claims would
follow the `observation_gate` `rfl` pattern but are not proved. They and the
unconditional claims generated in `EnvironmentTasksV1` are
still open. Concrete clients demonstrate non-vacuity, not all-site coverage.
The profile refusals, full source/world/resource/Osaka correspondence and all
full opcode rows remain unchanged.

Independent read-only finder and skeptic reviews cleared the native producer
proofs and concrete witnesses. Discharging the unconditional producer claims,
the routine fact proofs and broader control coverage remain open.

### SIGNEXTEND preservation below the selected sign bit

`SignExtensionPositive.lean` proves an explicit positive case of the numeric
bridge for every byte index `w : Fin 32`. When `b.toNat < 2^(w.val*8+7)`,
`signextend_positive_word` proves that the actual reference SIGNEXTEND mask
preserves `b`. The proof derives the real sign-bit position and masked value
from the existing UInt256/Fin operations; it does not assume a mask/cleanup
correspondence. `signed_clean_positive` proves the published intrinsic signed
cleanup preserves that same value. `signextend_positive_agreement` composes
both with the existing fetched step, exact charge 5, original mapped tail and
`X` continuation. Gas at least 5 and input stack capacity at most 1024 remain
explicit. Native execution starts with explicit width/value operands; native
PUSH-prefix execution and compiler/frame origin are not inferred.

Three populated clients cover byte indices 0, 1 and 31 with values 127, 128
and `2^255-1`. The intrinsic cleanup and native whole-State/continuation
observations agree. Three further controls distinguish the strict sign-bit
bound, byte-index units, and the exact code/resource observations. Value 128
at index 0 is excluded by the new case's strict bound and changes in the real
reference; this is not permission to exclude it from the admitted profile.
The residue and all-index theorems below cover the other arithmetic cases.
Full compiler/source/resource/Osaka correspondence and the full opcode row
remain open. Existing theorem signatures, source profiles and frozen interfaces
are preserved.

Independent read-only finder and skeptic reviews cleared the actual mask
argument, strict-domain witnesses and composition. The new positive case is
not a weakening or replacement of general in-range correspondence, and it
does not overlap the open environment fact claims.

### Arbitrary high-bit truncation with a clear residue sign bit

Three additional lemmas in `SignExtensionPositive.lean` extend coverage from
bounded full words to arbitrary discarded high bits. When
`b.toNat % 2^(Scalar.widthBits w) < 2^(Scalar.widthBits w-1)`,
`signextend_nonnegative_residue_word` proves that actual native SIGNEXTEND
returns the published `Scalar.unsignedClean w b` word. The proof reuses the
checked sign-bit equation and derives the clear bit from modular bitwise laws.
`signed_clean_nonnegative_residue` proves the independent signed cleanup
selects that same residue, and `signextend_nonnegative_residue_agreement`
composes intrinsic cleanup with actual fetched State/`X` transport. No bound
on the original full-word magnitude or signed view is assumed. Gas, stack
capacity and explicit initial operands retain the preceding execution bounds.

`SignExtensionResidueWitness.lean` supplies three nonzero clients:
`383 → 127` at byte index 0, `2^200+128 → 128` at index 1, and the full-width
word whose signed view is `-129 → 127` at index 0. Four additional controls
show real high-bit removal, the negative full-word view, the still-distinct
negative-residue case, and complete ordered stack/code/resource observations.
The last countercontrol confirms a low byte of 128 cannot use the unsigned
result. Negative low residues remain required by the original admitted
profile and are covered by the all-index theorem below. Native prefix/compiler
origin and full source/Osaka/resource closure remain open.
Existing positive-case signatures and frozen interfaces are unchanged.

Independent read-only finder and skeptic reviews cleared the modular masking
argument, arbitrary-high-bit domain and nonzero clients. The negative-residue
countercontrol distinguishes the two mathematical cases combined by the
all-index producer below.

### All-index SIGNEXTEND Scalar/reference primitive

Five additional lemmas complete the remaining arithmetic primitive in the
pinned reference model. `signextend_negative_residue_word` derives the actual
negative branch's upper-bit fill and connects it to the published
`Scalar.signedClean_nat`. `signextend_width_word` combines both sign cases for
every declared byte width and every value. `signextend_all_word` additionally
uses the real identity rule for indices at least 32.
`signextend_scalar_result` is the exact existing intrinsic step equation, and
`signextend_all_agreement` transports that result through actual fetched
execution and its `X` continuation for all index/value words.

The final producer has no sign or residue premise. It retains exact gas at
least 5, input stack capacity at most 1024, fuel and the explicit represented
operands. It derives decoding and execution without a supplied simulation.
Native PUSH-prefix execution, compiler/frame origin and whole-program resource
adequacy do not follow from this local producer.

`SignExtensionAllWitness.lean` has six unified clients: negative byte, negative
truncation, high-bit two-byte negative input, full-width minimum, first large
index 32, and maximum index/value. Four further controls distinguish an
incorrect unsigned result, incorrect index wrapping, signed views and complete
ordered code/stack/resource observations. The original caller/account/buffer
state and tail remain observed by complete State equality. Existing
SIGNEXTEND gas/fuel/stack controls are retained separately.

This closes the word/Scalar arithmetic and local fetched-step clause only.
It does not establish compiler/source correspondence, full Osaka approval or
closure of the full opcode row. Earlier positive and residue cases remain
valid consequences, with unchanged signatures. Frozen interfaces and source
profiles are unchanged.

Independent read-only finder and skeptic reviews cleared the negative fill,
all-index case composition and unified clients. The arithmetic producer has
no sign/residue premise, while gas, capacity, explicit operand representation
and the remaining full-V15 boundaries stay visible.

## Unsigned quotient and remainder at arbitrary emitted sites

`UnsignedDivisionConsumer.lean` proves `div_agreement` and `mod_agreement`
for any emitted site, arbitrary represented operands and spill, adequate gas
(at least 5), explicit stack capacity and positive driver fuel. Both results
retain exact Scalar output, complete charged target State and actual X
continuation. Public word equations expose the unsigned zero-divisor policy;
`div_capacity_refusal` derives actual overflow from the gate after gas and
operand checks, without assuming a refused storage or state frame.

A fixed-site predecessor (PC 0, single-byte code, gas 5) is not on master. This checkpoint covers arbitrary encoded
prefixes/suffixes, program counters and adequate initial gas. It adds no
opcode-row coverage.

`UnsignedDivisionControls.lean` observes nonzero quotient/remainder, high-bit
unsigned values, zero operands/divisors, maximum words, admitted input capacity,
actual output overflow, gas-before-arity and fuel-before-gas ordering, and
incorrect signed interpretation, operand order and remainder. Whole-State
success equations retain populated caller/accounts, memory, calldata, return
buffers and the ordered caller tail. These local results do not establish
source division guards, executed compiler prefixes, full resource adequacy or
Osaka approval. All full opcode rows and original parent obligations remain
open.

Independent read-only finder and skeptic reviews confirmed the unsigned
arithmetic and charged-state transport. Their prior-coverage finding was
resolved by recording the fixed-site predecessor explicitly; their capacity
finding was resolved with the general gate refusal and populated overflow
client. No earlier arithmetic coverage is counted twice.

## Integration record

Merged: the 21 modules above and their Bridge root imports. The DIV, BYTE and
SIGNEXTEND overflow refusals start from 1026 input words and EXTCODESIZE from
1025; they check the gate arithmetic on an over-limit stack that no
well-formed state reaches. Only the PC/GAS/MSIZE capacity boundary is
reachable. The environment-task generator and its JSON specification are not
on master. Read-only finder and skeptic reviews found no Lean defect.

## Storage warmth and key isolation (SLOAD/TLOAD)

`StorageWarmTransport.lean`:
- `sload_warm_cost`: after the vendor `sload` state update, a cost probe that
  reinstalls the same owner/key is charged the warm cost, for every state,
  slot, value, tail and cost. The probe installs the key itself; nothing says
  the next instruction or the returned value supplies it.
- `sload_distinct_cost`: the update keeps the persistent-read charge of every
  distinct owner/key pair (`storage_keys_compare_eq` turns the pinned
  comparator into pair equality). The inequality is about numeric keys; it is
  not hash injectivity or path distinctness.
- `tload_retains_sload_cost`: a transient read leaves that charge unchanged.
- `sload_resource_frame`: from the charged fetched SLOAD result
  (`driverSteps`) and the storage-preservation law, derives the warm cost and
  persistent/transient observations. First-read gas, stack room, represented
  input and fuel stay explicit premises; a following read needs its own.

`StorageWarmControls.lean` (eight controls) and
`StorageIsolationControls.lean` (four) instantiate these on populated states:
a two-read success that works only because the stored value equals its key, a
gas refusal when the returned value is a different cold key, wrong owner/key
and transient negatives, warm/cold distinct-pair clients (both with the code
owner, differing only in the key) and an equal-pair counterexample showing the
inequality premise is needed.

Open: source/compiler origin of keys, physical allocation and padding, full
resource adequacy, Osaka world/transaction composition, opcode-row coverage.

## Charged execution of the existing word emitter

`Bridge/SolidityBridge/RoadmapV15/P10/WordPushConsumer.lean` connects the actual
`Scalar.pushWord` emitter to the pinned reader, decoder, checked driver and X.
The emitter always uses PUSH32 and exactly 32 big-endian payload bytes, including
for zero. Its payload value is derived using the existing backend roundtrip and
`Bridge/SolidityBridge/RoadmapV15/ReferenceReader.lean`; pure encoding dependencies
are reused unchanged rather than counted as new proofs.

`push_word_value`, `decode_word_push` and `word_push_agreement` hold for arbitrary
words, seed state, represented caller tail and encoded prefix/suffix. The input
constructs the exact code image, selected nonwrapping PC and mapped stack.
Successful execution retains the Scalar result, complete charged native State
and actual X continuation. Explicit premises are gas at least 3, input length
at most 1023, selected PC fitting the native word and the stated positive fuel.
The actual instruction adds 33 to the native PC, charges 3 and advances the
execution count once. Prefix execution, source/frame origin, subsequent-PC fit,
whole-program resource adequacy and Osaka approval do not follow from this
constructed representation.

`word_push_full_stack` derives both driver and X overflow from a valid input of
1024 words after adequate gas. This is a valid-input local capacity refusal; it
does not rely on an already over-limit input. It contrasts with the explicit
success bound without weakening source or target resource requirements.

Thirteen controls directly use the producer and preserve complete State.
They cover nonzero data, zero still using PUSH32/gas 3, maximum and typed signed
words, constructor wrapping before emission, writable/static contexts, input
1023 success/input 1024 refusal, gas before overflow, counted-driver fuel
refusal, wrong byte order and wrong payload length. The populated fixture has
32 resident memory bytes with one active word, nonzero accounts and matching
initial account snapshot, complete caller tail, calldata and return buffers.
Full ordered code/stack/buffer observations are retained. Constructor wrapping
is not a source integer-overflow policy conclusion, and the X continuation
does not assert terminal buffer behavior.

The earlier selected-program PUSH fixtures remain valid separate evidence.
This consumer generalizes to the actual word emitter at arbitrary encoded
sites and adequate gas, and adds no full opcode-row closure. The two-instruction
signed-cleanup composition is proved below; original compiler/world/driver
obligations remain separate. Independent read-only finder and skeptic reviews cleared
payload derivation, checked state transport, the valid full-stack refusal and
all populated controls.

## Different-owner storage cost probes

`Bridge/SolidityBridge/RoadmapV15/P10/StorageOwnerControls.lean` adds
`different_owner_cost`, a direct instance of `sload_distinct_cost` with the same
numeric slot 13 at different owners 7 and 11. `populated_controls` distinguishes
the other owner's cold charge 2100, its prewarmed charge 100 and the read owner's
newly warm charge 100. Ordered code, stack, memory, calldata and return buffers
are explicit, with populated accounts and a retained caller tail.

These are observations of the actual vendor SLOAD update with a constructed
cost probe; they prove neither a following fetched read nor its gas adequacy.
The fixture's supplied charge 2100 is not a new resource-adequacy theorem.
No symbolic-path distinctness, hash injectivity, physical-memory validity or
source/world correspondence is inferred. This adds two control declarations,
not opcode-row closure. Independent read-only finder and skeptic reviews
confirmed the distinct-owner premise and these boundaries.

## Signed-cleanup tail at the emitted byte site

`Bridge/SolidityBridge/RoadmapV15/P10/SignedCleanupSites.lean` constructs the
SIGNEXTEND site after the actual word-index emitter in `Scalar.signedCode`.
`signed_cleanup_index_word` transports that emitted byte index through the
published all-width reference word law. In
`Bridge/SolidityBridge/RoadmapV15/P10/SignedCleanupTail.lean`,
`signed_cleanup_code` proves equality with the complete encoded signedCode image,
and `signed_cleanup_tail` pairs the full intrinsic cleanup result with the
actual fetched SIGNEXTEND driver step and X continuation. All widths and words
are quantified, including negative residues and truncation. The native entry
stack contains the explicit represented width index, value and arbitrary tail.
The selected PC fit, gas at least 5, capacity and positive fuel remain explicit.

Three declarations in
`Bridge/SolidityBridge/RoadmapV15/P10/SignedCleanupControls.lean` provide a direct
universal producer client, populated complete-State execution with gas/fuel
refusals, and signed/truncation/boundary/wrong-index plus ordered observations.
The negative 8-bit example uses 128; the input 2^200 + 384, whose low byte
is 128, also becomes -128. The 16-bit negative and full-width boundary are checked separately.
The wrong-index control distinguishes a byte index from the bit count 8.
The fixture retains populated accounts, a coherent 32-byte memory buffer,
caller tail, complete code, calldata and return buffers.

This is a tail-entry theorem. It neither assumes nor proves native execution
of the preceding PUSH, even though the complete emitted code image is exact.
Connecting the first step's output PC, gas and stack to this entry is proved
in the two-instruction composition below. Source/compiler origin, full resource
adequacy and Osaka/world/transaction correspondence remain separate, and no
full opcode row is closed. Independent read-only finder and skeptic reviews
confirmed these statement and non-vacuity boundaries.

## Complete two-instruction signed cleanup

`Bridge/SolidityBridge/RoadmapV15/P10/SignedCleanupAlignment.lean` proves native
gas subtraction leaves at least 5 after charging 3 from an initial budget of 8,
the modulo-word PC addition by 33, and complete equality of the actual PUSH
output with the represented SIGNEXTEND tail entry. Alignment includes the code
image, stack, all account/memory/buffer fields and the actual charged counters;
no intermediate frame is supplied as a premise.

`Bridge/SolidityBridge/RoadmapV15/P10/SignedCleanupComposition.lean` then proves
`signed_cleanup_composition` for every admitted width, value, caller tail,
seed and encoded prefix/suffix. It pairs the existing intrinsic signedCode run
with actual `driverSteps 2 (fuel+3)` and X continuation at `fuel+1`. The proof
consumes the word-emitter and tail results and the existing `fetched_steps_cons`
law; a redundant draft helper is not exported or counted as new coverage.

The initial stack is value followed by the arbitrary tail. Explicit premises
are gas at least 8, tail length plus 2 at most 1024, and the post-PUSH instruction
PC fitting the reference word. First-step fit, capacity, remaining gas and the
intermediate State equality are derived. Native PC arithmetic stays modular;
no subsequent-PC nonwrapping or prefix-origin claim follows. This establishes
adequacy for these two reference instructions, not a whole-program resource
abstraction or Osaka approval.

Four control declarations in
`Bridge/SolidityBridge/RoadmapV15/P10/SignedCompositionControls.lean` directly
consume the producer and check complete final States for negative, truncating
and full-width maximum examples. Exactly 8 gas becomes 0, PC 3 becomes 37 and
execution count 41 becomes 43. Gas 2 fails at PUSH, gas 7 fails at SIGNEXTEND,
and counted fuel 2 refuses the second instruction. Native underflow/wrap and
complete ordered code, caller tail, memory, calldata and return buffers are
retained. Direct dispatcher reduction hit the original heartbeat budget; the
passing controls use modular execution and simplify only resulting State fields.
No proof budget or observation was changed.

Independent read-only finder and skeptic reviews confirmed the actual step
composition and populated controls. Compiler/source/frame origin, whole-program
resources, account/world/transaction/trace correspondence and full opcode-row
coverage remain open. The theorem gives an X continuation, not STOP termination
or a terminal return-buffer assertion.

## Bitwise words at arbitrary emitted sites

Earlier fixed-entry checks of these operations are not on master. The delta
here is arbitrary emitted Site and adequate-gas transport plus reusable public
word equations, with zero new opcode rows.

`Bridge/SolidityBridge/RoadmapV15/P10/BitwiseWords.lean` exposes three reusable
native-word consequences for AND, OR and XOR. Each actual reference operation's
modulo is discharged by the existing intrinsic result bound. In
`Bridge/SolidityBridge/RoadmapV15/P10/BitwiseConsumer.lean`, three consumers pair
the existing Scalar result with charged fetched execution and complete-State X
continuation for arbitrary emitted sites, operands, tails and adequate gas.
The existing decoder theorem supplies each actual opcode. Gas at least 3,
capacity and selected-PC fit stay explicit; the gate, stack arity, both static
permissions and actual dispatcher step are derived.

Six declarations in
`Bridge/SolidityBridge/RoadmapV15/P10/BitwiseControls.lean` include direct
populated full-State clients distinguishing overlapping-bit AND/OR/XOR results.
OR uses writable permission and nonminimal gas 11 becoming 8; AND and XOR use
static permission and gas 3. All sites have a nonempty encoded prefix. A valid
1024-word binary input succeeds with 1023 output words. Gas, arity and counted
fuel failures retain their order. The extra overflow probe starts with 1026
items and is explicitly outside the well-formed profile; it proves no reachable
valid-profile overflow case. Symbolic length reasoning avoids unfolding the
large stack, with no recursion-budget increase.

Zero, maximum, high-bit, overlapping and nonoverlapping bit patterns and wrong
operation selection are checked alongside complete ordered code, stack, memory,
calldata and return buffers. These are local site/gas and word-transport results,
not full opcode-row closure. Source/compiler/frame origin, subsequent-PC fit,
whole-program resources and Osaka/account/world/transaction/trace correspondence
remain open. Independent read-only finder and skeptic reviews checked the
statements, non-vacuity and explicit profile boundaries.

## Complete unsigned-cleanup emitter execution

`Bridge/SolidityBridge/RoadmapV15/P10/UnsignedCleanupLayout.lean` consumes the
existing intrinsic `Scalar.unsigned_correct` theorem to obtain the emitted mask
result; it does not reimplement width arithmetic. Its reference gas-debit law
proves exact natural subtraction under `cost ≤ g.toNat`, deriving that the
encoded cost fits the native word. The actual complete unsignedCode image and
complete PUSH-output/AND-entry State equality are proved separately.

`Bridge/SolidityBridge/RoadmapV15/P10/UnsignedCleanupExecution.lean` composes the
actual PUSH32 mask and AND, for every byte width, value, tail, seed and encoded
prefix/suffix. The existing Scalar result is paired with `driverSteps 2` and the
actual X continuation. Gas at least 6, peak capacity (tail length plus 2 at most
1024), selected post-PUSH PC fit and fuel stay explicit. First-step fit, capacity,
remaining gas and the intermediate State equality are derived, not supplied as
an execution or frame premise. Existing word-emitter, AND and counted-prefix
producers are reused. This adds local emitter composition, not new arithmetic
or complete opcode-row coverage.

Six declarations in
`Bridge/SolidityBridge/RoadmapV15/P10/UnsignedCleanupControls.lean` directly
consume the producer on populated complete States. They cover nonzero and high-
bit truncation, 8/16-bit observations, full-width maximum identity, and strict
unsigned-versus-signed 128. An initial stack of 1023 succeeds at a peak of 1024;
a valid initial stack of 1024 refuses the emitted PUSH in both driver and X.
Gas of 2 fails at PUSH, gas of 5 fails at AND and counted fuel of 2 refuses the
second instruction. Exactly 6 gas becomes 0, PC 3 becomes 37 and count 41 becomes
43. Wrong byte order and an oversized
wrapping-cost counterexample retain the encoding and adequacy requirements.
Complete ordered code, caller tail, memory, calldata and return buffers remain
explicit. Independent read-only finder and skeptic reviews confirmed these
statement, capacity and non-vacuity boundaries.

The result does not establish source/compiler/frame origin, subsequent-PC fit,
whole-program resource abstraction, STOP termination or Osaka/account/world/
transaction/trace correspondence. All complete opcode rows remain open.

## Selected Boolean-not fetched consumer

The BooleanNotWords and BooleanNotConsumer modules consume the actual
`Scalar.selectUnary .not .bool` certificate. The word equation is universal;
the typed consequence uses an already evaluated canonical Boolean. At an
arbitrary emitted ISZERO site, the producer derives decoding, charged gate,
Scalar result, complete fetched-step State and full X continuation. Adequate
gas (at least 3), legal stack capacity and counted fuel remain explicit. The
supplied jump array is arbitrary, with no claim about scanner correctness.
No source expression evaluation, short-circuit or source-frame origin is proved.

Earlier private NumericRows02 coverage was a fixed-entry raw ISZERO law. This
increment adds arbitrary-site/resource/array transport and the selected typed
certificate consumer; it counts no new complete opcode row. BooleanNotControls
uses populated writable true and static false clients at PC 3, with distinct
caller-tail words, account fields, memory, calldata and both return buffers.
Raw zero, maximum and noncanonical 2 remain separate from canonical Booleans.
A legal 1024-word input succeeds without growth. Gas precedes arity failure;
counted-fuel refusal precedes gas. Exact ordered bytes distinguish ISZERO from
bitwise NOT, and complete State equalities retain all untouched observations.
The nonempty array is only a supplied-parameter probe. Independent read-only
finder and skeptic reviews inspect these non-vacuity and scope boundaries.

The result leaves all complete opcode rows open. It does not discharge compiler
representation/source origins, full driver/resource adequacy, fork approval,
physical allocation/padding, account/world, call/create, transaction or trace
composition. The frozen P10 signatures are unchanged.

## Selected unsigned bitwise-NOT fetched consumer

UintNotWords and UintNotConsumer connect actual `Scalar.selectUnary .bnot .uint`
and its `uintNot.correct` certificate to the native NOT operation. The typed
law retains the actual intrinsic evaluator's optional result; the native word
is the full 256-bit complement. The input is an already evaluated intrinsic
uint, not a source expression or compiler frame. Decoding and charged gates
are proved for arbitrary emitted sites, adequate gas, legal unary capacity,
counted fuel and arbitrary supplied jump arrays. Neither a desired native
execution nor a decoder result is assumed. Complete State and X conclusions
retain caller tails and untouched seed observations under the represented
initial code, PC and stack.

The private NumericRows01 fixed-entry raw NOT law is prior coverage. This
increment adds arbitrary-site/resource/array and selected-certificate consumer
transport, not new opcode arithmetic coverage or any complete opcode row.
Inhabited typed258 uses the existing source certificate and a writable populated
state. Static raw clients cover zero, maximum and the high bit; a legal
1024-word input succeeds without growth. Gas-before-arity and fuel-before-gas
refusals are explicit. Full ordered code, stack, memory, calldata and both
return buffers distinguish NOT from logical ISZERO, with exact gas, PC and
instruction-count changes. Constructor wrapping is a word probe, not a source
overflow-policy theorem; the nonempty supplied array is not scanner evidence.
Independent read-only finder and skeptic reviews confirmed these boundaries.
All complete opcode rows and the broader source/compiler, physical allocation,
resource/driver, fork, account/world and transaction/trace obligations remain
open. Frozen P10 signatures are unchanged.

## Selected wrapping arithmetic consumers

WrappingArithmeticWords and WrappingArithmeticConsumer connect the actual
`wrappingAdd`, `wrappingSub` and `wrappingMul` selections to emitted ADD, SUB
and MUL. Existing word-ring representation is reused. Each typed consumer
retains its actual optional intrinsic evaluator certificate, with already
evaluated uint inputs. It derives decoding, charged gates, native dispatch,
complete State and X continuation at arbitrary represented sites and supplied
jump arrays. ADD and SUB charge 3; MUL charges 5. Legal input capacity and
counted fuel stay explicit. No desired trace, decoder or intermediate-frame
premise is supplied by the client.

Private NumericReference already proves word morphisms, arbitrary-seed supplied
ADD/SUB/MUL steps and typed wrapping-certificate transport to complete supplied
steps (including an actual source result). NumericRows01 fixed-entry SUB/MUL is
also prior coverage. The new contribution is emitted-site decoding, actual
resource-gate admission, driver/X composition, selected code images and supplied-
array generality. This is not the first typed certificate/reference transport;
it counts no new arithmetic or complete opcode row. WrappingArithmeticControls applies all three selected laws and includes an
inhabited typed 0 minus 1 result with the actual full State/X. Raw maximum-plus-
one, zero-minus-one and high-bit-times-two wrap at exactly 256 bits. A legal
1024-word input becomes 1023 while retaining every caller-tail word. Operand
order, opcode bytes, differing MUL cost, gas-before-arity and fuel-before-gas
refusals are explicit, alongside complete ordered memory/calldata/return data.
Checked subtraction still rejects 0 minus 1; the wrapping result does not change
its profile or failure policy. Independent read-only finder and skeptic reviews
confirmed these boundaries.

The represented code/PC/stack and arbitrary jump-array parameters do not prove
source-frame origin, scanner validity, physical allocation, whole driver/resource
adequacy, approved fork correspondence, account/world or transaction/trace
composition. All complete opcode rows and the broader V15 obligations remain open. The
frozen P10 signatures are unchanged.

## Selected unsigned shift sequence consumers

LogicalShiftExecution connects the actual `uintShl` and `uintShr` emitters to
both fetched instructions: SWAP1 followed by SHL or SHR. Source operands are
value/count; the native shift consumes count/value. The first actual SWAP law,
complete intermediate-State alignment, post-SWAP PC and exact remaining gas
are derived, then the second charged gate and fetched step are composed into
driverSteps and X. The selected typed consequences retain the existing optional
intrinsic evaluator certificates on already evaluated uint values. Legal
capacity, gas at least 6, counted fuel and nonwrapping post-SWAP prefix remain
explicit. The first PC bound follows from that prefix. These sequence laws use
the empty supplied jump array; they make no scanner-correctness claim.

The prior private NumericRows05 word/saturation and fixed-entry raw shift laws,
published Scalar.Shifts two-instruction source certificates and published
StackFamilyConsumer fetched SWAP laws are existing coverage. The increment is
the actual selected two-instruction fetched composition and derived complete
intermediate state/resources, not new word arithmetic or first source-certificate
correctness. No complete opcode row is closed.

LogicalShiftControls consumes the typed producers on nonzero 3 shifted left by
2 and 128 shifted right by 7, including complete State/X. Static clients cover
counts 0, 255, 256 and maximum; the full count word is never reduced modulo 256.
Legal 1024-word inputs pass SWAP unchanged in height, then shift to 1023 words
with the original tail. Gas 2 fails at SWAP, gas 5 fails at the shift, and counted
fuel 2 fails before the second instruction. Omitted SWAP, wrong operand order,
low-byte count reduction and logical-versus-arithmetic right shift are negative
controls. Exact ordered code, intermediate/final stacks, PC, gas, instruction
count, memory, calldata and both return buffers are explicit. Independent
read-only finder and skeptic reviews checked these non-vacuity boundaries.

The X continuation law does not assert STOP success, source/compiler/frame
origin, physical allocation/padding, whole driver/resource adequacy, approved
fork, account/world or transaction/trace correspondence. Signed source counts
are outside these uint statements, without changing any profile or refusal.
All full opcode rows and broader V15 obligations remain open. Frozen P10
signatures are unchanged.

## Selected signed non-strict comparison

SignedLeExecution connects the actual `intLe` emitter, SGT followed by ISZERO,
to both charged fetched instructions. It derives the strict signed predicate,
complete intermediate State and second-instruction resource/PC requirements.
The existing `flag_not_lt` lemma turns that predicate into the non-strict
result, including equality. The typed consequence retains the actual optional
intrinsic certificate on already evaluated signed inputs. Legal capacity, gas
at least 6, counted fuel, post-SGT prefix fit and the empty supplied jump array
remain explicit. No desired trace, decoder, source frame or flag premise is
provided by the caller.

The reserved SignedOps word bridge, private NumericRows03 word/fixed-entry
strict-comparison and typed strict-source results, published Comparisons.intLe
source certificate, prior ISZERO and local PC/gas transport are existing
coverage. This increment is selected SGT/ISZERO fetched composition and its
derived complete intermediate state/resources. It is not first signed arithmetic,
strict-source, source-certificate or ISZERO correctness; no full opcode row closes.

SignedLeControls applies the selected producer to -1 versus 0 in both orders,
with source result, full State and X. Static clients include signed minimum,
signed maximum and equality. A legal 1024-word input becomes 1023 after SGT
and keeps that height through ISZERO, preserving its caller tail. Gas 2 fails
at SGT, gas 5 at ISZERO, and counted fuel 2 before the second instruction.
Unsigned comparison, strict comparison at equality and omission of ISZERO are
negative controls. Exact code, intermediate/final stack, gas, PC, instruction
count, memory, calldata and both return buffers remain ordered observations.
Independent read-only finder and skeptic reviews checked these boundaries.

The local continuation law asserts no STOP success, scanner validity, source/
compiler/frame origin, physical allocation, whole-resource or approved-fork
adequacy, account/world or transaction/trace correspondence. All full rows and
broader V15 obligations remain open; frozen P10 signatures are unchanged.

## Value-directed consecutive storage reads

StorageChaseExecution composes two actual emitted, fetched SLOAD instructions.
The first loaded word supplies the second key; it is never assumed equal to
the initial key. Both charges are computed from the actual intermediate states.
Their sum is an explicit exact resource-adequacy condition, from which the
second gate's remaining gas is derived. A separate 4200-gas sufficient bound
covers both reads. The complete State/X continuation, exact natural gas debit,
persistent storage-read function and transient read observations are proved.
Post-first prefix fit, legal stack capacity, counted fuel and the empty supplied
jump array stay explicit.

StorageChaseCost consumes the published warmth/isolation results: when the
loaded value equals the original key, the second charge is 100; otherwise it
is the original state's charge at that loaded value. This exhaustive numeric
case split adds no hash injectivity or symbolic-path premise. The intermediate
record and cost observations alone are recipes; the execution theorem ties
them to actual fetched execution under the stated resource condition.

Prior StorageReadConsumer charged/source-slot transport, StorageWarmTransport
reinstalled-key/frame/isolation laws, the same-value-as-key two-read fixture and
explicit-key reload sequences remain prior coverage. The increment is general
value-directed two-read composition and successful value-not-key clients. It
does not add compiler admission for pointer chasing or complete a symbolic
compiler-path, storage-layout, source or world correspondence clause.

StorageChaseControls executes 13 to 17 to 99 with two cold charges, and the alias
13 to 13 with a warm second read. A locally warm slot 17 reduces the charge;
a warm pair for another owner does not. Direct consumers exercise both arms of
the charge theorem. Legal 1024-word inputs retain their height and full tail.
Exact 2200-gas alias success is distinguished from nonalias second-read failure,
first-read gas failure, fuel failure and actual empty-stack refusal. Storage
and transient observations remain separate, with complete ordered code, stack,
accessed-key pairs, gas, PC, instruction count, memory, calldata and both return
buffers. Independent read-only finder and skeptic reviews checked these limits.

This numeric-reference consumer claims no compiler pointer feature, scanner or
STOP result, physical allocator/padding, whole-program resource abstraction,
approved fork, account/world or transaction/rollback/trace correspondence.
All complete opcode rows remain open; frozen P10 signatures are unchanged.

### Arbitrary-site charged POP

`../../Bridge/SolidityBridge/RoadmapV15/P10/PopConsumer.lean` consumes the
published decoder and actual checked/fetched reference step. `pop_agreement`
removes exactly the Scalar head and transports the complete resulting native
State and X continuation. It quantifies over emitted sites, adequate initial
gas, caller tails, fuel and supplied jump arrays. The input is explicitly
nonempty and at most 1024 words; the supplied array is a parameter, not a
proved jump set. Both static permissions are allowed. No decoder, execution
or caller-frame result is taken as a premise.

Earlier private `NumericRows01.row_pop_agreement` already covered a fixed-entry
POP with gas 2. The new result generalizes site, gas and array parameters;
it does not count POP as a newly handled primitive or close a full opcode row.
The two StackFamily consumers continue to own the existing DUP/SWAP coverage.

`../../Bridge/SolidityBridge/RoadmapV15/P10/PopControls.lean` instantiates the
producer on nonzero 17, zero and maximum words, writable and inherited-static
states, singleton and legal 1024-word inputs. Complete State equality preserves
accounts and ordered memory/calldata/return buffers. Distinct ordered-tail and
retained-head negatives reject incorrect stack observations. Actual driver
refusals retain fuel-before-gas and gas-before-stack ordering.

Independent finder and skeptic source reviews found no proof defect and
identified the earlier fixed-entry coverage for explicit accounting. These are
kernel reference-model consumers; source/compiler origin, valid-jump-set
adequacy, Osaka approval and global resource/account/transaction correspondence
remain separate. All full opcode rows remain open.

### Zero-condition JUMPI

`../../Bridge/SolidityBridge/RoadmapV15/P10/JumpZeroConsumer.lean` discharges the
actual reference gate for any destination word and supplied jump array when
the second stack word is zero. The destination is not checked on this branch.
The emitted site supplies the real decoded JUMPI byte; no successful gate,
decoder result or desired execution is assumed. The complete native output
removes both operands, charges 10 gas, increments execLength and falls through
using the reference word PC addition. The theorem retains explicit initial gas,
nonempty two-operand representation, legal input capacity and fuel bounds.
It transports the actual X continuation without asserting later termination.

The earlier `checked_jump_if` exposes both outcomes of the gate, and
`ExecutionControls.jump_if_skipped` already exercises a fixed skipped branch.
This adds a universal discharged-zero-gate consequence, not first JUMPI
correctness, general scanner agreement or a completed full opcode row.

`../../Bridge/SolidityBridge/RoadmapV15/P10/JumpZeroControls.lean` consumes the
producer with the maximum destination and an empty supplied array, with a
nonempty array and writable excess-gas state, and with minimum/full legal input
stacks. Nonzero conditions 1 and 2 restore bad-destination refusal. Additional
contrasts retain fuel-before-gas and gas-before-stack/destination ordering in
the checked driver. Complete State equalities retain account maps and ordered
memory, calldata, returnData and H_return bytes; wrong tail order and a taken
PC observation are rejected. Supplied arrays are parameter probes, not proved
scanner results or permission to accept bad targets on a nonzero branch.

Separate independent finder and skeptic source reviews found no defect.
These are conditional-on-resources kernel reference-model consumers, not
source control-flow, compiler origin, scanner, Osaka, account/world or global
resource adequacy proofs. All full opcode rows remain open.

### Supplied-membership JUMPI

`../../Bridge/SolidityBridge/RoadmapV15/P10/JumpMemberConsumer.lean` proves
`jump_member_agreement` for arbitrary emitted sites and condition words when
the actual supplied array contains the destination. It derives the checked
gate and decoded step, retaining the exact conditional PC, complete charged
State and X continuation. Adequate gas, two represented operands and legal
initial stack capacity remain explicit. Array membership is a data premise;
it is neither successful execution assumed as a premise nor scanner agreement.

`jump_missing_refusal` proves actual driver and X BadJumpDestination refusal
when the condition is nonzero and the supplied array lacks the destination.
It retains adequate gas and the represented two operands. No capacity premise
is needed because this target failure precedes capacity and static checks.
The shorter X fuel in this refusal theorem admits only the gate failure, not
a successful continuation or later termination.

Earlier `checked_jump_if` exposes the gate, and `ExecutionControls` already
contains fixed taken/skipped clients. The zero-condition consumer above has
no membership premise. These new consequences discharge membership and missing
target clauses universally; they do not count a new primitive or full row.

`../../Bridge/SolidityBridge/RoadmapV15/P10/JumpMemberControls.lean` consumes both
producers with a real fixture JUMPDEST at byte 5, static condition 2, writable
zero/maximum conditions, minimum and full legal stacks, and missing-target
contrasts. Gas, arity and fuel failure ordering is retained. Complete State
and ordered-tail/PC negatives retain account maps and ordered memory, calldata,
returnData and H_return. Computing the backend scanner on these exact bytes
yields `[5]`; this is only a finite fixture fact, not agreement with the reference
scanner or correctness of arbitrary supplied arrays.

Independent finder and skeptic source reviews found no defect. Compiler/source
control-flow, scanner, Osaka, global resources, account/world and transaction
correspondence remain separate. All full opcode rows remain open.

### Linked-reference JUMPI consumer

`../../Bridge/SolidityBridge/RoadmapV15/P10/LinkedJumpConsumer.lean` consumes
`LinkedProgram.reference` from the published assembly bridge. A reference in
the checked image yields its nonwrapping word address, membership in the
certified scanner array and actual JUMPDEST decoding. `linked_reference_member`
supplies the Boolean membership needed by the charged gate.
`linked_reference_jumpi` then transports the exact conditional-PC State and X
continuation of a Backend-encoded JUMPI site. Code equality with the linked
image and the original gas, legal-stack and fuel bounds stay explicit. No
membership, target decode or desired execution is assumed separately.

The new consumer does not recreate the linked-program checker, scanner,
reference or loop-certificate producers. The previous membership consumer
remains the raw supplied-array transport. Equality with opaque upstream D_J,
prefix execution, source/frame origin and subsequent termination remain open.

`../../Bridge/SolidityBridge/RoadmapV15/P10/LinkedJumpFixtures.lean` reuses the
published `LinkedChecks.loopProgram`. Its actual Backend encoding of the entire
loop image aligns by reflexivity. The represented entry is JUMPI at byte 36,
with populated accounts and ordered memory/calldata/return buffers; no preceding
prefix run is claimed.
`../../Bridge/SolidityBridge/RoadmapV15/P10/LinkedJumpControls.lean` consumes the
reference certificate for exit 72, proving target decode and actual charged
State/X. Zero falls through to 37; a nonzero word takes 72. Minimum and full
legal stacks are inhabited. STOP byte 73 is not a reference and is refused as
a nonzero target. Complete ordered bytes and wrong-tail/PC negatives prevent
mistaking this client for a reordered stack or different code image.

Independent finder and skeptic source reviews found no defect. This discharges
available linked-reference and representation clauses, not compiler/source,
physical frame, full scanner, global resource, Osaka or account/transaction
correspondence. All full opcode rows remain open.

### Resource-bounded linked exit completion

`../../Bridge/SolidityBridge/RoadmapV15/P10/LinkedCompletionLayout.lean` constructs
the represented JUMPI entry at byte 36 of the linked image above, with target 72
and canonical nonzero condition 1. Caller accounts, memory, environment, initial
gas and tail are arbitrary native data. These are State observations, not a
second transition semantics. The actual JUMPDEST and STOP gates are discharged
with their original gas, arity, capacity and static checks.

`../../Bridge/SolidityBridge/RoadmapV15/P10/LinkedCompletion.lean` composes the
certified fetched branch with the published `X_destination_stop` law. Eleven
initial gas, a legal two-operand input and fuel at least four suffice for actual
X success after JUMPI, JUMPDEST and the explicit STOP at byte 73. The target is
actually decoded from the linked certificate; STOP is decoded from the exact
emitted bytes. No successful gate, trace or final frame is assumed. Native
returnData is cleared by STOP, H_return is retained, and the PC stays at STOP.
The natural debit theorem proves that the constructed output has initial gas
minus 11; relating that output to execution also requires the execution
theorem's legal-stack and fuel clauses.

`../../Bridge/SolidityBridge/RoadmapV15/P10/LinkedCompletionControls.lean` consumes
the general result with populated static and writable callers. Exactly 11 gas
finishes with zero left; 27 leaves 16. Minimum and full legal input stacks are
inhabited. Ten gas fails at JUMPDEST and fuel three fails at STOP. The refusal
controls use modular step unfoldings. Full terminal State equalities retain
account maps, substate, ordered code, memory and calldata; ordered-tail, PC and
returnData negatives rule out reordered or differently halted observations.

Earlier linked-reference work proves one-step transport, and the published
assembly bridge supplies the scanner/reference and terminal helper laws. The
new result composes this particular three-instruction exit for arbitrary native
caller State and legal tail. It does not execute the preceding prefix, establish
source/frame origin or opaque D_J equality, or prove compiler, account/transaction,
global resource abstraction or full Osaka correspondence. Separate independent
finder and skeptic source reviews found no defect. All full opcode rows remain
open.

## Universal linked-exit resource refusals

`../../Bridge/SolidityBridge/RoadmapV15/P10/LinkedResourceBounds.lean` generalizes
the finite refusal controls to arbitrary native caller State and every legal
tail (length at most 1022). Exactly ten initial gas pays JUMPI but fails the
fetched JUMPDEST charge, with any dispatcher fuel at least three. Three fuel
units with at least eleven gas reach STOP but exhaust its evaluator fuel.
Both proofs compose actual decoder, driver gates and X steps; they assume no
successful trace, desired final frame or source-prefix execution.

`../../Bridge/SolidityBridge/RoadmapV15/P10/LinkedResourceControls.lean` checks
both permissions, populated distinct ordered tails and buffers, and full legal
input capacity. Eleven gas and four fuel succeed, while the corresponding
refused run cannot equal successful empty output. This reference suffix result
does not discharge full opcode, compiler, Osaka, account or transaction closure.

Separate independent finder and skeptic reviews found no defect in the universal
resource premises, populated controls or ownership boundaries.

## Nonbranch jump-table transport

`../../Bridge/SolidityBridge/RoadmapV15/P10/NonbranchTables.lean` proves that
changing the supplied destination array preserves the actual charged gate for
native opcodes other than JUMP and JUMPI. Every gas, stack, static, memory-range
and stipend clause remains in that gate. This is gate equality, not whole-run
table independence for CALL or for a later branch.

The same module consumes the existing emitted PUSH32 decoder and checked
producer to prove identical counted outcomes for any two arrays, for every
fuel value and with no gas or capacity premise. Its success consumer also
retains the Scalar result, complete native output State and actual X
continuation under the original gas, capacity and nonwrapping-PC clauses.
The continuation uses the same supplied array on both sides; no desired
decoder, gate, run, trace or source-frame result is assumed.

`../../Bridge/SolidityBridge/RoadmapV15/P10/NonbranchTableControls.lean` instantiates
arbitrary arrays and both permissions with populated callers. Duplicate and
unrelated entries, zero/nonzero/maximum words, legal full-input refusal and
gas-before-capacity/fuel-before-gas order are checked. A fetched JUMPI changes
its result when membership changes, demonstrating why branches are excluded.
Whole-State success retains complete ordered code, stack, memory, return and
calldata bytes, accounts and substate. No supplied table is asserted to equal
opaque D_J, and no source, Osaka, account/transaction or full-opcode closure
follows. Independent finder and skeptic reviews found no semantic defect;
their JUMP/JUMPI comment correction was applied.

## Fetched linked entry prefix

`../../Bridge/SolidityBridge/RoadmapV15/P10/LinkedEntry.lean` executes the first
two JUMPDESTs of the existing linked image from byte zero. Actual decodes,
charged gates and steps derive a two-step counted prefix and X continuation
at byte two for arbitrary native caller State, any supplied destination array
and every input stack of length at most 1024. Two initial gas and dispatcher
fuel at least three suffice for this prefix. The natural debit is exactly two.
The seed's original PC, code and stack are explicitly replaced at represented
entry; no source/compiler frame origin is inferred.

The frame theorem describes the constructed output. Its execution significance
comes from the prefix theorem, with its gas and capacity premises. Native world,
memory, returnData, H_return and the entire ordered stack remain as represented;
PC becomes two and execLength increases by two.

`../../Bridge/SolidityBridge/RoadmapV15/P10/LinkedEntryControls.lean` supplies
populated static/writable callers, empty/full legal capacity and complete
ordered code, stack, buffers and account observations. With two gas the counted
prefix succeeds, but continued X fails at ISZERO; short prefix fuel also
refuses. This proves neither terminal success nor the remaining prefix,
opaque D_J correctness, source origin, full resource abstraction or Osaka/world
correspondence. Independent finder and skeptic source reviews found no defect.

## Linked entry through ISZERO

`../../Bridge/SolidityBridge/RoadmapV15/P10/LinkedZero.lean` consumes the existing
ISZERO primitive producer at the actual state reached after both JUMPDESTs.
The intermediate full record and emitted code align by proof, not an input
hypothesis. For arbitrary scalar operand and caller tail, five initial gas,
legal input capacity and dispatcher fuel at least four derive the Scalar flag,
three counted fetched steps and X continuation at byte three. Natural gas
debit is exactly five; the native world, memory and return buffers are retained
as represented. The seed's original PC/code/stack are explicitly replaced at
entry; source/compiler origin is not asserted.

`../../Bridge/SolidityBridge/RoadmapV15/P10/CountedAppend.lean` proves the counted
driver composition equation used here, with its exact fuel offsets. This is
algebra of the existing counted driver; terminal opcodes are not thereby shown
to continue in X. The concrete prefix separately consumes nonhalting X laws.

`../../Bridge/SolidityBridge/RoadmapV15/P10/LinkedZeroControls.lean` checks zero,
nonzero signed-word, both permissions and minimum/full legal input capacity.
It retains an independently written full expected State record; the gas-word
field is proved from natural debit. Complete ordered code, stack, caller buffers
and account observations are checked. The prefix can succeed while the next
PUSH runs out of gas; short fuel refuses, and missing operands preserve native
gas-before-arity checks. These are raw scalar/reference word claims, not a new
source signedness or admission policy. Independent finder and skeptic source
reviews found no semantic defect. The following PUSH/branch/terminal composition,
source origin, full resources, scanner/D_J and Osaka/world correspondence remain
separate obligations.

## Particular linked-program exit

`../../Bridge/SolidityBridge/RoadmapV15/P10/LinkedProgram.lean` consumes the
existing emitted PUSH32 producer after ISZERO. Full record and code alignment
are proved, retaining arbitrary scalar operand and supplied table for the
four-step prefix. Eight initial gas and legal peak capacity suffice to reach
JUMPI at byte 36; natural debit is exactly eight.

For an initial zero operand, the computed condition is one. A proved alignment
connects this state to the existing certified linked exit. The theorem
`linked_program_exit` composes all seven fetched instructions from PC0 to
explicit STOP73 using the particular program's supplied linked array. It
requires tail.length+2<=1024, initial gas>=19 and dispatcher fuel>=8. Exact
natural debit is nineteen; the final native world and memory are retained,
returnData is cleared, H_return remains unchanged, the caller tail is restored
and execLength increases by seven. The seed's original PC/code/stack are
explicitly replaced at represented entry.

`../../Bridge/SolidityBridge/RoadmapV15/P10/LinkedProgramControls.lean` derives
an independently written full terminal record, populated static/writable
clients and minimum/full legal capacity. Eighteen gas and seven fuel refuse;
a wrong supplied table refuses at JUMPI. A nonzero signed-word witness covers
only the four-step prefix. Complete ordered code, stack, memory, return bytes,
calldata and account observations are retained. Independent finder and skeptic
source reviews found no defect.

This is a complete execution of this particular zero-operand reference path.
It does not establish source/compiler origin, correctness of opaque D_J,
Osaka fork approval, arbitrary nonzero loop behavior, general account/call,
resource abstraction, transactions or finite/infinite trace correspondence.
All full opcode and parent obligations remain open.

## Nonzero linked fallthrough

`../../Bridge/SolidityBridge/RoadmapV15/P10/LinkedFallthrough.lean` derives the
ISZERO flag from a nonzero scalar operand, proves the complete JUMPI input
alignment and consumes the existing zero-condition branch producer. Five
fetched instructions reach PC37 with eighteen initial gas; the actual next
JUMPDEST extends this to six instructions and PC38 with nineteen gas. Both
laws retain arbitrary native callers and supplied arrays, legal peak capacity
(tail.length+2<=1024), and exact dispatcher fuel offsets. No membership or
successful branch, decoder, frame or run premise is assumed. Natural debits
are eighteen and nineteen. Frame recipes gain execution meaning through the
corresponding prefix theorem and its nonzero/resource clauses.

`../../Bridge/SolidityBridge/RoadmapV15/P10/LinkedFallthroughControls.lean` retains
an independent full expected boundary State. Populated nonzero and raw signed
words, both permissions, empty/full legal capacity and arbitrary tables are
checked. Nineteen gas reaches PC38 but cannot fund the next PUSH; eighteen
fails at JUMPDEST37, and short prefix fuel refuses. Zero takes the other actual
branch and yields the earlier wrong-table counterexample. Complete ordered
code, tail, buffers and account observations are retained, including unchanged
returnData (this prefix has not stopped). These raw-word cases assert no new
source signedness or admission policy. Independent finder and skeptic source
reviews found no defect.

The final PUSH/JUMP cycle, arbitrary repeated nonzero iterations, compiler
origin, scanner/D_J correctness, Osaka approval, account/world/transaction
and complete resource/trace correspondence remain separate obligations.

## Backedge and finite-cycle consumers

| Modules | Native result and exact premises |
|---|---|
| [LinkedBackedgePush.lean](../../Bridge/SolidityBridge/RoadmapV15/P10/LinkedBackedgePush.lean), [controls](../../Bridge/SolidityBridge/RoadmapV15/P10/LinkedBackedgePushControls.lean) | Nonzero operand, arbitrary seed/tail and supplied array; `tail.length + 2 ≤ 1024`, gas ≥ 22, fuel `fuel + 8`: seven fetched steps reach PC 71 with zero above the original ordered tail; debit 22. |
| [LinkedCycle.lean](../../Bridge/SolidityBridge/RoadmapV15/P10/LinkedCycle.lean), [controls](../../Bridge/SolidityBridge/RoadmapV15/P10/LinkedCycleControls.lean) | Same nonzero/seed/capacity premises, certified linked array, gas ≥ 30, fuel `fuel + 9`: eight fetched steps return to PC 0 with the original tail; debit 30. JUMP0 membership is derived from the existing linked certificate. |

Both consumers derive emitted code/state alignment and the actual charged
step/`X` continuation. They retain complete native state, memory, active words,
return data and return buffer; instruction count increases by seven/eight.
Construction-level frame/debit laws acquire execution meaning through the
corresponding prefix theorem. Controls retain independent complete expected
States, signed/nonzero values, both permissions, legal capacity boundaries,
ordered code/stack/buffer/account observations and real gas/fuel failures.
Thirty gas completes one cycle and then refuses the next JUMPDEST charge;
there is no termination, invariant or repeated/infinite execution claim.

Independent reviews corrected confounded negatives: the PUSH test now changes
only the operand at gas 22; the cycle test retains the certified array, gas 30,
fuel 9 and spill and derives the zero-path terminal State at PC 73, gas 11,
count 48 with cleared return data. Missing JUMP0 membership is tested separately.
These sources have now passed focused target checks against the published H7
reference baseline, including their populated controls. No source/compiler, Osaka,
account/world, resource-abstraction or transaction/trace closure follows.

## Invocation environment consumers

[InvocationEnvironment.lean](../../Bridge/SolidityBridge/RoadmapV15/P10/InvocationEnvironment.lean)
generalizes earlier fixed-PC/exact-gas native coverage to arbitrary Backend
sites, gas ≥ 2, one available stack slot and explicit fuel. ADDRESS reads code
owner, CALLER reads execution source (distinct from ORIGIN's transaction sender),
and CALLVALUE reads the exact native value word under either permission flag.
It derives emitted decode, ordered driver checks, whole-State charged steps and
`X` continuation. Its three producer laws have been revalidated against the published H7 baseline. This is neither first opcode coverage nor
source-frame/CALL/world or full-row correspondence.

[InvocationEnvironmentControls.lean](../../Bridge/SolidityBridge/RoadmapV15/P10/InvocationEnvironmentControls.lean)
now has seven checked and registered controls. They retain distinct owner 7,
caller 11 and origin 19, value 37, independent complete expected States,
ordered observations, legal stack capacity and gas/fuel/overflow ordering.
Private proof glue establishes concrete gas/PC arithmetic and rewrites symbolic
stack length before the overflow check, avoiding deep list reduction without
changing statements, expected values or proof budgets. Independent reviews
confirmed those boundaries. The initial failed controls and cold dependency
closure timeout remain failures; subsequent focused H7 checks are separate
passing evidence. No source-frame/CALL/world or full-row correspondence follows.
The delegated universal environment-fact packet remains separate and open.

A read-only metadata review found an unqualified “checked” label in the new
module-map row. It was qualified to separate prior evidence from then-pending H7 validation.
The subsequent focused H7 checks now discharge that validation for these modules.

The H7 documentation correction also separates its published bounded logical
padding proof from the still-separate native allocation/extern boundary. V15
does not reimplement or claim completion of the transferred memory bridge.

The invocation controls were repaired after actual diagnostics identified three
whole-State equality goals and a recursion limit in full-stack reduction. The
repairs preserve all seven public statements and the original expected records;
no heartbeat, recursion, resource, fuel or test bound was increased. The native
CALL/RETURNDATA laws still do not construct `WorldCalls.FetchedPremises`: its
source Step, same invocation identity, raw outcome and execution relations must
come from concrete source/world/compiler producers, not an arbitrary relation.

The subsequent registered-root checkpoint did not complete: a process monitor
refused the closure after the focused checks and KeySort had passed. This is a
failed closure gate, separate from the passing per-file checks and the four
focused backedge/cycle module targets: LinkedBackedgePush,
LinkedBackedgePushControls, LinkedCycle and LinkedCycleControls. Full import and cumulative validation remain open.

## Header time and own balance

[HeaderEnvironment.lean](../../Bridge/SolidityBridge/RoadmapV15/P10/HeaderEnvironment.lean)
proves fetched TIMESTAMP and SELFBALANCE at arbitrary Backend sites, with exact
costs 2 and 5, sufficient gas, one available stack slot and explicit fuel.
The actual decoder, charged driver checks, whole native State and `X`
continuation are derived. TIMESTAMP converts the header Nat modulo the native
256-bit word size. SELFBALANCE reads the code owner's actual account-map entry,
returning zero for an absent entry. No independent balance oracle, warmth,
permission, source frame or desired execution is supplied as a premise.

[HeaderEnvironmentControls.lean](../../Bridge/SolidityBridge/RoadmapV15/P10/HeaderEnvironmentControls.lean)
retains independently stated complete result States and ordered code, stack,
memory, buffers, calldata, accounts and substate. Controls distinguish owner
balance 29 from another account's 41, call value 37 and remaining gas 4. They
cover both permissions, empty and maximal legal input stacks, real overflow,
gas and fuel failures, and a header `2^256 + 513` observed as word 513. The
oversized header and absent-account cases are explicitly raw-reference
behaviors, not source/consensus or driver-origin reachability witnesses.

Earlier private environment-production work already covers fixed-entry reads
with exact opcode charges. This increment generalizes those native clauses to
arbitrary emitted sites and adequate gas; it adds no source profile or first
opcode/full-row claim. Independent finder and skeptic reviews found no defect
in the statements, complete observations or proof boundaries. The new focused
module checks do not discharge the failed registered Bridge closure or the
remaining source/compiler/Osaka/account/world/resource/transaction obligations.

## Native metadata and source-slice refusals

[BlockMetadata.lean](../../Bridge/SolidityBridge/RoadmapV15/P10/BlockMetadata.lean)
proves charged fetched COINBASE, NUMBER, PREVRANDAO, GASLIMIT and BASEFEE
observations from explicitly Backend-encoded sites. Each reads the actual
pinned header field, costs 2, preserves the complete native State except its
specified gas/PC/count/stack update, and has an `X` continuation. Adequate gas,
stack capacity and fuel remain explicit. The supplied destination array is
arbitrary because these operations do not branch; no global scanner or later
jump correctness is inferred. PREVRANDAO reads the supplied word only, without
any randomness-generation or cryptographic interpretation claim.

These native reads are **not** new source support. The same module proves that
all five remain refused by the existing six-opcode `Backend.Environment`
slice: `admittedOp` is false and its local `step` returns `none` for every frame
and tail. This neither changes nor independently characterizes the broader
source parser/profile. No compiler emission, source/world origin or Osaka
approval follows from constructing the explicit Backend opcode sites.

[BlockMetadataControls.lean](../../Bridge/SolidityBridge/RoadmapV15/P10/BlockMetadataControls.lean)
checks five independent complete expected States, both permission flags, a
noncanonical supplied array, empty/maximal legal stacks, overflow and gas/fuel
ordering. Values distinguish beneficiary 23 from owner 7, block number 257 from
time 513, randomness word 43 from difficulty 13, fee 59 from gas price 61 and
call value 37, and gas limit 30000000 from remaining gas 7. A raw header number
`2^256 + 513` becomes word 513 without asserting consensus/source reachability.
Complete ordered code/stack/buffer/account observations and all five local
source-slice refusals remain explicit. Independent finder and skeptic reviews
found no defect. Full opcode rows, registered-root validation, WorldCalls and
source/compiler/account/transaction composition remain open.


### Fetched signed-negation body

[NegationBody.lean](../../Bridge/SolidityBridge/RoadmapV15/P10/NegationBody.lean)
connects the actual G25 selected signed-negation body (`PUSH32 0; SUB`) to
two fetched reference steps. For arbitrary typed signed operands, surrounding
Backend code, seed State and spill, `negation_body_execution` derives the Scalar
word result, exact two-step output and continuation equality. Post-PUSH PC fit,
peak stack capacity (`spill.length + 2 ≤ 1024`), gas at least six and explicit
fuel remain premises. Code, intermediate alignment, gas debit and retained
State/memory/return buffers are proved separately; no execution or decoder
agreement is assumed as an input.

[NegationBodyControls.lean](../../Bridge/SolidityBridge/RoadmapV15/P10/NegationBodyControls.lean)
checks independent complete expected States for positive, negative, zero,
minimum and maximum signed inputs, empty/full legal spills, wrong gas/fuel,
and ordered code/stack/buffer/account observations. The minimum wraps in the
native body while the existing Scalar guard returns the overflow payload and
the source evaluator fails. Native execution of that guard and panic path is
not proved here. Independent finder and skeptic reviews found no defect.
This body sequence establishes no compiler/frame origin, Osaka approval or
account/world/transaction closure; full opcode obligations remain open.


### Typed source result of the negation body

[NegationSourceConsumer.lean](../../Bridge/SolidityBridge/RoadmapV15/P10/NegationSourceConsumer.lean)
derives the negative operand's intrinsic range for every non-minimum signed
input, calculates the actual `UnOp.evalT` result, and relates its encoding to
the fetched body's output stack and continuation. The input's range is not a
source-success or execution hypothesis. The necessary non-minimum branch is
explicit; minimum source failure is proved separately. Original PC, capacity,
gas and fuel premises stay visible. This proves a result-value connection for
an explicitly constructed native body input, without compiler/frame origin or
execution of the checked guard/panic path.

[NegationSourceControls.lean](../../Bridge/SolidityBridge/RoadmapV15/P10/NegationSourceControls.lean)
provides signed, zero and maximum typed values, an ordered populated native
client, and the minimum's simultaneous source failure/native body success.
Finder and skeptic reviews prompted a direct populated application of the new
combined producer; this was added while retaining the expected observations.
Independent read-only reviews cover the branch boundary
and absence of a desired-execution premise. Broader correspondence remains open.


### General fetched equality consumer

[EqualityConsumer.lean](../../Bridge/SolidityBridge/RoadmapV15/P10/EqualityConsumer.lean)
generalizes earlier fixed-entry EQ coverage to arbitrary emitted instruction
sites, supplied destination arrays, words and caller tails. The consumer proves
representation equality from the actual word constructors, then discharges the
actual decoder, cost-three gate, binary dispatcher and continuation clauses.
Input capacity and gas/fuel remain explicit. `selected_equality_agreement`
consumes the published `Scalar.scalarEq` certificate for each intrinsic primitive
type; source evaluation is not supplied as an oracle. Existing raw word bridges
and the Scalar certificate remain read-only.

[EqualityControls.lean](../../Bridge/SolidityBridge/RoadmapV15/P10/EqualityControls.lean)
checks independent full expected States, a directly applied typed signed client,
equal versus high-bit-distinct words, zero/max words, empty/maximal legal tails,
and gas/fuel/arity refusals. Ordered code, stack, return buffers, calldata,
accounts and substate are retained. Boundary words are constructed with
`BitVec.ofNat`; symbolic list lengths avoid larger recursion budgets. Finder and
skeptic reviews found no semantic defect. This is reference-model instruction
transport, not compiler/frame origin, Osaka approval or closure of a full opcode
row. The full G46/G47 obligations remain open.


### Fetched negation overflow test

[NegationTest.lean](../../Bridge/SolidityBridge/RoadmapV15/P10/NegationTest.lean)
composes the actual G25 test (`DUP1; PUSH32 minimumInt; EQ`) through three
fetched steps and X continuation. For arbitrary typed signed operands, seed
State, surrounding Backend code and caller tails, the producer derives each
code/state alignment and the remaining gas, with gas at least nine, peak
`tail.length + 3 ≤ 1024`, explicit PC fit and fuel. The destination array is
explicitly empty. The flag equation is extracted from the existing typed
Scalar test theorem, without an execution, decode or caller-frame premise.
Gas debit and retained State/memory/return buffers are separate consequences.

[NegationTestControls.lean](../../Bridge/SolidityBridge/RoadmapV15/P10/NegationTestControls.lean)
checks independent complete States for ordinary/zero inputs and the minimum's
true overflow flag. The legal boundary starts with 1022 words and peaks at
1024; the overflow control starts legally with 1023, passes DUP1, then refuses
PUSH32's attempted 1025-word peak. A general modular refusal law avoids reducing
a large concrete spill. Gas eight and fuel three remain failures. Ordered
39-byte code, operand/tail, buffers, calldata and accounts are observed.
Independent finder and skeptic reviews prompted precise capacity wording;
no semantic defect was found. Conditional branching, panic execution,
compiler/frame origin, Osaka approval and full G46/G47 closure remain open.
