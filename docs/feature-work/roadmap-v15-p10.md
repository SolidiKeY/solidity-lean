# V15 P10: fetched-byte execution steps against EvmYul

Partial checkpoint of roadmap item V15 (EVM agreement), producer P10: single
fetched EVM steps over Backend-emitted code, checked against the pinned
EvmYul reference (`Bridge/vendor/EvmYul`). All modules live in
`Bridge/SolidityBridge/RoadmapV15/P10/`; nothing in the core changed. Every
theorem is proved; there is no `sorry`, no new axiom, and the printed axiom
sets are subsets of `propext`, `Classical.choice`, `Quot.sound`.

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
- RETURNDATACOPY uses the reference byte-memory operation; no physical
  padding (`PaddingCorrect`) witness is supplied.
- Open: compiler/source origin of sites, G45.03 execution meaning, Osaka
  agreement, resource abstraction, and source/ABI/world/account/transaction/
  trace closure; the full per-opcode rows remain open.

## Master integration review

Merged from producer head 515ac91d over master eba99fe7. Read-only finder and
skeptic reviews confirmed: no `sorry`/axiom/heartbeat changes, all imports and
module-map paths exist, core untouched. Fixed on merge: the producer's ten
per-step notes (VM paths, run logs, coordinator text) were replaced by this
page; the frozen-interface docstring now says its fields are discharged by
`FrozenV1.api` from existing theorems; `api` is a `theorem`; module-map rows
for `Site`, BALANCE and the frozen modules were made precise. Left out: the
producer's VM job-runner script, its test and its runtime-completion note. Noted, not changed: per-opcode `opcode_at`
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

A fixed-PC, fixed-gas predecessor stayed on the lane and is not on master.
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

`EnvironmentTasksV1.lean` was generated on the lane from a specification; the
generator and specification are not on master. It contains claim types only. `OriginClaim`, `GasPriceClaim` and `ChainIdClaim` describe
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
and the remaining full-lane boundaries stay visible.

## Unsigned quotient and remainder at arbitrary emitted sites

`UnsignedDivisionConsumer.lean` proves `div_agreement` and `mod_agreement`
for any emitted site, arbitrary represented operands and spill, adequate gas
(at least 5), explicit stack capacity and positive driver fuel. Both results
retain exact Scalar output, complete charged target State and actual X
continuation. Public word equations expose the unsigned zero-divisor policy;
`div_capacity_refusal` derives actual overflow from the gate after gas and
operand checks, without assuming a refused storage or state frame.

A fixed-site predecessor (PC 0, single-byte code, gas 5) stayed on the lane
and is not on master. This checkpoint covers arbitrary encoded
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

## Integration record (lane head 606729a8)

Merged: the 21 modules above and their Bridge root imports. The DIV, BYTE and
SIGNEXTEND overflow refusals start from 1026 input words and EXTCODESIZE from
1025; they check the gate arithmetic on an over-limit stack that no
well-formed state reaches. Only the PC/GAS/MSIZE capacity boundary is
reachable. Left out: the
lane's bounded-capture/completion and serial-shim runner scripts and their
tests, the environment-task generator and its JSON specification, the
per-module registration scripts, its routine-task list and its
runtime-completion note. Read-only finder and skeptic reviews found no Lean
defect; stale references to lane-only predecessors and checklists were
removed from this record.

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
