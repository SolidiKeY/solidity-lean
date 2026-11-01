# Inline assembly (Yul): proposed extension

Status (2026-10-31): **proposal, not started.** `inlineAssembly` is an approved
exclusion ([G00 Q1](../solidity-scope.md#user-decisions-2026-10-29)); only the
whole-buffer rethrow `assembly { revert(add(data,32), mload(data)) }` is
recognized (`canonicalRethrow`, `memoryRethrow?` in
`Solidity/Frontend/SolcJson/Body.lean`). This document plans the groups and
lanes that would cover inline assembly. **No lane starts before the user
answers the [decisions](#decisions-needed-before-any-lane) and they are recorded
in [solidity-scope.md](../solidity-scope.md).** A worker must not reopen an
exclusion or change a manifest status on its own.

Pinned references (solc 0.8.38, commit `1835d247de183f23e7b0e2bc4a50732af525b77c`):
`docs/assembly.rst`, `docs/yul.rst`, `docs/internals/layout_in_storage.rst`,
`docs/internals/layout_in_memory.rst`, the Yul rules of
`docs/grammar/SolidityParser.g4` (from line 520), `libyul/AsmAnalysis.cpp`,
`libsolidity/analysis/ReferencesResolver.cpp` and the
`test/libsolidity/semanticTests/inlineAssembly/` corpus
([solidity-upstream-tests.md](../solidity-upstream-tests.md)).

## What exists

- `Solidity/Backend/Opcode.lean`: the full Osaka opcode set, byte encoder and
  decoder, jump-destination analysis and vectors
  ([backend-assembler.md](backend-assembler.md)).
- `Solidity/Evm/Machine.lean`: the compiler's target machine, 46 instructions
  with word-cell memory (G06 disagreement D2).
- `Solidity/Storage/Hashed*.lean`: the hashed storage layout and its
  separation ([storage-hashed-layout.md](storage-hashed-layout.md)); value
  representation, widths and packing remain (G27.05).
- `Solidity/Source/State.lean`: logical source state (S04), storage typed by its
  layout, logical transient roots ([transient-storage.md](transient-storage.md)).
- `Solidity/Evm/Signed.lean`, `Solidity/Evm/Exp.lean`: word arithmetic.
- `Bridge/SolidityBridge/ExternalEvm/`: projected opcode agreements with
  EVMYulLean (M6 in [roadmap-g06-evm.md](roadmap-g06-evm.md)).
- SolKey has no assembly support: no taclet exists to mirror.

## Exclusions it reopens

Yul builtins reach most of the 30 approved exclusions in
`docs/solidity-features.json`:

| Builtins | Excluded rows | Tier |
|---|---|---|
| `mload`, `mstore`, `mstore8`, `mcopy`, free-memory pointer | `memoryLayout` | B |
| `sload`, `sstore`, `x.slot`, `x.offset` | `storageLayout` | B |
| `tload`, `tstore` | `transientLayout` | B |
| `calldataload`, `calldatasize`, `calldatacopy` | `rawCalldata` | B |
| `returndatasize`, `returndatacopy` | `rawReturndata` | C |
| `call`, `staticcall`, `delegatecall` | `lowLevelCall`, `lowLevelStaticcall`, `delegatecall` | C |
| `create`, `create2`, `selfdestruct`, `extcodesize`, `extcodecopy`, `extcodehash` | `create2Salt`, `selfdestruct`, `addressCode`, `addressCodehash` | C |
| `log0`–`log4` | `eventLog` | C |
| `coinbase`, `number`, `timestamp`, `prevrandao`, `gaslimit`, `chainid`, `basefee`, `blobbasefee`, `blockhash`, `blobhash`, `origin`, `gasprice` | the 13 block/tx rows | B |
| `gas`, `msize`, `pc`, own `codesize`/`codecopy` | `gasleft`, `machineResources` | stays excluded |

The last row returns values that depend on how the program was compiled, so it
has no compiler-independent source meaning (and contradicts G06 decision D6:
gas is a resource, never an observation). Admission refuses an assembly block
that uses one of them, with a precise reason.

## Tiers

- **Tier A — words only.** Yul control flow, functions and the pure builtins
  (`add` … `clz`, `byte`, `signextend`, `addmod`, `mulmod`, `exp`) over Yul
  locals and Solidity value-type locals. Covers `mulDiv`-style helpers. Needs
  only the `inlineAssembly` row reopened for this subset.
- **Tier B — physical state.** Adds storage, transient, memory, calldata,
  `keccak256` and environment reads. The source state gains physical views of
  its logical state.
- **Tier C — full Yul** minus the compiler-dependent row: raw calls,
  creation, logs, returndata, `selfdestruct`.

## Design constraints

- **Intrinsic.** The Yul AST is typed: variables are indexed by their scope
  context, functions by their argument and result counts, so out-of-scope
  references and arity errors are unrepresentable. No untyped intermediate
  layer ([intrinsic.md](../intrinsic.md), Gate G0). Yul has one type (`u256`),
  so a Yul value is the existing EVM word type.
- **Core stays dependency-free.** EVMYulLean agreement only in `Bridge/`.
- **Physical views are derived, not stored.** The logical state remains the
  source state. A physical view (slot map, byte memory) is a function of it
  through the documented layout, plus a residual part for locations outside
  every logical region (an assembly block can write a slot no declaration
  owns and read it back later). Writeback decodes the view back into logical
  state. Adding the residual part changes the state type: run Gate G0 and
  check `git log` for speed-motivated state changes first.
- **The source layout follows solc's documentation**, not the compiler of this
  repository. The compiler groups (G27, G32) then prove their representation
  agrees with it. So Y04/Y05 must be integrated before lanes V10/V11 start,
  or those lanes take Y04/Y05's layout definitions as an input obligation.
- **Notation.** Rules use `dl{ … }` / `tm{ … }` with printers. Every Yul rule
  gets a row in [lean-key-rule-map.md](../lean-key-rule-map.md) marked as a
  Lean-only extension without a SolKey taclet (decision YQ5).

## Groups

Each group follows the [VM execution contract](../coverage-plan.md#vm-execution-contract):
code, kernel-checked proofs, inhabited witnesses, negative controls,
combination regressions, finder/skeptic review, handoff in this document.

| Group | Deliverable | Depends on |
|---|---|---|
| Y01 | **Yul syntax and admission.** Intrinsic Yul AST (`Solidity/Yul/Syntax.lean`); import of solc JSON `InlineAssembly` (`AST`, `externalReferences`, `flags`, the `memory-safe-assembly` doc comment) in `Solidity/Frontend/SolcJson/Yul.lean`; builtin table pinned to Osaka and solc 0.8.38; admission per tier with precise refusals, including the compiler-dependent builtins; `canonicalRethrow` becomes an instance, not a special case. Checked Yul parsing over the G08–G11 lexer is child Y01.02. | S00, existing SolcJson frontend |
| Y02 | **Yul static semantics.** Scoping (functions visible in their whole block, no shadowing, function bodies see no outer variables), `leave`/`break`/`continue` placement, literal ranges; external references: value-type locals, `x.slot`/`x.offset` of storage references, `x.offset`/`x.length` of calldata, memory variables as pointers, `f.selector`/`f.address`. Checker sound and complete against the typing relation; solc's error tests as refusal controls. | Y01, S01 |
| Y03 | **Word semantics.** Statements, functions and pure builtins over words with EVM results (`div`/`mod` by zero is `0`, no Panic); fuelled divergence matching S03's horizons; embedding into S02/S03 statements. Solidity locals written from assembly with dirty high bits follow decision YQ4. | Y02, S02, S03 |
| Y04 | **Storage and transient views.** Physical slot map of persistent and transient storage from `Solidity/Storage/HashedLayout.lean` plus value packing and widths (the source half of G27.01–G27.05); residual slots; writeback; `sload`/`sstore`/`tload`/`tstore` with reset at transaction end and frame rollback (EIP-1153). Laws: decode∘encode = id; writeback of an unchanged view is the identity. | Y03, S04 |
| Y05 | **Memory view.** Byte memory from the documented memory layout (scratch `0x00`–`0x3f`, free-memory pointer `0x40`, zero slot `0x60`, length-prefixed arrays, word-per-member structs); `mload`/`mstore`/`mstore8`/`mcopy`; the `memory-safe` contract; allocation addresses per decision YQ3. Laws: logical memory reads agree with the view; memory-safe blocks preserve `MemOK` (V04b). | Y03, S04, V04b `MemOK` |
| Y06 | **Inputs and hashing.** `calldataload`/`calldatasize`/`calldatacopy` over the transaction's calldata bytes; `keccak256` over memory with the approved `Fixed` hash; environment builtins as universally quantified inputs (G00 Q2), which also reopens the Solidity `block.*`/`tx.*` rows. | Y05, S04.04 |
| Y07 | **World effects.** Y07.01: `call`/`staticcall` with raw bytes to known and environment callees, `returndatasize`/`returndatacopy` (the buffer of the last source-level frame; the compiler must not issue other calls), `create`/`create2` with raw initcode and the address formula. Y07.02: `delegatecall` (known callee: its code over the caller's storage; environment callee: storage havoc), `selfdestruct` under EIP-6780, `log0`–`log4` as observations (changes G01's event type; YQ6). `callcode` refused. | Y06, G22, G42 |
| Y08 | **Compilation.** Y08.01: Yul to the compiler's instructions with stack slots for Yul variables and frames for Yul functions; correctness against G24's state relation and the Y04/Y05 views. Y08.02: EVM correspondence of the new opcodes through G45/G46 and the Bridge (B05 rows). | Y04–Y06, G24, G27, G32, G45, G46 |
| Y09 | **Calculus.** Y09.01 rules for Y03; Y09.02 rules for Y04–Y06 (slot and byte terms with `save`/`find`-style update laws); Y09.03 rules for Y07. Soundness for each, rule-map rows, printed rules. | Y03–Y07, G51 interfaces |
| Y10 | **Composition and testing.** G03 ledger rows and combinations (assembly in loops, modifiers, `try`, `unchecked`, constructors, libraries); G48–G51 coverage with no residual assembly fragment predicate; G52 differential tests against solc 0.8.38 in both pipelines over the upstream `inlineAssembly` corpus. | Y01–Y09, V16 |

## Lanes

Sized by the [sizing rules](../coverage-plan.md#sizing-rules): three or four
groups, eight to ten hours each.

| Lane | Checkpoints, in order | Starts after | Tier |
|---|---|---|---|
| VY1 | Y01, Y02, Y03, Y09.01 | YQ1–YQ5 answered; V04 integrated | A |
| VY2 | Y04, Y05, Y06, Y09.02 | VY1; before V10/V11 start | B |
| VY3 | Y08.01, Y08.02 | V12 (Y08.01), V15 (Y08.02); backfill until then | B |
| VY4 | Y07.01, Y07.02, Y09.03 | VY2, V13 (G42); YQ6 answered | C |
| VY5 | Y10 | V16, VY3, VY4 | C |

Tier A is one lane, independent of the main chain. Tier B adds two, tier C
two more. VY2's layout definitions feed V10 (G27) and V11 (G32): if those
lanes start first, add "agrees with Y04/Y05's layout" to their checkpoints.
G27, G32, G46 and G47 grow by the corresponding opcode and view obligations;
that growth is counted in VY3/VY4, not in V10–V15.

## Decisions needed before any lane

| ID | Question | Recommendation |
|---|---|---|
| YQ1 | Reopen `inlineAssembly`, and which tier? | Tier A now; tiers B and C as separate decisions after VY1. |
| YQ2 | Keep `gas`, `msize`, `pc` and own-code `codesize`/`codecopy` excluded? | Yes: refuse at admission. |
| YQ3 | Memory pointer values depend on allocation order, which differs between pipelines. Make allocation addresses nondeterministic in the source (any choice satisfying the documented layout) with the final theorem a refinement, or fix one allocation discipline? | Nondeterministic with a refinement theorem; needs a G01 contract amendment. |
| YQ4 | A Solidity `uint8` local written from assembly with dirty high bits: model the bits, clean on write, or fail? | Model them exactly as solc does in each pipeline; record any pipeline difference in [solc-alignment.md](../solc-alignment.md). |
| YQ5 | Yul rules have no SolKey taclet. Accept Lean-only rules marked in the rule map? | Yes, marked; reconsider if SolKey gains assembly. |
| YQ6 | Logs become observations (tier C): extend G01's event type for Solidity `emit` too? | Yes, both at once, or tier C keeps `log*` refused. |
| YQ7 | Non-`memory-safe` blocks? | Refuse: via-IR's stack-to-memory mover depends on the flag. |

## Handoffs

None yet. Each checkpoint appends its handoff here (revision, theorems and
premises, checks, remaining obligations).


### VY5 partial backfill handoff (2026-10-31)

The [VY5 lane record](inline-assembly-vy5.md) and
[G03 assembly extension](../../tests/yul-composition/ledger.json) record pinned
inventory/extraction, both-pipeline compiler/reference probes, combination and
negative controls, exact pending child/dependency rows and independent reviews.
Base `0b078cefaf7daad79007b87b72df64eb6936420f`; branch
`codex/solidity-inline-assembly5-20261031/vy5-composition`.
Full committed head and artifacts are in `/workspace/vy5-composition/handoff.json`.
Y10/G48–G51 concrete composition, complete G52 observations and final joint
proof closure remain pending actual V16/VY3/VY4 and other recorded inputs.
The authorization is recorded in [scope](../solidity-scope.md#inline-assembly-decisions-2026-10-31);
the older proposal status above is historical, not a revocation of YQ1–YQ7.

### VY5 reference recovery — 2026-10-31

The [lane recovery record](inline-assembly-vy5.md#reference-adapter-recovery--2026-10-31)
and [per-fixture ledger](../../tests/yul-composition/reference-recovery.json)
record repaired raw ABI vectors, ordered anonymous logs/call sequences, pinned
host inputs and exact required runtime profiles. 227 profiles match; 21 retain
old-fork incompatibilities. Separate four-way probes retain eight intended
mutant mismatches. Full Y10/G48–G51 and world/memory/source correspondence remain
pending; the existing goal stays blocked. Original checkpoint/artifacts remain
preserved; new full head, commands, reviews and checksums are in
`/workspace/vy5-composition/recovery-20261031/handoff.json`.

### VY5 state observation checkpoint — 2026-10-31

The [lane observation record](inline-assembly-vy5.md#state-and-memory-observation-checkpoint--2026-10-31)
and [coverage ledger](../../tests/yul-composition/observation-coverage.json)
record public-API touched-account/slot worlds, frame memory and last-call buffers.
Four source-bound controlled fixtures match16 state-oracle profiles; the227
upstream byte/log matches retain pending independent state comparisons and21
older-fork blocks. Source/correspondence and Y10/G48–G51 proofs remain pending.
Original checkpoints/artifacts are preserved; new full committed identity,
commands, reviews and checksums are in
`/workspace/vy5-composition/observations-20261031/handoff.json`.

### VY5 finite state oracles — 2026-10-31

The [finite-oracle lane record](inline-assembly-vy5.md#finite-state-oracles--2026-10-31)
and [coverage ledger](../../tests/yul-composition/observation-coverage.json)
record seven independently specified local fixtures (28 profile matches) and
five pinned upstream fixtures (15 profile/30 call matches). CREATE identities are
predicted from nonce inputs; log windows and failed deployment use explicit
frame/phase/runCall boundaries. The227 byte/log matches,21 older-fork blocks and
eight intended mutants remain. Unselected state expectations and all concrete
Y10/G48–G51 proof obligations stay pending. New committed identities/artifacts:
`/workspace/vy5-composition/oracles-20261031/handoff.json`; earlier manifests remain
preserved and the existing goal remains blocked.

### VY5 physical and ordered-state backfill — 2026-10-31

The [lane backfill record](inline-assembly-vy5.md#physical-and-ordered-state-backfill--2026-10-31)
and [coverage ledger](../../tests/yul-composition/observation-coverage.json)
record source-derived storage pointers, MCOPY, ordered transient/cleanup and
additional control/calldata assertions.39 upstream sources cover121 runtime
profiles/275 calls;106 working profiles remain unselected, and CREATE2 target/
deferred cleanup domains stay explicit.227 byte/log matches,21 fork blocks and
eight intended mutants are unchanged. Published-master owner exports were read
without integration; all concrete Y10/G48–G51 proofs remain pending. New committed
identities/artifacts: `/workspace/vy5-composition/physical-20261031/handoff.json`.
Earlier artifacts are preserved and the original goal remains blocked.

### VY5 remaining finite-oracle backfill — 2026-10-31

From ec708bf11d7fd6f0b5abf521d9fab58b4d47bf1a, the
[VY5 handoff](inline-assembly-vy5.md#remaining-finite-oracle-backfill--2026-10-31)
adds source-derived finite assertions for the remaining34 working sources:
all73 working sources/227 profiles/458 calls now have selected assertions;
21 older-fork profiles remain blocked. Original ordered observations/settings
are unchanged. CREATE2 checks use independently predicted right-padded bytes32
salts and compiler-receipted initcode/runtime; five separate host beginFrame
cleanup records preserve the runCall versus runTx distinction. Neither proves
whole-world or source/target correspondence.183 JS+2 Python tests and final
pinned reference/integrated checks passed; the initial wrong-salt oracle exit1
is retained. Independent finder/skeptic reviews and versioned artifacts reside
at `/workspace/vy5-composition/remaining-20261031/`. Work2/BackfillA/B remain
partial, Work1/3 blocked: all24 proof obligations/six combinations and final
Y10/G48–G51 closure await actual assembly owner interfaces. No Lean/import or
shared owner code changed; prior kernel gates retain their original tested-tree
attribution and historical docs/G03 exit1 failures are preserved.


### VY5 parallel interface — 2026-11-01

The [VY5 consumer interface](inline-assembly-vy5.md#parallel-consumer-interface--2026-11-01)
uses hash-verified VY3/VY4 bodies in a private dependency worktree. Concrete
rollback/window/materialization and numeric ADD laws plus inhabited controls
pass affected kernel/MCP checks. These are supplied-completion and target-only
laws, not source try/catch, RETURNDATACOPY lowering or full EVM adequacy.
All24 obligations/six combinations stay pending; the early package permits
parallel consumers without duplicating producer semantics.


### VY5 parallel concrete components — 2026-11-01

The [VY5 concrete handoff](inline-assembly-vy5.md#parallel-concrete-components--2026-11-01)
adds actual target repetition, computed outer-slot transport and lossless
world/target word adapters;13 component facts are registered without closing
any of24full obligations/six source combinations. Actual peer VY3/VY4 modules
and compatible V16 certificate interfaces are checked in a private joint tree.
KeySort2jobs, library1005jobs, TestSuite262jobs, annotations, per-file MCP and
strict/trust checks pass.192JS+2Python, four pinned component profiles and exact
encoded target pass; original227byte/log matches,21fork blocks and eight intended
mutants remain intact. Concrete source/world/compiler adequacy still needs
specific producer inputs; neither generic V16 laws nor finite external tests
replace those proofs. New artifacts are versioned under
`/workspace/vy5-composition/parallel-20261101/final/`.


### VY5 actual physical/source consumer — 2026-11-01

Verified VY2 checkpoint2bb7bb20852e986f81a44aaaadfda104cac9c3f4 now feeds four
consumer modules with26named kernel laws: actual represented source writes,
three-journal child-success/outer rollback, physical/returndata/target byte
copying and typed heap-byte image agreement over valid placements. Private
validated tree a3b983b7abafbf299a0b2ac4452a55c849d6e37b passes KeySort/fullpolicy/
TestSuite/import closure/scoped axiom checks; trust invocation failures are
retained and the exact-inventory trust retry passes.247JS+2Python and32ordered
calls across4pinned compiler profiles pass. Read-only finder/skeptic findings
were fixed and rereviewed. All24full obligations/sixsource combinations remain
pending; physical-world journals/logs, dirty locals, allocation/G01 and actual
compiler/world/V16 assembly certificates still need concrete producer facts.
See [lane handoff](inline-assembly-vy5.md#actual-physicalsource-consumer-checkpoint--2026-11-01).
New artifacts: `/workspace/vy5-composition/physical-source-20261101/final/`.


### VY5 actual raw-local/physical/scoped-loop consumer — 2026-11-01

Sealed VY1 c7b128fd10df2fa51929cb68bdba020cf2ca07a5 now feeds the existing actual
VY2/VY3/VY4/V16 private tree.43new kernel laws cover halt-preserving physical-first
raw-local execution, dirty/two-Fn/nonword/source preservation, coupled rollback
transport, typed heap/target byte agreement and concrete scoped Yul loops.
Private validated head c6c529aaa6075488ff84b8606af508432dd50053 passes full kernel/
import/TestSuite/strict gates and43scoped axiom reports. The initial six-site trust
audit failure is retained; independently reviewed private-only ordinary .admit
method registrations make the unchanged checker pass.328JS+2Python and4profiles/
20native calls pass unchanged expectations. All24full obligations/six Source
combinations remain open: no raw ordinary-Source resume, full loop/compiler/world
adequacy, log conversion or G01 refinement is inferred. See the
[lane handoff](inline-assembly-vy5.md#actual-raw-local--physical--scoped-loop-consumer--2026-11-01).
Fresh sealed artifacts: `/workspace/vy5-composition/dirty-source-20261101/final/`.


### VY5 scoped function/loop component — 2026-11-01

Using only already-staged inputs, FunctionPhysical adds26actual kernel laws for
normal return, nested calls/leave from a scoped Yul loop, arity/refusal controls,
full physical result/two-journal retention and heap/nonword/raw/source agreement.
Raw uint8 results1793/1025/0 distinguish normal/wrong-callee/missing-leave cases.
Four pinned compiler profiles pass28orderedcalls;410JS+2Python, full private
1222-job library/262-job TestSuite/KeySort and scoped axiom/trust gates pass.
Private validated head cb325c26a3c9be45f41506d23fe60555369ace92 preserves all
previous checkpoints. All24full obligations/six Source combinations, full
Source/compiler/world/G01 closure and the two VY1 compiler-expectation questions
remain open. No new producer retrieval or goal change occurred. See
[lane handoff](inline-assembly-vy5.md#scoped-functionloop-composition--2026-11-01).
Artifacts: `/workspace/vy5-composition/function-source-20261101/final/`.

### VY5 recursive component handoff — 2026-11-01

VY5 adds an actual scoped self-call after the represented physical action, with
18kernel laws, inhabited32horizon/raw1025 result, bounded missing-decrement
control, full physical/journal/heap-window preservation and4finite native
profiles/24orderedcalls. Existing28call function evidence remains unchanged.
Reviewed parent-provenance omission is fixed and mutation-tested. Joint
KeySort/build/TestSuite/strict/trust gates pass;492JS+2Python pass.
All24full obligations/sixSource combinations and missing producer adequacy remain
open; no goal status change. See [lane details](inline-assembly-vy5.md#genuine-recursive-physical-composition--2026-11-01) and immutable artifacts
at `/workspace/vy5-composition/recursive-source-20261101/final/`.

### VY5 raw-local catch transport handoff — 2026-11-01

VY5 adds26kernel laws for actual completed raw caller-prefix continuation across
coupled physical rollback and exact supplied failure-byte copying. The separate
finite Solidity try/catch control passes4profiles/32orderedcalls, preserving
caller prefixes and observing reverted persistent/transient/log/frame effects.
586JS+2Python and joint KeySort/build/TestSuite/strict/trust/axiom gates pass.
Raw locals remain a companion to the actual old EMState physical carrier; this
is not general Source try/catch dispatch or full physical/world adequacy.
All24full obligations/sixSource combinations stay pending; see
[lane detail](inline-assembly-vy5.md#raw-local-catchrollback-transport--2026-11-01).
Versioned evidence is at `/workspace/vy5-composition/raw-catch-20261101/final/`.

### VY5 scoped functions after raw catch — 2026-11-01

VY5 directly consumes actual raw catch state in existing scoped function bodies,
without initialization/clean conversion.24new component laws include arbitrary
input/all-horizon transport and actual1793/1537/poison0/reset513 controls.
Four pinned native profiles pass40orderedcalls;690JS+2Python and joint
KeySort/build/TestSuite/strict/trust/scoped-axiom gates pass. All24 ORIGINAL
full obligations/sixSource combinations remain pending; no new source dispatch
or final adequacy is inferred. See [lane details](inline-assembly-vy5.md#scoped-functions-after-raw-catch--2026-11-01)
and versioned artifacts `/workspace/vy5-composition/catch-function-20261101/final/`.
