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


### VY2 preparation handoff (2026-10-31)

On `codex/solidity-inline-assembly5-20261031/vy2-physical` from exact base
`0b078cefaf7daad79007b87b72df64eb6936420f`,
[VY2](inline-assembly-vy2.md) adds dependency-free intrinsic physical-view
preparation under `Solidity/Yul/Views/`: packed-field read/update/frame/width
laws, typed canonical codecs and residual reconstruction, byte/word/copy
operations with both word roundtrips, raw calldata/fixed hash/environment
inputs, allocation and actual V04b MemOK extension obligations, and inhabited
negative/combination/source-reset/rollback controls. YQ1–YQ7 approval is recorded
in scope; no frontend or manifest exclusion is reopened.

This is partial backfill, not Y04/Y05/Y06/Y09.02 completion. VY1 is absent;
full typed source packing/writeback, dirty owned bits, residual journaling,
V10/V11 agreement instances, memory-safe MemOK preservation, allocation's final
refinement/adequacy, source builtin/row integration, notation/printers and
statement soundness remain open. Separate finder/skeptic findings and checks
are in the lane record. Committed revision, exact commands/outcomes/resources,
raw failures, patch/bundle and checksum paths are in
`/workspace/vy2-evidence/HANDOFF.md` on this VM.


### VY2 canonical scalar codec handoff (2026-10-31)

The lane's next preparation checkpoint adds concrete integer/fixed/address/
contract/enum/UDVT/bytesN/external-function canonical codecs over Source.Val,
proves their inverses and connects them to typed byte/residual regions. Signed
bounds, enum refusals, packing combinations and residual controls are inhabited.
Pinned solc raw-storage witnesses pass both pipelines. Final full gate passes
999/262 jobs and131 sort annotations; audit covers222 declarations/109 theorems.
Separate finder/skeptic reviews report no confirmed findings.
See [VY2](inline-assembly-vy2.md) for exact premises, evidence and remaining
full-lane dependencies; no admission row or whole-layout instance is claimed.
Full committed revision/patch/bundle/checksums remain in the VM handoff.


### VY2 aggregate and raw-fixture handoff (2026-10-31)

Further Backfill A constructs flat scalar fixed-array/heterogeneous-struct codecs
over actual Data/DataList, computes documented storage packing, and proves typed
roundtrip, extent/separation, unchanged and residual/padding preservation through
actual Word slot maps. Inhabited multi-slot controls and pinned compiler goldens
agree. A closed four-fixture raw adapter retains13 calls and4 deployments per
pipeline, fixes the previous raw-vector/host overclassification failures, and
passes81 fail-closed controls. Original failing records remain preserved.
Finder/skeptic findings (indexed match and unsupported storage-root observation)
were fixed and independently reviewed. Exact premises, proof/external boundaries,
remaining full Y04–Y09.02 dependencies and cumulative artifact paths are in
[VY2](inline-assembly-vy2.md) and `/workspace/vy2-evidence/HANDOFF.md`.


### VY2 disjoint and fixed nested handoff (2026-10-31)

The next [VY2](inline-assembly-vy2.md) checkpoint proves disjoint composition of
existing encoders and constructs two fixed nested forms over actual Source.Data/
DataList: struct with fixed scalar array plus struct, and fixed array of
heterogeneous structs. Real next-slot alignment/bounds, actual outputs, exact
residual and unchanged-view proofs are retained. Full5/7-word computational
goldens and pinned solc observations agree; prior ordered fixtures/81 controls
remain passing. Kernel audit407/213 and wrapper1007/262+131 pass.
Independent reviews found no remaining confirmed finding after documentation
fixes. This is bounded canonical Backfill A, not full Y04–Y09.02 completion;
source/MemOK/dirty/journal/compiler/allocator/calculus dependencies remain open.
Cumulative revision, evidence, prior-artifact preservation and checksum paths:
`/workspace/vy2-evidence/HANDOFF.md`.

### VY2 canonical scalar writeback handoff (2026-10-31)

[VY2](inline-assembly-vy2.md) now constructs a bounded singleton physical writeback
over actual Source.Storage and actual account/transient operations. Original-cell
administrative identity, unrelated paths, residual bytes and actual source-frame
controls are proved/tested. Canonical preparation does not model dirty values;
raw bool2 remains observable in both pinned pipelines. Nine additional ordered
observations,14 fail-closed controls, original fixtures/81 controls,489/260 axiom
reports and wrapper1010/262+131 pass after independent reviews. This is Backfill
progress, not full Y04–Y09.02 closure; raw residual journaling and source/heap/
MemOK/allocator/compiler/calculus integration remain open. Cumulative evidence:
`/workspace/vy2-evidence/HANDOFF.md`.

### VY2 fixed-domain residual journal handoff (2026-10-31)

[VY2](inline-assembly-vy2.md) constructs an intrinsically unowned-slot journal
beside actual typed Source state/frames. Actual source operations and residual
old-word undo compose through nested rollback, outer revert after child commit
and persistent/transient reset, with nontrivial controls. Fixed ownership is an
input, not whole-store coverage; owned dirty/padding bits and dynamic paths/Yul
integration remain open. Both pinned pipelines pass five new ordered state-rich
calls and33 negative controls after independent review fixes. Existing fixtures,
writeback vectors and budgets preserved. Kernel544/287 and wrapper1012/262+131
pass. Full Y04–Y09.02 and Backfills A/B stay unfinished; goal blocked unchanged.
Exact committed head and cumulative/versioned artifacts: `/workspace/vy2-evidence/HANDOFF.md`.

### VY2 finite-path writeback handoff (2026-10-31)

[VY2](inline-assembly-vy2.md) constructs finite heterogeneous canonical writeback
into actual Source.Storage, with real pairwise path/physical separation and
constructed finite agreement instance. Encoded views, unchanged administrative
identity, reconstruction/residual laws, permutation and actual source batches
are proved. Residual keys now derive from the same fixed registrations; combined
actual source/residual frames are controlled. Finite ownership is not whole-store
coverage or dirty/heap/Yul integration. New ten-call pinned fixture and55 negative
controls pass both pipelines; existing fixtures/controls preserved.659/348 scoped
signatures/axioms and wrapper1017/262+131 pass after independent read-only reviews.
Y04/Y05/Y06/Backfills A/B stay partial, concrete Y09.02 blocked and goal unchanged.
Exact revisions, raw gate failures/comparisons and cumulative/versioned artifacts:
`/workspace/vy2-evidence/HANDOFF.md`.

### VY2 actual selected heap-object handoff (2026-10-31)

[VY2](inline-assembly-vy2.md) constructs ordinary allocated bytes/string physical
writeback into actual Source.Heap, exact whole-heap identity and unchanged types/
next/bounds/other cells, original Placement transport and nonoverlap/residual/
reserved laws. It proves ACTUAL owner Source.MemOK transport for selected steps,
with inhabited source states and real reads through bytes/string alias locals.
Same-header-length preparation is not full heap/Y05 support: raw header growth
succeeds in both compiler pipelines and remains explicitly open in this model.
New ten-call exact-byte fixture and89 negatives pass, all previous observations/
controls preserved.768/413 signatures/axioms and wrapper1024/262+131 pass after
independent reviews/fixes. Full Y04/Y05/Y06/Backfills A/B stay partial, concrete
Y09.02 and original goal blocked. Exact heads/gates/limitations/versioned artifacts:
`/workspace/vy2-evidence/HANDOFF.md`.

### VY2 bounded heap-resize handoff (2026-10-31)

[VY2](inline-assembly-vy2.md) adds separate footprint-bounded bytes/string resizing
into actual Source.Heap, preserving the fixed API and proving old-domain
compatibility. Actual output Placement updates selected shape, retaining
addresses/free/other objects and deriving bounds/separation; real MemOK, aliases,
shrink-tail and two-object composition are proved/controlled. Historical capacity
and larger growth remain open, not refusals. Twelve new exact22-word observations
and103 negatives pass both pipelines; all old fixtures/controls unchanged.
859/470 signatures/axioms and wrapper1029/262+131 pass after independent reviews.
Entire Y04/Y05/Y06/Backfills A/B stay partial, Y09.02 and goal blocked unchanged.
Exact revisions/gates/full obligations/versioned artifacts: `/workspace/vy2-evidence/HANDOFF.md`.


### VY2 retained-allocation handoff (2026-10-31)

Constructive selected-object retained-allocation lineage now preserves original
real Placement extents across bytes/string shrink-to-zero and regrowth, with
exact current shapes, full-region separation, actual owner MemOK and logical/
physical two-order laws. Fixed/bounded APIs and original counter-control remain.
See [VY2 checkpoint](inline-assembly-vy2.md#retained-ordinary-allocation-checkpoint-2026-10-31)
and `/workspace/vy2-evidence/retained-allocation/HANDOFF.md` for full committed
revision, premises, reviews and gates. Initial allocator provenance, whole-store/
heap/assembly/source/compiler/calculus/refinement closure remain open. Y04–Y06
partial, Y09.02 blocked, both backfills unfinished; no admission promotion.


### VY2 supported byte-heap view handoff (2026-10-31)

Continued original backfill constructs finite ordinary bytes/string whole-
supported-heap views from actual Heap.get witnesses and valid Placement, with
exact typed layout reads/reserved/residual/unchanged laws. Real three-object and
retained-regrowth controls are inhabited. An actual owner-MemOK oversized object
provably lacks ordinary Placement; no obligation signature or scope changed.
See [VY2 realization](inline-assembly-vy2.md#constructive-supported-byte-heap-realization-2026-10-31)
and `/workspace/vy2-evidence/heap-realization/HANDOFF.md`. Universal realization,
source/assembly/allocator/compiler/calculus closure and full VY2 remain open.


### VY2 mixed ordinary aggregate view handoff (2026-10-31)

New intrinsic constructor witnesses serialize actual scalar/pointer struct and
static/dynamic array members alongside bytes/string images. Real child typing,
placement-derived bounds, supported covered-heap source layout reads, actual
owner invariants and six-object alias controls are constructive. Both pipelines
compare complete pointer/header/alias/ABI observations with157negative controls;
initial broken fixture evidence preserved. See [lane checkpoint](inline-assembly-vy2.md#mixed-ordinary-aggregatepointer-views-2026-10-31)
and `/workspace/vy2-evidence/mixed-heap/HANDOFF.md`. Universal realization,
writeback/allocation/source/compiler/calculus closure and full VY2 remain open.


### VY2 selected word writeback handoff (2026-10-31)

Continued after mixed-view checkpoint: concrete full-width static uint256 array
decode/writeback and ownership-based pointer decoder composed with actual typed
Source.writeLoc, all-initial-H owner MemOK, unchanged and concrete physical/source
two-order controls. Isolated pinned fixture checks both combinations/maxword/
revert/fresh with149negative controls. See [lane record](inline-assembly-vy2.md#concrete-selected-array-and-pointer-writeback-2026-10-31)
and `/workspace/vy2-evidence/static-uint/HANDOFF.md`. Selected support is not
universal whole-memory/dirty/shared-zero/source/compiler/calculus closure;
full VY2 and both backfills remain unfinished, goal blocked unchanged.


### VY2 dynamic uint256 writeback handoff (2026-10-31)

Concrete fixed-length and retained-original-extent dynamic array writeback,
actual current Placement/all-H MemOK, exact residual/tails and source alias
controls, plus18ordered pinned pipeline calls/153negative controls. See
[lane record](inline-assembly-vy2.md#dynamic-full-width-array-writeback-2026-10-31)
and `/workspace/vy2-evidence/dynamic-uint/HANDOFF.md`. Full lane/both backfills
remain unfinished, including simultaneous general aggregate/source integration;
this component does not promote admission or replace full obligations.


### VY2 simultaneous struct writeback handoff (2026-10-31)

Constructive actual declared DataList member decoding, whole-state unchanged,
actual heapPut full Except/state/all-initial-H MemOK and Placement/residual laws;
canonical bool/fulluint/real owned pointers, including shared children. See
[lane record](inline-assembly-vy2.md#simultaneous-heterogeneous-struct-writeback-2026-10-31)
and `/workspace/vy2-evidence/aggregate-writeback/HANDOFF.md`. Both pinned pipelines
retain all prior214calls and add12/153negative controls. Full lane/both backfills
remain unfinished; no admission, full writeback or source/compiler/calculus
closure follows from these supported components.


### VY2 canonical array-family handoff (2026-10-31)

Actual fixed/header-preserving bool/u256/owned-reference array decode/writeback,
complete Source.heapPut result/all-H MemOK, unchanged state/placement/residual
laws and alias controls. See [lane record](inline-assembly-vy2.md#canonical-array-element-families-2026-10-31)
and `/workspace/vy2-evidence/member-arrays/HANDOFF.md`. Pinned pipelines add12calls
and183strict negatives, retain all previous226fields/calls. Full lane/both
backfills remain unfinished, including retained-capacity/general memory/source/
compiler/calculus closure; no admission promotion or original obligation change.


### VY2 retained array-family handoff (2026-10-31)

Constructive actual retained-capacity canonical array resizing, output current
Placement/history, complete source heapPut/all-H MemOK and bool/reference
shrink/regrow/alias/tail controls. [Lane record](inline-assembly-vy2.md#retained-array-element-family-resizing-2026-10-31),
`/workspace/vy2-evidence/retained-members/HANDOFF.md`. Both pinned pipelines add
16orderedcalls/195negatives; every prior238reportfield/call unchanged. Full lane/
both backfills remain unfinished; no admission/universal writeback/allocator/
source/compiler/calculus closure inferred.


### VY2 canonical scalar-memory handoff (2026-10-31)

Pinned pre-proof audit establishes canonical signed/width/address/bytesN memory
alignment against actual Source.Val.word. Constructive inverse/RefOK and parallel
canonical array/struct/retained adapters reuse actual Heap/Placement/owner MemOK,
keeping all old decoder APIs untouched. [Lane record](inline-assembly-vy2.md#canonical-scalar-memory-extension-2026-10-31),
`/workspace/vy2-evidence/memory-scalars/HANDOFF.md`. Both pipelines preserve all
prior254calls and add28/99+155negative controls. Full lane remains unfinished;
no dirty cleanup, new admission exclusion or compiler/source adequacy inferred.


### VY2 canonical compatibility/alias handoff (2026-10-31)

Exact old-domain all-raw decoder/heap/state API equality and genuine typed source/
external aliases with complete Panic bytes. [Lane record](inline-assembly-vy2.md#canonical-compatibility-and-genuine-aliases-2026-10-31),
`/workspace/vy2-evidence/canonical-aliases/HANDOFF.md`. Both pipelines add14calls/
137negatives, all preceding282fields/calls unchanged. This follows the canonical
scalar checkpoint, not full VY2 completion or Yul/compiler correspondence.


### VY2 joint ordinary-memory preparation handoff

See [lane checkpoint](inline-assembly-vy2.md#joint-ordinary-memory-writeback-2026-10-31).
New lane modules construct joint struct/array source writeback, all-raw candidate
transport, complete-result order/error laws, exact raw re-encode and retained
placement/history; actual source controls and pinned both-pipeline alias fixtures
remain distinct evidence. Original Y04–Y06/backfills partial, Y09.02/source/
compiler/calculus closure blocked. No admission promotion or goal transition.
Full SHAs/commands/checksums: `/workspace/vy2-evidence/joint-memory/HANDOFF.md`.


### VY2 finite owned-inventory preparation handoff

See [lane checkpoint](inline-assembly-vy2.md#finite-owned-memory-inventory-2026-11-01).
Constructive arbitrary finite canonical inventory codecs, actual source writes,
per-step placement/history/candidate closure, exact sequential/unchanged/raw-view
and distinct-ID permutation laws; inhabited multi-root/alias/late-error/retained
controls and separate pinned reference evidence. Original full lane/goal remains
partial/blocked, no admission promotion. Exact SHAs/artifacts/commands at
`/workspace/vy2-evidence/owned-inventory/HANDOFF.md`.


### VY2 computed heap-inventory preparation handoff

The [VY2 lane record](inline-assembly-vy2.md#computed-ordinary-heap-inventory-2026-11-01) now constructs intrinsic images and finite inventory directly from actual Heap.next/get and valid Placement, deriving complete coverage/unique IDs and exact sparse/unsupported accounting. Actual owner MemOK plus explicit canonical declared-family support derives preparation without supplied images or completeness laws. Generated inventories feed existing real source writeback, retained placement/history, raw reads, unchanged state and every-H preservation. Full lane, allocator refinement, broader representations and producer/compiler/calculus closure remain open; no admission promotion. Versioned evidence: `/workspace/vy2-evidence/heap-enumeration`.
