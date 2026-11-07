# Inline assembly (Yul): authorized extension

Status (2026-10-31): **implementation authorized for VY1–VY5; not yet implemented.**
The human approved tiers A–C and YQ1–YQ7 in the
[decision record](../solidity-scope.md#inline-assembly-decisions-2026-10-31).
`inlineAssembly` remains excluded by current admission until implementation
and validation replace that behavior; only the whole-buffer rethrow `assembly { revert(add(data,32), mload(data)) }` is
recognized (`canonicalRethrow`, `memoryRethrow?` in
`Solidity/Frontend/SolcJson/Body.lean`). This document plans the groups and
lanes to cover inline assembly. The decisions below are approved; the exact
human answer is recorded in [solidity-scope.md](../solidity-scope.md#inline-assembly-decisions-2026-10-31).
Workers may implement the authorized extension, but must keep manifest status
honest and preserve all prerequisite gates.

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
| Y01 | **Yul syntax and admission.** Intrinsic Yul AST (planned: Solidity/Yul/Syntax.lean); import of solc JSON `InlineAssembly` (`AST`, `externalReferences`, `flags`, the `memory-safe-assembly` doc comment) in the planned Solidity/Frontend/SolcJson/Yul.lean; builtin table pinned to Osaka and solc 0.8.38; admission per tier with precise refusals, including the compiler-dependent builtins; `canonicalRethrow` becomes an instance, not a special case. Checked Yul parsing over the G08–G11 lexer is child Y01.02. | S00, existing SolcJson frontend |
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
| VY2 | Y04, Y05, Y06, Y09.02 | VY1; V10/V11 inherit layout agreement obligations | B |
| VY3 | Y08.01, Y08.02 | V12 (Y08.01), V15 (Y08.02); backfill until then | B |
| VY4 | Y07.01, Y07.02, Y09.03 | VY2, V13 (G42); YQ6 answered | C |
| VY5 | Y10 | V16, VY3, VY4 | C |

Tier A is one lane, independent of the main chain. Tier B adds two, tier C
two more. VY2's layout definitions feed V10 (G27) and V11 (G32): if those
lanes start first, add "agrees with Y04/Y05's layout" to their checkpoints.
G27, G32, G46 and G47 grow by the corresponding opcode and view obligations;
that growth is counted in VY3/VY4, not in V10–V15.

## Decision questions and original recommendations

The table preserves the original proposal recommendations. The human approved
all five lanes and the choices in the [decision record](../solidity-scope.md#inline-assembly-decisions-2026-10-31),
including tiers A–C together for YQ1. These questions are no longer pending.

| ID | Question | Original recommendation |
|---|---|---|
| YQ1 | Reopen `inlineAssembly`, and which tier? | Tier A now; tiers B and C as separate decisions after VY1. |
| YQ2 | Keep `gas`, `msize`, `pc` and own-code `codesize`/`codecopy` excluded? | Yes: refuse at admission. |
| YQ3 | Memory pointer values depend on allocation order, which differs between pipelines. Make allocation addresses nondeterministic in the source (any choice satisfying the documented layout) with the final theorem a refinement, or fix one allocation discipline? | Nondeterministic with a refinement theorem; needs a G01 contract amendment. |
| YQ4 | A Solidity `uint8` local written from assembly with dirty high bits: model the bits, clean on write, or fail? | Model them exactly as solc does in each pipeline; record any pipeline difference in [solc-alignment.md](../solc-alignment.md). |
| YQ5 | Yul rules have no SolKey taclet. Accept Lean-only rules marked in the rule map? | Yes, marked; reconsider if SolKey gains assembly. |
| YQ6 | Logs become observations (tier C): extend G01's event type for Solidity `emit` too? | Yes, both at once, or tier C keeps `log*` refused. |
| YQ7 | Non-`memory-safe` blocks? | Refuse: via-IR's stack-to-memory mover depends on the flag. |

## Coordination review (2026-10-31)

Separate read-only finder and skeptic reviews checked the five lane assignments,
the complete Y01–Y10 child coverage, intrinsic and ownership constraints,
dependency gates, compact persistent goals and exact human authorization.
Neither used the Lean server. Both found stale proposal/pending wording in the
navigation and coverage summaries; it was corrected. The decision table now
labels its recommendations as historical. No implementation or runtime gate is
claimed by this preparation review.

The publication finder and skeptic reviews also checked the pending documentation
against all five frozen lane assignments and verified the decision links. They
found stale proposal wording in the title and a VY2 prerequisite that assumed
V10/V11 had not started; both were corrected. The scope record now distinguishes
the original launch authorization from the subsequent integration authorization.

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


### VY2 packed-slot complement handoff

The [lane record](inline-assembly-vy2.md#packed-slot-complement-journaling-2026-11-01) now derives complement masks from actual finite typed registrations, reconstructs whole raw slots after canonical typed writeback and couples both parts through existing journals and actual Source.applyOp/frame checks. Nonempty actual source controls and pinned mixed-field/padding/order/rollback/reset vectors are included. Pure unchanged preparation is distinct from journaled/static source behavior. Whole ownership/dirty/dynamic/Yul/compiler/calculus closure remains open; no admission or owner-contract change. Versioned evidence: /workspace/vy2-evidence/packed-residual.


### VY2 computed word-layout registration handoff

The [lane record](inline-assembly-vy2.md#computed-word-layout-registrations-2026-11-01)
adds checked actual Source paths through the existing word-granular owner locator,
approved Fixed preimage bytes, derived finite canonical storage instances and
source/journal controls. Root0/layout inputs and real per-run region conditions
remain explicit; no packed-layout or whole-source adequacy is claimed. Full lane
and producer/compiler/calculus closure remain open. Evidence:
/workspace/vy2-evidence/hashed-registrations.


### VY2 declaration-derived packing handoff

The [lane record](inline-assembly-vy2.md#declaration-derived-packed-registrations-2026-11-01)
now derives canonical mixed scalar registrations from actual source declarations
using existing packing arithmetic, proves disjoint ownership and connects the
computed registry to source/frame/complement journaling. A declaration-derived
fixed-array/struct boundary adapter and14new pinned ordered calls are included.
Whole nested/source/layout/dirty/compiler/calculus obligations remain open;
no admission promotion. Evidence: /workspace/vy2-evidence/declaration-packing.


### VY2 nested declaration source-registry handoff

The [lane record](inline-assembly-vy2.md#nested-declared-source-registry-and-writeback-2026-11-01)
now computes complete fixed-array/inner-struct Source.SPath registrations and
proves actual whole-store snapshot/source equality, raw reencoding, nonwrapping
bounds, alias/index-error/MemOK and paired journal controls. Existing380 pinned
external calls remain unchanged. Arbitrary declarations/dirty/dynamic/Yul/
compiler/calculus closure remain open. Evidence:/workspace/vy2-evidence/nested-declarations.


### VY2 recursive fixed-path handoff

The [lane record](inline-assembly-vy2.md#recursive-fixed-declaration-paths-2026-11-01)
now derives complete recursive fixed-array/struct source registrations from an
intrinsic finite actual-metadata certificate, including exact extent, path
coverage/separation/nonwrapping and concrete whole-source/residual snapshot
composition. New14pinned calls supplement the unchanged380observations.
Whole storage/dirty/dynamic/allocation/Yul/compiler/calculus closure remains
open; goal BLOCKED unchanged. Evidence:/workspace/vy2-evidence/recursive-fixed.
The follow-up also derives actual owner pathTy presence for every enumerated
leaf from root and field metadata; missing-path fallback is not assumed valid.


### VY2 ordered ordinary-root handoff

The [lane record](inline-assembly-vy2.md#ordered-ordinary-root-declarations-2026-11-01)
now threads one computed cursor across checked ordinary roots, derives complete
cross-root geometry/coverage and actual declaration/bank lookup, and connects
whole typed storage/actual residual journals/source readback. Constructor and
padding/reset controls plus14new pinned calls supplement unchanged394calls.
Scope/origin/inheritance/dirty/dynamic/compiler/calculus closure remains open;
full goal stays BLOCKED. Evidence:/workspace/vy2-evidence/root-sequence.


VY2 inherited-root handoff (2026-11-01): constructive canonical active-contract
root inventory uses reversed ACTUAL Source owner C3 and original typed packer;
private qualified base members/cross-contract packing, source/store/residual/frame
and reset controls, pinned diamond pipelines and actual frontend lineage-validator
controls. Full lane PARTIAL, source/compiler/calculus dependencies and origin
agreement still OPEN; YQ1–YQ7 unchanged. See lane inherited-active-contract section
and /workspace/vy2-evidence/inherited-roots/HANDOFF.md for committed head/gates.


VY2 computed-origin handoff (2026-11-01): actual active Source contract clause,
existing rational/literal profile/range checks now compute default0/nonzero Word
and independent transient0; no caller origin in new preparation entry. Actual
inherited packed source/store/residual/frame/reset/MemOK and shifted42 diamond
controls, pinned pipelines and compiler expression-boundary controls are in lane
computed-active-layout-origin section. Full assignment PARTIAL, original goal
BLOCKED unchanged; general expressions/dynamic/dirty/whole source/compiler/calculus
closure remain open. Exact committed head/gates/artifacts:
/workspace/vy2-evidence/layout-origin/HANDOFF.md.

VY2 dynamic-header/live-inventory checkpoint (2026-11-01): extends the existing
actual declaration packing/origin computation to uint256[] length cells and
approved Fixed-hashed element paths, with uncapped runtime-length finite
inventory, exact canonical raw-map reconstruction, actual Source length/index/
static/MemOK and paired source/frame controls. See the [lane handoff](inline-assembly-vy2.md#computed-dynamic-headers-and-live-element-inventories-2026-11-01).
Canonical preparation and finite compiler/EVM controls are not whole Y04/Y05/
Y06/Y09.02 or source/compiler adequacy; original full lane/goal remains partial/
BLOCKED. Exact reviewed tree/gates/premises in
`/workspace/vy2-evidence/dynamic-storage/HANDOFF.md`; no admission promotion.


VY2 ownership-changing dynamic-complement checkpoint (2026-11-01): actual
Source.readLen-derived inventories, complete old/new raw-map/complement transport,
source-success-only journaling, source/pure snapshot equality, dependent shrink /
regrowth, exact alias tail reads, frame rollback and transaction controls. See
[lane scope](inline-assembly-vy2.md#ownership-changing-dynamic-complements-2026-11-01).
Full original lane remains PARTIAL/BLOCKED, no admission promotion. Committed
identity, checks, reviews and exports: `/workspace/vy2-evidence/ownership-transport/HANDOFF.md`.


VY2 packed dynamic unsigned checkpoint (2026-11-01): declaration-derived generic
unsigned element packing, partial-slot complement transport and actual source /
frame/static/alias/MemOK controls; uint16 and uint24 finite pinned pipeline
observations are separate from kernel/source/compiler correspondence. See
[lane handoff](inline-assembly-vy2.md#packed-dynamic-unsigned-ownership-2026-11-01).
Full lane PARTIAL/BLOCKED, no admission promotion. Exact committed identity,
gates/reviews/exports: `/workspace/vy2-evidence/packed-dynamic/HANDOFF.md`.


VY2 signed dynamic integer checkpoint (2026-11-01): additive actual-declaration
integer inventories, existing signed-codec inversion, negative source/alias
reads and actual source-success-only complement/frame transport. See
[lane scope](inline-assembly-vy2.md#signed-dynamic-integer-ownership-2026-11-01).
Full lane remains PARTIAL/BLOCKED; kernel source laws and finite pinned pipeline
controls are separate from full Yul/compiler adequacy. Exact committed tree /
gates/exports: `/workspace/vy2-evidence/signed-dynamic/HANDOFF.md`.

### VY2 scalar-family dynamic ownership checkpoint (2026-11-01)

New intrinsic bool/address/fixedBytes declaration certificates and typed scalar
header/element/component snapshots reuse existing source codecs, one declaration
cursor, Source.readLen and Source.applyOp. Persistent canonical complement/frame
transport is proved; no frontend admission or compiler/source adequacy is claimed.
Bool2 growth remains unsupported canonical preparation while pinned EVM growth
succeeds; storage bytesN low alignment is distinct from ABI/memory left alignment.
Full queue, premises, reviews and versioned handoff:
[inline-assembly-vy2.md](inline-assembly-vy2.md),
`/workspace/vy2-evidence/scalar-dynamic/HANDOFF.md`.

### VY2 combined primitive dynamic ownership checkpoint (2026-11-01)

One declaration-derived inventory includes registered fields once plus all live
integer and bool/address/bytesN elements, using actual Source.readLen and existing
typed selectors/codecs. One source-success-only account/complement execution proves
whole supplied-map reconstruction and frame/reset laws; no separate-family masked
runs are substituted. Original full-lane source/compiler/calculus closure remains
open. [Lane premises/queue](inline-assembly-vy2.md) and versioned evidence:
`/workspace/vy2-evidence/combined-dynamic/HANDOFF.md`.


VY2 nested primitive members checkpoint: actual struct field paths and one packing
cursor derive nested length headers and hashed live entries, combined with fixed
siblings/top-level primitive roots. Actual-source changing ownership and residual
journal share one success-only operation; full reconstruction, alias/frame/reset
controls and compatibility are constructive canonical preparation, not full Y04
or Yul adequacy. [Exact premises and entire queue](inline-assembly-vy2.md#vy2-nested-primitive-members-2026-11-01),
versioned handoff `/workspace/vy2-evidence/nested-dynamic/HANDOFF.md`. Original full
lane remains unfinished; YQ1-YQ7 and whole obligations unchanged.


VY2 recursive dynamic structs: additive intrinsic finite certificates derive full
nested paths/headers/packing from actual metadata, with exact one-level/old-root
compatibility and coupled actual source/complement/frame reconstruction. Three
struct levels and both-pipeline observations are inhabited; canonical preparation
is not Yul/compiler adequacy. [Full original queue/premises](inline-assembly-vy2.md#vy2-recursive-dynamic-structs-2026-11-01).
Versioned handoff `/workspace/vy2-evidence/recursive-dynamic/HANDOFF.md`. Original
lane remains partial; YQ1-YQ7 and full original closure obligations unchanged.


VY2 aggregate dynamic-array preparation checkpoint: see
[the lane record](inline-assembly-vy2.md#vy2-aggregate-dynamic-array-preparation-2026-11-01).
Derived aggregate stride, typed nested live collection and actual canonical
snapshot/source application are partial preparation. Dormant aliases after outer
shrink expose a concrete retained-path/history obligation, not a new exclusion.
Full original queue and producer/compiler/calculus closure remain unfinished.
Exact signatures, tested-tree/gates/reviews/resources and committed full SHA:
`/workspace/vy2-evidence/aggregate-dynamic/HANDOFF.md`.


VY2 retained-reference checkpoint: [original lane queue](inline-assembly-vy2.md#vy2-retained-source-references-2026-11-01).
Actual source formation/bind/sub traces, current-or-retained child traversal,
complete canonical source/complement writes and real prefix/frame controls are
implemented for a supported persistent component. This is not universal
producer/alias capture, whole storage/heap semantics or full-lane completion.
Exact committed SHA, theorem premises, final gates/reviews/resources and artifacts:
`/workspace/vy2-evidence/retained-storage/HANDOFF.md`.

- VY2 computed entry/return capture: [lane checkpoint](inline-assembly-vy2.md#vy2-computed-entry-and-return-capture-2026-11-01); partial, final source/compiler closure open.

- VY2 tuple capture and concrete parallel consumers: [lane checkpoint](inline-assembly-vy2.md#vy2-runtime-tuple-and-argument-capture-parallel-physical-consumers-2026-11-01); partial source assignment, exact peer-input exports and isolated consumers.

- VY2 owned bool representation/source journals: [lane checkpoint](inline-assembly-vy2.md#owned-bool-representation-and-source-journals-2026-11-01); partial physical preparation, dirty local/source/compiler closure remains open.

- VY2 owned bool dynamic inventory: [lane checkpoint](inline-assembly-vy2.md#owned-bool-changing-dynamic-inventory-2026-11-01); actual source/representation/complement transport, partial original lane with retained/local/compiler closure open.

VY2 handoff: [actual location producer capture](inline-assembly-vy2.md#actual-location-producer-capture-2026-11-01) extends typed source-path capture; full lane remains partial.

VY2 handoff: [actual byte/string allocation placement](inline-assembly-vy2.md#actual-bytestring-allocation-placement-2026-11-01) adds constructive actual heap allocation; full lane remains partial.

VY2 handoff: [retained allocation lineage extension](inline-assembly-vy2.md#retained-allocation-lineage-extension-2026-11-01) preserves original capacities across actual allocation; full lane remains partial.

VY2 computed-inventory allocation integration: [lane checkpoint](inline-assembly-vy2.md#computed-inventory-after-allocation-2026-11-01). This derives actual fresh-ID coverage and retains capacity history; full lane closure remains open.

VY2 [actual allocation physical-view bridge](inline-assembly-vy2.md#actual-allocation-physical-view-bridge-2026-11-01) connects the real raw encoder and source writeback under explicit initial-view premises; full closure remains open.

VY2 [generic ordinary object allocation](inline-assembly-vy2.md#generic-ordinary-object-allocation-2026-11-01) constructs typed struct/array physical/source allocation under actual operand and initial-view premises; full closure stays open.

VY2 [actual struct constructor producer](inline-assembly-vy2.md#actual-struct-constructor-producer-2026-11-01) derives constructor execution and physical allocation reuse; full source/compiler closure remains open.

VY2 [actual calldata array allocation](inline-assembly-vy2.md#actual-calldata-array-allocation-2026-11-01) connects the real memory decoder, retained allocation and whole-map writeback; final adequacy remains open.

VY2 [actual memory hash binding](inline-assembly-vy2.md#actual-memory-hash-binding-2026-11-01) connects exact source memory bytes and checked keccak expression to physical hash; final adequacy remains open.

VY2 [actual source environment inputs](inline-assembly-vy2.md#actual-source-environment-inputs-2026-11-01) derives supported source magic and physical context observations; full source/call/compiler closure remains open.

VY2 [concrete packed World adapter](inline-assembly-vy2.md#concrete-packed-world-adapter-2026-11-01) commits actual same-plan source/residual/frame-completion agreement in the private peer-input tree; full lane partial.

VY2 [actual target input frame](inline-assembly-vy2.md#actual-target-input-frame-2026-11-01) supplies concrete bounded source/target Word/address/frame input conversion; lowering and full lane remain open.

VY2 [actual source balance inputs](inline-assembly-vy2.md#actual-source-balance-inputs-2026-11-01) derives the actual balance-read/constructed-funds boundary; independent target ledger and final adequacy remain open.

VY2 storage-effect/input checkpoint: validator-derived persistent/transient packed writes preserve actual source code/balance/history observations and constructed target funds; actual static errors and complete resulting state retained. See [lane accounting](inline-assembly-vy2.md). Independent target-ledger/Yul/compiler/full-lane closure remains open.

VY2 actual effectful balance operand equations and exact halt-prefix controls: [lane checkpoint](inline-assembly-vy2.md). Conditional actual-run premises remain explicit; no global producer or target-ledger adequacy claimed.

VY2 constructive scratch-copy/whole-heap view and computed source writeback transport: [lane checkpoint](inline-assembly-vy2.md). General output-memory and compiler/call adequacy remain open.

VY2 checked residual-window/real retained-tail ownership and actual source writeback: [lane checkpoint](inline-assembly-vy2.md). No new admission or full memory safety/call/compiler claim.


VY2 chronological residual-copy handoff: [lane record](inline-assembly-vy2.md#chronological-residual-memory-copies).
Actual typed current-memory sources, snapshot overlap, arbitrary finite
chronological copies, whole-map/source-state identity, every-original-H
MemOK and reserved/unknown-byte laws are additive preparation results.
Full Y04–Y06/Y09.02 and joint producer/compiler closure remain unfinished.


VY2 mapping and transient handoff: [lane record](inline-assembly-vy2.md#mapping-slot-views-and-transient-slots).
Constructive actual-declaration/key mapping encoding and whole-store roundtrip/
unchanged laws use the original HashedLayout per-run region contract. Actual
transient source/complement load/store, static failure, paired frame rollback
and every-slot transaction reset are additive physical results. Full source/
Yul/compiler and universal layout/dirty ownership remain unfinished.


VY2 actual frame calldata/hash handoff: [lane record](inline-assembly-vy2.md#actual-frame-calldata-copy-and-hash).
Actual raw frame bytes, source-preserving residual copy, zero padding at maximum
source offset and SAME-Fixed hashing are standalone proved physical components.
Concrete producer/compiler/calculus and universal source closure remain open.
Each checkpoint appends its handoff here (revision, theorems and premises,
checks, remaining obligations).

- VY1 (2026-11-03): Yul syntax, static checks, closed execution and word
  logic; see [inline-assembly-vy1.md](inline-assembly-vy1.md).
- VY2 (2026-11-03): memory views and adapters; see
  [yul-physical-memory.md](yul-physical-memory.md).
- VY3 (2026-11-03): compilation combinators; see
  [inline-assembly-vy3.md](inline-assembly-vy3.md).
- VY4 (2026-11-03): world interface; see
  [inline-assembly-vy4.md](inline-assembly-vy4.md).
- VY5 (2026-11-03): composition pieces; see
  [vy5-composition.md](vy5-composition.md).
VY1 follow-up: Boolean-post and absent-condition Source adapters, concrete Rule-premise soundness, Lean-only rule-map rows, guarded Checks and restored generators/fixtures; general Source embedding and final composition remain open. See inline-assembly-vy1.md.
VY1 follow-up: shared Roadmap.Word reuse and universal signed-operation/target-step agreement for SDIV, SMOD, SLT and SGT, with intrinsic-expression and machine-composition controls; compiler lowering and general Source adequacy remain open. See inline-assembly-vy1.md.
VY1 follow-up: parser composition moves to Frontend/Yul while intrinsic preparation retains its original certificates and premises; the layer gate rejects core paths to checked parser adapters. General Source embedding and final lane gates remain open. See inline-assembly-vy1.md.
VY1 follow-up: universal ADD/SUB/MUL/DIV/MOD target-step agreement and wrapped MUL-then-DIV composition, with intrinsic fuel and malformed-stack controls. General Source embedding and final composition remain open. See inline-assembly-vy1.md.
VY1 follow-up: universal comparison, bitwise, shift and EXP target-step agreements, with mixed SHL/PUSH/SHR/AND composition and kernel boundary/refusal controls. General Source embedding and final composition remain open. See inline-assembly-vy1.md.
VY1 follow-up: concrete Source void-return, skipped-tail and enclosing-block equations with full raw-frame retention at every horizon; dirty-frame/context-changing-tail controls. General Source embedding and final composition remain open. See inline-assembly-vy1.md.
VY1 follow-up: concrete Source do/while, unchecked and literal-while void-return transport; skipped assignment effects, dirty-frame retention and existing initializer-refusal controls. General Source embedding and final composition remain open. See inline-assembly-vy1.md.
VY1 follow-up: an executed context-growing Boolean Source declaration with typed local snapshots, exact timeout/clean-projection equations and complete older raw-prefix/world preservation. General Source embedding and final composition remain open. See inline-assembly-vy1.md.
VY1 follow-up: executed Boolean declaration/scope closure with exact Source suffix restoration, full snapshot/frame agreement, existing adapter packaging and concrete two-scope controls. General Source embedding and final composition remain open. See inline-assembly-vy1.md.
VY1 follow-up: certified constant-default declarations and unconditional all-IntTy Source correspondence, with concrete uint8/uint256 growth and dirty-prefix controls. General Source embedding and final composition remain open. See inline-assembly-vy1.md.
VY4 follow-up: intrinsic LOG, returndata and CALL-family port bindings retain full observations/return buffers, with constructive normal LOG rules, actual coupled transient rollback and lifecycle snapshot preparation. CALL completion survives output-copy refusal; source/world/static-operation/compiler/G01/G51 and final lane adequacy remain open. See [the VY4 lane record](inline-assembly-vy4.md) for exact premises and scoped controls.
VY3 exponent checkpoint: actual EXP compiler-model execution is proved for all
word operands, preserving machine fields and symbolic caller tails. Native gas,
feasible large-power evaluation and general source/G24/frontend closure remain
separate. See [the lane handoff](inline-assembly-vy3.md#exponent-compiler-model-execution).
VY3 signed-comparison checkpoint: existing signed readings agree by a budget-
preserving cast proof, and actual SLT/SGT compiler-model runs preserve full dirty
words, machine fields and symbolic callers. General source/G24/native/frontend
closure remains open. See [the lane handoff](inline-assembly-vy3.md#signed-comparison-compiler-model-execution).
VY3 signed-quotient checkpoint: actual published VY1 step producers now drive
complete SDIV/SMOD compiler-model runs, preserving raw results and caller/machine
state. General Source/G24/native/frontend closure remains open. See
[the lane handoff](inline-assembly-vy3.md#signed-quotient-consumption-of-published-word-producers).
VY3 charged-bitwise checkpoint: actual AND/OR/XOR source/compiler origins and
ordered code images connect to real three-gas P10 steps at emitted sites. DUP-
prefix execution and general Source/G24/Osaka closure remain open. See
[the lane handoff](inline-assembly-vy3.md#charged-bitwise-compiler-origin-correspondence).
VY3 charged ISZERO checkpoint: see [lane handoff](inline-assembly-vy3.md#charged-raw-iszero-slice). Both native DUP1/ISZERO steps and X continuation are derived; full Source/G24/frontend/Bridge adequacy remains partial.
VY3 charged NOT checkpoint: [lane handoff](inline-assembly-vy3.md#charged-raw-not-slice). Actual two-step native continuation; full original lane remains partial.
VY3 logical shift compiler slices: [lane handoff](inline-assembly-vy3.md#charged-logical-shift-compiler-slices). Original source evaluation and complete native X continuations; full lane remains partial.
VY3 SAR compiler slice: [lane handoff](inline-assembly-vy3.md#charged-arithmetic-shift-compiler-slice). Original source evaluation and native continuation; full lane remains partial.
VY3 arity-three modular compiler slices: [lane handoff](inline-assembly-vy3.md#charged-arity-three-modular-compiler-slices). Original source/native continuations and exact DUP3 frames; full lane remains partial.
VY3 dynamic-cost EXP compiler slice: [lane handoff](inline-assembly-vy3.md#charged-dynamic-cost-exponent-compiler-slice). Original source/native continuation with actual exponent-byte gas; full lane remains partial.
VY3 concrete arithmetic selection clients: [lane handoff](inline-assembly-vy3.md#published-selection-interface-arithmetic-clients). Actual success/refusal certificate bodies; full native/Source-G24 lane remains partial.
VY3 selection sequence composition: [lane handoff](inline-assembly-vy3.md#actual-selection-certificate-sequence-composition). Exact model/Scalar success and failure composition with real ADD/MUL instances; full lane remains partial.
VY3 finite DUP selection: [lane handoff](inline-assembly-vy3.md#finite-dup-selection-and-actual-compiler-read-prefixes). Concrete all-index bodies connect actual ADD/MUL compiler read prefixes to sequence transport; full lane remains partial.
VY3 source local-write/model composition: [lane handoff](inline-assembly-vy3.md#local-writes-through-actual-swappop-selection). Concrete SWAP/POP bodies and original assignment/read-after-write sequence instances; full lane remains partial.
VY3 literal/scoped source-model composition: [lane handoff](inline-assembly-vy3.md#literal-push-and-initialized-source-scopes). Real PUSH body and initialized/zero scope instances; full lane remains partial.
VY3 source-to-structured control: [lane handoff](inline-assembly-vy3.md#normal-source-control-to-the-published-structured-relation). Actual compiler branches/sequences establish the published stack relation; native realization/full lane remain partial.
VY1 follow-up: concrete constant-default scope closure and existing integer adapters, with unconditional all-IntTy Source composition and mixed uint8/uint256 controls. General Source embedding and final composition remain open. See inline-assembly-vy1.md.
VY1 follow-up: concrete Boolean literal initialization with actual Source correspondence, both values, exact horizons and dirty-prefix/nondefault controls. General Source embedding and final composition remain open. See inline-assembly-vy1.md.
VY1 follow-up: concrete Boolean initializer scope closure, actual Source/frame correspondence and existing adapters, with literal/default mixed-scope controls. General Source embedding and final composition remain open. See inline-assembly-vy1.md.
VY1 follow-up: universal in-range integer literal initialization with concrete Source conversion/typing laws, exact prefix preservation, boundary/refusal controls and actual signed/unsigned item composition. General P16 and final composition remain open. See inline-assembly-vy1.md.
VY1 follow-up: concrete in-range integer initializer scope closure, all-fuel Source/frame correspondence and existing adapters, with signed/unsigned/Boolean combinations and same-fuel empty-block controls. General P16 and final composition remain open. See inline-assembly-vy1.md.
VY1 follow-up: context-growing initialization by actual certified Boolean expressions, all-tree/all-fuel clean Source correspondence, retained partial effects, raw-copy and short-circuit controls. General P16 and final composition remain open. See inline-assembly-vy1.md.
VY1 follow-up: scope closure of actual Boolean-expression initialization, concrete all-tree/all-fuel Source composition and retained outer-local effects on success/timeout. General P16 and final composition remain open. See inline-assembly-vy1.md.
VY1 follow-up: actual Boolean binding followed by an expression in its extended context, with concrete all-fuel Source item composition and reached-context partial-state controls. General P16 and final composition remain open. See inline-assembly-vy1.md.
VY1 follow-up: intrinsic certificates and concrete all-list/all-fuel Source composition for Boolean declaration/expression lists, retaining typed reached contexts on failure. General P16 and final composition remain open. See inline-assembly-vy1.md.
VY1 follow-up: arbitrary certified Boolean item scope closure with derived typed suffix restoration, concrete Source block correspondence and retained reached-context failures. General P16 and final composition remain open. See inline-assembly-vy1.md.
- VY1: LocalBoolIf adds concrete clean-input Source conditional/scope agreement with retained condition effects and partial branch contexts; full lane gates remain open. See [lane handoff](inline-assembly-vy1.md).
- VY1: LocalBoolIfElse adds clean-input Source agreement for independently indexed conditional branches, retaining partial effects; see [lane handoff](inline-assembly-vy1.md). General P16 and final gates remain open.
VY4 follow-up: the intrinsic STOP/RETURN/REVERT outcome leaf reads exact raw bytes and distinguishes genuine revert from unavailable memory, with cross-word/empty/refusal controls. Interpreter exit, frame completion, Source/G01/G51/compiler/resource adequacy remain open; see [the VY4 lane record](inline-assembly-vy4.md).
VY4 reconciliation: published master already contained the earlier owned modules. The newer lifecycle names now alias the pre-existing `Lifecycle.destructKnown` and `Lifecycle.rollbackDestruction`; this removes duplicate implementations without changing semantics or claiming new adequacy. Terminal leaf and scoped validation remain in [the VY4 record](inline-assembly-vy4.md).
VY4 follow-up: intrinsic SELFDESTRUCT now binds to the existing frame/lifecycle preparation, with dirty-address/delegated-owner/static/deletion controls. Outcome tagging is not interpreter or Source/world adequacy; see [the lane record](inline-assembly-vy4.md).

- VY1: LocalBoolWhile adds concrete clean-input Source agreement for context-growing scoped loop bodies; partial contexts and dirty runtime words are retained. See [lane handoff](inline-assembly-vy1.md); full P16 and lane gates remain open.

- VY1: LocalBoolDivergence proves no finite normal completion for constant-true certified scoped loops, for arbitrary raw frames and actual clean Source execution. See [lane handoff](inline-assembly-vy1.md); full lane remains open.

- VY1: LocalBoolDoWhile adds concrete clean Source agreement for body-first context-growing scoped loops, with partial-body/condition and recursion controls. See [lane handoff](inline-assembly-vy1.md); full P16 and lane gates remain open.

- VY1 integration review: conditional and scoped-loop proofs reuse RawSequence.restore_self; the duplicate was removed, with unchanged agreement statements and control expectations.

- VY1: LocalBoolDoDivergence adds universal raw/clean-Source no-normal-completion laws for constant-true certified do/while bodies; full lane remains open.

- VY1: LocalBoolFor adds concrete clean Source agreement for a Boolean for initializer and scoped item body without post, preserving enclosing effects and partial contexts. Full lane remains open.

- VY1: LocalBoolPostIter/LocalBoolForPost add concrete all-fuel clean Source composition for present Boolean posts, preserving post effects and scoped failure contexts. Full lane remains open.

- VY1: LocalBoolForNoGuard adds exact Source omitted-guard transport and concrete clean adapters for both post modes, with independent Source and raw guard controls. Full lane remains open.

- VY1: LocalBoolUnchecked adds concrete clean Source item/block composition across unchecked and ordinary scopes, retaining reached failure contexts. Full lane remains open.

- VY1: LocalDefaultBinding adds concrete clean Source constant-default declaration/body composition with typed context growth; allocating references and dirty compiler adequacy remain separate obligations.

VY1: constant-default scopes now have concrete clean-input Source block agreement and raw restoration controls; full P16 and lane validation remain open.

VY1: heterogeneous constant-default declaration sequences have concrete clean-input Source item agreement and raw partial-context controls; general P16 remains open.

VY1: heterogeneous default sequences now have raw scope closure and concrete clean-input Source block agreement; general P16 and final lane validation remain open.

VY1: unchecked heterogeneous default scopes and ordinary continuations now have concrete clean-input Source item/block composition; full P16 and lane gates remain open.

VY1: pure local item/default/unchecked runners now preserve the existing world for all raw inputs and fuel values; local effects and broader P16 remain distinct.

VY1: conditional selection between independently typed default scopes now has concrete Source agreement, raw world preservation and condition-effect controls; full P16 remains open.

VY1: loops over heterogeneous default scopes have concrete Source agreement, raw world preservation and constant-true finite-normal exclusion; full P16 remains open.

VY1: body-first default-scope loops now have concrete Source agreement, raw world preservation and finite-normal exclusion; full P16 remains open.

VY1: scoped default for-iterations with Boolean posts have concrete Source agreement, raw purity and post-value-discard controls; full P16 remains open.

VY1: H22 rebased with H21 registries; omitted-guard default iterations reuse actual Source transport and have concrete scoped agreement/purity/noncompletion. Full P16 remains open.

VY1: local Boolean expression/control failures are proved to be timeouts for all raw inputs and fuel; see [lane handoff](inline-assembly-vy1.md#boolean-failure-classification). General P16 remains open.

VY1: actual statement/initialization and context-growing item failures are proved to be timeouts without erasing reached locals; see [lane handoff](inline-assembly-vy1.md#context-growing-item-failures). General P16 remains open.

VY1: concrete scoped-loop timeout classification and all-horizon omitted-guard Source output proved, with retained raw results and a break counterexample; see [lane handoff](inline-assembly-vy1.md#concrete-finite-horizon-loop-timeouts). General P16 remains open.

VY1: concrete post/do-while classifications and omitted-guard post-loop Source horizons proved; see [lane handoff](inline-assembly-vy1.md#post-and-body-first-horizons). General P16 remains open.

VY1: exact constant-loop reductions and constant-true do/while Source horizons proved, with effectful-post and breaking-body counterexamples; see [lane handoff](inline-assembly-vy1.md#constant-loop-reductions). General P16 remains open.

VY1: exact-word congruence now composes through certified Boolean expressions, context-growing items, scopes, conditionals and loops, including Boolean-initialized no-post for execution; see [lane handoff](inline-assembly-vy1.md#boolean-initialized-for-congruence). General P16 remains open.

VY1: all-fuel exact-word congruence now covers certified guarded Boolean post iterations, retaining body/post partial states while discarding post values; see [lane handoff](inline-assembly-vy1.md#post-iteration-exact-word-congruence). General P16 remains open.

VY1: exact-word congruence now composes Boolean initialization with guarded post iteration and normal-only scope closure; see [lane handoff](inline-assembly-vy1.md#initializer-and-post-loop-congruence). General P16 remains open.

VY1: exact-word congruence now covers certified heterogeneous defaults and unchecked scope/continuation composition, with related clean/raw frames whose Source projections differ; see [lane handoff](inline-assembly-vy1.md#heterogeneous-default-and-unchecked-congruence). General P16 remains open.

VY1: exact-word congruence covers independently indexed heterogeneous branches and default-scope while/do-while execution, retaining typed failure prefixes; see [lane handoff](inline-assembly-vy1.md#independently-indexed-default-control-congruence). General P16 remains open.

VY1: exact-word congruence covers default-scope post iterations and existing omitted-guard wrappers, with controls separating post effects from discarded values; see [lane handoff](inline-assembly-vy1.md#default-post-and-omitted-guard-congruence). General P16 remains open.

VY1: exact-result congruence covers checked uint8 arithmetic, comparison and Boolean selection within each pipeline, retaining operand order and partial errors; see [lane handoff](inline-assembly-vy1.md#checked-uint8-and-comparison-congruence). General P16 remains open.

VY1: checked-u8 terminal horizon stability and timeout controls; see [lane handoff](inline-assembly-vy1.md#checked-uint8-terminal-horizons). Full lane remains open.

VY1: checked-u8 comparison terminal horizon stability and pipeline/timeout controls; see [lane handoff](inline-assembly-vy1.md#checked-uint8-comparison-horizons). Full lane remains open.

VY1: Boolean full-run terminal horizon stability and selected/skipped branch controls; see [lane handoff](inline-assembly-vy1.md#boolean-terminal-horizons). Full lane remains open.

VY1: concrete comparison/Boolean conditional terminal horizon composition; see [lane handoff](inline-assembly-vy1.md#mixed-comparison-and-boolean-conditional-horizons). Full lane remains open.

VY1: context-growing completed item horizon stability and multi-declaration controls; see [lane handoff](inline-assembly-vy1.md#context-growing-completed-item-horizons). Full lane remains open.

VY1: heterogeneous default-item and restored-block completed horizon stability; see [lane handoff](inline-assembly-vy1.md#heterogeneous-default-item-and-block-horizons). Full lane remains open.

VY1: completed unchecked-scope/ordinary-continuation horizon stability; see [lane handoff](inline-assembly-vy1.md#unchecked-scope-and-ordinary-continuation-horizons). Full lane remains open.

VY1: independently typed conditional-scope completed horizon stability; see [lane handoff](inline-assembly-vy1.md#independently-typed-conditional-scope-horizons). Full lane remains open.

VY1: adopted the published P16 dependency without changing its interface; retained local checkpoints and explicit P20 producer obligations. See [lane handoff](inline-assembly-vy1.md#published-p16-dependency-adoption).

VY1: recursive default-scoped while completed horizon stability and mutating-iteration controls; see [lane handoff](inline-assembly-vy1.md#recursive-while-completed-horizons). Full lane remains open.

VY1: body-first recursive do/while completed horizon stability and two-iteration controls; see [lane handoff](inline-assembly-vy1.md#body-first-dowhile-completed-horizons). Full lane remains open.

VY1: guarded for/post completed horizon stability and retained-post-effect controls; see [lane handoff](inline-assembly-vy1.md#guarded-forpost-completed-horizons). Full lane remains open.

VY1: concrete full initialized-for completed horizon composition and exact scope/iteration agreement; see [lane handoff](inline-assembly-vy1.md#full-for-initializer-completed-horizons). Full lane remains open.

VY1: concrete initialized no-post for completed horizon composition and nested-scope caller-write controls; see [lane handoff](inline-assembly-vy1.md#initialized-no-post-for-completed-horizons). Full lane remains open.

VY1: concrete initialized omitted-guard noncompletion and clean Source consequences; [scope and controls](inline-assembly-vy1.md#initialized-omitted-guard-noncompletion). Full lane remains open.

VY1: concrete full Boolean for timeout classification and clean Source outcomes; [scope and controls](inline-assembly-vy1.md#full-boolean-for-timeout-classification). Full lane remains open.

VY1: concrete Source firstDone horizon selection; [scope and controls](inline-assembly-vy1.md#concrete-source-horizon-selection). Full lane remains open.

VY1: concrete completed raw-frame statement horizons; [scope and controls](inline-assembly-vy1.md#completed-raw-frame-statement-horizons). Full lane remains open.

VY1: completed raw sequence/block horizons; [scope and controls](inline-assembly-vy1.md#completed-raw-sequence-and-block-horizons). Full lane remains open.

VY1: completed raw condition/control-body horizons; [scope and controls](inline-assembly-vy1.md#completed-raw-condition-and-loop-body-horizons). Full lane remains open.

VY1: completed raw control-sequence/block horizons; [scope and controls](inline-assembly-vy1.md#completed-raw-control-sequence-horizons). Full lane remains open.

VY1: completed raw controlled-while horizons and read views; [scope and controls](inline-assembly-vy1.md#completed-raw-controlled-while-horizons). Full lane remains open.

VY1: completed raw sequence-bodied while horizons; [scope and controls](inline-assembly-vy1.md#completed-raw-sequence-bodied-while-horizons). Full lane remains open.

VY1: concrete P16 loop-adapter horizons; [scope and controls](inline-assembly-vy1.md#concrete-p16-loop-adapter-horizons). Full lane remains open.

VY1: concrete P16 sequence-loop adapter horizons; [scope and controls](inline-assembly-vy1.md#concrete-p16-sequence-loop-adapter-horizons). Full lane remains open.

VY1: concrete body-first adapter horizons; [scope and controls](inline-assembly-vy1.md#concrete-body-first-adapter-horizons). Full lane remains open.
VY3 arithmetic source/model branch: [lane handoff](inline-assembly-vy3.md#arithmetic-source-branches-through-actual-model-execution). Real child-code certificates derive complete model execution; native/full lane remains partial.

- VY3 checked control selection: `ControlRealization` constructs scalar iff
  lowering certificates and forward whole-model sequence/conditional proofs,
  including actual nested/prefixed source compiler instances. Exact leaf byte
  origins are checked; loops/native/G24/full-lane closure remain open. See the
  [lane document](inline-assembly-vy3.md) and sealed checkpoint handoff.

- VY3 review follow-up: selection imports use published V2, signed quotient
  axiom reports are enforced, and the excluded routine ledger stays archived.
  No capacity or full-lane closure is inferred; see the lane handoff.

- VY3 whole selected-block lowering now supplies the published iff certificate
  and exact model-fault transport for supported scalar/sequence/conditional
  blocks, with original source prefix witnesses. Native/G24/capacity and full
  lane closure remain open; see the [lane document](inline-assembly-vy3.md).

- VY3 concrete read/write/nested-update slices now inhabit nonvacuous V2 frame
  certificates with real caller-tail capacity and transient-prefix witnesses.
  Native/function/G24 and full-lane obligations remain open; see the
  [lane document](inline-assembly-vy3.md).

- VY3 SUB/DIV/MOD certificates now compose with an actual mixed source sequence
  and exact emitted-program iff lowering witness. Earlier refusal tables and
  admission remain unchanged; native/G24/full-lane work stays open. See the
  [lane document](inline-assembly-vy3.md).

- VY3 structured selection now consumes the concrete arithmetic table through
  typed leaf certificates, with source/whole-iff witnesses for DIV-controlled
  mixed arithmetic under live prefixes. Legacy verdicts remain unchanged;
  native/G24/full-lane closure stays open. See the [lane document](inline-assembly-vy3.md).

- VY3 bitwise/shift certificates now compose with actual guarded source and
  whole-iff lowering under live prefixes, including full-word count boundaries.
  Native/G24/full-lane work remains open; see the [lane document](inline-assembly-vy3.md).

- VY3 signed structured selection: concrete SDIV/SMOD/SLT/SGT certificates,
  original source conditional with ordered updates, general source/model and
  whole-iff artifacts at depths0/2, exact candidate validation and negative
  controls. Generated Bridge import closure passes. Full source/G24/native/
  frontend composition remains partial; see [lane](inline-assembly-vy3.md).

- VY3 unsigned comparison selection: concrete LT/GT/EQ certificates and an
  original-source EQ conditional with ordered updates, general source/model
  and whole-iff artifacts at depths0/2, full-word/unsigned/refusal controls.
  Full source/G24/native/frontend closure remains partial; see
  [lane](inline-assembly-vy3.md).

- VY3 unary selection: actual ISZERO/NOT certificates, original nested-unary
  conditional with ordered writes, general source/model and whole-iff artifacts
  at depths0/2, and height-only capacity laws with separate operand refusal.
  Full source/G24/native/frontend composition remains partial; see
  [lane](inline-assembly-vy3.md).

- VY3 EXP selection: concrete full-word certificate, ordered original-source
  EXP/ISZERO conditional, general source/model and whole-iff artifacts at
  depths0/2, and explicit height-capacity versus operand-arity controls. Native
  gas and full source/G24/frontend closure remain open; see
  [lane](inline-assembly-vy3.md).

- VY3 software BYTE selection: bounded exact PUSH1 certificates and existing
  expansion composed with original-source conditional/ordered updates and
  source/model/whole-iff artifacts at depths0/2. Mixed-width refusals and native/
  full Source/G24/frontend limits remain explicit; see
  [lane](inline-assembly-vy3.md).

- VY3 occurrence-indexed selection: exact mixed PUSH32/PUSH1 certificates,
  constructive success/fault and scalar-leaf iff, and original BYTE literal
  assignment source/model instances at depths0/2. Legacy interfaces remain;
  structured/native/full Source/G24/frontend closure is pending. See
  [lane](inline-assembly-vy3.md).

- VY3 positional structured selection: constructed realization/classification
  for code/sequence/conditional blocks, whole iff/failure transport and original
  mixed-width BYTE conditional instances at depths0/2. Loop/native/full Source/
  G24/frontend obligations remain open; see [lane](inline-assembly-vy3.md).

VY3 finite target-loop preparation: `SolidityBridge.Yul.LoopRealization` derives
finite iteration witnesses and whole forward model runs from actual
`StructuredExec`, with terminating countdown and separate no-finite-outcome
controls. This does not reopen loop admission or close source/G24/native
correspondence; see [VY3](inline-assembly-vy3.md#finite-target-loop-realization).

VY3 target-loop follow-up: finite-prefix reverse classification and a separate
recursive target selector now construct existing whole-iff/failure certificates
for nested loops. Model macro-turns are distinct from native/source divergence
prefixes; [source/G24/native closure remains open](inline-assembly-vy3.md#target-loop-classification-and-selection).

VY3 additional bounded handoff: actual closed checked-JSON preparation now
feeds scoped scalar compilation, and original let/zero scopes compose with
normal structured bodies. General kernel laws and synthetic controls are in
[the VY3 lane record](inline-assembly-vy3.md); complete Source/G24/native and
frontend adequacy, broad imports and final lane validation remain open.

VY3 recursive-compiler handoff: original Yul scopes now recurse under branches
and sequences with same-horizon source and structured target proofs. The
[lane record](inline-assembly-vy3.md) retains unsupported constructs and the
separate G24/native/frontend/final-validation obligations.

VY3 checked-JSON handoff: actual checked word JSON now feeds recursive normal
structured compilation with source/model proofs and a conditional arithmetic
witness. [VY3](inline-assembly-vy3.md) records the separate admission, Source/G24,
native and final joint-validation obligations.

VY3 switch handoff: original case-list compilation now has same-horizon source
and structured target proofs with one selector evaluation and exact retirement.
[VY3](inline-assembly-vy3.md) records the root-component domain and separate
recursive-visitor, Source/G24/native and final-validation obligations.


VY3 ordered switch composition: `SolidityBridge.Yul.SwitchControl` adds an
original-AST sequence/conditional visitor, with constructive exact-horizon
source and whole-block target proofs. Reviewed controls show a second switch
reads the first switch's updated locals, preserving dirty words and callers.
Lexical-scope/case-body switch compilation and full Source/G24/native/final
gates remain open; see [the lane record](inline-assembly-vy3.md).


VY3 lexical switch scopes: `SolidityBridge.Yul.ScopedSwitch` adds an
original-statement scope adapter over concrete switch/control lowering, with
exact source horizons and constructive initialized-prefix entry/retirement
proofs preserving outer mutations and arbitrary caller tails. Reviewed nested
scope/dirty-word/model controls pass. Case-body nesting and full source/native
adequacy remain open; see [the lane record](inline-assembly-vy3.md).


VY3 recursive cases/defaults: `SolidityBridge.Yul.NestedSwitch` constructs
original-AST source/structured-target certificates through mutually recursive
statement/case compilation, including lexical scopes inside nested arms.
Reviewed dirty-word, no-fallthrough, source/model and refusal controls pass.
General source/native adequacy remains open; see [the lane record](inline-assembly-vy3.md).


VY3 checked JSON consumer migration (partial): `StructuredJson` now uses the
concrete nested-switch compiler without changing its kernel source/model
contracts. Synthetic JSON and emitted-prefix controls distinguish21/999/42/17
and preserve ingress refusals. A specific raw-JSON kernel certificate remains
pending as H14 NJ1; no Body admission or source/native adequacy is claimed.
See [the lane record](inline-assembly-vy3.md).


VY3 NJ1 kernel components: the explicit typed syntax/preparation and concrete
lowering are inhabited. Exact checked-packet reconstruction is proved only
under the visible premise `blockAux 20 ast = .ok tree`; that raw decoder
equality remains the H14 routine task, so NJ1 is still partial. See
[the lane record](inline-assembly-vy3.md).


VY3 NJ1 closed for the fixed fixture: `StructuredSwitchJsonKernelAttachment`
proves the exact original decoder equality and unconditional packet,
compilation and source endpoints. Its model theorem retains the actual
represented-stack premise; a fixed low-fuel refusal is also proved. Bounds and
observations are unchanged. Full lane/source/native obligations remain open;
see [the lane record](inline-assembly-vy3.md).

- VY3 finite emitted while: `SolidityBridge.Yul.LoweredWhile` derives exact finite structured/model runs from real emitted slice certificates with explicit pre-body/final guard premises and arbitrary prefix/caller preservation. Original AST leaf compiler controls are inhabited; Source FOR/native/resource/full-lane adequacy remains open. See [VY3](inline-assembly-vy3.md#finite-emitted-while-execution).

- VY3 normal FOR slice: `SolidityBridge.Yul.NormalFor` prepares original intrinsic components and proves finite original closed-word FOR/horizon execution plus matching structured/model emission. Prelude/body/post ordering is witnessed with dirty words; guards and component bounds remain explicit. Logical Solidity Source/G24/native/full-lane adequacy stays open. See [VY3](inline-assembly-vy3.md#normal-original-for-compilation-slice).

- VY3 direct MSTORE slice: concrete local byte-target/VY2 view refinement, typed-image disjoint framing, canonical hash composition and exact actual-prefix capacity. The published host-writer counterexample remains open and unexcluded; this is not native/global MemOK/Source-G24 adequacy. See [VY3](inline-assembly-vy3.md#direct-mstoreview-composition).

- VY3 branch-bearing FOR: `StructuredFor` consumes actual normal-control compiler outputs for pre/body/post and proves original finite closed-source/whole-target/model execution. Shared `ForSource` laws are discharged by real old/new compiler facts; previous NormalFor interfaces/controls remain unchanged. General Source/G24/native/admission/divergence closure remains open. See [VY3](inline-assembly-vy3.md#branch-bearing-for-components).

- VY3 FOR noncompletion: actual compiler facts now derive source noncompletion at every horizon and exact continuation after every finite model macro-turn count, with an inhabited branch-bearing invariant and whole selected-program denotation. Model `.fault` here encodes no finite outcome, not native exceptional halt. Full Source/G24/native/admission closure remains open. See [VY3](inline-assembly-vy3.md#all-horizon-for-noncompletion-and-finite-model-turns).

- VY3 source-completion FOR transport: actual successful original evaluation now supplies the finite count/guards internally, then matches the exact source output through actual emitted/selected code. Branch, zero-guard and refused horizon/noncompletion controls preserve raw words and caller frames; full Source/G24/native/admission closure remains open. See [VY3](inline-assembly-vy3.md#source-completion-driven-for-transport).

- VY3 finite FOR reflection: target determinism and actual compiler emissions now recover source counts/guards/output from finite structured/model success, including exact machine framing and pending zero. Real component horizon bounds remain explicit; native/G24/admission and final-lane adequacy stay open. See [VY3](inline-assembly-vy3.md#finite-for-target-to-source-reflection).

- VY3 H26 P20 success-interface V1: original closed compiler alias plus explicit uninstantiated source/G24 success-link fields using actual Input/Rep, with real joint success and represented/payment-free witness requirements. Full P20 and original lane work remain open. See [VY3](inline-assembly-vy3.md#h26-p20-success-interface-v1).

- VY3 emitted FOR shape: exact real instruction layout, operand/height refinements, scalar prefix capacities and separate expansion room now cover the actual branch-bearing FOR with caller bounds. Existing BlockShape iff is h+2<=1024 at h>=5; native realization/G24/full-lane closure remains open. See [VY3](inline-assembly-vy3.md#emitted-for-physical-shape-and-room).

- VY3 scope/switch FOR: actual component compilers now lower lexical temporaries and switch/default within original FOR, with finite whole-source/structured/model proofs and a real order-sensitive dirty-word witness. Exact compile-entry equality and unsupported-flow controls are checked; full frontend/G24/native/lane closure remains open. See [VY3](inline-assembly-vy3.md#for-with-lexical-scope-and-switch-components).

- VY3 scoped FOR completion: actual source success at any horizon now supplies count/guards internally for exact whole structured/model transport. Shared source induction retains real premises discharged by both concrete compilers; old completion contracts/controls are unchanged. Full Source/G24/native/frontend/lane adequacy remains open. See [VY3](inline-assembly-vy3.md#source-success-transport-for-scoped-for).

- VY3 scoped FOR reflection: actual finite scope/switch target/selected-model success derives original source completion and exact caller/raw-word/frame/pending result; `compilerFuel ≤ base` remains explicit. See [lane handoff](inline-assembly-vy3.md#target-success-reflection-for-scoped-for). Full native/G24/frontend adequacy remains open.

- VY3 closed scoped FOR: exact raw-output iff and all-horizon noncompletion correspondence for actual packets; genuine unending literal-true scoped/switch witness, never runtime-executed. See [lane handoff](inline-assembly-vy3.md#closed-scoped-for-result-and-noncompletion-equivalence). This remains mathematical-model preparation, not full G24/native adequacy.

- VY3 finite scoped FOR prefixes: actual selected condition/body/post turns preserve exact raw locals/caller/full machine frame; actual prelude is proved separately. Universal unending prefixes and bounded third-turn wrap witness are kernel/model results, not native/G24 completion. See [lane handoff](inline-assembly-vy3.md#finite-scoped-for-macro-turn-prefixes).

- VY3 target shape: actual execution/caller framing is derived from existing intrinsic CodeShape; exact shifted all-prefix capacity remains independent. Last-slot dirty update and underflow/peak-overflow controls are kernel target preparation, not native/G24 adequacy. See [lane handoff](inline-assembly-vy3.md#constructive-target-shape-and-caller-capacity).

- VY3 pure-expression operand shapes: actual literal/local/binary emissions, original intrinsic subtraction visitor/source/target witness, shifted DUP16 and exact raw/caller/capacity controls. Explicit primitive-row and child-metadata premises remain; no full G24/native coverage. See [lane handoff](inline-assembly-vy3.md#actual-pure-expression-operand-certificates).

- VY3 arithmetic visitor operand producer: actual successful original visitor/emission now derives recursive CodeShape without public child metadata or primitive-row premises. Nested original MUL/ADD/SUB source/target and peak-three/depth controls are kernel preparation, not full G24/native adequacy. See [lane handoff](inline-assembly-vy3.md#recursive-arithmetic-visitor-operand-producer).

- VY3 statement visitor operand producer: actual skip/assignment/sequence visitor/emission derives balanced CodeShape with no public child metadata or slot-range premises. Dependent sequential-write source/target and shifted-prefix/capacity controls remain kernel preparation, not full G24/native adequacy. See [lane handoff](inline-assembly-vy3.md#recursive-statement-visitor-operand-producer).

- VY3 word visitor operand producer: actual recursive word compiler/emission derives metadata for its arithmetic/quotient/comparison/unary domain. Mixed DIV/MOD/EQ/NOT source/target and universal zero-divisor/full-word-complement controls remain kernel preparation, not full G24/native adequacy. See [lane handoff](inline-assembly-vy3.md#recursive-word-visitor-operand-producer).

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

### VY5 actual Source attempt consumer — 2026-11-01

VY5 consumes actual EM.attempt with explicit old callee locals/raw caller
companion.28component laws retain all outcome/poststate branches, bind only
actual revert-byte length into existing raw continuation, and distinguish
post-log99 retention from separate physical/native rollback. New4profile24call
finite controls and781JS+2Python pass; joint KeySort/build/TestSuite/strict/trust/
scoped-axiom gates pass. All24 ORIGINAL full obligations and six full Source
combinations remain pending; no Source.tryStmt/heapcatch/frame adequacy inferred.
See [lane details](inline-assembly-vy5.md#actual-source-halt-capture-with-raw-companion--2026-11-01) and immutable artifacts
at `/workspace/vy5-composition/attempt-20261101/final/`.

### VY5 captured-byte typed heap consumer — 2026-11-01

VY5 uses actual allocRef/heap allocation/bytesOfRV/heapBytes for full captured
revert bytes while preserving the raw caller.38component laws prove exact
reference/content/length/frame changes, readback continuation and refusal effects;
physical copying retains real placement premises, not heap-index/EVM equality.
148focused tests and required joint KeySort/build/TestSuite/strict/trust/axiom
gates pass.16new Source byte comparisons reuse four sealed native profiles; no
compiler/EVM rerun is claimed. All24 ORIGINAL full obligations/six Source
combinations remain pending. See [lane details](inline-assembly-vy5.md#typed-heap-allocation-of-captured-bytes--2026-11-01)
and immutable artifacts `/workspace/vy5-composition/heap-catch-20261101/final/`.


### VY5 typed catch-local scope consumer (2026-11-01)

[Lane handoff](inline-assembly-vy5.md#typed-catch-local-scope-consumer-2026-11-01):
actual captured/allocated reference bound via indexed Source locals/EM.sub, read
through readLoc/bytesOfRV, outer restoration on any halt without rollback, raw
companion retention and subsequent continuation;28 component laws/123focusedJS.
Existing canonical resolved rethrow is checked distinctly from missing general
Source try selection. New Source readback links16 full bytes across four profiles
to fully validated historical24call evidence; no fresh native execution. All24
original obligations/six Source combinations and final adequacy remain pending.
Incremental artifacts: `/workspace/vy5-composition/scope-catch-20261101/final/`.


### VY5 captured typed scope to canonical rethrow (2026-11-01)

[Lane handoff](inline-assembly-vy5.md#captured-typed-scope-to-canonical-rethrow-2026-11-01):
actual returned allocated catch-local scope feeds existing resolved execS rethrow,
with exact full bytes/state/restoration for every positive fuel, zero timeout,
wrong-index/dangling refusal and raw caller retention;20 component laws/129JS.
New Source driver12cases/6controls; historical24nativecalls are regression only,
ZERO new native rethrow comparisons. No general Source.try selector or final
adequacy claim; all24 original obligations/sixSourcecombinations remain pending.
Resource incident/ENOSPC and recovered verified current metadata copies are
explicit; old protected data and failing baseline gates preserved.
Artifacts: `/workspace/vy5-composition/rethrow-20261101/final/`.


### VY5 fresh finite native rethrow evidence (2026-11-01)

[Lane handoff](inline-assembly-vy5.md#fresh-finite-native-canonical-rethrow-2026-11-01):
actual pinned solc/Osaka try/catch canonical rethrow. Original fixture retains
STRICTFAIL five optimized viaIR journal checks/all36calls captured. Separate
pre-frozen externally audited fixture passes36calls/four profiles,20 finite
Source failure/fullbyte projections/eight executed negatives; native state
independently checked, no SourceSt/compiler proof inferred.138JS tests pass.
No kernel/import change; all24 obligations/sixSourcecombinations remain pending.
Artifacts: `/workspace/vy5-composition/native-rethrow-20261101/final/`.


### VY5 actual Source runtime block/error consumers (2026-11-02)

[Lane handoff](inline-assembly-vy5.md#actual-source-runtime-block-and-abi-error-consumers-2026-11-02):
28 new kernel laws execute real typed declInit/evalE/execItems/block rethrow and
reraise/attempt/heap allocation, then actual extReturn full-revert/short-return
error transport. Inhabited dirty caller/heap/prefix and fullbytes/alias/fuel/error
controls;130JS, joint1230/TestSuite262/signatures/strict/trust/MCP pass.
Exact VY4 ordinary typed-function packet requested, not assumed. No new native
fixture/comparison, five native strictFAILs retained. All24/six/fulladequacy pending.
Artifacts: `/workspace/vy5-composition/runtime-block-20261102/final/`.


### VY5 actual modifier/internal rethrow (2026-11-02)

[Lane handoff](inline-assembly-vy5.md#actual-modifier-and-internal-call-rethrow-2026-11-02):
30kernel laws consume real runMods/placeholder/callInternal, fullbyte alias-body
rethrow and arbitrary savedframe restoration across both Sourcepipelines.
42Sourcecases/two directplaceholders/138JS; selected resolvedprogram ONLY, not
frontendderived/generalmodifier/Source.try/compiler/world adequacy. Actual
joint1231/TestSuite262/KeySort/signature/strict/trust gate passes. Original five
native journal FAILs and all24/six remain open. Capacity approval rejection and
separate safe resolution retained, no guard or protecteddata cleanup.
Artifacts: `/workspace/vy5-composition/modifier-body-20261102/final/`.

### VY5 selected returning decoder (2026-11-02)

The [VY5 lane](inline-assembly-vy5.md#actual-selected-returning-callstaticcall-decoder-2026-11-02)
adds19 actual selected CALL/STATICCALL→Source.extReturn laws using verified VY4
`fd3da385f5e4ada7aa889821d3ae59a34833d235`, real heap inputs/full carrier and
separate bounded output-copy decoding.23 provenance/mutation tests pass; finder
and skeptic's coordinated-provenance finding was repaired. Private joint
KeySort/full1283/TestSuite262/axioms/strict pass; initial combined command EXIT1
from incomplete trust stdin remains failure, corrected full trust passes
separately. No fresh native evidence or nonempty-revert producer inferred.
All24 obligations/six full Source combinations/G01/compiler/world/V16 remain
pending; original five native journal FAILs, historical docs/G03 EXIT1 and
unanswered semantic holds remain unchanged. Exact sealed incremental handoff:
`/workspace/vy5-composition/return-consumer-20261102/final/`.

### VY5 actual unchecked/while constructors (2026-11-02)

The [VY5 lane](inline-assembly-vy5.md#actual-unchecked-and-while-constructors-2026-11-02)
adds24 selected Source kernel component laws: actual unchecked alias/rethrow,
normal scope restoration/rest under original frame, actual false/true while,
break and all-horizon literal-true/continue timeout. Existing represented source
state/raw companion and journals are retained explicitly, not a new rollback.
44ordered actual Source cases/two pipelines match a pre-execution frozen oracle;
56script mutation/receipt tests pass. Correct complete-input joint gate EXIT0
includes KeySort, full1284/TestSuite262, signatures/axioms/strict/trust. No native
execution or frozen unchecked-add decision. All24 ORIGINAL full obligations and
six general Source combinations remain pending; five original native journal
FAILs and historical docs/G03 EXIT1 remain unchanged. Immutable handoff:
`/workspace/vy5-composition/unchecked-loop-20261102/final/`.

### VY5 actual Source for-loop (2026-11-02)

The [VY5 lane](inline-assembly-vy5.md#actual-source-for-loop-composition-2026-11-02)
adds30 selected actual Source.forLoop/forIter component laws: typed init/false
scope exit, full-byte rethrow/post/rest suppression, real break/bodytail versus
AFTER-loop rest, actual continue/post bool changes/next test and all-horizon
missing-post timeout. Old raw callers/journals remain explicit companions.
56ordered Source cases/two pipelines and72script mutation/receipt tests pass;
ZERO new native comparisons. Private joint KeySort/full1285/TestSuite262/scoped
axioms/strict/complete-trust EXIT0. All24 ORIGINAL full obligations/six general
Source combinations and missing raw/selector/producer/G01/compiler/world/V16
adequacy stay pending; original native5FAILs/docs/G03 EXIT1 and semantic holds
unchanged. Immutable reviewed incremental handoff:
`/workspace/vy5-composition/for-loop-20261102/final/`.


VY5 (2026-11-02): selected actual ordinary nonempty CALL/STATICCALL failure now
composes through full-byte decoding, heap allocation and typed alias rethrow,
with actual refusal/timeout/copy controls. 29 component laws,30 ordered Source
cases,107 tests; no fresh native comparisons. All24 original obligations/six
general combinations remain pending. See [lane handoff](inline-assembly-vy5.md#vy5-selected-ordinary-failure-consumer-2026-11-02)
and `/workspace/vy5-composition/failure-consumer-20261102/final/` for exact
producer premises, source hashes, failed diagnostics and sealed evidence.


VY5 (2026-11-02): actual Source doWhile body-first, normal scope restoration,
break/continue/return and timeout consumers add20 component laws,50 ordered
Source cases and74 mutation tests. No fresh native comparison; all24 original
obligations/six full combinations stay pending. See [lane handoff](inline-assembly-vy5.md#vy5-actual-source-dowhile-consumer-2026-11-02)
and `/workspace/vy5-composition/do-while-20261102/final/` for exact premises,
source signatures, resource receipts and retained failures.


VY5 (2026-11-02): the earlier real ModifierPhysical placeholder branch was
already complete. New actual bytes-parameter/alias/postlude consumer adds37
component facts,48 ordered Source cases and80 mutation tests, distinguishing
normal/return postludes from body-revert suppression. Native comparisons0; all24
original obligations/six combinations pending. See [lane handoff](inline-assembly-vy5.md#vy5-actual-modifier-argument-and-postlude-consumer-2026-11-02)
and `/workspace/vy5-composition/modifier-post-20261102/final/`.


VY5 (2026-11-02): H1 cleanup resolves disk admission (99own exited containers;
commits/latest handoffs/data retained;4GiBOSreserve/12GiBcap/no swap). H3 reviewed
pinned per-pipeline trace contract passes fresh36calls/4profiles/20Sourcebyte
projections/8intended negatives and175tests. Original strict report remains
FAILED, unchanged. All24original/six full combinations pending. See
[lane handoff](inline-assembly-vy5.md#vy5-h1-resource-recovery-and-h3-per-pipeline-traces-2026-11-02)
and `/workspace/vy5-composition/pipeline-contract-20261102/final-v2/`.


VY5 (2026-11-02): actual nested modifier/placeholder composition adds23component
facts,78ordered Source cases and91tests, with complete caller/raw/journal
retention and late-timeout frame restoration. Native comparisons0; all24original
obligations/six general combinations pending. H3LIB1/unchecked decisions are
answered; VY1 committed inputs still required, no re-ask/duplicate implementation.
See [lane handoff](inline-assembly-vy5.md#vy5-actual-nested-modifiers-and-answered-vy1-h3-inputs-2026-11-02)
and `/workspace/vy5-composition/nested-modifier-20261102/final/`.


VY5 (2026-11-02): actual represented write→indexed caller-local Source.emit→
pre-write outer rollback adds31 component facts, real full heap/log agreement,
three-journal restoration and operational wrong-owner/slot/encoding/mark controls.
Private joint gate EXIT0;35 new receipt mutation tests/92 relevant regressions;
no new native comparisons. All24 original obligations/six full combinations remain
pending. Remaining ready-input audit is blocked on explicit producer contracts,
not whole-lane publication. See [lane handoff](inline-assembly-vy5.md#vy5-indexed-write-and-emit-2026-11-02)
and `/workspace/vy5-composition/indexed-write-20261102/final/`.
VY5 moved to a Claude VM (2026-11-05, H37). The lane was merged with master.
MonetaryLifecycleControls and `Monetary.wide` are in no ref on origin (checked 2026-11-05), so they stay
out of this checkpoint. Three modules that import unpublished VY4 producers are
held outside the library. See [the lane handoff](inline-assembly-vy5.md#move-to-a-claude-vm-2026-11-05-h37).
VY5 consumer checkpoint: actual published Source try/catch bytes allocation
and canonical rethrow are composed with complete-state/all-byte/horizon≥3
kernel laws in `Yul/Composition/SourceCatchBinding.lean`. See
[the lane record](vy5-composition.md). This is not general Yul/compiler
adequacy or native execution; the24 full obligations/six combinations stay open.

VY5/H16 producer checkpoint: actual scheduled Source root dispatch, rollback,
full-state/error-byte controls and measured legacy-path preservation; see
[the lane record](vy5-composition.md). General assembly and P8 closure remain open.

VY5 H16 request-admission child: rebased on published6f3eedf0; actual
requestValueScope reuses unchanged requestScope with exact-Nat sender-value
admission, four general/preservation laws and eleven full-state controls.
Checkpoint at674cc1797b911fbf5bf3d626cc4a44e2af949ec1 passes library3359,
trust/layers/roots/doc-paths/axiom-pins and strict classification. V17 WhileReturn
needs only one proof-side legacy None disambiguation. Evidence/interface:
`/workspace/vy5-composition/request-admission-20261104/final`. The held
factored-core timing candidate is not landed. H16 session/P8, H19 and all24/six
remain open; no new native evidence or full-lane/runtime-gate pass.

VY5 H16 no-cut primitive child: eight cursor/check laws, one actual emitter
execution law and eleven complete-state/negative controls;21 exact axiom
guards. Checkpoint at6889b6dc686f15492df703e5b550614505bc3898 passes
library3362, strict classification and all checkpoint static gates. Structural
CutFree is an explicit real premise; NoFail plan alone is insufficient on
arbitrary cursors. Existing evaluator/cursor bodies unchanged. Interface and
receipts: `/workspace/vy5-composition/no-cuts-20261104/final`. Full Source
coherence/NoFail/session/P8, H19 and all24/six remain open. No native pass.
