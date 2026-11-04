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
