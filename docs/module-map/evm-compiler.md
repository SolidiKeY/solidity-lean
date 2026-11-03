# The EVM compiler

`docs/compiler-verification.md` has the theorem, the fragment and what is out.

| Module | What it defines |
|---|---|
| `Evm/Machine.lean` | A straight-line EVM: slots as terms, wrapping words, a bounded `WordStore` (`Slot → Fin (2^256)`, numeric reads, normalized writes), relative forward jumps, the accounts' balances; memory addressed by level (`Nat`). |
| `Evm/Memory.lean` | Literal-base and runtime-pointer primitive-array access code and a bounded representation of actual typed heap objects; exact reads, writes and out-of-bounds reversion. |
| `Evm/MemoryStruct.lean` | One-word member offsets for memory structs, typed primitive-field representations with no-wrap bounds and no length header, exact runtime-pointer read/write instructions and same-object field preservation. |
| `Evm/MemoryStructHeap.lean` | Global struct identity bases, struct/local/array interval separation, and both directions of struct/array write framing. |
| `Evm/MemoryStructAlloc.lean` | Allocator ownership of live struct intervals in addition to arrays; cursor, zero-tail, separation and both layouts preserved by local, struct-field and array-element writes. |
| `Evm/MemoryStructGrow.lean` | Combined struct/array ownership across typed allocations; exact headerless struct allocation, primitive default fields, fresh/older interval separation, retained old addresses and cursor/zero-tail growth. |
| `Evm/MemoryStructExamples.lean` | Populated mixed struct/array allocator and public compiler witnesses: alias declaration/rebinding, fields, scopes, arrays and later allocation; signed field reads, old-reference reuse, reserved-cell/no-wrap checks, exact RHS failure and the array-only ownership counterexample. |
| `Evm/MemoryHeap.lean` | Global object-identity bases, separated primitive-array regions above reserved local frames, preservation by heap and local writes. |
| `Evm/MemoryAllocExamples.lean` | Inhabited allocator, nonzero old array, repeated typed allocations, reserved-cell preservation, old-alias reads and empty-array bounds checks. |
| `Evm/MemoryAlloc.lean` | Checked bump-allocation instructions, cursor/zero-tail invariants, actual fresh typed arrays, and global heap/address-map preservation across allocation, local writes and heap writes. |
| `Evm/MemoryAllocSource.lean` | Primitive `new T[](n)` source-copy, declaration and allocating-rebinding equivalence; exact simulation with grown addresses, retained old pointers and allocator invariants. |
| `Evm/MemoryAllocSourceExamples.lean` | Inhabited public allocation/rebinding, deletion, increments/decrements, captured results and scopes: aliases, retained objects, typed defaults, repeated empty deletion, bounds failures, both branches, escaped pointers, reused locals, temporary frame rejection, skipped maximal requests and failed conditions. |
| `Evm/MemoryGrowResult.lean` | Extended address-map results preserving older typed identities, exact allocator/cursor growth and reached-capacity input composition through zero-cost and allocating statements. |
| `Evm/MemoryScope.lean` | Scope exit retains heap objects and older locals at their runtime levels; branch joins weaken the core alias flags by their meet. |
| `Evm/MemorySource.lean` | The core simulation augmented by pointers at all memory-local reference types, separated struct/array heaps, cross-separation and typed reference-member words; array reads/writes and local assignments preserve the shared state and combined allocator. |
| `Evm/MemoryRefs.lean` | Typed reference-member words under the shared identity map, preserved across locals, primitive/array writes and non-reference-bearing allocation; exact pointer reads. |
| `Evm/MemoryRefArray.lean` | Dynamic reference-element words, checked local reads/writes, global interval ownership and parent-pointer framing. |
| `Evm/MemoryRefArrayState.lean` | Supplementary reference-array state relation; retained locals, primitive child writes and parent redirection. |
| `Evm/MemoryRefArrayPaths.lean` | Fallible typed reference paths with genuine indexed bounds reverts. |
| `Evm/MemoryRefArrayStatements.lean` | Source alias rebinding and reference/primitive indexed assignment simulations. |
| `Evm/MemoryRefArrayCompile.lean` | Narrow certified nonallocating reference-array program compiler and composition theorem. |
| `Evm/MemoryRefArrayExamples.lean` | Inhabited dynamic alias input/observations, bounds and corrupt-pointer refutation; additive constructor/fixed registration controls. |
| `Evm/MemoryObjects.lean` | Typed value words and complete positive ownership for dynamic/fixed arrays, structs and reference fields. |
| `Evm/MemoryObjectAccess.lean` | Headerless fixed bounds and generic primitive/reference indexed read/write simulations. |
| `Evm/MemoryObjectFrame.lean` | All-object separation, identity injectivity, element/local write framing. |
| `Evm/MemoryObjectAllocator.lean` | Complete live intervals, projected legacy allocator and cursor/free-tail preservation. |
| `Evm/MemoryObjectPaths.lean` | Fallible typed local/field/dynamic/fixed pointer paths and primitive reads. |
| `Evm/MemoryObjectExpr.lean` | Expression composition over full ownership, sharing existing arithmetic tails. |
| `Evm/MemoryObjectValues.lean` | Certified primitive reads and expressions through either array layout. |
| `Evm/MemoryObjectStatements.lean` | Generic typed indexed stores and local/alias statements preserving the complete allocator. |
| `Evm/MemoryObjectCompile.lean` | Narrow full-object certificate compiler and sequence correctness. |
| `Evm/MemoryObjectGrow.lean` | Typed array adoption and old-child pointer preservation across actual source heap growth. |
| `Evm/MemoryObjectEmpty.lean` | Actual empty default/literal-zero source copying, scoped declarations/rebinding and complete allocator simulation. |
| `Evm/MemoryObjectArrayExamples.lean` | Inhabited fixed-parent/dynamic-child public inputs, reads, alias changes, bounds and allocator controls. |
| `Evm/MemoryFixedChildArrayExamples.lean` | Inhabited headerless primitive children, fixed reference parents, aliases, reads and bounds controls. |
| `Evm/MemoryObjectReserve.lean` | Parent gaps, raw pointer-write framing and late typed parent adoption. |
| `Evm/MemoryObjectChildLoop.lean` | Concrete target condition/body steps for distinct default children. |
| `Evm/MemoryObjectChildrenCopy.lean` | Actual source default-child fold and distinct appended identities. |
| `Evm/MemoryObjectChildrenSim.lean` | Finite k+1-turn loop simulation, pointer segment, complete allocator and retained memory. |
| `Evm/MemoryObjectNested.lean` | Actual runtime-length nested-array source copying and parent/child layout simulation. |
| `Evm/MemoryObjectConstructionSource.lean` | Scoped nested allocation/rebinding and generic grown-state pointer preservation. |
| `Evm/MemoryObjectPrimitive.lean` | Existing primitive array allocation under complete reference/fixed object ownership. |
| `Evm/MemoryObjectAllocationCost.lean` | Source-computed reached construction cost and growing results; nonallocating suffix fast path. |
| `Evm/MemoryObjectConstructionCompile.lean` | Certified linear constructor composition with exact parent/child capacity. |
| `Evm/MemoryObjectFlatStruct.lean` | Complete ownership and actual primitive-struct source defaults. |
| `Evm/MemoryObjectFlatFixed.lean` | Actual headerless primitive fixed defaults and allocator layout. |
| `Evm/MemoryDefaultBuilder.lean` | Type-indexed source default/cost/identity certificates. |
| `Evm/MemoryDefaultChildren.lean` | Actual typed default-copy fold and generic target child steps. |
| `Evm/MemoryDefaultChildrenSim.lean` | Finite generic child-loop simulation preserving pending parent gaps. |
| `Evm/MemoryDefaultArraySource.lean` | Actual dynamic/fixed reference-parent source copy equations. |
| `Evm/MemoryDefaultParent.lean` | Shared complete ownership for typed default parent adoption. |
| `Evm/MemoryDefaultFixedBuilder.lean` | Recursively composed fixed reference defaults with exact cost. |
| `Evm/MemoryDefaultDynamic.lean` | Runtime-length arrays of certified reference child defaults. |
| `Evm/MemoryDefaultCompile.lean` | Structural type-directed default compilation and reference-struct refusal. |
| `Evm/MemoryObjectFieldFrame.lean` | Primitive struct updates frame all fixed/dynamic/reference arrays. |
| `Evm/MemoryReferenceDefaultSource.lean` | Scoped public generic default/allocation/rebinding simulation. |
| `Evm/MemoryPrimitiveStructArrayDefaultExamples.lean` | Inhabited Box[] alias/default source and target results and bounds. |
| `Evm/MemoryFixedDefaultExamples.lean` | Fixed-parent/fixed-child default aliases and bounds. |
| `Evm/MemoryDynamicFixedDefaultExamples.lean` | Nonempty runtime fixed-child arrays and exact capacity controls. |
| `Evm/MemoryNestedFixedDefaultExamples.lean` | Finite nested fixed reference defaults and retained aliases. |
| `Evm/MemoryReferenceArrayRebindExamples.lean` | Allocating fixed-child array rebinding preserves old aliases. |
| `Evm/MemoryFixedDynamicDefaultExamples.lean` | Fixed parent of empty dynamic children with redirected aliases. |
| `Evm/MemoryObjectConstructionExamples.lean` | Source-spliced inhabited public constructors/rebinding, actual results, distinct defaults, bounds and capacity controls. |
| `Evm/MemoryStructArrayInputExamples.lean` | Populated reference-bearing struct-array input, actual RefFieldsRepr aliases/writes/bounds and constructor refusal. |
| `Evm/MemoryPaths.lean` | Structurally compiled typed local/reference-field paths with exact pointer simulation, nested primitive-field/array reads, lengths and writes with exact RHS/bounds failures, and child aliases/rebinding. |
| `Evm/MemoryRefDelete.lean` | Fresh default primitive-array/primitive-member-struct children installed after resolving a reference-valued parent field; exact source growth, retained old aliases, target stack order, ownership and cursor simulation. |
| `Evm/MemoryRefWrite.lean` | Reference-valued struct-field assignment updates the actual typed child identity and pointer word, preserving primitive data, mixed heap ownership, local frames and allocator state without allocation/copying. |
| `Evm/MemoryPathExamples.lean` | Populated wrapper/holder/leaf/array pointer-word and ownership witnesses, public nested reads, primitive/reference writes, child redirection/restoration, repeated/scoped reference-member deletion, compound/standalone bumps across scopes/allocation, exact cursor/content observations and wrong-pointer/bounds/arithmetic failures. |
| `Evm/MemoryStructSource.lean` | Typed source struct-field reads/writes through local pointers, with exact instruction simulation and shared heap, aliases, local frame and combined allocator preservation. |
| `Evm/MemoryStructDefault.lean` | Primitive-member classification, exact default-copy/declaration/deletion source growth, headerless struct allocation and pointer binding and allocating local deletion; empty model layouts reserve a padding cell so every allocation requires an allocator. |
| `Evm/MemoryStructDefaultExamples.lean` | Ordinary positional/named constructors, allocating rebinding, repeated/scoped/conditional whole-local deletion, default primitive arrays, primitive field deletion, compound updates and bump captures, with aliases, signed values and mixed arrays; inhabited public agreement, source/target observations, seven arithmetic failures, capacity/reverted-prefix and model-only empty-layout checks. |
| `Evm/MemoryStructCopy.lean` | Primitive-member storage copies preserve actual typed fields, allocate one fresh object, weaken locals and retain old heap objects; exact RHS/declaration/rebinding source equations. |
| `Evm/MemoryStructCopyCode.lean` | Checked storage-root member-load plans and emitted initialization stores, preserving arbitrary caller stacks, outside cells and the actual copied field representation. |
| `Evm/MemoryStructCopyAlloc.lean` | Populated primitive-struct reservation preserves the complete state, old arrays/structs/reference words, separated intervals, frame and allocator from explicit fresh-region and tail facts. |
| `Evm/MemoryStructCopySource.lean` | Exact storage-root copy body, declaration and allocating-rebinding simulation, connecting typed copied fields to loads, fresh allocation, initialization and pointer binding. |
| `Evm/MemoryStructCopyExamples.lean` | Ordinary populated storage-root struct copies and rebinding with retained aliases, independent signed/Boolean/unsigned data, scoped copies, deletion and later mixed arrays; inhabited public agreement, exact growth/contents, capacity refusal and unreached zero-capacity reversion. |
| `Evm/MemoryStructReferenceAlloc.lean` | Initialized reference-bearing parent reservation, retaining old objects, separated intervals and the zero tail. |
| `Evm/MemoryStructReferenceCode.lean` | Relative child-pointer initialization instructions and complete represented parent allocation. |
| `Evm/MemoryStructDefaultLayout.lean` | Finite default-layout specification and rank-bounded executable cost equivalence. |
| `Evm/MemoryStructDefaultPlan.lean` | Typed child-first recursive default allocation certificates, exact cost, base growth and source/target simulation. |
| `Evm/MemoryStructDefaultCode.lean` | Typed executable layout data and erasure, soundness and cost transport from certificates. |
| `Evm/MemoryStructDefaultSource.lean` | Finite default declaration and local/member deletion simulation with preserved aliases. |
| `Evm/MemoryStructArrayChild.lean` | Existing primitive dynamic-array allocation composed with struct-field initialization, respecting allocation-before-receiver evaluation. |
| `Evm/MemoryStructReferenceDefaultExamples.lean` | Inhabited nested finite-default compiler agreement, exact observations, failure and refusal controls. |
| `Evm/MemoryStructReferenceDefaultModes.lean` | Independent viaIR nested-default observations and inhabited public correctness. |
| `Evm/MemoryStructReferenceDefaultLiterals.lean` | Legacy/viaIR nested literals and allocating rebinding with retained default children and aliases. |
| `Evm/MemoryStructReferenceDefaultBoundaries.lean` | Finite member/local deletion, model-only empty children, invalid pointer words, capacity and unreached-allocation controls. |
| `Evm/MemoryLocals.lean` | Source/machine agreement for array lengths, typed memory alias rebinding/declarations, primitive declarations including defaults, and local assignments; preservation of both heaps under the reserved-frame bound. |
| `Evm/MemoryExpr.lean` | Compositional source/machine agreement for checked operators, short-circuit Boolean operators and conditional expressions with memory operands. |
| `Evm/MemoryStatements.lean` | Primitive storage writes and require guards preserve the full heap/pointer simulation; exact source/machine reversion. |
| `Evm/MemoryDelete.lean` | Primitive element deletion equals a typed default write; array-local deletion equals fresh empty rebinding and a default declaration equals empty allocation; checked index code preserves heap aliases and exact failure. |
| `Evm/MemoryCompound.lean` | Compound array/field/local updates and standalone prefix/postfix bumps equal checked binary writes; pure evaluator failures justify read reordering while preserving the complete typed result. |
| `Evm/MemoryCapture.lean` | Captured array/field/local prefix/postfix bump values, complete source-result equalities and a stack-preserving capture/step/store simulation; the final local store follows the bump, retaining old index reads and local self-assignment. |
| `Evm/MemoryStorageCopyCompile.lean` | Additive copy-bearing finite certificates, preserving the published copy-free finite compiler and loop/call proof interfaces. |
| `Evm/MemoryCompile.lean` | A memory compiler with erased fragment certificates: core/array/primitive-field values, nested reference-field paths for primitive reads/writes/deletion/updates and child aliases, typed memory aliases and reference-member assignment/default-child deletion, primitive-array allocation/default declarations/rebinding/deletion, finite nonrecursive struct construction/local and member deletion with nested struct/primitive-array children, primitive field deletion, compound/bump local/array/field updates, storage writes, guards, scopes and branches; reached costs bound allocations and peak contexts bound every temporary frame. |
| `Evm/MemoryLoop.lean` | Typed reached loop prefixes, exact allocation cost, source-prefix capacity, zero-cost and one-turn witnesses, unbounded memory-loop simulation and legacy refusal reproduction. |
| `Evm/MemoryLoopCompile.lean` | Sequential checked finite-body memory loops; typed cost/demand certificates, full body frame reservation, source-only capacity and exact growth composition, nonallocation and exhaustion controls. |
| `Evm/MemoryLoopExamples.lean`, `Evm/MemoryLoopAllocExamples.lean`, `Evm/MemoryLoopSourceExamples.lean` | Inhabited public inputs, both evaluators, aliases, zero turns, reverts, reached allocations, capacity/frame refusals, mathematical divergence and source legacy/viaIR array/struct loops. |
| `Evm/MemoryLoopScope.lean`, `Evm/MemoryLoopScopeMeta.lean`, `Evm/MemoryLoopScopeSound.lean`, `Evm/MemoryLoopScopeRoom.lean` | Typed enclosing block/conditional loop certificates, generalized recursor metadata with native equality links, full state/frame/allocation/halting simulation and inhabited nonallocation. |
| `Evm/MemoryLoopScopeDemand.lean`, `Evm/MemoryLoopScopeBudget.lean`, `Evm/MemoryLoopScopeCompile.lean` | Reached-demand/cost eliminators, selected-scope room and finite-prefix capacity bounds; checked scope compiler with kernel/native equality links and shared constructor equations. Loop bodies retain the existing finite certificate. |
| `Evm/MemoryLoopScopeExamples.lean`, `Evm/MemoryLoopScopeAllocExamples.lean`, `Evm/MemoryLoopScopeDivergenceExamples.lean`, `Evm/MemoryLoopScopeSourceExamples.lean` | Inhabited public source/target scope controls: zero/revert/refusal, arrays/structs, nontrivial local drop and retained heap growth, last-word allocation capacity, mathematical divergence and allocation before divergence, both source evaluation orders. |
| `Evm/MemoryCalls.lean` | Typed internal-call expansion certificates over the full memory relation: private frames, nested calls, primitive/pointer arguments, primitive returns and supported memory-reference export; reached allocator costs and source/machine simulation. |
| `Evm/MemoryCallExamples.lean` | Inhabited public call-compilation inputs, source/machine observations, alias/copy/rebinding and nested return controls, exact reverts, and frame/capacity/external/recursive/payment refusals. |
| `Evm/Compiler.lean` | A unified checked entry selecting the core, finite-memory, reference-array, object, construction, direct-loop, scoped-loop or internal memory-call compiler, with correlated code, input and output relations and one agreement theorem retaining each memory path's heap/pointer relation. |
| `Evm/MemoryCompileExamples.lean` | Populated source aliases and an independent array; compiled reads/writes, alias declarations/rebinding, lengths, defaults, composed RHS/index reads, public-entry dispatch, capacity and exact-revert regressions. |
| `Evm/MemoryExprExamples.lean` | Public-compiler source/target arithmetic, compound updates and all four standalone/captured bump forms, alias preservation, operand/range/divisor failures, short-circuit/conditional skips, guards and a storage/memory round trip. |
| `Evm/MemoryExamples.lean` | A populated typed-heap representation witness, checked reads/writes, shared-base visibility, frame/length preservation, boundary reversion and address-wrap rejection. |
| `Evm/Layout.lean` | The storage layout (`size`, `offset`, `rootSlot`), its injectivity (`Occ`, `occ_*_disjoint`), what `delete` clears (`leaves`), the fragment's operators (`binInFrag`, `unInFrag`) and static types (`static`), and solc's guard and code sequences (`uTail`, `sTail`, `expCode`, `boundsCheck`, `pushSlotCode`, …). |
| `Evm/StorageLemmas.lean` | The typed storage read along a path, for the simulation: a live read below a path (`findLiveM_append`), a live read is a read (`findM_of_findLiveM`), the reads and index checks of a reference's member, key and element (`Sto.findLive_field` …, `Sto.checkIndex_dyn` …), a default's members below a rank (`get_dfltBelow`; at full rank `SFields.dflt_get`, `Theory/Typed/Obs.lean`). |
| `Evm/Repr.lean` | The representation of the typed storage: `ReprV` (a word represents a typed primitive), `ReprAt` over `SVal T`, `ReprStore`, `PathAt`/`PathSlot` over typed paths and `SRef`s; `find_repr`, `save_repr`, `zero_repr`, `pop_repr`, `move_repr`, `overlay_repr`, `push_repr`, `live_mono` (`OccAt`, `LenSlot`, `PrimSlot`), `initStorage_repr`. |
| `Evm/Signed.lean` | The signed guard sequences, exact on two's complement. |
| `Evm/Exp.lean` | `**`: solc's `checked_exp_unsigned`, unrolled. |
| `Evm/SimLemmas.lean` | The machine lemmas of the simulation: the guard sequences computed (`add_tail`, …), the operators' tails on the typed operators (`tail_simT` from `utail_simT` and its signed half `stail_simT`, `neg_simT`, `bnot_simT`, `compound_simT`, `bump_simT`: `BinOp.evalT`'s integer result and `PrimTy.ofInt?`'s range check against the guard's word), `ValOutT`, the slot sequences (`boundsCheck_run`, `elemSlot_run`), `EnvSim` over `TTx`, `netAt`, the store sequences (`zeroCode_run`, `popCode_run`, `storeLeaves_run`, `pushSlotCode_run`), `push_eq`, `write_ref`. |
| `Evm/Compile.lean` | The compiler over the scoped syntax (M5, `docs/intrinsic.md`): a local at its level (`cell`, `lvl`), a call's body in its own frame, the fragment `inFrag` over `Frag Γ` (alias flags only), `Stmt.pushes`, `Stmt.pays`. |
| `Evm/Examples.lean` | Programs of `StandardExample`, `CallsExample` and `TestSuite` (`Evm.Examples.setAge` …), scoped blocks compiled by `Evm/Compile.lean`, run by `decide +kernel`. |
| `Evm/Sim.lean` | The simulation over the scoped syntax: `SimL` of a global part (`State C []`) and the locals by position, typed (`Look C Γ`, `Seen`: a value, an alias's `SRef`; `Look.ofTEnv`), declarations as `Look.cons` (`SimL.consVal`/`consAlias`/`consFragile`/`consDead`), a scope's end as `SimL.drop`, the fragment's flags (`SimL.flags`, `meet`, `storeDrop`), a call's frame (`SimL.enter`, `SimL.return`); `Sim C L b F σ m` of a typed state; compiled code at base `b` stores to no level below `b` (`storesFrom_compileStmt`, `storesFrom_callFrame`, `exec_mem`). |
| `Evm/Expr.lean` | The expression lemmas over the typed run: `LocOutT` over the typed storage, `simple_sim`, `spath_sim`, `loc_sim`, `val_sim`. |
| `Evm/Stmt.lean` | One lemma per statement of the fragment over the typed run, a storage write the typed save (`save_repr`): `StmtOut` (with `Keeps`: cells below the frame, array lengths), `assign_sim` … `transfer_sim`. |
| `Evm/Correct.lean` | `stmt_sim`/`prog_sim` over the scoped syntax and `Prog.run` (within `maxHeartbeats 11000`) (one lemma per family, `ite_sim`, `block_sim`, `callNone_sim`/`callVal_sim`), then `compile_correct`, `compile_exact`, `compile_box`, `compile_net`, `compile_storage`; no `not_stuck` (no stuck outcome). |
| `Evm/Interpreter.lean` | The compiler's interpreter theorems over `Prog.run` (`setAge_interpreter`, `overflow_interpreter`, `payOwner_interpreter`, `callTwice_interpreter`), from `Evm/Examples.lean`'s machine runs. |
| `Backend/Opcode.lean` | The backend's target (G45.05, [backend-assembler.md](../feature-work/backend-assembler.md)): every Osaka opcode (`Op`, with `CLZ`, `TLOAD`/`TSTORE`, `MCOPY`; `DUP`/`SWAP`/`LOG` indexed by `Fin`), `Instr` with `PUSHn` immediates of exactly `n` bytes, `encode`/`decode` (`decode_encode`, `encode_injective`, `encode_decode`). |
| `Backend/Jumpdest.lean` | Jump-destination analysis on any bytes (`starts`, `jumpdests`, `validJumpdest`, `InPushData`): valid iff `JUMPDEST` outside push data (`validJumpdest_iff`, `mem_starts`), and on encoded programs iff a `JUMPDEST` instruction sits at that offset (`validJumpdest_encode_iff`, `starts_encode_append`). |
| `Backend/Assembler.lean` | The assembler (G45.04): solc-style items (`tag`, `pushTag`, `pushTagRel`, `pushLibraryAddress`), big-endian immediates (`toBytesBE`, `ofBytesBE`, `byteWidth`), per-label `PUSH` widths by a terminating fixpoint (`fixWidths`), `assemble` at a base offset with link references; every resolved jump reaches its label's `JUMPDEST` (`assemble_pushTag`), success (`assemble_isSome`), linking (`link_patch`). |
| `Backend/Control.lean` | G45.03 preparation: structured blocks (`code`, `seq`, `ite`, `loop`) expanded into assembler items with fresh `Nat` labels in solc's legacy shapes; each label defined once and every reference defined (`tags_nodup`, `refs_defined`), so assembly succeeds (`expand_assemble_isSome`); wherever a loop or `if` is placed, its backedge, exit and branch jumps push the offsets of its own labels (`loop_jumps`, `ite_jumps`). |
| `Backend/EvmVectors.lean` | Generated by `scripts/check-backend-vectors.mjs`: EthereumJS's Osaka opcode table, the vendored EVMYulLean `parseInstr`/`argOnNBytesOfInstr` table, 300 randomized jump-destination scans and 200 randomized encoded programs (EthereumJS's scan and `PUSH` values, transliterations of EVMYulLean's `D_J_aux` and `decode` immediate), each `#guard`ed against `byteName`, `immWidth`, `decode`/`encode` and `jumpdests`. |
| `Backend/Checks.lean` | Byte-encoding and assembler vectors (`#guard`) and the axiom pins of the encoder, decoder, jump-destination and assembler theorems. |
