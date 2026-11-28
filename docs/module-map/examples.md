<!-- Generated from docs/module-map/examples.d/ by scripts/coord-tools/fragments.sh; edit the fragments there, not this file. -->
# Examples

Two directories, by proof style (`.claude/rules/derivations.md`).

`Examples/Chains/` — the calculus's worked examples, one file per section in
its order, each example a chain in its printed lines and fresh names, read by
the scoped calculus (`open scoped Solidity.Scoped`):

| Module | Its examples |
|---|---|
| `Examples/Chains/Storage.lean` | Storage writes and reads, roots, rebinding, index, `push`/`pop`, nonsimple paths, side effects in receiver and index. |
| `Examples/Chains/StorageArrays.lean`, `Examples/Chains/StorageDelete.lean` | The further storage array cases; storage `delete`. |
| `Examples/Chains/StorageCoverage.lean` | One chain per storage rule, from a concrete state. |
| `Examples/Chains/FixedLength.lean` | A fixed array's length: copied to a dynamic one (`fixedCopy`, `lenOnSaveFixedCopy`), deleted, an element pushed; each to `true` past the program but the push. |
| `Examples/Chains/Arithmetic.lean` | The compound storage update. |
| `Examples/Chains/Memory.lean`, `Examples/Chains/MemoryDelete.lean`, `Examples/Chains/MemoryArrays.lean` | Memory aliasing, writes and reads; memory `delete`; memory arrays. |
| `Examples/Chains/MemoryCoverage.lean` | One chain per memory rule, from a concrete state. |
| `Examples/Chains/StorageToMemory.lean`, `Examples/Chains/MemoryToStorage.lean` | The copies between the two, with lazy reads. |
| `Examples/Chains/Payment.lean` | `transfer` under the box: a literal amount, a nonsimple amount, a storage receiver. |
| `Examples/Tactics/CheckedBlock.lean` | `checked { … }`: an underflow refuted inside the block and valid outside it, what the block writes, guards discharged by the closer, `&&` and a loop's condition in evaluation order, a narrow type's `assert`; `ignoringOverflow { … }`: a diamond that holds only with the overflow assumed away. |
| `Examples/Tactics/Bytes.lean` | `bytesN`, `bytes` and `string` as solc runs them, on the elaborator's reading (`docs/semantic-gaps.md`, "Bytes and strings"): literals left-aligned, comparison, bitwise operators, indexing (out of range reverts), `.length`, conversions between sizes and to `uintM`, implicit widening; in state variables, mapping keys and values, parameters and returns. |
| `Examples/Tactics/Hashing.lean` | `keccak256` (one byte string hashed twice), `abi.encode`/`abi.encodePacked` layouts proved, `abi.decode`, the `concat`s and a dynamic encoding run (`#run`), a `mapping(string => uint)` keyed by the hash (`docs/semantic-gaps.md`, "Hashing and the ABI"). |
| `Examples/Tactics/HashingNames.lean` | `Names` (`mapping(string => uint) ids`), §3's contract of `Examples/Tactics/Hashing.lean`, light so that `Examples/DecisionHashes.lean` does not import the hashing examples. |
| `Examples/Tactics/AbiFeatures.lean` | Kernel ERC-7201/byte-roundtrip proofs, ABI layouts, type rejection and malformed decoder input regressions. |
| `Examples/Tactics/AbiFeaturesImport.lean` | Exact-solc-0.8.38 source fixture, namespace/ABI/recovery runs and a deliberately false assertion. |
| `Examples/Tactics/InheritedSelectorsImport.lean` | Exact-solc-0.8.38 fixture `tests/abi-0.8.38/InheritedSelectors.sol`: selectors, `abi.encodeCall` and external function values of overridden and inherited (renamed) functions, pinned; calls through external function values refused by name. |
| `Examples/Tactics/AbiHexCall.lean` | Exact-width source hex evidence, declaration-based encodeCall conversion, source execution/proof scripts and a false-property counterexample. |
| `Examples/Tactics/Recovery.lean` | Kernel generator/address reductions and valid/high-s/invalid/boundary recovery vectors. |
| `Examples/Tactics/RevertData.lean` | Revert data reaching a `catch` (`docs/semantic-gaps.md`, "Revert data"): a self-call's `require(false, "boom")` reason bound by `catch Error(string memory r)` and its bytes proved, two reasons over-approximated, `catch (bytes memory d)`, the run on a concrete state, `catchDataBox` pinned; a custom error of a symbolic argument (`symbolicCustom`, data known in part) and another contract's reason (`externalReason`, `Fml.allocAll`). |
| `Examples/Tactics/RevertFormulas.lean` | Revert data read in formulas (`dl!{ φ ↯ ψ }`): printers pinned, `revert(hex…)` reverting with `Error("boom")`, a top-level string reason reverting with no data, negative controls. |
| `Examples/Tactics/ComputedRevert.lean` | Exact execution certificates for computed reasons, alias writes, empty payloads and eager require arguments; nested catch executable guards and rejected assembly imports. |
| `Examples/Tactics/FunctionTypes.lean` | Internal function types on the elaborator's reading (`docs/semantic-gaps.md`, "Function types"): a value is its function's tag, a call through it a dispatch over the functions of its signature; in locals, parameters, returns, state variables and struct members; reference arguments (memory/storage arrays, nonrecursive structs) dispatched by reference with aliasing runs; tuple assignments with several value returns and struct memory returns through function values, non-name callees included; an unassigned value reverts when called, `delete`, `==`; external address/selector projection, guarded cancellation and overflow-rejection regressions. |
| `Examples/Tactics/MemoryReturns.lean` | Several returns with memory ones (`CallRet.rets`, `RetBinders.snocMem`): kernel-checked runs of a value and a memory return, two memory returns with aliasing of a returned parameter, the unassigned default, a rebound target, two fresh objects, `bytes memory`, an omitted target, a narrow element, the same through function values named and not (`fnTupleDispatch`), two calculus proofs of the value target, the printed program; storage returns among several, a target of another element width, a mismatched return location and a narrow element through a function value refused. |
| `Examples/Tactics/CleanTail.lean` | Dirty array tails (O6): `Tokens.dangling` reachable and not clean, a push recycling a dirty slot (`reused_slot_retains_value`), runs that repair it, and the boundaries refuted (`leaveDirty_boundary_rejected`, `interruptRepair_callback_boundary_rejected`). |
| `Examples/Tactics/Assumptions.lean` | Assumption records and policies (O10, O13): `pushRead` under `ValidA` with clean tails and refuted under `.solc`, `withdrawUnsafe` without and refuted with payment callbacks at one invariant, a legacy contract refuted under via-IR, policies refusing them (`pushRead_refused`, `withdrawUnsafe_refused`) and admitting by weakening (`solc_record_not_allowed`), the pinned profile and a via-IR profile that does not fit (`viaIR_profile_not_fits`, `legacy_record_not_valid_viaIR`), the CLI's small table (`table_verdicts`) and the exhaustive one read from `tests/cli/assumption-policies.txt` and checked against `Policy.verdict` (`checkLine`). |
| `Examples/Tactics/TailMode.lean` | The option of O6: `tokens.push()` read back proved under `ValidTail .clean` by `sol_prove` and `sol_decide` (`pushRead_clean`, `pushRead_clean_box`, `pushAlias_clean`), refuted under `.solc` at `Tokens.dangling` (`pushRead_solc_refuted`), and a dirty write of the program read back under either (`recycledWrite_solc`); as a contract's invariant (`Prog.exposesNone` decided, `pushRead_reachable`). |
| `Examples/Tactics/Reachable.lean` | O12's witnesses and controls. `Bag`, with a safe and a dirty interface: a recycled slot's default under `.reachable safeM` (`pushRead_validStart`) and the `withCallback` stub (`pushRead_withCallback`), refuted under `.any` at a non-entry dirty state, under the dirty interface (`dirty_refutes`) and under `Exec.top` (`top_refutes`); entry states after a commit and a rollback (`entry_after_add`, `entry_after_rollback`). `Counter`: the persistent invariant `x <= 10` by one box per entry gives `x != 11` (`never11`), not under `.any` (`never11_not_any`) or an interface adding `eleven()` (`eleven_refutes`); an entry state (`counter_entry`). |
| `Examples/Chains/CheckedArithmetic.lean`, `Examples/Chains/EvaluationOrder.lean` | Overflow reverts; the evaluation order of an indexed write. |

`Examples/Tactics/` — theorems `⊨ᶠ dl!{ … }` proved by `sol_symex; sol_close`
or `sol_decide`, derivations `⊢ φ` built one `apply` per taclet, and runs:

| Module | What it shows |
|---|---|
| `Examples/Tactics/Tour.lean` | The running example end to end. |
| `Examples/Tactics/PushReceiver.lean` | Kernel-checked primitive push binding execution, dirty-slot behavior and old-target-index positive/false cases; native capture rule-name pins in both modalities and a simple-alias update pin. |
| `Examples/Tactics/NewArrays.lean` | Kernel execution checks for fresh primitive and nested arrays, allocation-size effects and target evaluation order, with false-value and empty-read cases. |
| `Examples/Tactics/Aggregates.lean` | Inline common typing, snapshot timing, aliasing, tuple captures, negative admission and kernel execution checks. |
| `Examples/Tactics/AggregatesImport.lean` | Pinned Solidity 0.8.38 aggregate fixture, imported nonvacuity runs and a symbolic literal proof. |
| `Examples/Tactics/AggregateSlices.lean` | Stable slice identities, endpoint/index effects, binary schedules and catchable bounds panic. |
| `Examples/Tactics/SliceCopies.lean` | Primitive slice materialization, internal frames, returns, storage and hash consumers; finite execution certificates lifted to the unbounded run; readonly and shape refusals. |
| `Examples/Tactics/SliceCopiesImport.lean` | Pinned modern Solidity 0.8.38 source regression for slice copies, calldata locations and non-array aliases. |
| `Examples/Tactics/SliceReferenceCopies.lean` | Both-pipeline source certificates for fixed primitive-row slice copying, independent aliases, rebinding, widths, lazy branches, bounds and nominal refusals. |
| `Examples/Tactics/StorageSteps.lean` | One storage statement form at a time, as `apply` walks. |
| `Examples/Tactics/StorageSuite.lean`, `Examples/Tactics/StorageDelete.lean`, `Examples/Tactics/LedgerDelete.lean` | solkey's taclet suite on storage; `delete`; a struct holding a mapping deleted. |
| `Examples/Tactics/Branch.lean`, `Examples/Tactics/Revert.lean` | Two-goal splits; box and diamond on `revert`, `require`, `assert` (a check: `[ assert(false); ] true` is not valid). |
| `Examples/Tactics/Join.lean` | The join after a conditional (`ifElseJoin`): `n` sequential `if (c) { x = x + 1; }` in `5n + 3` nodes and one leaf, pinned; the M6 family proved. |
| `Examples/Tactics/LoopNotices.lean` | Located literal-loop warnings with annotation/nesting/callee/import controls and unchanged diamond-result/refutation certificates; a pinned constructor-only source fixture. |
| `Examples/Tactics/JoinControls.lean` | Conditional-term notation, lazy branch evaluation, signed-offset reader controls and inhabited false bounds (AU03). |
| `Examples/Tactics/LongContext.lean` | Kernel long-array certificate with a supplied local in a nonempty peeled context; true supplied-candidate and missing-argument refusal controls. |
| `Examples/Tactics/PolySize.lean` | The size of symbolic execution (`docs/automation.md`, M8): `#proof_size` (nodes, branches, open goals, the largest leaf in `Fml.tmSize`) of sequential `if`s that both assign, literal-bounded loops under their invariants, and the two combined, pinned for small `k`. |
| `Examples/Tactics/CallSummary.lean` | A call by its callee's summary (`internalCallSummary`): the family `f₀(x) = x + 1`, `fₖ(x) = fₖ₋₁(fₖ₋₁(x))`, its walk pinned (one node per call, where inlining made `7·2^(k+1) − 3`), proved for `k = 1…6`; a callee whose body drops an owed value is inlined; the checked family `f₀(x) = x * 3` proved for `k = 1…5`, its leaf one call site at a time (`Calculus/LeafShare.lean`), a false leaf failing within the heartbeats, and the leaf of sixteen products evaluated whole (`triplingFourWhole`). |
| `Examples/Tactics/Payment.lean`, `Examples/Tactics/Net.lean` | `transfer` and `send` as `⊢` walks with checked sequents; the frame, the ledger's postconditions and the runs, a refused send's included. |
| `Examples/Tactics/Values.lean`, `Examples/Tactics/Operators.lean`, `Examples/Tactics/Checked.lean` | Operators, checked arithmetic, `−−`, bitwise, shifts, `unchecked`, `uint8` … `int248`, casts. |
| `Examples/Tactics/LocalBindings.lean` | Binding-local width/ABI metadata under shadowing, captures and parallel updates; nearest-binding refinement and metadata-independent formula binders. |
| `Examples/Tactics/Calls.lean`, `Examples/Tactics/CallOperands.lean`, `Examples/Tactics/Callback.lean`, `Examples/Tactics/TryCatch.lean`, `Examples/Tactics/Contracts.lean` | Internal calls, call-valued operands, callbacks (`ProvesC`), `try`/`catch`, calls by contract (`useContract`). |
| `Examples/Tactics/CallerModel.lean` | The caller-model lattice is strict (O11), one `Reentry` `setX` guarded by `locked`: `exit_none`/`exit_staticOnly` (the invariant owed on exit), `open_staticOnly`/`open_setX` (the lock free), `lock_setX`/`lock_any` (the lock taken); the lock judgment `setX_guards`, `setX_reachAny`; `lock_staticOnly` by `ValidM.weaken`. |
| `Examples/Tactics/CallExceptions.lean` | Source positive/negative regressions for eager error operands, failure priority, exact enum/unset-function panic payloads and rollback; ordinary and symbolic catch proofs plus admitted-state unset-alias counterexamples. |
| `Examples/Tactics/Recursion.lean` | Recursive functions (`Stmt.callRec`): a countdown, a recursive sum and two mutually recursive functions elaborated and run (`decide +kernel`); the countdown's box without panic and `add(x, y) == x + y` by contract, proved by induction over the frames (`rec_contract_by`, `RecContract.unroll`, `sol_symex_rec`); under the callback reading, a countdown after a value call and a recursion that calls back (`rec_auto_c`, `ProvesC.recContract`). |
| `Examples/Tactics/SelfCall.lean` | A `try` of the contract itself (`tryCallSelfBox`): the callee's writes and return seen on success, refuted under the oracle reading by a typed run; no code at address `0`. |
| `Examples/Tactics/Constructors.lean` | A deployment: `constructor(args);` with initializers, `Contract.deployT`, `#deploy`, and solkey's `{storage := mtSt ‖ …}` start closed by `sol_close_mt`; the obligations `problem!{constructor}` and `spec!{constructor}` (solkey's `Counter.sol`, `\old(net(a))` of `oldNet := mtSt`), the refusals, the initializer/modifier order, and what `sol_close_mt` leaves open. |
| `Examples/Tactics/Lifetime.lean` | Escrow lifetime safety, concrete payment/refund witnesses and persistent settlement possibility; rollback, time, payment, fresh-memory, exhaustion and failed-deployment regressions. |
| `Examples/Tactics/ContractWorld.lean` | Explicit factory, instance identity, funding, rollback, catch boundary and linked-context regressions for the typed world API. |
| `Examples/Tactics/ContractWorldSource.lean` | Restricted complete source new/try-new and linked storage-field mutation fragments, with environment-admission and positive/negative regressions. |
| `Examples/Tactics/TransientWorld.lean` | Kernel controls for delegate-owned transient cells, distinct instances, transaction reset and rollback of successful descendants. |
| `Examples/Tactics/TransientWorldSource.lean` | Both-pipeline closed transient factory targets composed as typed frames: owner isolation, dirty-entry/exit reset, caught/uncaught and later rollback, static refusals, source false controls and axiom audits. |
| `Examples/Tactics/Memory.lean`, `Examples/Tactics/CrossDomain.lean`, `Examples/Tactics/Theory.lean` | Memory, storage↔memory copies, the theory's rewriting. |
| `Examples/Tactics/SelectOnSaveConsr.lean` | Reading a write back through a `consr` path, by hand and in solkey's order. |
| `Examples/Tactics/Dangling.lean` | Historical dangling-resurrection formulas, refuted by kernel-checked initial-state counterexamples after the resetting-push migration; longer rounds retain storage-stack capacity regressions. |
| `Examples/Tactics/NestedArrays.lean` | Concrete storage histories closed by `sol_prove` (solkey's `Array*` shapes): a fixed matrix's row alias, its checked indices folded; thirteen pushes after a delete, past `normalizationDepth`. |
| `Examples/Tactics/ApplySteps.lean`, `Examples/Tactics/UpdateRules.lean`, `Examples/Tactics/Decide.lean`, `Examples/Tactics/TermTaclets.lean` | The proof style, update simplification, `sol_decide`, term taclets. |
| `Examples/Tactics/UpdRulesScoped.lean` | The scoped update rules and merges (`Fml.updAtS`, `Fml.simpUpdsS`, `Fml.mergeAtS`) computed by the kernel on `dl!{ … }` leaves, each entry point (`Fml.Valid.of_simpUpdsS`, `Fml.Valid.of_updAtS`, `Fml.Valid.of_mergeAtS`) used on a `⊨ᶠ` goal; `applyOnRigid` under the diamond on an alias to a root's field; a rule refused under a negation, and `Upd.seqPar` refusing a memory term after a storage write that the storage merge reads. |
| `Examples/Tactics/Specs.lean` | Clauses as obligations (`spec!{f}`, `sol_spec`) beyond the benchmarks. |
| `Examples/Tactics/Loops.lean` | `while`, `for`, `do … while`, `break`, `continue`, `return` in a loop: the lowering's shapes pinned, `#run` of loops, a concrete loop decided with fuel (`Prog.runF_approx`); loops proved by unwinding (`whileUnwind`, `loopExit`), solkey's two solc loop ports among them; by an invariant (`whileInvariantBox`, `whileInvariantDiamond`): a counting loop, a sum with a closed form, a loop with `break`, a walk and its proof tree. |
| `Solkey/QuantifiedDiamond.lean` | Separately pinned legacy/viaIR scalar quantified-loop imports, all eight obligations retained. |
| `Examples/Tactics/QuantifiedDiamond.lean` | Quantified scalar diamonds, for/continue, nonempty and false quantified posts, concrete successful-run witnesses and imported divergence controls in both pipelines. |
| `Examples/Tactics/LoopsImport.lean` | Loops from solc's AST (`tests/solc/Loops.sol`): the `/// @custom:key` clauses `scripts/solc-ast.mjs` reads from the source by the loop's `src` offset, printed above the loop by the front end (a clause over several `///` lines joined, as solkey's `KeyNatspec`); a `return` inside a loop lowered on import; five of its seven obligations proved, the two not proved named with why. |
| `Examples/Tactics/AllLeftLater.lean` | Quantified premises at a later universal index, a program local and an anonymised invariant-loop counter, through the public strategy and closer; proved and unavailable guard cases. |
| `Examples/Tactics/ArrayScans.lean` | Pinned-solc unsigned and signed ABI array scans, later loop-counter instances, box safety and a diamond termination proof with a supplied variant. |
| `Examples/Tactics/Rigid.lean` | A memory-writing diamond loop proved by bounded rigid branch pruning; forty self-doublings refuse before exponential substitution, contradictory unused premises conservatively retain both branches, and a division-by-zero prefix stays invalid. |
| `Examples/Tactics/SymbolicCounterexample.lean` | Counterexamples past every storage the search builds: a counting loop over a `2^255`-element array run in closed form (`Prog.runA` against `Prog.runF`), refuted by `sol_refute` where it overflows and where it ends late; a true property of the same loop not refuted. |
| `Examples/Tactics/OpenLoops.lean` | The original pinned-solc open-loop source and its three-row nested-memory binomial; the retained nine-row obligation is in `Examples/Tactics/OpenLoops/RowsNine.lean`, in the H109 slow library. |
| `Examples/Tactics/Nonlinear.lean` | Symbolic/strict/coefficient multiplication order for both signs, four-variable product bounds, compound and difference squares, budget/noise regressions and checked Solidity multiplication order. |
| `Examples/Tactics/Symex.lean` | `symex` on three programs, checked by the kernel (`Eq.refl`), printed. |
| `Examples/Tactics/Step.lean` | The arms of `Stmt.step` by rule family (storage, memory structs and arrays, arrays of mapping-holding structs, operators, payments, loops, calls, `try`): each program's `symex` kernel-checked (`Eq.refl`). |
| `Examples/Tactics/Rules.lean` | `#rule_of` pinned: the scoped rule a statement fires (an update, a hole's unfolding, a write, a branch, `revert`, a block, a loop's unwinding and exit). |
| `Examples/Tactics/Print.lean` | The scoped taclets printed as their rule lines, a block's `}`, and the strategy's formulas printed from their `Expr` as `Fml.show` prints them (calls, `try`, `send`, a loop invariant); the `branches`/`cases`/`inv`/`inline` premises; `Proves` goals as sequents. |
| `Examples/Tactics/Notation.lean` | `cdl!{}` pinned: parameters, updates' targets, branch scopes, errors; `#wp`/`#step` on scoped formulas. |
| `Examples/Tactics/DlNotation.lean` | `dl!{}` pinned (moved out of `Calculus/SurfaceNotation.lean`): the scoped `Fml C []`, with or without a modality (`elabDlAuto`); captures, connectives, memory objects, `where`, `dl![m]{}`, Lean formulas, chain-only spellings. |
| `Examples/Tactics/Chains.lean` | Scoped chains pinned: a step, a named step, several, a rewrite past the program, a branch run into its `}`, the box; `#derivation`, `#chain` (pasted back and checked), `#chain_rest`, `#last_line`, a `FreshNames` table, a chain proving `Fml.Valid`, and the chains the tactics write on `dl!{ … }` read scoped (`sol_chain?`, `#chain`, `sol_rws?`). |
| `Examples/Tactics/Spec.lean` | `cspec!{f}` and `cproblem!{constructor}` pinned on a contract with snapshots and a result; the deployment's in solkey's syntax. |
| `Examples/Tactics/CallbackStrategy.lean` | The strategy with callbacks: `withdrawSafe`, a value call, a `try` with and without `noCallback`, a gas-limited send then a `try`, an `if` on a condition that is not a local, a loop unwound and a payment's operand captured where they call back (`ProvesC.capture`, `ProvesC.loopExit`), by `sol_prove`; `sol_derive?`'s walks pinned. |
| `Examples/Tactics/CallbackRuns.lean` | The typed callback reading used: the deterministic run of a program that pays is a callback run (`Prog.exec_run`), and every callback run of one that does not is its deterministic run, decided by the kernel (`ExecP.forall_iff`); a send's three goals under `ProvesC`. |
| `Examples/Tactics/Derive.lean` | The scoped strategy tools pinned: `sol_prove`, `sol_symex`/`sol_close`, `sol_derive?`'s walk (replayed) and `sol_derive` on `Fml.Valid` goals, `sol_derive` leaving the leaves; `sol_prove` and a walk under `⊢ₖ` (`rule_admits`), and `sol_prove` refusing `loopFalse` there while it proves it under `⊢`. |
| `Examples/Tactics/ProofTree.lean` | The proof tree of a scoped goal pinned: `#proof_tree`, `#proof_node`, `#proof_tree_json` on `cdl!{}`. |
| `Examples/Tactics/Surface.lean` | The switch `open scoped Solidity.Scoped` pinned: the same text read inside the scope and outside it; the callback taclets printed. |
| `Examples/Tactics/Sequents.lean` | Scoped walks with checked `show sequent!{ … }` lines. |
| `Examples/Tactics/SolSpec.lean` | `Examples/Tactics/Specs.lean`'s obligations scoped and proved by the same `sol_spec`. |
| `Examples/Tactics/Boundaries.lean` | Pins typed external inputs, bounded ledger keys, segment composition and EVM word storage (including rejected ill-typed terms). |
| `Examples/Tactics/PushSuffixRun.lean` | Checks the native typed primitive push suffix runs and two-stage agreement on empty and recycled slots. |
| `Examples/Tactics/PushSuffixGuards.lean` | Checks outer DIV/MOD guards, signed zero typing and guarded pair quotation across an intermediate context. |
| `Examples/Tactics/PushSuffixRules.lean` | Checks all nine native push suffix rule premises, primitive-binding receiver capture, both complex storage-source captures, memory copy, twenty-six typed text roundtrips and the SolKey admission boundary for RHS and receiver capture. |
| `Examples/Tactics/PushSuffixSource.lean` | Imports the pinned Solidity push suffix fixture and checks signed/unsigned execution, indexed receiver order, recycled slots and arithmetic failures. |
| `Examples/Tactics/PushSource.lean` | Imports ten compiled primitive/reference push-source functions and checks copy independence, source effects, invalid indices, fresh-shaped source names and numbered capture-chain replay. |
| `Examples/Tactics/MemoryPush.lean` | Imports nine compiled memory-push functions and checks independent array/struct copies, recycled slots, changing receivers, complex memory-source capture, false-postcondition panics and invalid-source reversion; it refutes the old receiver-duplicating expansion. |
| `Examples/Tactics/StorageReturns.lean` | Pins seventeen elaborated storage-return source rows, twelve execution outcomes, sixteen closed-program printer checks (eight programs through both printers) and eight open-tail prefix/continuation checks. Direct push/pop call receivers use native capture; the imported effectful receiver also closes by `sol_prove`. |
| `Examples/Tactics/DeferredSource.lean` | Checks twenty-one kernel execution outcomes for the deferred-operand foundation: getter order, prefix failures, snapshots, caller locals, memory growth and explicit capture. It does not enable native effectful call-receiver syntax. |
| `Examples/Tactics/DeferredCallback.lean` | Checks nine deferred-capture callback cases, including resumed storage changing the pushed value, violated invariants suppressing a bad source, getter failure ordering and heap growth retained after scope end. |
| `Examples/Tactics/CallbackWk.lean` | Checks callback weakening with a fresh unset alias: resumed storage and allocation survive, violations propagate, and a prefix's memory temporary is dropped while the new alias remains. |
| `Examples/Tactics/CallbackUnwk.lean` | Recovers four explicit weakened callback runs: a push reads resumed storage and retains an allocation, a broken invariant propagates, a paying loop allocates and exits on its changed guard, and prefix scope exit retains the allocation after removing the temporary. |
| `Examples/Tactics/DeferredCorrespondence.lean` | Checks direct-to-capture resumed storage and allocation, unset getter precedence, prefix violation before a bad source, capture-to-direct resume, and a reference operand copied from allocated memory with the getter run once. |
| `Examples/Tactics/NativeDeferred.lean` | Checks six ordinary native outcomes: increments, getter failure, allocation, combined heap growth, caller-local mutation and memory-reference copy. |
| `Examples/Tactics/NativeDeferredSource.lean` | Checks four source programs and both printer roundtrips for canonical increment and primitive-call operands, including private scope exit. Empty deferred prefixes and private-local dependencies retain explicit fallback rendering; arbitrary prefixes do not have a reconstructed Solidity-expression spelling. |
| `Examples/Tactics/NativeDeferredCallback.lean` | Checks resumed storage/allocation, unset getter precedence, callback violation before a bad source and a copied memory reference through native callback clauses. |
| `Examples/Tactics/Nonvacuity.lean` | A normally returning program's true result proved and false result refuted and unprovable; strict primitive capture realizability and delayed landed-binder macro regressions. |
| `Examples/Tactics/Latex.lean` | Both LaTeX backends pinned: formulas, judgements, line breaking, proved chains, a derivation with the filter, `tests/solc/FixedLength.sol`'s obligation and derivation, the symbol table's coverage, definition links. |
| `Examples/Tactics/ProgramTrace.lean` | Checked program traces: capture order, read continuations, JSON rows, parameters, kernel submission, budget failure. |
| `Examples/Tactics/SelfPowerData.lean` | Both-pipeline concrete kernel executions for unsigned-power panic bytes in ordinary self-call frames, conditional/index ordering, rollback and negative expectations. |

At the root, the notation's own tests:

| Module | What it shows |
|---|---|
| `Examples/ChainNotation.lean`, `Examples/ChainRewrites.lean`, `Examples/ExampleNames.lean` | How a chain is written and checked, its rewrite links, the printed names of fresh variables. |
| `Examples/ChainExpand.lean` | The expansion links past the program (`Calculus/ExpandLaws.lean`), the closer on the expanded lines, which types expand. |
| `Examples/ChainRewritesOpen.lean` | The rewrite links while the program is open, on the scoped line (`Calculus/RewriteScoped.lean`), a step of the strategy after them in the same chain. |
| `Examples/Notation.lean` | What taclets, premises and sequents print, pinned. |
| `Examples/Verify.lean`, `Tools.lean` | `#verify`, `#counterexample` and the other commands, pinned. |
| `Examples/ProofTree.lean` | The proof tree's commands, `sol_derive?` and `sol_prove?`, pinned. |
| `Examples/Benchmark/*.lean` | solkey's benchmark contracts with their `@custom:key` clauses proved (`Counter`, `SimpleStorage`, `Mapping`, `Purchase`, `Coin`, `EtherWallet`, `ERC20`), and `Syntax`, which pins what elaborates away (units, casts, events, errors, enums, struct constructors, modifiers). |
| `Examples/Tactics/SignedNumericImport.lean` | Both-pipeline signed numeric source controls, negative assertions and checked/unchecked width/parity regressions. |
| `Syntax/Numeric.lean` | Typed value composition for checked signed power, with distinct signed base and unsigned exponent. |
| `Examples/Tactics/Mutability.lean` | Witnesses and negative controls of the mutability metatheorems (`Theory/Mutability/`): decided `view`/`pure` premises, a write and a state read outside them breaking the conclusions, payable and value-free entries that commit. |
| `Examples/DecisionHashCore.lean` | Bounded va1-decision checkpoint; typed scope and retained obligations are stated in the module. |
| `Examples/DecisionHashFamilies.lean` | Bounded va1-decision checkpoint; typed scope and retained obligations are stated in the module. |
| `Examples/DecisionHashKeys.lean` | Bounded va1-decision checkpoint; typed scope and retained obligations are stated in the module. |
| `Examples/DecisionHashKinds.lean` | Bounded va1-decision checkpoint; typed scope and retained obligations are stated in the module. |
| `Examples/DecisionHashMixed.lean` | Bounded va1-decision checkpoint; typed scope and retained obligations are stated in the module. |
| `Examples/DecisionHashQuantifiers.lean` | Bounded va1-decision checkpoint; typed scope and retained obligations are stated in the module. |
| `Examples/DecisionHashThreeKinds.lean` | Bounded va1-decision checkpoint; typed scope and retained obligations are stated in the module. |
| `Examples/DecisionHashUpdates.lean` | Bounded va1-decision checkpoint; typed scope and retained obligations are stated in the module. |
| `Examples/DecisionHashesChecks.lean` | Bounded va1-decision checkpoint; typed scope and retained obligations are stated in the module. |

| `Examples/Tactics/StaticStorageCompatibility.lean` | Inhabited conditional frame, changed balance, reentry refusal and malformed decoder controls; no opaque static preservation assertion. |
| Module | Its examples |
|---|---|
| `Examples/Benchmark/Algorithms/BinarySearch.lean` | Sorted-array half-open binary search; hit or absence specification. |
| `Examples/Benchmark/Algorithms/FastExponentiation.lean` | Repeated squaring; exact natural power target retained pending specification lowering. |
| `Examples/Benchmark/Algorithms/Fibonacci.lean` | Two-accumulator Fibonacci; exact recurrence target retained pending specification lowering. |
| `Examples/Benchmark/Algorithms/FindIndex.lean` | First negative element; predicate-search bounds and minimality. |
| `Examples/Benchmark/Algorithms/Gcd.lean` | Euclid remainder loop; zero case and exact common-divisor characterization. |
| `Examples/Benchmark/Algorithms/InsertionSort.lean` | Small memory-array insertion sort; sortedness clauses and full permutation target. |
| `Examples/Benchmark/Algorithms/LinearSearch.lean` | First matching index; successful, absent, and minimality cases. |
| `Examples/Benchmark/Algorithms/Maximum.lean` | Nonempty-array maximum; upper bound and attained-element specification. |
| `Examples/Benchmark/Algorithms/Reverse.lean` | In-place storage-array reversal; entry-state element and length specification. |
| `Examples/Benchmark/Algorithms/Sum.lean` | Array prefix sum; exact fold target retained pending specification lowering. |
| Module | Its examples |
|---|---|
| `Examples/Benchmark/DataStructures/BitMap.lean` | OpenZeppelin bitmap set; bucket frames proved, membership after set/unset unknown (bitwise laws). |
| `Examples/Benchmark/DataStructures/EnumerableSet.lean` | OpenZeppelin swap-and-pop set with inverse-index invariant; contains proved, add/remove unknown. |
| `Examples/Benchmark/DataStructures/LinkedList.lean` | Mapping-linked list insert/remove link consistency; node clearing proved, full specs unknown. |
| `Examples/Benchmark/DataStructures/Queue.lean` | OpenZeppelin two-index queue; front and slot components proved, int128 index advance unknown. |
| `Examples/Benchmark/DataStructures/RingBuffer.lean` | OpenZeppelin fixed-size circular buffer; push, count and last proved. |
| `Examples/Benchmark/DataStructures/Stack.lean` | Storage-array stack; top and length/top components proved, element frames unknown. |
| Module | Its examples |
|---|---|
| `Examples/Benchmark/Defi/ConstantProduct.lean` | Uniswap v2 zero-fee reserve kernel: `swap` proved by `sol_prove`, including exact reserve effects and nondecreasing k. No external token/callback claim. |
| `Examples/Benchmark/Defi/Escrow.lean` | OpenZeppelin v4.9.6 fixed-owner escrow: constructor and `depositsOf` proved. `deposit` unknown: payable old-storage snapshot plus mapping save does not close credit equality/owner frame. `withdraw` unknown: cleared credit, owner frame and oldNet debit/self-payment remain after save/pay; mapping-frame/ledger snapshot closure missing. |
| `Examples/Benchmark/Defi/FixedRateVault.lean` | EIP-4626-inspired 1:1 native-asset accounting example (not the ERC4626 API): `withdraw` and deposit/withdraw round trip proved. `deposit` unknown: shares/assets/supply = old values + msg.value after payable snapshot and three saves; snapshot normalization across mapping/scalar saves missing. |
| `Examples/Benchmark/Defi/RefundEscrow.lean` | OpenZeppelin v4.9.6 crowdfunding state machine: constructor, `close`, `enableRefunds` proved. `deposit` unknown: Active and old credit+value after payable snapshot/save; payable mapping closure missing. `withdraw` unknown: Refunding, cleared credit and oldNet debit/self-payment after save/pay; mapping/ledger closure missing. `beneficiaryWithdraw` unknown: state Closed proved separately, but nonself payment must leave balance zero; calculus pay balance-update rule missing (operational State.pay debits it). |
| `Examples/Benchmark/Defi/StakingRewards.lean` | Source-extracted staking reward calculator: both `rewardPerToken` (including zero supply) and `earned` proved, with original 1e18 scaling/truncation. Does not implement the source's complete token pool. |
| `Examples/Benchmark/Defi/WrappedEther.lean` | Solmate v6 WETH mint/burn/payment kernel with source unchecked arithmetic: both unqualified deposit/withdraw equations refuted over arbitrary typed stores by kernel-checked counterexample runs. Balance=max/supply=0 wraps the deposit balance; balance=1/supply=0 wraps the withdrawal supply. These are unreachable inconsistent source stores, not WETH exploits. Exact specification obligations retained; global supply invariant is absent from typed layout. |
| `Examples/Benchmark/Defi/StakingPool.lean` | H1710: full pinned staking pool source and IERC20 interface, unchanged except natural NatSpec clauses, via solc importer. Constructor and `setRewardsDuration` proved. `_min` and `lastTimeRewardApplicable` unknown: conditional/alias normalization. `rewardPerToken` and `earned` unknown: conditional and nonlinear/division closure. `stake`, `withdraw`, `getReward` unknown: snapshot/mapping/accrual and foreign-call frame closure. All exact obligations retained. `notifyRewardAmount` unknown at admission: nested `rewardsToken.balanceOf` has no callable signature in this expression context; full source/clauses preserved, no replacement call. |
| `Examples/Benchmark/FixedPoint/WadMath.lean` | Morpho Blue v1.0.0 `MathLib` WAD mul/div rounded down/up: `wMulDown` rounding direction proved. `mulDivDown`, `mulDivUp`, `wDivDown`, `wDivUp` unknown: quotient-of-product bounds (`(n / d) * d <= n < (n / d + 1) * d`, `n` nonlinear) missing in the closer. Upper bounds written overflow-free (`n - q * d < d`); the literal `n < (q + 1) * d` is false at the uint256 edge. `wMulDown(x, 0) == 0` proved. |
| `Examples/Benchmark/FixedPoint/RayMath.lean` | Aave v2 `WadRayMath.rayMul`/`rayDiv`, round half up: both half-up obligations unknown (closer heartbeats in `simp`; same missing quotient bound). `rayMul(0, b) == 0` proved. |
| `Examples/Benchmark/FixedPoint/LinearInterest.lean` | Aave v2 `MathUtils.calculateLinearInterest`: index at least one ray and exactly `rate * Δt / year + ray` proved. |
| `Examples/Benchmark/FixedPoint/Vesting.lean` | OpenZeppelin v4.9.6 `VestingWallet` ether kernel: `vestingSchedule <= total` and `release` keeping `released` within total received unknown (missing `a * b / d <= a` for `b < d`). Nothing vested before start, everything past start + duration proved. |
| `Examples/Benchmark/FixedPoint/FeeSplit.lean` | OpenZeppelin v4.9.6 `PaymentSplitter._pendingPayment` plus two-payee harness: pro-rata bound and parts summing to at most the amount unknown (quotient bounds, `a / d + b / d <= (a + b) / d`). |
| `Examples/Benchmark/FixedPoint/BondingCurve.lean` | Ratimon linear curve `getPoolBalance` (PRB `UD60x18` ops in `uint256`), `buy` and added mirror `sell`: both proved. Buy/sell round trip unknown: equal `getPoolBalance` chains under different fresh names; `sol_close` hits `simp` recursion. |
| `Examples/Benchmark/Governance/Ownable.lean` | OpenZeppelin owner state machine; all four function specifications proved by `sol_prove`. |
| `Examples/Benchmark/Governance/Pausable.lean` | OpenZeppelin pause state machine; all four function specifications proved by `sol_prove`. |
| `Examples/Benchmark/Governance/Voting.lean` | Direct-vote Ballot variant: one vote and tally/frame effects; all three function specifications proved by `sol_prove`. |
| `Examples/Benchmark/Governance/Timelock.lean` | Bound Ether-operation timelock: delay, cancellation and permanent completion; all four function specifications proved by `sol_prove`. |
| `Examples/Benchmark/Governance/EnglishAuction.lean` | Solidity SimpleAuction: constructor proved; bid, refund and final payout obligations retained as unknown, with snapshot/payment closer gaps documented in the module. |
| `Examples/Benchmark/Governance/Multisig.lean` | Two-owner Ether multisig: constructor, revocation and threshold execution proved; fresh submission and no-double-confirmation specifications retained as unknown with snapshot/Boolean closer gaps. |
| `Examples/Benchmark/Inheritance/SuperInConstructor.lean` | solc `super_in_constructor`: diamond `D, C, B, A` linearized, `super.f()` chain called from the constructor (`data == 15`); all five specifications proved by `sol_prove`. |
| `Examples/Benchmark/Inheritance/ModifierStacking.lean` | solc `function_modifier_multiple_times`: one modifier applied three times, outermost first (stacking; the additions commute, so not order); the specification proved by `sol_prove`. |
| `Examples/Benchmark/Inheritance/ModifierOverride.lean` | solc `function_modifier_calling_functions_in_creation_context`: overridden modifier and virtual hook in the constructor (`0x4300`); all seven function specifications proved by `sol_prove`. |
| `Examples/Benchmark/Inheritance/AbstractHook.lean` | solc `call_unimplemented_base`: an abstract contract calls a hook its heir implements; both specifications proved by `sol_prove`. |
| `Examples/Benchmark/Inheritance/ExplicitBase.lean` | solc `explicit_base_class`: virtual dispatch beside a static `BaseBase.g()` call; all four specifications proved by `sol_prove`. |
| `Examples/Benchmark/Inheritance/UsingFor.lean` | solc `using_for_function_on_int`: a library function bound with `using … for uint`, inlined; both specifications proved by `sol_prove`. |
| `Examples/Benchmark/Inheritance/ConstructorArgs.lean` | solc `base_constructor_arguments`: a base constructor's header argument, then the derived body (`m_a == 49`); all four specifications proved by `sol_prove`. |
| `Examples/Benchmark/Inheritance/ConstructorOrder.lean` | solc `order_of_evaluation`: base constructor arguments evaluated in linearization order, not header order (`[1, 3, 2, 4]`); `f` and constructor proved by `sol_prove`, `g` (memory copy) without a clause. |
| Module | Its examples |
|---|---|
| `Examples/Benchmark/MathLib/Average.lean` | OpenZeppelin v4.9.6 `Math.average` (`(a & b) + (a ^ b) / 2`): exact floor-average target, overflow-free form. Unknown: bitwise carry identity over `uintBitwise` missing. |
| `Examples/Benchmark/MathLib/CeilDiv.lean` | OpenZeppelin v4.9.6 `Math.ceilDiv`: exact ceiling by quotient and remainder. Unknown: division/remainder closer for a symbolic divisor missing. |
| `Examples/Benchmark/MathLib/Log2.lean` | OpenZeppelin v4.9.6 `Math.log2` (eight unchecked shift steps): natural `2^r <= v < 2^(r+1)` as a Lean `NaturalSpec`. Unknown: no `**`/`>>` in clauses; eight joined conditional updates exceed `sol_close_ite_split`'s six. |
| `Examples/Benchmark/MathLib/MinMax.lean` | OpenZeppelin v4.9.6 `max`/`min` and Solady v0.1.0 `clamp` (branchless select as conditionals): all three proved. |
| `Examples/Benchmark/MathLib/MulDiv64.lean` | OpenZeppelin v4.9.6 `mulDiv` contract for `uint64` operands (plain full-precision product, overflowing result reverts): exact floor quotient proved. |
| `Examples/Benchmark/MathLib/Saturating.lean` | OpenZeppelin v5.4.0 `saturatingAdd`/`saturatingSub` (helpers inlined, branchless arithmetic kept): `saturatingSub` proved. `saturatingAdd` unknown: xor-select closer missing. |
| `Examples/Benchmark/MathLib/SignedAbs.lean` | OpenZeppelin v4.9.6 `SignedMath.abs` and checked negation at `type(int256).min`: `neg` proved; kernel runs show `abs(min) = 2^255` and `neg(min)` halting. `abs` clause unknown: no `int`/`uint` comparison in clauses. |
| `Examples/Benchmark/MathLib/Sqrt.lean` | Uniswap v2-core Babylonian `Math.sqrt` with loop invariant and variant: exact floor-root target. Unknown: the `y <= 3` leaf closes; the loop leaves need a nonlinear floor-division closer. |
| Module | Its examples |
|---|---|
| `Examples/Benchmark/MemoryAlgorithms/ArrayEquals.lean` | Equality of two memory arrays; result iff equal lengths and elements (unknown: quantified step leaf). |
| `Examples/Benchmark/MemoryAlgorithms/BubbleSort.lean` | In-place bubble sort of at most eight elements; sortedness clauses, full permutation target (unknown: memory-write loop frame). |
| `Examples/Benchmark/MemoryAlgorithms/CountOccurrences.lean` | Occurrences of a key; exact counting target retained pending a counting aggregate (unknown). |
| `Examples/Benchmark/MemoryAlgorithms/Dedupe.lean` | Distinct values of a sorted array into a caller's array; increasing and covering clauses (unknown: memory-write loop frame). |
| `Examples/Benchmark/MemoryAlgorithms/IsSorted.lean` | Adjacent-pair sortedness scan; result iff every adjacent pair is ordered (unknown: quantified step leaf). |
| `Examples/Benchmark/MemoryAlgorithms/PairSum.lean` | Two-pointer pair sum on a sorted array; result iff two positions sum to the target (unknown: existential leaf). |
| `Examples/Benchmark/MemoryAlgorithms/PrefixSums.lean` | Prefix sums into a caller's array; zero entry and recurrence clauses (unknown: memory-write loop frame). |
| `Examples/Benchmark/MemoryAlgorithms/Rotate.lean` | Rotation by k into a caller's array; placement clause, false when `r` aliases `xs` (counterexample in the docstring). |
| `Examples/Benchmark/Patterns/CommitReveal.lean` | Solidity by Example SecuredFindThisHash commit-reveal: constructor and commitSolution proved, getMySolution's guard proved, its returns unspecified (an unnamed tuple cannot be named by a clause); revealSolution retained as unknown (heartbeat exhaustion on string hashes and payment branches). |
| `Examples/Benchmark/Patterns/StateMachine.lean` | Solidity docs StateMachine with timed transitions: forward-only stage clauses for g, h, i proved; bid and reveal retained as unknown (read-after-save stage arithmetic missing in the leaf closer). |
| `Examples/Benchmark/Patterns/Withdrawal.lean` | Solidity docs WithdrawalContract pull payments: constructor and withdraw proved; becomeRichest retained as unknown (quantified mapping-save leaf against the snapshot). |
| `Examples/Benchmark/Patterns/RateLimiter.lean` | ConsenSys per-period withdrawal limit, timestamp periods: constructor proved; withdraw retained as unknown (repeated-save normalization with the ledger debit). |
| `Examples/Benchmark/Patterns/CircuitBreaker.lean` | ConsenSys circuit breaker with silent-skip modifiers: all four function specifications proved. |
| `Examples/Benchmark/Patterns/Mutex.lean` | Solidity by Example re-entrancy guard on EtherStore: deposit, guarded withdraw (with its payment) and getBalance proved; calls run no recipient code here, so re-entry is not exercised. |
| `Examples/Benchmark/Patterns/TwoStepOwnership.lean` | Compound Unitroller pending-admin handover with error codes: all three function specifications proved. |
| Module | Its examples |
|---|---|
| `Examples/Benchmark/SolkeyBench/AccessRestriction.lean` | solkey 50a1469 `benchmark/AccessRestriction.sol`, modifiers inlined: `changeOwner` proved. `disown` unknown: owner = 0 after `delAt` (delete) not closed. `forceOwnerChange` unknown: `x & 0 == 1` branch not refuted (bitwise-and closer missing) and refund needs the pay ledger rule. |
| `Examples/Benchmark/SolkeyBench/Fund.lean` | solkey 50a1469 `benchmark/Fund.sol`: `withdraw` unknown: cleared share, oldNet debit and mapping frame after save/pay; mapping-frame closure and pay ledger rule missing. |
| `Examples/Benchmark/SolkeyBench/SendContract.lean` | solkey 50a1469 `benchmark/SendContract.sol`: constructor proved. `becomeRichest` unknown: net debit of the old richest after `pay`; pay ledger rule missing. |
| `Examples/Benchmark/SolkeyBench/SendingEther.lean` | solkey 50a1469 `benchmark/SendingEther.sol` (`SendEther` only): `sendViaTransfer`, `sendViaSend`, `sendViaCall` unknown: net clauses after `pay(_to, msg.value)`; pay ledger rule missing. |
| `Examples/Benchmark/SolkeyBench/SimpleAuction.lean` | solkey 50a1469 `benchmark/SimpleAuction.sol` (solkey variant; distinct from Governance/EnglishAuction): constructor proved. `bid`, `withdraw` unknown: mapping/snapshot closure (and pay for withdraw). `auctionEnd` unknown: pay ledger rule missing. |
| `Examples/Benchmark/SolkeyBench/Todos.lean` | solkey 50a1469 `benchmark/Todos.sol`: `toggleCompleted` proved (struct array field toggle, length frame). `get`, `updateText` carry no clauses. |
| `Examples/Benchmark/SolkeyBench/WithdrawalContract.lean` | solkey 50a1469 `benchmark/WithdrawalContract.sol`: constructor proved. `becomeRichest` unknown: credit to old richest and mapping frame; `withdraw` unknown: as Fund. |
| Module | Its examples |
|---|---|
| `Examples/Benchmark/SolkeyGames/KingOfEther.lean` | solkey's pull-payment King of the Ether (DoS fix): `claimThrone` proved by `sol_prove`, including the dethroned king's credit and the payable booking. `withdraw` refuted (`¬ ⊢`, kernel-checked): the contract calling itself with a credit pays itself and books nothing, so the `net(msg.sender)` clause fails. |
| `Examples/Benchmark/SolkeyGames/EtherGame.lean` | solkey's forced-ether-proof EtherGame: `deposit` proved (winner and target clauses under the invariant). `claimReward` refuted by `sol_refute`: a winner that is the contract itself pays itself, so `net(msg.sender)` does not drop. |
| `Examples/Benchmark/SolkeyGames/EtherStore.lean` | solkey's re-entrancy victim with the invariant `balances[a] == net(a)`: `deposit` unknown (the quantified invariant after the save and the booking is left to the closer). `withdraw` refuted (`¬ ⊢`, kernel-checked) at a self-call state that satisfies the invariant: the credit is zeroed while the ledger entry stays. The callback re-entrancy is not stated (default payment semantics). |
| `Examples/Benchmark/SolkeyGames/SendEther.lean` | solkey's three ways to send ether: `sendViaTransfer`, `sendViaSend` and `sendViaCall` each refuted by `sol_refute`: with `_to == msg.sender == this` the booked `msg.value` is never paid out, so the self-payment clauses fail. |
| Module | Its examples |
|---|---|
| `Examples/Benchmark/SolkeyMisc/Account.lean` | solkey real-world `Account` (solidity-by-example error handling): `deposit` and `withdraw` proved by `sol_prove`. |
| `Examples/Benchmark/SolkeyMisc/DocsBallot.lean` | solkey real-world `DocsBallot` (Solidity docs delegated Ballot): `giveRightToVote`, `vote` proved. `delegate`, `winningProposal`, `winnerName` unknown: loop leaves print with `‹…›` escapes; closer gaps for struct-member saves under quantifiers and `∃` witnesses. |
| `Examples/Benchmark/SolkeyMisc/FunctionModifier.lean` | solkey real-world `FunctionModifier`: constructor, `changeOwner` and recursive reentrancy-guarded `decrement` proved. |
| `Examples/Benchmark/SolkeyMisc/TimeLock.lean` | solkey real-world `TimeLock` (0.8 overflow port): `deposit`, `increaseLockTime` proved. `withdraw` refuted by a kernel run: a self-withdrawal books no net debit. |
| `Examples/Benchmark/SolkeyMisc/WETH9.lean` | solkey real-world `WETH9` (canonical WETH, 0.8 port): `deposit`, `approve` proved. `withdraw` unknown: the contract's own `transfer` shadows `address.transfer` in the front end. `transferFrom` unknown: closer exhausts heartbeats on consecutive mapping saves. |
| `Examples/Benchmark/SolkeyOz/OZCounters.lean` | solkey's OpenZeppelin `Counters` port: all four clauses proved (unchecked increment/decrement by the leaf closer). |
| `Examples/Benchmark/SolkeyOz/OZMath.lean` | solkey's OpenZeppelin `Math` port: `tryAdd`, `max`, `min` proved; `trySub`, `tryMul`, `tryDiv`, `tryMod`, `average`, `ceilDiv` unknown, each with its stuck leaf and missing closer law. |
| `Examples/Benchmark/SolkeyOz/OZNonces.lean` | solkey's OpenZeppelin `Nonces` port: `nonces`, `useNonce` proved; `useCheckedNonce` unknown (wrapping add with a Boolean `!=` binding). |
| `Examples/Benchmark/SolkeyOz/OZOwnable2Step.lean` | solkey's OpenZeppelin `Ownable2Step` port: all six clauses proved. |
| `Examples/Benchmark/SolkeyOz/OZPausable.lean` | solkey's OpenZeppelin `Pausable` mock port: all six clauses proved. |
| `Examples/Benchmark/SolkeyOz/OZReentrancyGuard.lean` | solkey's OpenZeppelin `ReentrancyGuard` mock port: all five clauses with both contract invariants proved, the recursive re-entry reverting. |
| `Examples/Benchmark/SolkeyOz/SolmateOwned.lean` | solkey's Solmate `Owned` port: both clauses proved. |
| Module | Its examples |
|---|---|
| `Examples/Benchmark/Swc/IntegerOverflowMinimal.lean` | SWC-101 `integer_overflow_minimal.sol` (registry 1b62270), 0.4 wrapping `-=` as `unchecked`: `run` (`count == \old(count) - input`) refuted by a kernel-checked run from `count = 1` wrapping to 2^256-1. |
| `Examples/Benchmark/Swc/IntegerOverflowMinimalFixed.lean` | SWC-101 `integer_overflow_minimal_fixed.sol`, SafeMath `sub`: `run` proved under the same clause. |
| `Examples/Benchmark/Swc/WalletRefundNoSub.lean` | SWC-105 `wallet_02_refund_nosub.sol`: `refund` (`balances[msg.sender] == 0`) refuted by a run that pays and keeps the credit. Constructor, `withdraw`, `migrateTo` proved. `deposit` unknown (payable-snapshot leaf, as in WalletOk). |
| `Examples/Benchmark/Swc/WalletOk.lean` | SWC-105 `wallet_01_ok.sol`: constructor, `withdraw`, `refund`, `migrateTo` proved. `deposit` unknown: `old` is not resolved through the parallel payable update after the mapping save (closer gap, as in Defi/Escrow). |
| `Examples/Benchmark/Swc/MultiOwnedVulnerable.lean` | SWC-105 `multiowned_vulnerable.sol`, `onlyOwner` missing on `newOwner`: `newOwner` (only an owner adds owners) refuted by a run where a non-owner makes itself owner. Constructor and `deleteOwner` proved. |
| `Examples/Benchmark/Swc/MultiOwnedFixed.lean` | SWC-105 `multiowned_not_vulnerable.sol`: constructor, `newOwner`, `deleteOwner` proved under the same clauses. |
| `Examples/Benchmark/Swc/HashForEther.lean` | SWC-100 `visibility_not_set.sol`, default visibility written `public`: `_sendWinnings` (pays only a winner, `uint32(msg.sender) == 0`) refuted by a run paying account 1. `withdrawWinnings` proved. |
| `Examples/Benchmark/Swc/HashForEtherFixed.lean` | SWC-100 `visibility_not_set_fixed.sol`, `_sendWinnings` internal: `withdrawWinnings`, the only public function, proved. |
| Module | Its examples |
|---|---|
| `Examples/Benchmark/TokenExtensions/FeeOnTransfer.lean` | Pinned weird-erc20 `TransferFeeToken` (fee credited to the `balanceOf[address(0)]` sink). Constructor proved. `transferFrom`, `transfer`: unknown at the three-slot balance-sum leaf; exact src/dst/sink effects, supply, frame and allowance spend proved as components. |
| `Examples/Benchmark/TokenExtensions/AllowanceDelta.lean` | Pinned OpenZeppelin 4.9.6 `increaseAllowance`/`decreaseAllowance` with `allowance`/`_approve`. Getter and `_approve` proved. `increaseAllowance`: unknown as one obligation (disjunctive two-key frame), every clause proved as a component. `decreaseAllowance`: unknown at guarded unchecked subtraction; frames proved. |
| `Examples/Benchmark/TokenExtensions/RoleMint.lean` | Pinned OpenZeppelin 4.9.6 `ERC20PresetMinterPauser.mint` with AccessControl roles. `hasRole`, `_grantRole`, `grantRole` proved. `_mint`, `mint`: unknown at the unchecked balance credit; role guard, supply and frame proved. |
| `Examples/Benchmark/TokenExtensions/CappedSupply.lean` | Pinned OpenZeppelin 5.0.2 `ERC20Capped` (post-`_update` cap check). Constructor and `cap` proved. `_update`, `_mint`: unknown (cap bound beside unchecked saves, wrapped credit); mint supply and frame proved. |
| `Examples/Benchmark/TokenExtensions/Burnable.lean` | Pinned OpenZeppelin 5.0.2 `ERC20Burnable` over the `_update` hub. `_approve` proved. `_spendAllowance`, `_burn`, `burn`, `burnFrom`: unknown at guarded unchecked subtractions; burn frame and infinite allowance proved. |
| `Examples/Benchmark/TokenExtensions/VestingWallet.lean` | Pinned OpenZeppelin 5.0.2 `VestingWallet` ether release. Constructor and `end` proved. `_vestingSchedule`: unknown (ternary, nonlinear bound), before-start clause proved. `release`: unknown at the payment update. |
| `Examples/Benchmark/Tokens/ERC20.lean` | Pinned Solidity by Example ERC20. Full `transfer`, `_mint`, `_burn`, `mint`, `burn` clauses/frames proved. `approve`, `transferFrom`: unknown guarded two-key allowance frames. Supply equals finite-support balance sum: unknown sum syntax/update laws; approve normal-termination diamond proved; six other no-overflow diamonds unknown at checked-update definedness/range propagation. |
| `Examples/Benchmark/Tokens/ERC721.lean` | Pinned Solidity by Example non-safe ERC721 core. `ownerOf`, `balanceOf`, `approve`, `getApproved`, `transferFrom`, `_mint`, `_burn` proved, including unique owner slot, transfer approval clearing and frames. `setApprovalForAll`: unknown two-key frame; `_isApprovedOrOwner`: unknown short-circuit Boolean equivalence. Aggregate owner-count invariant and safe receiver callbacks unproved. |
| `Examples/Benchmark/Tokens/ERC1155.lean` | Pinned OpenZeppelin 5.0.2 callback-free `_update` core. `balanceOf`, `isApprovedForAll` proved. `_setApprovalForAll`, `setApprovalForAll`: unknown two-key frames. `_update`: unknown memory length lower bound, quantified snapshot frame and filtered prefix-sum invariant/update laws (duplicates, self-transfer and zero-address cases retained). |
| `Examples/Benchmark/Tokens/ERC20Capped.lean` | Pinned OpenZeppelin 4.9.6 cap constructor/getter and inlined capped base mint; exact unchecked balance-addition cases retained. Constructor and cap getter proved; full mint unknown at wrapped-add piecewise normalization/frame closure. Cap-bound component proved separately; no reachable supply-sum premise assumed. |
| `Examples/Benchmark/Tokens/ERC20Burnable.lean` | Pinned OpenZeppelin 4.9.6 burn/burnFrom, finite/infinite allowance spending and base burn; exact unchecked supply-underflow case retained. All four full obligations unknown at guarded two-key frames and wrapped-subtraction piecewise normalization; infinite-allowance component proved separately. |
| `Examples/Benchmark/Tokens/ERC721Burnable.lean` | Pinned OpenZeppelin 4.9.6 authorized NFT burn with owner/approval deletion, former-owner count and full frame; unchecked zero-count case retained. Full burn obligation unknown at guarded wrapped-subtraction/old-owner normalization; owner/approval-clearing component proved separately. |
| `Examples/ExecutableGoalBinding.lean` | Exact-target refutation and wrong-target, retained-value, argument and layout refusal examples. Test-only kernel replay is checked by `scripts/trust/executable-goal-replay.lean` in Lean CI. |
| `Examples/ExecutableRequestData.lean` | Shared synthetic request and nondefault raw contract data for quotation and retained-candidate examples; not source admission. |
| Module | Its examples |
|---|---|
| `Examples/FrontendValidation/SolcJson.lean` | Accepted and rejected literal controls for `J.get`, `J.opt`, `J.str`, `J.arr`, `J.str?`, `J.arr?`, `J.ref?`, `J.id?`, `J.hasOperatorFunction`, `J.operatorFunction?`, and `J.typeRef?`. |
| `Examples/FrontendValidation/SolcJson/Ir.lean` | Literal accepting/rejecting controls for IR channel selection, source/contract paths, lookup, and extracted text. |
| `Examples/FrontendValidation/SolcJson/CallMetadata.lean` | Literal profile, call-shape, static-target, location and attachment controls; structural metadata only. |
| `Examples/FrontendValidation/SolcJson/YulIngress.lean` | Literal JSON grammar, metadata, documentation safety and closed/scoped ingress controls; no source or execution authentication. |
| `Examples/FrontendValidation/SolcJson/BodyHelpers.lean` | Literal rational, expression, tuple, storage-reference, aggregate and declaration-owner acceptance/refusal controls. |
| `Examples/FrontendValidation/SolcJson/YulReferences.lean` | Literal declaration IDs, namespace selection, shadowing, source spans, occurrence collection and unique reference coverage controls. |
| `Examples/FrontendValidation/SolcValidation.lean` | Inline accepted and rejected controls for the frozen solc literal, lexer, parser, data lookup, structural and renaming validators. |
| `Examples/DecisionResidue.lean` | M7-next: residue members (halting `||` APF guard valid and false; VA1 mapping-field and normalization-budget labels; a leaf every hash try refuses), witness controls (in-target non-residue feature fixtures of earlier milestones answered through `DecisionTheorem'`; the answering route is not pinned) and the negative control (a valid and a false residue leaf, neither claimed). |

## H109 slow loop obligations

| Module | Its examples |
|---|---|
| `Examples/Tactics/OpenLoops/RowsNine.lean` | Existing `binomialRowsNine` obligation, checked with chunk 128 and preserved in the non-default H109 slow library and CI/full/lane-end/axiom-audit closure. Scoped CI acceptance uses 600 s; the 300 s default/VM STOP remains. |
| `Examples/Tactics/OpenLoops/RowsNine/{Checkpoint,Stage1,Stage2,Stage3,Finish}.lean` | Kernel-checked continuation checkpoints for the unchanged nine-row binomial walk; 128-step chunks, the original aggregate iteration allowance, and one slow-library time cap per module. |
| `Examples/RedTeam/Evm/Dup17.lean` | Red-team witness: `rows.push(one)` of a 16-word static value is in the compiler fragment and compiles to `DUP17`, which the abstract machine runs and the EVM does not have; no false theorem. |
# Storage layout red team

| Module | Its examples |
|---|---|
| `Examples/RedTeam/StorageLayout/BoolPacking.lean` | Concrete full-word/solc mismatches for adjacent booleans, fixed and dynamic boolean arrays, packed structs and the following field. External metadata reproduced by `check-solc.cjs` and `Layout.sol` beside the module. |
| `Examples/RedTeam/StorageLayout/ReferenceChecks.lean` | Executable independent Keccak vectors for dynamic arrays, mappings inside mapped structs, packed boolean array base and ERC-7201 namespace; reference runner `check-reference.py`. |
| `Examples/RedTeam/Statements/InFragmentNames.lean` | Witness: `Shrink.Lowering.InFragment` (premise of `loweringBySimulation`/`V2`) is name matching alone; a compilation with no entries is `Accepted`. |
| `Examples/RedTeam/Statements/BackendTotalZeroBound.lean` | Witness: `compilerTotal`'s conclusion holds at array bound `L = 0` for a dynamic-array contract while every input is refused. |
| `Examples/RedTeam/Statements/GoalPinsUnsat.lean` | Witness: `goalPinsCorrect` is false as stated (`Laws.check_exact` parses as `(Observed → check = out) ↔ CheckGraph`); also the pin graph of a folded definition ignores its body. |
| Module | Its examples |
|---|---|
| `Examples/RedTeam/Syntax/LiteralFolding.lean` | Red-team witness: literal expressions with `%`, `**` or `<<` run as `uint256` arithmetic (`7 % 2 / 2 * 2` returns `0`, `2 ** 256 - 1` reverts) where solc folds them exactly (`1`, `2^256 - 1`). |
| `Examples/RedTeam/Syntax/NegNegPrinter.lean` | Red-team witness: the program and clause printers write `-(-y)` as `--y`, a Solidity pre-decrement; runs of both programs from `y := 3` disagree. |
| `Examples/RedTeam/Trust/ExternBoundary.lean` | Controlled kernel/native disagreement exposing the source trust lint's missing external-implementation inventory; no false theorem. Companion Node test pins the weak lint and stronger census boundaries. |
| `Examples/RedTeam/Trust/HeadlineAxioms.lean` | Exact registered headline/endpoint type checks and transitive axiom queries; intrinsic model and instruction-list boundary only. |
| `Examples/RedTeam/Typing/AddressRange.lean` | Red team: `address a = 2^200; address b = a + 1;` (both rejected by solc) elaborate and run to an address above `2^160`. |
| `Examples/RedTeam/Typing/BytesIntMix.lean` | Red team: implicit `uint8`↔`bytes1`, a short hex literal at `bytes2` and `bytes1 + bytes1` (all rejected by solc) elaborate and run. |
| `Examples/RedTeam/Typing/ConstantWrite.lean` | Red team: assignments to a `constant` and to an `immutable` outside the constructor (rejected by solc) elaborate and change the values. |
| `Examples/RedTeam/Typing/EnumConversions.lean` | Red team: implicit enum↔`uint` conversions and `E(5)` (rejected by solc) elaborate; the last runs to a panic. |
| `Examples/RedTeam/Typing/Mutability.lean` | Red team: a `view` body writing storage, a `pure` body reading it and `msg.value` in a non-payable function (rejected by solc) elaborate and run. |
| `Examples/RedTeam/Typing/NarrowRootWrite.lean` | Red team: widths live outside `Ty`, so the typed statement `s = 300;` at a `uint8` root is a `Stmt` and its run leaves `s > 255`. |
| `Examples/Panic/Origins.lean` | Typed panic-origin regressions V1 erases the cause of a panic. |
