# KeY taclet → Lean `Taclet` mapping

The name-by-name map from solkey's `solidityProgramRules.key` (plus
`ifThenElseRules.key`) to `Solidity.Taclet` (`Calculus/Rules.lean`), then the
symbol table for updates and the data-structure theories. **Pinned to solkey
`473da8944c`**: 377 program taclets, enumerated in `Calculus/KeyTaclets.lean`.

These tables are the prose companion of `Calculus/RuleShapes.lean`, which
checks the correspondence: `tacletOrigins` gives every constructor a typed
`KeyOrigin` (`.taclet t` or `.merged [t₁, …]`; a missing or misspelled row
fails the build), `unclaimedTaclets` excuses the rest with a reason,
`callbackOrigins` does the same for `CallbackTaclet`, and `taclets_partitioned`
says every taclet is claimed, architecturally excused, or a pending migration
gap, in exactly one category (`claimedTaclets_count = 342`,
`unclaimedTaclets_count = 35`, 0 pending). The pending-name list is empty;
semantic and source-support gaps, including effectful call-receiver operands,
remain tracked in `docs/solkey-migration.md`.
The existing `LeanTaclet` layer (`leanTaclets`) has, among others, the rules
`addmodAssignment`, `mulmodAssignment`, `hashAssignment`, `functionCallArgCapture`,
`tryCallDiamond`, `transferDiamond`, `assumeFalse`, `loopExit`,
`whileClose`, `whileNoVariantDiamond`, `pushCompoundUnfoldReceiver`,
`pushIncrementUnfoldReceiver`, `storageMemorySourceSave`,
`pushMemorySourceCapture`, `storageFixedCopySave`, `pushFixedCopySave`,
`tryCallSelfBox`, `tryCallSelfDiamond`, `recursiveCallUnfold`, `ifElseJoin` and
`internalCallSummary`.
The two push-suffix rules capture a complex receiver; upstream's bare
push receiver capture does not match that arithmetic target.
The memory-source rules preserve internal snapshot assignments and capture
complex memory paths; upstream's native memory push requires a memory variable.
A taclet may be claimed by two constructors (the
member reads by their `.length` rules, since KeY reads `sp.length` as the
member `length`; `memoryFieldWrite`/`memoryIndexWriteArray` by the value and
reference writes). What stays prose here is what a `KeyOrigin` cannot say:
why a merge is a merge, and the symbol maps of the second half.

The scoped reduction applies the existing data-structure read eliminator to
demanded primitive `find` and `len` terms before later writes duplicate them.
This schedules the same `Decide.lean` read clauses earlier; it adds no taclet
or independent decision procedure. Each input must fit the shared 24,000-node
and depth-12 bounds. Only literal results replace the read; symbolic or
oversized inputs retain the original term for normalization under later
hypotheses. `LTm.literalRead_eval` proves exact equality, including undefined
reads, and `Tm.toL_drel` carries it through the scoped reduction.

Legend (a row with several taclets or constructors lists them in one cell):

- **same** — a constructor of the taclet's own name.
- **find same** — the same name and `\find`, but the replacement differs; the
  note says how.
- **merged** — one constructor covers this taclet with others: an operator
  family, a value/reference source split, a mapping/array receiver split
  (increments and compound assignments only), or two captures one step covers.
- **unclaimed** — no constructor; the note is the reason from
  `unclaimedTaclets`.
- **Lean only** — a `LeanTaclet`: no taclet behind it.
- **⊢ rule** — no `Taclet` constructor: a `Proves` constructor or a derived
  theorem (`Calculus/Proves.lean`, `Calculus/Symex.lean`) is the rule.  A
  `solidityProgramRules.key` taclet is listed in `RuleShapes.unclaimedTaclets`;
  a row from another `.key` file names that file.

**`\sameUpdateLevel`.** solkey `78f42fde33` adds it
to the four allocation taclets (`memoryReferenceDeclFreshAlloc`,
`memoryRootDeleteFreshRebind`, `memoryArrayFreshAlloc`, `memoryStorageCopy`);
the memory index and delete taclets with an `\add` carry it already. In KeY
it lets a taclet with an `\add` fire under the update prefix of its `\find`,
the added formula read under the same updates. Here the updates of a goal sit
in its context (`Proves.update` appends `.upd m U` to `Γ`) and a premise's
hypothesis is appended after them (`.pre c`), so every rule fires at the
goal's update level and reads what it adds there: nothing to port.

## Modality / sequent rules

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `functionBodyExpand` | `functionBodyExpand` | same | a call with targets (`fbs`, `CallRet.isRets`: a tuple assignment's call, a specification obligation's `result = f(x̄)`, KeY's `FunctionBodyStatement`) carries its callee inlined (`Stmt.call`), closed over a frame of its own; with every argument simple the premise is KeY's `expand_function_body`, the targets the statements after it (`t = r;`, KeY's `function-frame{…} t0 = r0;` without the frame), and the frame ends with the expansion (`Premise.inline`: `functionFrameEmpty`, claimed merged). The parameters are positions in that frame (named by the elaborator's fresh names in the binders, `Args`/`CallRet`; `Syntax/Elab.lean`), so KeY's fresh renaming is done once, at elaboration; the returns start at their defaults (solc's), where KeY's `R ri;` leaves them unconstrained.  An unnamed return is `_ret` (one) or `_ret0`, `_ret1`, … (several), KeY's `ret0`, `ret1`, …; the solc import names them the same way (`Frontend/Import.lean`, `retNames`).  A deployment, `constructor(x̄);`, is one with no targets (`CallRet.rets []`, `elabCtor`): its body is the state variables' initializers (`x = e;`, in declaration order), then the constructor's modifiers and body, as solkey `a764703bf1`'s `ExpandFunctionBody` prepends them after the renaming |
| `internalCallExpand` | `internalCallExpand` | same | any other call without a summary (`CallRet.summary? … = none`; `internalCallSummary`, below) (`ic`: `f(a);`, `y = f(a);`, a memory return `T memory p = f(a);` or storage return `T storage p = f(a);`, KeY's `InternalCall`, decision 19 of `docs/intrinsic.md`), same premise, frame end and soundness (`Stmt.sound_call`). **Lean only:** it also inlines a callee with modifiers (`wrapMods`), where KeY's `InternalCall` refuses one and leaves the call stuck; and it waits for simple arguments (`functionCallArgCapture`), where KeY's binds `T p = arg` as written. A single storage return enters unset and exports its alias (`CallRet.storage`), as pinned `ExpandFunctionBody` preserves the return variable's data location; source binding follows the call, as for memory. The three native call-receiver capture taclets below retain the getter before its array operation; effectful operands still require deferred capture. A bare call of a function of several returns declares them in its body (`CallRet.none`) |
| `blockReturn`, `functionFrameReturn` | — | unclaimed (architectural) | returns are lowered at elaboration (`lowerReturns`: a `return` in a block splices the block into the statements after it, which is `blockReturn`'s effect), so there is no `return` in `Stmt` to rewrite |
| `functionFrameEmpty` | `functionBodyExpand`, `internalCallExpand` | merged | a call's body is a frame closed over its parameters and returns (`Stmt.call`, `Syntax/Scoped.lean`); the expansion's premise (`Premise.inline`) drops the frame under the return variables it exports once the body is done, which is `function-frame{} ⇝` with nothing printed (the frame's end is a `Thin`, `Calculus/Delab.lean`).  Claimed since the intrinsic refactor; the SolKey reader excuses the row, the pairing being one its shapes cannot see (decision 74) |
| — | `LeanTaclet.functionCallArgCapture` | Lean only | `unfoldArgument`, which solkey's `docs/net.md` lists as missing: the leftmost non-simple argument is captured into a fresh `se` first, so that `Stmt.step` has one rule per call |
| — | `LeanTaclet.internalCallSummary` | Lean only | KeY's contract-based method call (`methodCall` with an operation contract) with the contract derived, not written, which solkey's strategy does not run (it inlines, `internalCallExpand`): a call of one value assigned to a value local (`y = f(a);`, `T y = f(a);`), its arguments simple, whose callee calls and has a summary is one update, `⟨[ y = f(args); ]⟩ ⇝ { y := R(args) } ⟨[ ]⟩`. The summary `R` is the callee's body run symbolically once, in its own frame (`Prog.sym`, `CallRet.sumOf`, `Calculus/CallSummary.lean`): value declarations and assignments, blocks, and calls of the same kind, each read through its callee's summary at its arguments; a term that may revert stays owed by its local until a term that always reads it takes it over, so the update fails exactly where the call reverts. Gated (`Tm.sumGate`): the summary reads value locals only, pushes nothing and is smaller than `16 * body.size + 16`, so `Stmt.step_tmSize_le` still holds. `internalCallExpand` carries the converse side condition (`CallRet.summary? … = none`), so a call has one rule. Sound by `Premise.sound_callSummary` (`Calculus/SoundSummary.lean`: `Prog.sym_sound`, `CallRet.summary_agrees`); `docs/automation.md`, M6 |
| `expand_function_body` parameter declarations | `Args.snocStorage`, `Args.snocMemory`, `Args.declsThen` | same | reference formals retain their data location: storage paths bind aliases, memory paths bind identities, without allocation. The source elaborator's ordered preparation (`hoistCallArgs`) is Lean-only normalization; it emits ordinary reference declarations and storage-to-memory copy statements before the call. Pure value/path evaluations return or revert (`Semantics/RevertOnly.lean`), which justifies primitive capture past an earlier reference without changing failure priority. The SolKey program-rule fragment checks every argument's `keyValues`, including reference indices; the verified EVM fragment currently excludes reference arguments. |
| `emptyModality` | `Proves.empty` (also `Proves.emptyModality`) | ⊢ rule | `⟨[ ]⟩ φ ⇝ φ` under either modality, as KeY's `#allmodal`; the proof tree prints the step under this name (`Calculus/ProofTree.lean`) |
| `impRight` (`propRule.key`) | `Proves.intro` (also `Proves.impRight`) | ⊢ rule | `⟹ a → φ` becomes `a ⟹ φ` |
| `impRight`, `notLeft` (`propRule.key`) | `Proves.notLeft`, `ProvesC.notLeft` | ⊢ rule (deviation) | `⟹ ¬X → φ` becomes `⟹ X`: KeY's succedent keeps `φ` beside `X`, one formula is kept here. The walks take it on a premise that reads a program (`Fml.negModal?`, a self-call's `catch` goal), where `X` closes |
| `impRight`, `hide_left` (`propRule.key`) | `Proves.hideLeft`, `ProvesC.hideLeft` | ⊢ rule | `⟹ a → φ` becomes `⟹ φ`: the walks drop a premise that reads a program where `notLeft` does not close |
| `allRight` (`firstOrderRules.key`) | `Proves.allIntro` (also `Proves.allRight`) | ⊢ rule | `⟹ ∀ T x; φ` becomes `∀ T x ⟹ φ`: the local holds any value of `T`, KeY's skolem constant (`Hyps.all`) |
| `allLeftHide`, `allLeft` (`firstOrderRules.key`) | `Hyps.instAll`, `Hyps.instAll_valid` (`Calculus/AllLeft.lean`), applied by `sol_leaf`; `sol_close_all` (`Calculus/CloseAll.lean`) after opening binders | leaf step (Lean-only term choice) | The scoped pre-pass uses the body under `{x := t}` (`Fml.instTm_holds`), at literal indices and locals of the premise's scope (`Seq.allLeftLits`, `Seq.allLeftBudget`). The closer fallback applies the original universal proof to later `Int`/`Nat` locals or typed value projections, so it moves no term into an older scope. It proves supplied guards and retains unproved ones as implications. Fixed scan, candidate, application and binder budgets bound term choice; `sol_close_all?` prints explicit proof applications. A used premise may be hidden (KeY's `insert_hidden` retains its hidden copy). |
| `closeFalse`, `cut` (`propRule.key`) | `Proves.closeFalse` | ⊢ rule (deviation) | a context the logic refutes (`Γ ⟹ false`) closes any goal. KeY's `closeFalse` has no premise and finds a literal `false ⟹`; solkey derives Lean's rule as `cut` on `false`, its TRUE goal `Γ, false ⟹ φ` closed by `closeFalse`, its FALSE goal `Γ ⟹ false, φ` Lean's premise weakened.  The scoped walk closes a split's branch so when its condition is ground under its updates (`Hyps.groundS`, `Calculus/LeafDerive.lean`, and `Seq.refuteS`, `Calculus/ProvesDerive.lean`); inside the closer, `Facts.refute` (below) |
| `closeTrue` (`propRule.key`) | `Proves.closeTrue` | ⊢ rule | `⟹ true`, behind a context with no diamond update (`Hyps.boxOnly`; scope ends may stand in it) |
| `blockEmpty` | `blockEmpty` (stated by hand); `Frames.pop .block`, `Frames.exit` | same | a block `{ body }` (`Stmt.block`) steps into its body under a block frame, printed `}` (`Fml.show`, `Calculus/Delab.lean`); each branch of a split ends with one too.  When the body is done, `Frames.exit` pops its locals and goes on with the rest, which is `blockEmpty`'s `{} ; rest ⇝ rest` (`Proves.empty`).  Unclaimed until the intrinsic refactor, when a program had no nested block (`docs/intrinsic.md`, M6a) |
| — | `Frames.pop .capture`, `Premise.unfold`'s `Ext` (the capture pop) | Lean only | the scope of the fresh `se`/`sp`/`ie` a rule declares (`T storage sp = nsp; v = sp.fld;`): popped after the rule's statements, so the rest `ω` is never re-typed (Gate G0's condition 6).  KeY's fresh program variables are global and need no end.  Printed as nothing (`Fml.show`, `Delab`), so a premise reads as the solkey taclet; `dl{ … }` inserts it (`RuleSyntax.lean`'s `schemaTacletCore`, under `open scoped Solidity.Schema`) |
| `localValueDeclInitDrop`, `storageLocalDeclInitDrop` | `Premise.bind` (`Stmt.step`'s `declLocal`/`declStorage` arms), `Fml.bind`, `Proves.bind`/`bindIntro` (the hidden binder) | Lean only (the binder) | `T v = e; ⇝ v = e;`: the declared local is put in scope by a binder ("for every value of `v : T`") in front of the assignment, printed as nothing, so the premise reads as solkey's `⟨[ v = e; ]⟩`; KeY's `\addprogvars(v)` |
| `memoryLocalDeclInitDrop` | `Premise.bind` at a memory type (`Stmt.step`'s `declMem` arm with an initializer), `Fml.bind` (the hidden binder) | Lean only (the binder) | `T memory mv = r; ⇝ mv = r;`, the binder as in the row above.  It ranges over the objects of `mv`'s type and over an unset `mv` (decision 17', `docs/intrinsic.md`), as an alias may be unset (`storageLocalDeclSkip`): no statement leaves a memory local unset, but the premise's `mv = r;` from an unset `mv` runs as the declaration does even where `r` allocates, which no existing object gives (`sound_declMemInit`).  A read through an unset memory local reverts (`State.memRefT`, `MPath.mvalT`), as through an unset alias |
| `revertDiamond` | `revertDiamond` | same | closes to `false`: a reverted run satisfies no diamond formula |
| — | `LeanTaclet.assumeFalse` | Lean only | `⟨[ assume(false); ]⟩ ⇝ true` under either modality: the run is assumed away (it halts as exhaustion does, which both accept). solkey has no such statement; `ignoringOverflow { … }` writes it where an operation leaves its range (`docs/options.md`, O5) |
| `revertBox` | `revertBox` | same | closes to `true`. Only revert, send, transfer and try (`revertBox`/`revertDiamond`, `sendNoCallbackBox`/`sendNoCallbackDiamond`, `transferNoCallbackBox`/`transferDiamond`, `tryCallNoCallbackBox`/`tryCallDiamond`) and the loop invariant rules tell the modalities apart: the modality is a parameter of `Taclet`, so every other rule fires under either |

The later-index fallback also reads ABI memory-array premises through local
pushes and counter assignments (`CloseS.push_readId`, `setLocal_readId` and
the corresponding length laws). `index_uint_eta` removes a reconstructed
index's proof from matching, and `exists_val_eq` reuses a captured subtype
value. These are **Lean-only representation normalizations**, not additional
SolKey memory taclets; `Solidity/Examples/Tactics/ArrayScans.lean` supplies the imported loop proofs.

## Storage root/field write & read

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `storageRootWriteStore`, `storageRootWriteCopySource`, `storageRootReadSelect` | same names | same | |
| compatible fixed-array copy through `storageRootWriteCopySource` / `storageFieldWriteCopySource` and `pushStoreSource` | `LeanTaclet.storageFixedCopySave`, `LeanTaclet.pushFixedCopySave` | Lean-only typed adapters | `FixedCopy` changes only the outer shape: fixed to dynamic, or to a longer/equal fixed array, with the same mapping-free element type. `Op1.fixedCopy` preserves one snapshot; `FixedCopy.observe_apply`, `Src.lower_valueT` and `fixedCopyRd_rep` justify its lazy reader. The destination uses ordinary `save`/overlay. Missing source values retain their failure guard. KeY erases these outer types into `Struct`; the adapters are excluded from the native fragment and EVM compiler. A term prints and reads as `fixedCopy(T, source)`, `T` the destination type (`NSValT.fixedCopy`; `tm{ … }`, `SValT.fixedCopyTo`), so a composed conversion keeps each length; a destination type not known at printing (a schema variable) prints as an exact Lean escape.  A line is written with the conversion, not the copy it came from: `save(storage, d2, find(storage, d1))` reads as another line than `save(storage, d2, fixedCopy(uint[], find(storage, d1)))`. |
| `storageFieldWriteSave`, `storageFieldWriteCopySource` | same names | same | |
| `storageFieldReadBindLocalRoot`, `storageFieldReadStoreRoot` | same names | same | |
| `storageFieldReadFind` | `storageFieldReadFind`, `storageLengthRead` | same | the second at the member `length`: `v = sp.length ⇝ { v := sp.length }`, the term `Term.len` (KeY's `find(storage, sp.size)`) |
| `storageFieldRead_unfold_rightFst` | `storageFieldRead_unfold_rightFst`, `storageLengthRead_unfold_rightFst` | same | the second: `v = nsp.length ⇝ T storage sp = nsp; v = sp.length` (a length is a `Val`, not a typed-syntax member) |
| `storageFieldRead_unfold_rightSndResult` | `storageFieldRead_unfold_rightSndResult` | same | also claims `storageFieldWriteCaptureSrc` |
| `storageFieldWriteCaptureSrc` | `storageFieldRead_unfold_rightSndResult` | merged | the chain also captures a complex storage source into a fresh local |
| `storageFieldWrite_unfold_leftFst` | `storageFieldWrite_unfold_leftFst` | same | `nsp.fld = e ⇝ T se = e; T storage sp = nsp; sp.fld = se`: the value is frozen into `se` before the receiver is captured |
| `storageFieldWriteStorageRef_unfold_leftFst` | `storageFieldWriteStorageRef_unfold_leftFst` | same | the reference-source twin: no freeze (a reference is aliased, not read) |

## Storage index (mapping and array)

Each array rule takes an implicit `ak : ArrTy R E` (`IndexTy.arr ak`), `dyn`
for `T[]` and `fixed` for `T[n]`, so one constructor covers both kinds as
solkey's `Path[…,array]` sort does; the memory index rules take the same
argument.

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `storageIndexWriteMappingSave`, `storageIndexReadMappingFind`, `storageIndexReadMappingBindLocalRoot`, `storageIndexWriteMappingCopySource`, `storageIndexReadMappingStoreRoot` | same names | same | |
| `storageIndexWriteArraySave` | same | same | one rule for both modalities; an out-of-range write reverts in the path's own bounds check (`PTerm.at`, `Storage.checkIndex`), not as a separate goal |
| `storageIndexReadArrayFind`, `storageIndexReadArrayStoreRoot`, `storageIndexWriteArrayCopySource` | same names | same | |
| `storageIndexReadArrayBindLocalRoot` | same | same | `lsv = darr[ie]`, a non-mapping element (`nonMappingElement`, `SPath.elemMapping darr = false`) |
| `storageIndexReadArrayBindLocalRootMappingElement` | same | same | `lsv = marr[ie]`: KeY's `atMap(ie)` is the same `Seg.at` here, a mapping being what `delete` leaves alone |
| `storageIndexWriteStorageRefRhsCapture` | `storageIndexRead_unfold_rightSndResult` | merged | a reference source at an index is hoisted into `se`, the storage twin of the field case |
| `storageIndexRead_unfold_rightSndResult` | same | same | also claims the row above |
| `storageIndexRead_unfold_rightSndIndex`, `storageIndexRead_unfold_rightFst` | same names | same | |
| `storageIndexWriteCaptureAllNonSimpleIndex` | same | same | `sp[nse] = e ⇝ T se = e; T storage sp' = sp; T ie = nse; sp'[ie] = se`: the simple receiver is bound again, as KeY does |
| `storageIndexWriteStorageRefCaptureAllNonSimpleIndex` | same | find same | `… sp'[ie] = path`: KeY also binds the source to an alias `rv`; a copy source is written as it stands (`kernel-port.md`, Decisions) |
| `storageIndexWriteCaptureAllComplexRecv` | same | same | `nsp[e1] = e2 ⇝ T se = e2; T storage sp = nsp; T ie = e1; sp[ie] = se` |
| `storageIndexWriteStorageRefCaptureAllComplexRecv` | same | find same | the source is not captured, as above |

## Storage push / pop

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `storagePushValue_unfold_leftFstReceiver`, `storagePush_unfold_leftFstReceiver`, `storagePop_unfold_leftFstReceiver`, `storageLocalRootPush_unfold_leftFstReceiver`, `storagePushValueSave` | same names | same | |
| `storagePushValue_unfold_leftCallReceiver`, `storagePush_unfold_leftCallReceiver`, `storagePop_unfold_leftCallReceiver` | same names | same on typed sources | Retain `fc` until its native capture, evaluate the getter once, bind its returned alias, then push/pop. The value-push taclet covers both pure sources and scoped deferred prefixes; operand effects run after getter validation. `ProvesC.unfoldReceiver` preserves callbacks in the getter and prefix through exact capture correspondence. |
| `storagePushLengthSave` | same | same | `parr.push()`: a primitive element, the slot cleared (`STerm.pushSlot`) |
| `storagePushLengthSaveReferenceElement` | same | same | `rarr.push()`: a nonmapping reference element, the recycled slot exposed as it is, with the length saved (`STerm.pushSlot`); read as the default only under `cleanTail(storage)` (`docs/options.md` O6) |
| `storagePushLengthSaveMappingElement` | same | same | `marr.push()`: the length-only save (`STerm.extend`), mapping entries preserved |
| `storagePushValueCopySource` | same | reference-copy case | Direct storage-reference copy requires both `sp1` and `sp2` simple, matching upstream's path conditions. Complex reference sources use the named capture below. |
| `storagePushMemoryCopySource` | same | same | A simple receiver and memory variable use one update, with `copyMem(mtSt, memory, mv)` at the old length and the incremented length. The typed source is `Src.copyMem`; the receiver is resolved once. |
| `pushMemorySourceCapture` | none | Lean-only | A complex memory source is bound to a memory local before the native copy. This extension is excluded from the SolKey fragment; it is not claimed as an upstream expression-capture taclet. |
| `storageMemorySourceSave` | none | Lean-only | An embedded `Src.copyMem` storage assignment uses the existing save symbol directly. Ordinary Solidity memory-to-storage assignment still elaborates to `Stmt.assignFromMem` and its upstream rules. |
| `storagePushValue_unfold_rightFstReferenceArgument` | same | same | `sp.push(nsp)` binds `T storage source = nsp` before copying through that alias. The alias names the source; the appended value is a deep copy, including when source and destination share an array. |
| `storagePushValue_unfold_rightFstPrimitiveArgument` | same | same | `sp.push(nsp)` reads a complex primitive storage path into `T source` once before the push. |
| `storagePushValue_unfold_rightSndArgument` | same | expression case | The general non-simple primitive-expression capture excludes direct complex storage reads, which use the preceding rule. Other arithmetic and memory reads retain the expression capture. |
| `storagePushAddAssign`, `storagePushSubAssign`, `storagePushMulAssign` | same names | same | Typed numeric push compound assignments: reset and extend, then a sequential save of the appended primitive's arithmetic result. Kernel correspondence, typed text roundtrips and checked source statement elaboration are registered. Returned suffix values and unchecked push arithmetic remain unsupported. |
| `storagePushDivAssign`, `storagePushModAssign` | same names | same | Outer nonzero guard; its true branch keeps the two updates and its false branch reverts. The sound false-branch simulation also permits interpreter capacity exhaustion. |
| `storagePushPreincrement`, `storagePushPostincrement`, `storagePushPredecrement`, `storagePushPostdecrement` | same names | same | Discarded numeric increment/decrement statements: reset and extend, then update the appended slot. No returned prefix/postfix value is claimed. |
| `addAssignValueRhsCapture`, `subAssignValueRhsCapture`, `mulAssignValueRhsCapture`, `divAssignValueRhsCapture`, `modAssignValueRhsCapture` | `pushCompoundAssignValueRhsCapture` | merged | These existing general RHS captures accept a push expression as their assignment target; this adds no upstream taclet name to the inventory. |
| — | `LeanTaclet.pushCompoundUnfoldReceiver`, `LeanTaclet.pushIncrementUnfoldReceiver` | Lean only | Capture the receiver once after the compound assignment's RHS. Outside the SolKey fragment. |
| `storageLocalRootPushBind`, `storageLocalRootPushBindMappingElement` | same names | same | `lsv = darr.push()` / `marr.push()` |
| `storageLocalPrimitivePushBind` | same | deviation | `uint y = values.push();`, `y = values.push();` with `y` a value local (`Stmt.assignLocalPush`): the array grown as `storagePushLengthSave` grows it (`STerm.pushSlot`), and `y := defVal(T)`, the default the cleared slot holds, where KeY reads it back, `find(delAt(storage, sp[n]), sp[n])`: Lean's typed `delAt` has no reading at the slot past the end. The receiver is simple at this rule; the calculus captures a complex receiver with the native rule below. The declaration form is two statements (`valueDeclSkip`, then this rule), where KeY fires `localValueDeclInitDrop` first |
| `localValuePush_unfold_leftFstReceiver` | same | same | `v = nsp.push()` becomes `T storage sp = nsp; v = sp.push()` for a complex primitive-array receiver. `Stmt.assignLocalPush` retains the receiver; `assignLocalPushStep` chooses this capture or the disjoint simple-receiver update. |
| `storagePopSave` | same | same | `darr.pop()`, both modalities: the element cleared into the recycled slots (`STerm.pop`) |
| `storagePopSaveMappingElement` | same | same | `marr.pop()`: the element kept (`STerm.shrink`) |

A push is one term, not KeY's two parallel `save`s (see "Deviations").

## Storage local declarations

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `storageLocalDeclInitDrop`, `storageLocalRootRebind` | same names | same | |
| `storageLocalDeclSkip` | same | deviation | `T storage lsv; ⇝ {lsv := unset} ⟨[ ]⟩`, where KeY's `\replacewith` is the empty program: the alias is bound to no path (`Rhs.unset`, an alias at `none`), so a read or a write through it reverts, and a loop's next iteration does not see the previous one's binding.  solc rejects such a read statically; Lean only, the printer shows `lsv := unset`.  The update declares the alias (`Upd.decl lsv Rhs.unset`, `Rhs.unset`): the local is in scope after it, at its alias type, bound to no path |

## Storage delete

Since `048a74de51`, solkey's `delete` and `pop()` taclets no longer exclude a
path through a fixed-size array element (`noFixedArrayElement` was dropped from
`storageRootDelete`, `storageFieldDelete`, `storageIndexDelete`,
`storageIndexArrayDelete` and `storagePopSave`). The Lean constructors never
had that restriction: `SVal.defaultOf` keeps a fixed-size array's `n` elements
(reset) where it empties a dynamic one, and `push`/`pop` are written at
`.array` only.

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `storageRootDelete` | same | same | `delete(gsp) ⇝ { storage := delAt(storage, gsp) }` |
| `storageFieldDelete`, `storageFieldDelete_unfold_leftFst`, `storageIndexDelete_unfold_leftFst`, `storageIndexDeleteNonSimpleIndexCapture` | same names | same | |
| `storageIndexDelete` | same | same | a mapping entry |
| `storageIndexArrayDelete` | same | same | KeY's `inBounds` split is the path's own bounds check, which reverts; where it reads as `true`, the reduction lowers the path as the plain index (`foldAt`), as KeY's closed branch leaves `at(i)` |

## Memory allocation, aliasing, declarations

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `memoryReferenceDeclFreshAlloc` | same | same | `T memory mv; ⇝ { mv := freshId(addM(memory)) ‖ memory := addM(memory) }`, the pair KeY writes: `ITerm.alloc` and `MTerm.addM` agree on the minted root because both read the same pre-state |
| `memoryArrayFreshAlloc` | same | same | `mv = new T(se); ⇝ { mv := freshId(copySt(memory, newArr(se))) ‖ memory := copySt(memory, newArr(se)) }`: Lean copies in `newArrVal R n` (defaults, each struct element its own object, as solc allocates) where KeY writes `size`; a non-simple size is captured by the elaborator |
| `newArrayCapture`, `newArrayCaptureStorageRoot` | `newArrayCapture` | merged | `tgt = new T(se) ⇝ T memory mv = new T(se); tgt = mv`, `tgt` a storage or memory location (`NewLhs`), including a storage root (`NewLhs.store (.root …)`). The shared replacement binds the same fresh memory local before copying it to either target. |
| `memoryRootDeleteFreshRebind` | same | same | `delete mv; ⇝` the allocation pair (see "Memory delete") |
| `memoryRootRebind` | same | same | `mv₁ = mv₂; ⇝ { mv₁ := mv₂ }`; a storage right-hand side is `memoryStorageCopy` |
| `memoryStorageCopy` | same | same | `mv = sp;` deep copy: fresh identity plus `copySt` |
| `memoryStorageCopyUnfold` | same | same | a complex storage path is captured first |
| `memoryLocalDeclInitDrop` | same | same | one generic decl-with-init split; the assignment rules take over |

## Memory field/index write & read

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `memoryFieldWrite` | `memoryFieldWrite`, `memoryFieldWriteCopy` | merged | Lean's sorts are not generic: a value source and a reference-path source are two rules |
| `memoryIndexWriteArray` | `memoryIndexWriteArray`, `memoryIndexWriteCopy` | merged | likewise; KeY's `inBounds`/`outOfBounds` split is the write's own bounds check, which reverts |
| `memoryFieldRead` | `memoryFieldRead`, `memoryFieldReadAliasRoot`, `memoryLengthRead` | merged | the same split on reads (a value lands on a local, a reference on a memory alias); `memoryLengthRead` is the member `length` (`Term.mlen`, KeY's `read(memory, mv, size)`) |
| `memoryIndexReadArrayValue` | same | same | KeY's `inBounds`/`outOfBounds` split is the read's own bounds check, which reverts |
| `memoryIndexReadArrayMemory` | same | same | likewise |
| `memoryFieldRead_unfold_rightFst` | `memoryFieldRead_unfold_rightFst`, `memoryLengthRead_unfold_rightFst` | same | |
| `memoryFieldRead` at `size` | `Grown.lenId`, `CloseS.eval_mlen` | bridge | packages the existing `HRef.ofId?`/`Heap.lenU` length read with a heap-independent result type. `Landed.memT_lenId` and `push_memT_lenId` transport it across unchanged globals and local pushes; `Grown.lenId_ref` resolves an intrinsically valid identity. Invalid identities still fail. This repairs closer normalization, without a new taclet or a range assumption. |
| `memoryIndexRead_unfold_rightFst`, `memoryIndexRead_unfold_rightSndIndex` | same names | same | |
| `memoryFieldWrite_unfold_leftFst` | same | same | also claims the row below |
| `memoryFieldWriteMemRef_unfold_leftFst` | `memoryFieldWrite_unfold_leftFst` | merged | `msrc` is a value or a memory reference, one rule for both |
| `memoryIndexWriteCaptureAllComplexRecv` | same | same | `nmp[e1] = e2 ⇝ T se = e2; T memory mv = nmp; T ie = e1; mv[ie] = se` |
| `memoryIndexWriteMemRefCaptureAllComplexRecv` | same | find same | `… mv[ie] = mpath`: a memory path is a source as it stands |
| `memoryIndexWriteCaptureAllNonSimpleIndex` | same | find same | `mv[nse] = e ⇝ T se = e; T ie = nse; mv[ie] = se`: KeY rebinds the receiver (`T memory mv' = mv`); the receiver is already a simple memory local, typed by its position, so the rebinding would only rename it: left out to keep the rule text and its fresh names (a deviation in shape) |
| `memoryIndexWriteMemRefCaptureAllNonSimpleIndex` | same | find same | `mv[nse] = mpath ⇝ T ie = nse; mv[ie] = mpath` |
| `memoryFieldWriteCaptureSrc`, `memoryIndexWriteMemRefRhsCapture`, `memoryFieldRead_unfold_rightSndResult`, `memoryIndexRead_unfold_rightSndResult` | — | unclaimed | KeY captures a memory reference into an alias before using it as a source; here a memory path is a source as it stands (`mpath`), so `memoryFieldWriteCopy` writes it in one step. A value read is captured by the value-RHS rules below |

## Memory delete

`Stmt.deleteMem p` deletes a memory local, a member or an element. KeY's
primitive/reference split (`\hasMemoryFieldSort(fld, alphaPrim)`,
`Path[…,primitiveElement]`) is the type the rule fixes: `T := Ty.prim p`
against `T := Ty.ref R` (the stems in `RuleSyntax.lean`'s table). KeY's
`inBounds` split of an index delete is the write's bounds check, which reverts.

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `memoryRootDeleteFreshRebind` | same | same | listed above, with the allocation rules |
| `memoryFieldDeletePrimitive` | same | same | `{ memory := write(memory, mv.pfld, defVal(T)) }` |
| `memoryFieldDeleteReference` | same | same | `{ memory := write(addM(memory), mv.rfld, freshId(addM(memory))) }`: the member gets a fresh default object |
| `memoryIndexDeletePrimitive`, `memoryIndexDeleteReference`, `memoryFieldDelete_unfold_leftFst`, `memoryIndexDelete_unfold_leftFst`, `memoryIndexDeleteNonSimpleIndexCapture` | same names | same | |

## Memory → storage copies

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `memoryToStorageStoreRoot`, `memoryToStorageIndexMappingCopyRoot`, `memoryToStorageField_unfold_leftFst` | same names | same | |
| `memoryToStorageFieldCopyRoot` | same | same | also claims the row below |
| `memoryToStorageFieldCopyField` | `memoryToStorageFieldCopyRoot` | merged | the one member-source shape, read directly |
| `memoryToStorageIndexArrayCopyRoot` | same | same | both modalities |
| `memoryToStorageIndexCaptureAllComplexRecv` | same | find same | `nsp[e] = mpath ⇝ T storage sp = nsp; T ie = e; sp[ie] = mpath`: the memory source stands (KeY: `T memory rv = src`) |
| `memoryToStorageIndexCaptureAllNonSimpleIndex` | same | find same | `sp[nse] = mpath ⇝ T storage sp' = sp; T ie = nse; sp'[ie] = mpath` |

## Value declarations and value-RHS capture

KeY writes the value-RHS captures once, at any receiver; Lean states one
instance per receiver kind, the memory ones claiming the same taclet as the
storage ones.

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `localValueDeclInitDrop` | same | same | |
| `valueDeclSkip` | same | find same | `T v; ⇝ { v := defVal(T) } ⟨[ ]⟩`: KeY drops the declaration (`\addprogvars(v)`) and leaves `v` unconstrained; a Lean declaration is its default, as solc's |
| `localValueAssign` | same | same | terminal `v = se;` |
| `storageRootWriteValueRhsCapture` | same | same | `gsp = nse; ⇝ T se = nse; gsp = se;` |
| `fieldWriteValueRhsCapture` | `fieldWriteValueRhsCapture`, `memoryFieldWriteUnfoldSource` | same | the second is the memory instance |
| `indexWriteValueRhsCapture` | `indexWriteValueRhsCapture`, `memoryIndexWriteUnfoldSource` | same | likewise |

## Operators

One constructor per **shape**, not per operator: `op : BinOp` is a free
variable, so an instance is `binopAssignment (op := .add)`. The comparison and
boolean operators share the arithmetic constructors. The proof tree prints a
node of an operator family as KeY's taclet at its operator
(`RuleShapes.operatorOrder`, `keyTacletAt`): `binopAssignment` at `==` is
`boolEqualityAssignment`.

| KeY taclets | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `{addition,subtraction,multiplication,power,division,modulo}_unfold_left`, `{boolEquality,boolInequality,lessThan,greaterThan,lessEqual,greaterEqual,logicalAnd,logicalOr}CaptureLhs` | `binopUnfoldLeft` | merged | `v = nse ⊕ e; ⇝ T se = nse; v = se ⊕ e;` |
| `{addition,…,modulo}_unfold_right`, `{boolEquality,boolInequality,lessThan,greaterThan,lessEqual,greaterEqual}CaptureRhs` | `binopUnfoldRight` | merged | requires `¬ op.shortCircuits`; `&&`/`||` have the short-circuit rows below |
| `{addition,subtraction,multiplication,power,division,modulo}Assignment`, `{boolEquality,boolInequality,lessThan,greaterThan,lessEqual,greaterEqual,logicalAnd,logicalOr}Assignment` | `binopAssignment` | merged | terminal `v = se₁ ⊕ se₂;`; `**` is checked `uint` exponentiation (`op := .pow`); solkey has no `**=` taclets |
| `bitAndAssignment`, `shiftLeftAssignment`, `shiftRightAssignment`; `bitAnd_unfold_{left,right}`, `shiftLeft_unfold_{left,right}`, `shiftRight_unfold_{left,right}` | `binopAssignment`, `binopUnfoldLeft`, `binopUnfoldRight` | merged | `&` and `>>` at `uint` or `int` (two's complement, `uintBitwise`; `>>` rounds toward `-∞`), `<<` at `uint`, wrapping as solc (deviation: solkey's `shiftLeftAssignment` writes the unbounded `se1 * 2^se2`); solkey's `binaryAnd*` lemmas are closer clauses (below) |
| `logicalAndShortCircuitRhs`, `logicalOrShortCircuitRhs` | same names | same | `v = se && nse; ⇝ if (se) { v = nse; v = v && true; } else { v = false; }`, and its dual |
| `logicalNotCapture`, `unaryMinusCapture` | `unopCapture` | merged | |
| `logicalNotAssignment`, `unaryMinusAssignment` | `unopAssignment` | merged | |
| `ternaryCaptureCond` | same | same | |
| `ternaryToIf` | same | same | also claims the row below |
| `ternaryToIfStorage` | `ternaryToIf` | merged | one rule for a local or storage target; a memory target is lowered the same way, a conditional never being a write's source (`Val.notTernary`) |

## Compound assignment

The frozen upstream inventory has no native `addmod`/`mulmod` taclets.
`LeanTaclet.addmodAssignment` and `LeanTaclet.mulmodAssignment` preserve the
three typed operands in `Op3.modular`, using unbounded intermediate
arithmetic (`ModOp.evalT`). Literal folding (`foldModular`) has a general
evaluation-preservation proof, `foldModular_eval`; symbolic operands remain
native terms. These are **Lean-only**, excluded recursively from
`Stmt.inSolkey` even in initializers and path indices. They are outside the
verified EVM compiler fragment. Their regression and imported proof are
`Examples/Tactics/ModularArithmetic.lean` and `TestSuite/Derived18.lean`.

`LeanTaclet.hashAssignment` (`v = hash(mpath)` is
`{ v := hash(memory, mpath) }`, `Op2.hash`, the hash `hh : HashKind` a schema
variable: `keccak256`, `sha256`, `ripemd160`, `ecrecover`) has no solkey
taclet: solkey has no hash (`docs/semantic-gaps.md`, "Hashing and the ABI");
the hashes are Keccak-256, SHA-256 and RIPEMD-160 (`keccakBytes`,
`sha256Bytes`, `ripemd160Bytes`; `Keccak.lean`, `Hashes.lean`), kept from
unfolding, and `ecrecover` an address uninterpreted where the signature is
well formed (`ecrecoverBytes`).
**Lean-only**, excluded from `Stmt.inSolkey` (`Val.keyValue`) and from the
EVM compiler's fragment.

Pattern per `⊕ ∈ {Add, Sub, Mul, Div, Mod}`; one constructor per receiver
shape, `op` free. Mapping and array stay **separate** here, unlike increments.

| KeY taclets | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `local{Add,…,Mod}Assign` | `localOpAssign` | merged | terminal `v ⊕= se;` |
| `storageRoot…Assign` | `storageRootOpAssign` | merged | |
| `storageField…Assign` | `storageFieldOpAssign` | merged | |
| `storageIndexMapping…Assign` | `storageIndexMappingOpAssign` | merged | |
| `storageIndexArray…Assign` | `storageIndexArrayOpAssign` | merged | no bounds split: the update reverts in the path's bounds check |
| `memoryField…Assign` | `memoryFieldOpAssign` | merged | |
| `memoryIndexArray…Assign` | `memoryIndexArrayOpAssign` | merged | no root or mapping form: a memory root binds an identity, memory has no mappings |
| `storageField…Assign_unfold_leftFst` | `storageFieldOpAssignUnfoldLeftFst` | merged | `nsp.fld ⊕= se; ⇝ T storage sp = nsp; sp.fld ⊕= se;` |
| `storageIndex…Assign_unfold_leftFst` | `storageIndexOpAssignUnfoldLeftFst` | merged | |
| `memoryField…Assign_unfold_leftFst` | `memoryFieldOpAssignUnfoldLeftFst` | merged | |
| `memoryIndex…Assign_unfold_leftFst` | `memoryIndexOpAssignUnfoldLeftFst` | merged | |
| `{add,sub,mul,div,mod}AssignValueRhsCapture` | `compoundAssignValueRhsCapture` | merged | location-neutral capture of a non-simple RHS |

## Increment / decrement

Pattern per `{Pre,Post}{increment,decrement}`. A decrement is `x−−`/`−−x` in
`sol{ … }`; an `++`/`−−` inside an expression is captured by the elaborator
(`uint se1; se1 = i++;`), so it reaches these rules as a statement. Here a
mapping and an array receiver **do** share one constructor: solkey splits the
receiver kind, Lean does not.

| KeY taclets (all four `Pre/Post × increment/decrement`) | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `local…` | `localIncrement` | merged | bare `v⊕⊕;` on a stack local |
| `storageRoot…`, `storageField…` | `storageRootIncrement`, `storageFieldIncrement` | merged | |
| `storageIndexMapping…`, `storageIndexArray…` (8) | `storageIndexIncrement` | merged | one constructor over both receiver kinds |
| `memoryField…`, `memoryIndexArray…` | `memoryFieldIncrement`, `memoryIndexArrayIncrement` | merged | |
| `storageField…_unfold_leftFst`, `storageIndex…_unfold_leftFst`, `memoryField…_unfold_leftFst`, `memoryIndex…_unfold_leftFst` | `storageFieldIncrementUnfoldLeftFst`, `storageIndexIncrementUnfoldLeftFst`, `memoryFieldIncrementUnfoldLeftFst`, `memoryIndexIncrementUnfoldLeftFst` | merged | |
| `localAssign…`, `localDecl…` (8) | `localAssignIncrement` | merged | `v = lv⊕⊕;`; KeY has one taclet for the assignment and one for the declaration, Lean reaches the declaration through `localValueDeclInitDrop` |
| `storageRoot…Assignment`, `storageField…Assignment`, `storageIndexMapping…Assignment`, `storageIndexArray…Assignment` (8), `memoryField…Assignment`, `memoryIndexArray…Assignment` | `storageRootIncrementAssignment`, `storageFieldIncrementAssignment`, `storageIndexIncrementAssignment`, `memoryFieldIncrementAssignment`, `memoryIndexArrayIncrementAssignment` | merged | |

## Assert, require, if-then-else

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `assertConditionCapture` | same | same | |
| `assertSimple` | same | same | KeY's two branches: "Holds" `se = true ⟹ ⟨[ ]⟩` and "Violated" `se = true` (`Premise.check`, `Proves.check`); a failed `assert` panics (`THalt.panic`), which neither modality accepts (`Modality.afterRunTR`) |
| `requireConditionCapture` | same | same | the assert capture over `Stmt.require` |
| `requireSimple` | same | find same | reshaped: `require(se); ⇝ se = true ⟹ ⟨[ ]⟩ ; se = false ⟹ ⟨[ revert(); ]⟩`. KeY writes each goal as a disjunction, "Holds" `se = FALSE \| ⟨[ ]⟩ post` and "Reverts" `se = TRUE \| ⟨[ revert(); ]⟩ post`; for a `bool` each is the implication Lean's `.split` premise states with the condition in the context: KeY's two goals under either modality (`Proves.split`) |
| `ifElseUnfold` | same | same | also claims `ifUnfold` |
| `ifUnfold` | `ifElseUnfold` | merged | `Stmt.ite` always has both branches (an absent `else` is `[]`) |
| `ifElseSplit` | same | same | where the branches are not joinable (`LeanTaclet.ifElseJoin`, below; a side condition, `Upd.ifJoin? … = none`): `if (se) thenStm else elseStm; ⇝ "if s#se true": se = true ⟹ ⟨[ thenStm ]⟩ ; "if s#se false": se = false ⟹ ⟨[ elseStm ]⟩`: a `.split` premise is the two-goal shape. The labels are the taclet's text (`Taclet.branchLabels`); the proof tree fills in `s#se` with the node's condition, as KeY's `NodeInfo.setBranchLabel` does (`if true true`). The derivation has KeY's two goals under either modality (`Proves.split`; `splitBox` in a walk is the same rule): the condition is a typed `bool`, so no third goal says it is one.  Also claims `ifSplit` |
| `ifSplit` | `ifElseSplit` | merged | |
| — | `LeanTaclet.ifElseJoin` | Lean only | KeY's join after a conditional (its merge rule with the `ifThenElse` merge procedure), which solkey's strategy does not run: an `if` on a simple condition with one branch empty and the other empty or one assignment of a value local (`Prog.joinable`, `Upd.ifJoin?`, `Calculus/Arms.lean`) is one update, `if (se) { x = x + 1; } ⇝ { x := se ? x + 1 : x } ⟨[ ]⟩`, its right-hand side read where the `if` starts. An `if` that assigns in both branches splits: `Upd.ifJoin` joins it soundly too, but the closers read its two cases more cheaply than the conditional term. The rest of the program runs once, not once per branch (`docs/automation.md`, M6). Sound by `sound_iteJoin` (`Calculus/SoundControl.lean`): such a branch never panics, never diverges and hands control to nobody, and the conditional term evaluates only the side its condition picks, so the update fails exactly where the branch the condition picks reverts. `ifElseSplit` carries the converse side condition (`Upd.ifJoin? … = none`), so an `if` still has one rule |
| `ifTrue`, `ifFalse`, `ifElseTrue`, `ifElseFalse`, `ifElseNegated` | — | unclaimed | `concrete_solidity` strategy shortcuts. A literal is simple, so `ifElseSplit` applies (one goal assumes `true = false`); `!se` is not simple, so `ifElseUnfold` captures it. The table has no strategy |

## Payments

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `transfer_unfold_leftFstReceiver`, `transfer_unfold_rightSndArgument` | same names | same | |
| `transferNoCallbackBox` | same name | extended | One terminal `pay(sadr, se)` update records the hypothetical successful ledger and balance debit. The runtime separately checks funds and the payment response; refusal reverts and satisfies the box. Self-payment moves neither balance nor ledger. The added balance effect is a Lean extension of KeY's net booking. |
| `transferNoCallbackDiamond` | — | not ported | KeY's two goals, "non-negative amount" `0 <= se` and "transfer booked" (the box's booking under the diamond), have no counterpart: a payment under the diamond closes to `false` instead (`LeanTaclet.transferDiamond`, below), which is sound and proves less |
| `transferWithCallbackBox` | `CallbackTaclet.transferWithCallbackBox` | same | a constructor of `CallbackTaclet`, sound for the callback reading (`holdsC`), not of `Taclet`. The premise is `transferNoCallbackBox`'s booking `U`, read as KeY's two goals (`holdsC_transferCb`): `{U} I` ("invariant on exit") and `{U} {havoc} (I → [ ω ] φ)` ("resume after callback"; `{havoc}` is KeY's anonymising update, read by `ExecS.transferResume`). Used by `ProvesC` |
| `transferWithCallbackDiamond` | — | not ported | No diamond transfer rule: runtime refusal reverts, so normal completion requires an acceptance premise that the calculus does not expose. |
| `send_unfold_leftFstReceiver`, `send_unfold_rightSndArgument` | same names | same | the transfer captures over `Stmt.send` (`pv = sadr.send(se);`, `pv` a `bool` local): the receiver first, then the amount, each into a fresh `uint se`, as for `transfer`. `bool ok = r.send(a);` is `bool ok; ok = r.send(a);`, so Lean fires `valueDeclSkip` where solkey fires `localValueDeclInitDrop` (same node count; the default is set, then overwritten by the send) |
| `sendNoCallbackBox` | same name | extended | Two labeled goals: successful `pay(sadr, se)` with `pv := true`, and unchanged globals with `pv := false`. `TRun.send` chooses using available funds and the transaction oracle. The amount is intrinsically unsigned. The success update includes the Lean balance extension. |
| `sendNoCallbackDiamond` | same name | extended | The same two outcomes after KeY's retained non-negative-amount goal. Refusal returns false normally; the hypothetical success update is a stronger sufficient premise independent of acceptance. |
| `sendWithCallbackBox` | `CallbackTaclet.sendWithCallbackBox` | extended | Invariant on exit after `pay`, success after `pay` and `pv := true` followed by storage/ledger/balance havoc under the invariant, and refusal with `pv := false`. `ExecS.sendRefused` covers runtime refusal, and the callback relation may also refuse an otherwise accepted send. |
| `sendWithCallbackDiamond` | `CallbackTaclet.sendWithCallbackDiamond` | same | `sendWithCallbackBox` under the diamond, with "non-negative amount" `0 <= se` (`sendNoCallbackDiamond`'s formula goal), read by `ProvesC.sendD` (`holdsC_sendCb`, over any modality): a send's refusal is an outcome of the run (`TRun.send`), so the diamond is the run's; a lowered or written value call (`Stmt.send`'s `full`) takes it under either `transferSemantics` (`docs/options.md`, O4) |
| `(bool ok, ) = a.call{value: v}("")` | — | front end | not a taclet: solkey's parser lowers exactly this shape to `bool ok = a.send(v);` (`SolJSONParser.isValueCall`); Lean keeps it, a send with all the gas (`Stmt.send`'s `full`, the solc import's `valueCall?`, `sol{ (bool ok, ) = a.call{value: v}(""); }`). **Deviation from solkey**, its bug 5: a value call forwards all gas, so its callee may call back under `transferSemantics:noCallback` too (`ValidT .noCallback`, `Stmt.forksIn`, `docs/options.md`); the send rules apply under `Fml.Valid`, which reads every callee as keeping the state |

## External calls (`try`/`catch`)

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `tryCallNoCallbackBox` | same | same | sound for `Fml.Valid` (every callee keeping the state), solkey's reading; under `ValidT .noCallback` a `try` calls back and takes `tryCallWithCallbackBox` (`ProvesC I false`, solkey's bug 5, `docs/options.md`). One goal per clause (`Premise.branches`, `Proves.branches`): "call succeeded", "Error caught", "Panic caught", "other failure caught". KeY declares the return locals and the `Panic` code without an initializer, leaving them unconstrained; here they are bound under `∀` (`Hyps.all`), since a Lean declaration is its default. `s#call` is an `ExtCall`, whose receiver and arguments are simple: the elaborator captures any other before the `try` |
| `tryCallWithCallbackBox` | `CallbackTaclet.tryCallWithCallbackBox` | same | read by `ProvesC.tryCall` (`holdsC_tryCb`): `I` where control leaves ("invariant on exit"), the success block after `{havoc}` and `I` ("call succeeded"), each `catch` block from where the call was made |
| — | `LeanTaclet.tryCallSelfBox` | Lean only | a `try` whose callee is a function of the contract declared before the caller (`Stmt.tryCall`'s `self`, `docs/options.md` O8): solkey's `try` never runs a callee. Five goals: the receiver the contract (`require(a != 0); require(a == address(this));`), the callee inlined with the returned values as targets (`.call … (.rets rets)`, `functionBodyExpand`) and then the success block; the receiver another (`require(a != 0); require(a != address(this));`), the success block for every value of the returned data; each `catch` block from the caller's state, which a failed self-call goes to, behind `fails(call)`: `¬⟨ require(a == address(this)); f(args) → rets; ⟩ true` (`ExtCall.selfFails`, `Branch.hyp`), the call not ending normally as a self-call; the `Panic` block behind the codes the callee may panic with, `require(a != address(this) || c == k₁ || …);` (`CodeBinder.guard`, `Prog.panicCodes`, printed `panics(selfBody) →`), where they are known. `tryCallNoCallbackBox` takes only a `try` with no such callee (`self = false`) |
| — | `ProvesC.trySelf` (with `LeanTaclet.tryCallSelfBox`) | Lean only | `tryCallSelfBox` read with callbacks (`holdsC_trySelfCb`, `docs/options.md` O8), as `ProvesC.tryCall` reads `tryCallNoCallbackBox`'s goals: `I` where control leaves; the self goal as `tryCallSelfBox`'s, the callee inlined and run with callbacks; the other receiver's goal after `{havoc}` and `I`; each `catch` block from where the call was made, behind `fails(call)` |
| — | `LeanTaclet.tryCallSelfDiamond` | Lean only | a self-call `try` under the diamond closes to `false`, as `tryCallDiamond` |
| — | `LeanTaclet.recursiveCallUnfold` | Lean only | `⟨[ f(args); ]⟩ ⇝ ⟨[ f(args); ]⟩`, a recursive call (`Stmt.callRec`) read as the ordinary call (`Stmt.call`) of its body, the next frame of its unrolling (`recUnroll`, `docs/kernel-port.md`, "Recursion"); the next step is `internalCallExpand` or `functionBodyExpand`. solkey inlines a recursive callee as any other, without end |
| — | `LeanTaclet.tryCallDiamond` | Lean only | a diamond `try` closes to `false`; solkey has no rule. The call may revert in the caller (no code at the address, data that does not decode), which no clause catches and no formula rules out |
| — | `LeanTaclet.transferDiamond` | Lean only | a diamond payment closes to `false`; solkey's diamond rules are not ported. Whether the world pays is the compiler theorem's, not the calculus's |

## Loops

Solkey's loop taclets exist at the migration pin and are in the `Taclet` table.
Their bounded unwinding, frame restrictions and typed variant are documented
below; `docs/loops.md` gives the shapes and their soundness arguments.
The supported invariant is a typed boolean expression, not an arbitrary
quantified KeY formula, and the variant is a `uint`, rather than KeY's
unbounded `int`. Conditions and specifications must be capture-free. These
restrictions and the conservative frame prove fewer obligations; the port
does not claim coverage of the wider upstream syntax.

| KeY taclet | Lean | Status | Notes |
| --- | --- | --- | --- |
| `whileUnwind` | `Taclet.whileUnwind` | literal schema, bounded search | `while (cond) body` ⇝ `if (cond) { body; while (cond) body; }`, KeY's `s#cond`, `s#body` as `cond`, `body`. Unannotated loops use `LoopAnn.auto`; the one constructor's `LoopUnwind` mode also supports explicit bounds, decrementing `unwind n + 1` to `unwind n`. Sound by `Premise.sound_whileUnwind` (`TLoop.run_unfold`, `Calculus/SoundLoops.lean`). Annotations are proof-strategy metadata and do not change execution; exhausted search fails, while an exhausted explicit bound leaves an exit obligation. `sol_prove?` retains its discovered walk budget for replay |
| — | `LeanTaclet.loopExit` | Lean only | a loop at its bound (`unwind 0`, the annotation of a loop with no clause): a check (`Premise.check`, `Proves.check`; walk: `apply checkLean r`), "loop exited" the rest with `{ b := cond } (b = FALSE)` assumed, "unwound to the end" `{ b := cond } (b = FALSE)`: the condition read by an update under the diamond, as the invariant rules read it, so a condition that halts is not false (KeY's terms cannot halt; the program evaluates them). Sound by `Premise.sound_loopExit`. Not `assert(!cond)`, which would make running out of unwindings a panic of the program |
| `whileInvariantBox` | `Taclet.whileInvariantBox` | restricted port | `[ /// @custom:key invariant inv while (cond) body; ]` ⇝ "invariant initially valid": `inv = TRUE ∧ ¬broke`, where `inv = TRUE` is the invariant with its quantified clauses (`invFml inv qs`: `\forall T x; a -> c` read as `∀`, solkey's `\getInvariant` over the specification language); "invariant preserved and used": `{anon(body)} (inv = TRUE ∧ ¬broke → { b := cond } (b = TRUE ⟹ ⟨[ body ]⟩ (¬broke → inv = TRUE) ∧ (broke → ⟨[ ]⟩) ; b = FALSE ⟹ ⟨[ ]⟩))`. `broke` is solkey's `\getLoopBreak` (`loopBreak`): the lowered `break` flag read `true` where the elaborator lowered one (`LoopAnn.inv … brk`) and the condition starts with its negation (`Val.breakExit`), none otherwise, where the goals are the ones above without it. Deviation: the first goal also asks `¬broke`, which solkey's lowering gives by declaring the flag `false` before the loop; Lean's rule is sound for any loop. The body's goal is split by `andRight` (`Proves.andIntro`), the walk's step for a conjunction still holding a program. KeY's `s#b` (`bType b = cond;`) is a fresh local (printed `se`), `#loopAnon` is `{anon(body)}` (`Fml.anonHavoc`: `{anon(xs)}` of the body's frame `Prog.frame`, with `{havoc}` when the body writes storage or pays). `b = TRUE` is KeY's `=` (`Fml.eq`) of a local and a literal; `inv = TRUE` is the Theory equation, any state predicate the rule needs. Premise `Premise.inv`; in a walk the scoped `Proves.inv` (a `Proves` step by `Taclet.toStep`; `apply invBox r`, `apply invLean r` under the diamond), its goals `init`, and `thn`, `els` past the context's `{anon(body)}` (`Hyps.anonHavoc`): solkey's two goals. A condition, invariant or variant that needs a capture (a call, a cast, a narrow operation, a constructor, an `++`) is refused at elaboration (`loopExpr`), where solkey evaluates it per iteration. Sound by `Premise.sound_whileInvBox` (`Calculus/SoundLoops.lean`, `TLoop.run_induct`) |
| `whileInvariantDiamond` | `Taclet.whileInvariantDiamond` | restricted port | the box's premise with `{ variant := dec ‖ b := cond }` and the body's postcondition `inv = TRUE ∧ { b := cond } (b = TRUE → 0 <= dec ∧ dec < variant)`: KeY's skolem `variant` a fresh local (printed `ie`), the variant checked only where the condition holds again, `0 <= dec ∧ dec < variant` read in the Theory (KeY's `=`): the bound is the Theory value of `dec`, which the next head's update reads as the interpreter does (`Tm.denote_eval`); and under the diamond the cover (`b` is `TRUE` or `FALSE`, `Premise.inv`). Sound by `Premise.sound_whileInvDiamond` (`TLoop.run_variant`) |
| — | `LeanTaclet.whileClose` | Lean only | a loop with an invariant whose body has no frame (`Prog.frame`: it writes memory, pushes, pops, rebinds an alias or calls out), under either modality, closes to `false`: sound, and nothing about it is derived. solkey refuses only memory-writing bodies (and unwinds them); a push, a pop or a call it frames as writing storage and the ledger, so those refusals are Lean's own (`Stmt.within`) |
| — | `LeanTaclet.whileNoVariantDiamond` | Lean only | a loop with an invariant and no `decreases` closes to `false` under the diamond (solkey unwinds it). `Stmt.inSolkey` is `false` on every loop |
| `LoopLowering` (meta-construct) | `lowerLoops` (`Syntax/Elab.lean`) | elaborator | `break`/`continue`/`return` in a loop to the flags `brk`/`cnt`/`ret`, `for` and `do … while` to `while`, shape for shape |

## Function contracts

| solkey | Lean | Status | Notes |
|---|---|---|---|
| `useContract_g` (planned: one per specified function, behind `functionTreatment:contract`; not at the pin) | `useContract` (`Calculus/FunContract.lean`) | ⊢ rule | a derived theorem, sound from the typed run (`useContract_of_valid`, from `FunContract.ofValid`), not a `Taclet`. Goals "pre" `[ params := args ] requires` and "post" `[ params := args ] {old := storage ‖ oldNet := net} {havoc} ∀ T r. (ensures → [ res = r; ..ω ] φ)`, `{havoc}` for a `nonpayable` callee only (`Fml.anonC`; `pure`/`view` by `Prog.within`). Box only |
| the obligation `requires -> [g(args)@C] ensures` (planned) | `FunContract.obligation` (the formula), `FunContract.ofValid` (a contract from its proof) | — | over the callee's block `T r; body`, the parameters free; `ensures ∧ typed(r)` (KeY's `inUInt(result)`) |

## Update algebra (`updateRules.key`)

An update is a term (`Upd C Γ Δ`, a list of `UpdElem`s read against the
pre-state), so KeY's update rules are rules here too: `UpdRuleS` in
`Calculus/UpdRuleScoped.lean`, each one way over the typed state
(`UpdRuleS.sound`; why not both ways is its docstring's "One way"), at the
positive positions of a formula; on sequents they are `Proves.merge` and
steps derived from `Proves.closeHolds` (`Calculus/UpdateRules.lean`), usable
with the program still to run. A side condition KeY's rule lacks exists
because a term here can halt and KeY's cannot, or because a local is a
position (`Calculus/UpdRuleScoped.lean`, "What the scope changes").

| KeY rule | Lean | Status | Notes |
| --- | --- | --- | --- |
| `sequentialToParallel1-3` | `UpdRuleS.sequentialToParallel`, `Proves.merge`; + under a branch (`FmlRw.mergeIn`) | done | `{u}{u2}φ ⇝ {u ‖ {u}u2}φ`.  On the sequent (`Proves.merge`, `Calculus/Proves.lean`; read as `refine merge rfl ?_` and `Proves.mergeStorage`, `core_merge`): one rule for both rows, `{U}{V}φ ⇝ {W}φ` with `W = Upd.seqPar U V` (`Calculus/Graft.lean`): `V`'s locals read as `U` leaves them (`Upd.held`), the rest as in the row below.  **Lean only:** it merges past the hidden binders between the two updates (`Hyps.binds`), the earlier update moved under them (`Upd.liftBinds?`, scope ends included), which KeY, with no binders, does not need.  **On a chain's scoped line** while the program is open: the spine's merge (`Fml.mergeRun`, `Calculus/Merge.lean`), one over a storage write, a memory write, or locals then a memory write (`FmlRw.stateMerge`, `MergeNameS`: `Upd.mergeSt?`, `Upd.mergeMem?`, `Upd.mergeMemL?`, `Calculus/StatePartsScoped.lean`), and one under `∧`, `→` (`FmlRw.mergeIn`, `Calculus/RewriteScoped.lean`); `sol_merge` on a scoped goal: `Fml.simpUpdsS` (`Calculus/UpdRuleScoped.lean`), past hidden binders too (`Fml.mergeB`); one direction each.  `UpdRuleS.sequentialToParallel` is the taclet's shape (`Upd.seqPar`); `sol_upd .sequentialToParallel` is the **Lean-only** `UpdRuleS.mergeHidden` (`Fml.mergeB`: through hidden binders, the scope ends after absorbed, `UpdRuleS.absorbPops`) |
| `sequentialToParallel1-3` over a storage write | `Proves.merge` (spelled `refine Proves.mergeStorage ?_`) | done | `{storage := s}{V}φ ⇝ {storage := s ‖ {storage := s}V}φ`: `V`'s `storage` is replaced by the storage `U` last wrote (`Upd.lastSt`), where `U` writes no other global part, sound because a storage term changes only the storage of the state it is read in (`Tm.eval_st_glob`); any other merge reading the global part needs `U` to write none (`Upd.envOnly`), else it is refused |
| `sequentialToParallel1-3`, a chain's line past the program | `FmlRw.mergePast` (`Calculus/RewritePast.lean`) | done (W9.4) | the scoped line's spine merged, `n + 1` updates from a position, innermost first (`Fml.mergeRunP`); through a hidden binder the binder absorbed into the update that sets its local before reading it (`Upd.absorb`, `holds_bind_absorb`), else the update moved under it (`Upd.liftG?`), else every binder absorbed (`Fml.absorbAllMergeP`: a local its update sets after declaring others is declared first, which reorders the printed parallel update, a Lean-only deviation); a storage write a later one shadows dropped (`Upd.dropSh`) |
| `sequentialToParallel1-3`, read backwards | `Upd.toLS` (`Calculus/DecideScoped.lean`) | Lean only | `sol_prove`'s leaf closer reads a parallel update element by element, each in the update's pre-state (`UpdElem.toLS`), so nothing splits it: an allocation's pair and a push with its returned alias are read as they are; **Lean only**, a hidden binder of a value is read as the `∀` it is (`LFml.allB`) |
| — (KeY keeps an update on its formula) | `Proves.updIntro` | arch | `⟹ {U} φ` becomes `{U} ⟹ φ`: the update joins the context, where every rule reads it, the sequent KeY writes with the update on the formula. A specification's `{ old := storage }` enters the derivation so |
| `applyOnElementary`, `applyOnParallel` | `Tm.substH`, `UpdElem.substH`, `Upd.graft` (`Calculus/Graft.lean`) | functions | `{u}` pushed into right-hand sides |
| `applyOnPV`, `applyOnPVLastInParallel`, `applyOnDifferentPV`, `applyOnDifferentPVLastInParallel` | `Upd.held` (`Calculus/Graft.lean`), `Fml.substU` | functions | the last write of a local wins; an unwritten local is kept.  On a chain's scoped line while the program is open, where the update is not applied whole: `FmlRw.applyOnPV` (`Calculus/RewriteScoped.lean`), a local the update leaves holding a literal (`Upd.held`, `Held.litVal?`) read as that literal in the atoms of the propositional skeleton below it, the update kept in front; one direction (`Fml.applyOnPVTop_sound`) |
| `simplifyUpdate1-3` | `UpdRuleS.simplifyUpdate`, `Proves.simplify` (`Calculus/UpdateRules.lean`) | done | under the box, the elements of the last update that set a local the update pops later are dropped (`Upd.simp`), derived from `Proves.closeHolds`.  Shadowed writes (`Upd.simpS`, `Calculus/UpdRuleScoped.lean`): a write a later one to the same local overwrites goes (`Upd.unsetAt`), and a declaration so overwritten takes the later right-hand side (`Upd.redecl`), any element under the box, one that cannot halt under the diamond (`holds_upd_shadow`); `UpdRuleS.simplifyUpdate` is the taclet's shape (`{u}φ ⇝ {u.simpS m}φ`); `sol_upd .simplifyUpdate` is the **Lean-only** `UpdRuleS.absorbPops` then it (`Fml.simpAt`, `Fml.simpAt_rule`), and on a chain's scoped line `FmlRw.simplifyUpdate` (with the scope ends after the update merged in first where the line under it is an update).  The walks are recursors with `match` twins (`Upd.shadow`/`Upd.shadowM`, `Upd.unsetAt`, `Upd.redecl`).  **Not yet** while the program is open: an element setting a local the formula does not read, which needs the formula strengthened out of that local's scope (past the program, the row below) |
| `simplifyUpdate1-3`, a chain's line past the program | `FmlRw.simplifyPast` (`Calculus/RewritePast.lean`) | done (W9.4) | every declaration nothing reads afterwards dropped with its writes (`every`, `Upd.thinIO`, `Fml.thinS?`), else the ones the update ends itself; the scope ends after it merged in where the line under it is an update (`Fml.absorbIf`); a hidden binder in front absorbed or dropped (`Fml.dropBindTop`); a dropped write must not halt (`Rhs.totalB`) |
| `applySkip1-3`, `applyOnSkip` | `UpdRuleS.applySkip` | done | `skip` is `[]`; for a formula with no modality (`Fml.modalFree`, `holds_congr_reads`) |
| `parallelWithSkip1-2` | — | arch | `‖` is `++`, `skip` is `[]`: nothing to rewrite |
| `applyOnRigidFormula` | `UpdRuleS.applyOnRigid` (`Fml.substU`); + through `∧`, `→`, `¬` (`FmlRw.applyOnRigid`, `Calculus/RewriteScoped.lean`) | done | one direction (`UpdRuleS.sound`), for an update that cannot halt (`Upd.totalB`) or under the box.  On a scoped line: `FmlRw.applyOnRigid`, one direction, for an update that cannot halt (`Upd.totalS`: locals, and storage writes and deletes at a root or a member of one of values that cannot halt, `Tm.totalW` — KeY's updates never halt, a Lean one only where a path checks an index) or under the box; the first-order parts applied (`Fml.substU`), the update kept in front of the rest (`Fml.pushS`); through the scope ends under it, merged in first (`FmlRw.applyOnRigidPops`, `Fml.absorbPops`), so `{U}{pop} true` is `true`.  Past the program every rewrite reads through the premises a line begins with (`FmlRw.inPath`: an obligation's `wt(storage) → ψ` rewrites `ψ`) |
| `applyOnRigidFormula`, under the box | `Proves.applyOnRigidBox`; `sol_apply_upd` | done | one direction, **no totality premise**: the last update of the context is applied to a first-order goal and dropped (`Fml.substU`, `Tm.denote_substH`), for a goal reading no global part the update writes; a halting box update proves what follows; derived from `Proves.closeHolds`.  On a chain's scoped line while the program is open, `~[applyOnRigidBox]~>` is `FmlRw.applyOnRigid`: under the box any update, under the diamond or `m` one that cannot halt (proposal 105); `~[applyStorageBox]~>` is `FmlRw.applyStorageBox`, the box's only and an update of the storage and locals only (`Fml.pushStAt`, `Upd.stOnly`) |
| `applyOnRigidFormula` on a lone storage write, a chain's line past the program | `FmlRw.applyStorageBoxP` (`Calculus/RewritePast.lean`) | done (W9.4), box only | `{storage := S}_□ φ ⇝ φ[S/storage]` for a first-order `φ` (`Fml.substSt`, the storage merge's `Tm.substP`) |
| — (`delAtExpand`, a chain's line past the program) | `FmlRw.expandPast .delAt` (`Calculus/ExpandLaws.lean`) | Lean only | `delAt(s, p) ⇝ save(…save(s, p.l₁, 0)…, p.lₙ, 0)` over the leaves of a type `Ty.expandable` accepts (finite shape, 1–64 words); exact (`Tm.eval_delAtLeaves`, from `Storage.delete_expand`), under either modality (`holds_upd_expand_iff`); a link only, never tried by `~=>` |
| — (`copyExpand`, idem) | `FmlRw.expandPast .copy` | Lean only | `save(s, p, find(s, q)) ⇝ save(…save(s, p.l₁, select(s, q.l₁))…)`, the words read in `s` (`Tm.eval_copyLeaves`, from `Storage.write_find_expand`); at a type that is no word |
| — (`pushExpand`, idem) | `FmlRw.expandPast .push` | Lean only | `push(s, p, x) ⇝ save(pushSlot(s, p), p[p.length]@s, x)` for an array of words (`Tm.eval_pushWord`, from `Storage.push_prim`); out of gas alike at a full array (`Tm.exhB_pushWord`) |
| — (`popExpand`, idem) | `FmlRw.expandPast .pop` | Lean only | `pop(s, p) ⇝ shrink(save(s, p[p.length - 1]@s, 0), p)` for an array of words (`Tm.eval_popWord`, from `Storage.pop_prim`); the `- 1` reverts on an empty array, as the pop |
| `elimSelfUpdate*` | — | not ported | commented out in KeY (`Calculus/UpdRuleScoped.lean`) |
| `simplifyIfThenElseUpdate1-4`, `commuteSimpleUpdates` | — | arch | commented-out dead code in KeY |

### Closing the first-order goal

What symbolic execution leaves is closed by first-order steps derived from
`Proves.closeHolds` (`Calculus/UpdateRules.lean`), each needing a context with no
diamond (`Hyps.boxOnly`). There is one equation, `a = b` (`Fml.eq`), KeY's
`=`: what the sides denote in the Theory, total as KeY's terms are, so it is
reflexive even where a side halts.  A condition is read by the program (a
captured local, or an update `{ b := cond }`), never by a definedness test;
`wt(storage)` is a predicate (`Fml.wellFormed`), KeY's `wellFormed(heap)`.
The closer reads an equation by value where the Theory reads its sides as
the interpreter does (`Tm.agreeB`, `Calculus/TermAgree.lean`: locals,
literals, operators, reads at declared places), and an equation it is to
prove otherwise by an update under the diamond (`Fml.evalEqs`,
`Calculus/EvalEqs.lean`).

| KeY rule | Lean | Status | Notes |
| --- | --- | --- | --- |
| — | `Proves.closeHolds` (`Calculus/Proves.lean`) | Lean only | with no modality left anywhere in the sequent (`Fml.modalFree`), what is left is proved over the typed reading (`holds`).  Every step after the program (`Calculus/UpdateRules.lean`: `andSplit`, `eqRefl`, `eqClose`, `applyOnRigidBox`, `simplify`) is derived from it; `rewrite` is a rule (`Proves.rewrite`), and `Proves.rewrite'` only writes its result out |
| `close` on `I ⟹ I` (`propRule.key`), at a callback's resume | `Proves.assumeInv` (`Calculus/CallbackSound.lean`) | done | the invariant assumed past a frame end that drops every local (`…, {havoc}, I ⟹ I`) is the goal past the program's scope ends: both the same closed first-order formula (`Fml.closedB`, `Frames.popsOnly`), the scope ends printing as nothing; derived from `Proves.closeHolds` |
| — | `Proves.openInv` (`Calculus/CallbackSound.lean`) | Lean only | at a leaf, each assumed invariant past its frame end is read at the scope it is assumed in (`Hyps.openInv`, `Fml.reclose?`), a closed first-order formula the closer reads; KeY's invariant is a formula over global symbols and needs no reopening.  Derived from `Proves.closeHolds` |
| — (KeY's anonymising update `{storage := storageSk ‖ net := netSk}`, its skolem constants fresh) | `CloseS.holds_havoc` (`Calculus/CloseScoped.lean`), `close_rw_s` | Lean only | `{havoc} φ` read as `φ` for every storage `st` and ledger `nt` (universally bound in place of fresh skolems); a snapshot `old`/`oldNet` taken before it is a local and keeps the storage it took |
| `findOnSave` (a scoped leaf) | `CloseS.wp_box_write`, `wp_box_write_prim` (`Calculus/CloseFrame.lean`), `close_rw_s` | done (W9.8.4) | a box write names the storage it leaves: `find(st', r)` is the written value (`Storage.writeVal`: a word itself, a struct overlaid on what was there) |
| `findOnSaveFrame`, `lenOnSaveFrame` (a scoped leaf) | `CloseS.wp_box_write`: `Storage.find_save_frame`, `len_save_frame`, `checkIndex_save_frame` | done (W9.8.4) | a read, a length and an index check at a path diverging from the write's (`Theory.diverges`, `Theory/Segs.lean`) read the storage before it; below the written path by `Path.append` |
| `findOnDelAt`, `findOnDelAtFrame` (a scoped leaf) | `CloseS.wp_box_delete` (`Calculus/CloseFrame.lean`) | done (W9.8.4) | the deleted path reads its default (`SVal.dflt`), a diverging path the storage before |
| `readOnWrite` (a scoped leaf) | `CloseS.wp_box_writeT`, `Grown.writeT_facts`, `MAddrT.apart_resolve` (`Calculus/CloseFrame.lean`) | done (W9.8.4) | a memory write reads back at its address and leaves an address apart from it (`MAddrT.Apart`) unchanged |
| `copyStToMem`/`copyMemToSt` member reads (a scoped leaf) | `SVal.copyStToM_field`, `MVal.copyMToSt_field`, `CloseS.readId_copySt_field`, `copyMToSt_find_field` | done (W9.8.4) | a member of a copy reads the member copied, on the typed heap (`SFields.copyStToM_get_prim`, `MVal.copyMToSt_findM_field`; W10.5.4) |
| — (a total path in a diamond) | `CloseS.wp_diamond_write_total`, `wp_diamond_delete_total`, `wp_find_total` (and `_root`), `Storage.write_ne_none_total` | Lean only (W9.8.4) | a write, delete or read at a path with no index (`Path.total`) does not halt, so a diamond leaf reads it as the box does; a deployment's storage (`Storage.find_init_total`) likewise |
| `selectOnEmptyStorage` at a root and below it (a deployment's storage) | `CloseS.find_init_ofRoot`, `CloseS.find_init_append` (`Calculus/CloseFrame.lean`), `close_rw_s` | done (W9.8.4) | the typed empty storage (`Storage.init`) reads a root, and a path through no array slot below it (`Path.total`), at its type's default (`Storage.find_init_total`) |
| — (an index checked at a mapping root; a checked index) | `CloseS.atT_map_root`, `CloseS.atT_bind` (`Calculus/CloseScoped.lean`), `close_rw_s` | Lean only (W9.8.4) | a key of a mapping at a root is always a slot (the check passes), so two reads of `balances[0]` name one reference; any other index is its check, then the slot's reference: the typed `Storage.atT` unfolded so the closer compares references |
| `binaryAndZeroRight`, `binaryAndZeroLeft`, `binaryAndOne`, `binaryAndOneLeft` (`binaryLemmas.key`) | `Close.uintBitwise_and_zero_right`, `…_zero_left`, `…_one_right`, `…_one_left` (`Calculus/CloseLemmas.lean`), `close_rw_s` | done | on `uintBitwise`, at `uint` and `int`; `i & 1` is `i % 2` where solkey writes `\if(mod(i, 2) = 0) \then(0) \else(1)`, the same integer without an `if` in a value |
| `binaryAndIdentity` | `Close.uintBitwise_and_self`, `sol_close`'s `grind` | done | conditional on `-2^255 ≤ i`, which an `int256` local carries (two's complement reads the word back); `binaryAnd_literals` is `Nat.reduceAnd` on numerals |
| `smod_lessPositiveDenom`, `smod_NumPos`, `smod_NumNeg`, `smod_geZero`, `smodMultiple` (`intDiv.key`) | `Int.tmod_lt_of_pos`, `Int.lt_tmod_of_pos`, `Int.tmod_nonneg`, `Close.tmod_nonpos`, `Int.mul_tmod_left`, `sol_close`'s `grind` | done | a signed remainder within a positive divisor, of the dividend's sign, and none of a multiple (`Examples/Tactics/Operators.lean`, `signedRemainder`) |
| `multiply_2_inEq0` (`intSimplificationRules.key`, `inEqSimp_nonLin_multiply`) | `Close.multiply_2_inEq0`, `sol_close_nonlin` (`Calculus/CloseNonlin.lean`), `sol_close`'s last alternative | done | from `c <= d` and `a <= b`, `a * c >= -b * d + b * c + a * d`; instantiated at tightest literal bounds and relevant symbolic linear comparisons. Strict premises use integer successor bounds. Term selection is Lean-only and bounded; `grind` reads the resulting monomials. The existing triangular recursion contract remains a regression. |
| `multiply_inEq0` (`intSimplificationRules.key`) | `Close.multiply_inEq0`, `sol_close_nonlin` | done | From `a <= b`, add `if 0 <= c then a*c <= b*c else b*c <= a*c`, at factors selected from the goal's products. Literal coefficients in symbolic bounds are admitted; higher-degree bound scans must complete before they are accepted as linear. |
| `square_nonneg`, `add_non_neg_square` (`intSimplificationRules.key`) | `Close.square_nonneg`, `sol_close_nonlin` | done | `0 <= x*x`; instantiated at factors and pairwise atom differences (Lean-only term choice), including compound factors. This proves squares without literal bounds and `2*x*y <= x*x+y*y`. All nonlinear families share scan, atom, factor, comparison, fact and heartbeat budgets; `sol_close_nonlin?` prints explicit applications for replay. |
| `storeSt`/`selectSt` on the ledger (`netHeader.key`) | `Close.lookupBy_setBy_int` (`Calculus/CloseLemmas.lean`), `close_rw_s` | done | a ledger entry after a write: the written amount at that address, the old entry elsewhere, the entries KeY `int`s (`Srt.kint`) |
| — (a push's room under the diamond) | `Upd.exhL`, `guardM` (`Calculus/DecideScoped.lean`), `Upd.exhL_sound`, `guardM_holds` (`Calculus/DecideTyped.lean`) | Lean only (W10.4) | a push at a full array is out of gas, which both modalities accept: under the diamond the update's guard is asked only where the array is not full (`fullL`), and what follows only where the update lands; the elimination's push asserts `len < 2^256 - 1` (`maxLen`). The reader covers a single storage push and a storage push paired with a local binding; the latter retains the parallel RHS's returning guard (`pushLocalExhL`). Other multi-element shapes remain outside this shortcut. KeY's `int` lengths need no room |
| `eqClose` | `Proves.eqRefl`; `Proves.eqClose` (`v = v`); on two literals in a chain, `FmlRw.concrete` (`Fml.litCS`) | done | `t = t` for any term, halting or not (`Fml.eq` compares `Tm.denote`s by `=`); `v = w` for distinct literals folds to `false` |
| `concrete_and_1-4`, `concrete_impl_1-4`, `concrete_not_2` | `FmlRw.concrete` (`Calculus/RewriteScoped.lean`, `Fml.concreteAlongS`) | done | on a chain's scoped line while the program is open: `true ∧ A ⇝ A`, `false → A ⇝ true`, `A → false ⇝ ¬A`, `¬false ⇝ true`, …, bottom-up through `¬`, `∧`, `→`, `false` being `¬true`; `concrete_not_1` (`¬true ⇝ false`) rewrites nothing |
| `andRight` | `Proves.andIntro` (`Proves.andSplit`, `apply andRight` in a walk) | done | a constructor of `Proves`, on any sequent; the walk takes it where a conjunct still holds a program, and leaves a first-order conjunction to the closer |
| any theory taclet on a sequent | `Proves.rewrite` (`Calculus/Proves.lean`, a rule), `rw [r]`/`sol_rw` (`Calculus/RewriteSyntax.lean`) | done | a term taclet `r : TermTaclet t t'` (`Calculus/TermLib.lean`) or a `Tm.Theq` at the empty scope rewrites every closed side of an equation of the sequent's preconditions and goal reading `t` there (`Tm.closedAs`; `Hyps.rwEqC`, `Fml.rwEqC`, `Calculus/SeqRewrite.lean`), a modality open or not, `core_rw`; `TermTaclet.sound` proves each rule once, from its Theory lemma; decision 90 |
| the same, inside an update | `Proves.updRw`, `sol_rw` | done | an update's right-hand side runs in the interpreter, so the rewrite asks `Tm.EvalRefines t t'`, which a Theory equation onto a literal gives (`Tm.EvalRefines.of_theq`); on the **last** box update of the context only, its closed occurrences of `t` read at the empty scope (`Upd.rwC`, `holds_upd_rwC`, `core_rw`); on a chain's scoped line while the program is open, any box update of its spine (`FmlRw.lawUpd`, `Calculus/RewriteScoped.lean`, a `TermTaclet`) |
| the same, inside an update, on a chain's line past the program | `FmlRw.lawUpdS` (`Calculus/RewriteLaws.lean`) | done (W9.4), any modality | a term taclet (`TermTaclet`), a memory law (`EvalLaw`) or a literal law (`LitLaw`) at an update's right-hand sides, its two sides read at the update's scope (`LawPair`); exact where the update holds the write it reads back (`LawCov.covered`, `Upd.covers`; `LawCov.ref`, `Upd.coversRef`; `LawCov.eval`, `Upd.coversEval`) or member-wise (`LawCov.eqv`, `Tm.sameBase`) (`Calculus/TermLaws.lean`) |

### The closer's clauses (`Calculus/Closer.lean`)

The scoped tactic closer also exposes `exLeft`/`andLeft` witnesses and
conjunctions with checked single-branch eliminations (`sol_close_enrich`,
`Calculus/CloseScoped.lean`). Equality substitution follows `applyEq`; goal
introductions follow `allRight`. Anonymous dependent locals retain their
intrinsic unsigned/signed ranges (`CloseS.uintRange`, `CloseS.intRange`),
which are Lean type facts rather than new SolKey taclets. This fallback runs
after the existing arithmetic closer. Each range scan inspects at most 8,192
declarations/expression nodes and adds 128 facts; witness elimination inspects
8,192 declarations across its scans and performs at most 128 eliminations.
There are two range scans per fallback, and these inspection limits do not
bound the cost of subsequent simplification or arithmetic.

`sol_prove` closes a leaf inside one `Bool`: the reduction (`Fml.toLS`),
the reads of writes eliminated (`LFml.elimF`), memory read
(`Calculus/MemRead.lean`) and `LFml.close` over what is left, proved sound
once (`LFml.close_valid`, `LFml.decideMem_valid`): a KeY first-order or
arithmetic taclet it subsumes is a clause of that function, not a proof
step.  The terms are typed (W10.4): a value is in its type's range and the
storage has the shape its contract declares, so no clause reads a layout.
"closer clause X" names the definition the clause lives in.

| KeY taclet | Lean | Status | Notes |
| --- | --- | --- | --- |
| `add_literals`, `sub_literals`, `mul_literals`, `div_literals`, `pow_literals` | `fold2` (`Calculus/Decide.lean`, where a term is built), closer clause `Facts.fold2` | subsumed | the interpreter's checked operation on two literals (`BinOp.evalT`), `/` and `%` truncating as solc does, out of range folded to `err` (it reverts); a power folded up to the exponent 256 (`expBig`). `fold2_eval`, `Facts.fold2_eval` |
| `less_literals`, `leq_literals`, `greater_literals`, `qeq_literals`, `equal_literals` | `fold2`, `Facts.fold2` | subsumed | comparisons of two literals |
| `eqClose` | closer clauses `Facts.fold2`, `Facts.direct` | subsumed | `a == a` folds to `true` and `a != a` to `false` on a term that returns; an equation closes on equal normal forms that return |
| `ifthenelse_true`, `ifthenelse_false` | closer clause `Facts.fold3` | subsumed | a conditional on a literal, or with one branch twice |
| `boolean_equal`, `true_to_not_false`, `concrete_not_*` | `fold1`; closer clauses `eqBoolLit`, `Facts.boolDecomp` | subsumed | `!` on a literal; `x == true` read as `x`, `x == false` as `!x`; a boolean premise taken apart |
| `applyEq`, `applyEqRigid` | closer clauses `Facts.addEqR` (`orient`), `Facts.rw`, `Facts.rebuild` | subsumed | a premise `t = v` rewrites `t` to a literal or a lower position everywhere after it, a constant included; every fact is read again under the others (`Facts.rebuild`, KeY's `applyEq` on the antecedent), the pairs apart kept |
| `closeFalse` (in the closer), `replace_known_left` | closer clauses `Facts.refuteEq`, `Facts.apart` | subsumed | a premise refuted (two literals apart, a side that halts, a pair the premises keep apart) closes the leaf; a comparison of a pair kept apart folds (`a == b` to `false`, `a != b` to `true`, `Facts.fold2`) |
| `cut`, `cut_direct` on a `bool` | closer clauses `boolSplit`, `LTm.pick`, `Facts.proveEqN` | subsumed | a case split on a `bool` local, or on a key comparison the normal forms leave open (KeY's `cut` on `k = j`), at most `closeFuel` deep |
| `selectOnShape{Struct,Element,Member,Size}`, `wfFixedSize`, `wfDynSize`, `wf{Fixed,Dyn,Map}Elem` | none | subsumed | a typed storage has its contract's shape (`Storage C`): a read at a path its type gives returns, and `has` at a member, a mapping's entry or a fixed-size array's index in range is its base's (`hasOf`, `hasN`; on the starting storage `TSegs.hasFrom`, `findM_atF`) |
| `sizeNotNegative` | closer clause `Facts.range` | subsumed | a length is at least `0`, its type's range (`PrimTy.lo`), KeY's `\add(0 <= selectSt<[int]>(st, size) ==>)`. The slot at `(len + 1) - 1` after a `push` is the one pushed: `(a + b) - b` cancels (`Facts.cancel`) and `len < len + 1` folds (`Facts.ltSucc`, Lean only), so `storagePushReadBack` is derived (W10.4) |
| `arrayLengthNonNegative` with a bound a premise gives | closer clauses `Facts.hasIdxDyn`, `Facts.hasRange` | subsumed | a dynamic array has a slot at every index its ranges put below its length |
| `inEqSimp_*` on bounds by constants | closer clauses `Facts.range`, `Facts.rangeOp`, `Facts.arithOk`, `ltDec`, `leDec`, `Facts.cmpFold`, `Facts.lessBnd`, `Facts.cmpBnds`, `Facts.neEdge`, `Facts.neBnd` | subsumed | a value's type range, a premise `t op k` or `t ≠ k` narrowing `t`, ranges added through `+`, `-`; a comparison whose ranges decide it folds, and an addition or subtraction whose operands' ranges keep it in its type returns |
| `polySimp_*` on `(a + b) - b`, `(a - b) + b` | closer clauses `Facts.cancel`, `Facts.cancelAdd` | partly | the sum or difference cancelled to `a` where it returns |
| — (KeY's polynomial normal form) | closer clause `isTwo` in `Facts.fold2` (`evalT_two_mul`) | Lean only | `2 * a` read as `a + a`: both check the one integer `2·a` against the range |
| — | closer clause `Facts.ltSucc` | Lean only | `a < a + c` for a positive literal `c` reads `true` where the sum returns |
| — | closer clause `Facts.cancelDiv` | Lean only | `(a * k + c) / k` read as `a` at `uint` for literals `0 <= c < k` where the sum returns (`Facts.cancelDiv_eval`): an external function value `address * 2^32 + selector` read back to its address (`docs/semantic-gaps.md`, "Function types") |
| — (KeY has no byte layout) | closer clauses `bitsShr` (`shrZeroU?`), `bitsMod` (`modModU?`, `modShrModU?`) in `Facts.fold2` | Lean only | at `uint`: `x >> 0` read as `x`; `(t % m) % n` as `t % n` where `n` divides `m`; `((t % 2^m) >> j) % 2^w` as `(t >> j) % 2^w` where `j + w <= m` (a byte of a narrowed word: `uint8(uint160(a) >> 152)`); `shrZeroU?_eval`, `modModU?_eval`, `modShrModU?_eval` (`emod_pow_ediv`) |
| — (KeY has no byte layout) | closer clause `bitsAdd` (`hornerU?`, `shrMatch`) in `Facts.fold2` | Lean only | Horner's step on bytes at `uint`: `((q >> k) % 2^w) * 2^k + q % 2^k` read as `q % 2^(w+k)`, `w + k < 256`, the left operand reading `q >> k` modulo `2^w` (`(t >> (j+k))` where `q` is `t >> j`, or `(q % 2^m) >> k`); an `abi.encodePacked` word read back byte by byte (`eval_horner`, `Int.emod_mul_split`; `Examples/Tactics/Hashing.lean`, `wordReassembled`) |
| — (a `uint`'s shift and remainder return) | closer clause `Facts.arithOk` | Lean only | `x >> c` at `uint` returns, and `x % c` for a positive literal `c` (`Facts.arithOk_isSome`): an ABI byte under the diamond |
| — (a guard is Lean's) | closer clause `kiteBool?` | Lean only | `c = true ? true : false` read as `c` |
| — (a guard is Lean's) | closer clauses `kiteAssert`, `assertArg?`, `Facts.addAsserts` | Lean only | a guard `kite(c, true, a, err)` that returns, like `assert(c)`, gives the premise `c = true` |
| `inEqSimp_*` on differences, `polySimp_*` in general | — | open | no bound on `y - x` for two symbolic terms, no polynomial normal form |
| — (Lean only: a cost bound) | `Seq.closeSize`, `Seq.stackSize` (`Calculus/DecideComplete.lean`), `LFml.fits`, `LFml.stDepth`, `LFml.boundsOk` (`Calculus/ReadBounds.lean`) | Lean only | a leaf whose reduction is past `closeSize` nodes, or stacks more than `stackSize` storage updates, is left to the walk, unless every storage history is concrete (`LTm.known?`), where `concreteSize` and `concreteDepth` apply |

### The storage readers (`Calculus/Decide.lean`)

`sol_decide`'s elimination (`LTm.elim`) is the typed Theory read
symbolically: a storage term is eliminated to its guard and a reader of its
observations (`SFun`; word, live length, presence, `CK`), each write a
`save` at its symbolic path (`SPath`) of the value there with the operation
made on it.  A read is compared with a write by `relSegs` (the symbolic
`Path.strip?`, two keys the terms do not settle one `kite`: `keyCmp`,
`keyTree`); at or below the write it is the operation's reading of the rest,
apart from it the old read (`writeAt`).  Each reader is proved to read the
observations of the value it stands for (`VRd.Rep`, `SRd.Rep`,
`Calculus/DecideEval.lean`) through the bridges of `Theory/Typed/Obs.lean`
(`Storage.obs_write`, `obs_delete`, `obs_push`, `obs_pop`, …); the Theory
law is cited by its solkey name.  Under the premises the readers compare
what the premises say (`LFml.elimF`, `Calculus/ElimFacts.lean`).

| KeY taclet | Lean | Status | Notes |
| --- | --- | --- | --- |
| `findDefinition*`, then `selectOnSaveCons` (`a1 = a2` down the written path, `a1 ≠ a2` off it), `saveOnEmptyPrim` at the word | `SFun.save`, `writeAt` with `relSegs`, `ovRS`, `svalRd` | subsumed | the read compared with the write a segment at a time: the written value's reading of the rest at or below it (a word the word written), the old read apart. `SFun.save_rep`, `writeAt_rep`, `relSegs_sound`, `ovRS_rep`, `svalRd_rep`; the Theory's `Obs.findOnSave`, `findOnSavePrefix`, `findOnSaveFrame`, `lenOnSaveFrame` |
| `selectOnDelAtCons`, then `delFieldDefault`, `delFieldRef`, `delFieldMap`, `delFieldFixed`, `selectStDelNode{Map,Ref,Fixed,Element,Member,Size}`, `selectStDelNodeFixed{Element,Size,Value}` below the deleted node | `SFun.delAt`, `writeAt` with `delRS` | subsumed | the symbolic `TVal.delR`: at and below the deleted path the default, a mapping's entries and a dynamic array's slots past its live end kept, a fixed-size array's length kept and a dynamic one's `0`; the node's kind is its type. `SFun.delAt_rep`, `delRS_rep`; the Theory's `Obs.findOnDelAt`, `findOnDelAtFrame`, `lenOnDelAtFrame`, `Obs.delAt_word_below` |
| `selectOnSaveEmptyRef`, `selectOnSaveEmptyFixed`, `selectOnSaveEmptyIndexStruct`, `selectOnSaveEmptyIndexPrim`, `selectOnSaveEmptyMember`, `selectOnSaveEmptySize`, `selectOnSaveEmptyDefault` | `SFun.save` with `ovRS`, the source read by `Op2.elim` at `sfind` (`SRd.at`); `selectOnSaveEmptySize` of a `fixedCopy` save also `TermTaclet.lenOnSaveFixedCopy` | subsumed | the symbolic `TVal.ovR`: member by member, element by element over the old slots, the old elements past the new length deleted, the old slots past both kept. `ovRS_rep`, `sfind_rep`; the Theory's `Obs.copyTo` (`SVal.obs_overlay`) |
| `selectOnSaveEmptyMap` below a key of a copy | `ovRS` at a key | subsumed | a mapping met in both keeps the target's entries; a well-typed program copies none, solc rejects it |
| `selectOnSaveCons` on a `size` write, `selectOnDelAtCons` past the end (`storagePushValueSave`, `storagePopSave`) | `SFun.push` with `pushRd`, `SFun.pop` with `popRd`, `SFun.extend` with `extendRd` | subsumed | the symbolic `TVal.pushA`, `popA`, `extendA`: a read below the array compares its index with the old length, the pushed value (stripped, `stripRS`) there, the old element below it; a pop deletes the last element unless `keep`; the length one more or one less (`LTm.succK`, `predK`). `SFun.push_rep`, `SFun.pop_rep`, `SFun.extend_rep`, `pushRd_rep`, `popRd_rep`, `extendRd_rep`; the Theory's `Obs.findOnPushFrame`, `findOnPopFrame` |
| `storageFieldWriteSave`, `storagePushValueSave` with `sp` a stale alias (bound before the storage last changed, dangling after a `pop`) | the alias's path, its index checked in the storage it was bound in (`pathAtIn`), then `SFun.save`/`SFun.push` at it | subsumed | KeY's `consr(sp, at(ie))` names a slot, checked only when `storageIndexReadArrayBindLocalRoot` bound it: the write is a plain `save` there.  The observations keep an array's slots past its live end (`SLoc.dangling`, `TVal.delR`), so no reader of its own is needed. `pathIdx_rep`, `SFun.save_rep` |
| `storagePushLengthSaveReferenceElement`, `storagePushLengthSaveMappingElement` | `extendRd` | subsumed | since solkey `d85018517f` an empty push saves the length only: the appended reference slot is exposed as it is (`TVal.extendA`), a missing slot starts at its default. `extendRd_rep`, `Storage.obs_pushPlace` |
| `selectStDelNodeIndexStruct`, its `iv ≥ size` branch | `delRS` at an index past the live end | subsumed | a `delete` keeps the slots past the end (`TVal.delR`). `delRS_rep` |
| `selectStDelNodeIndexStruct` to `delNodeIndex`, `selectStDelNodeIndex`, `selectStDelNodeElement` (in bounds only), `fixedDelNodeIndex`, `wfDelNodeIndexRight` (solkey `473da8944c`) | `delRS` at an index | subsumed | below a deleted dynamic array an element in its live range reads the deleted element's value, one past it the slot as it was (`TVal.delR`; the interpreter's `Storage.delete`, `SVal.defaultOf`, moves the cleared elements in front of the old shadow); a node's kind and well-formedness are its type, so `fixed` and `wf` have no counterpart. `delRS_rep` |
| `selectOnSaveEmptyIndexStruct`, branches 2 and 3, under the folded copy of `storageRootWriteCopySource` or `storageFieldWriteCopySource` | `ovRS` at an index | subsumed | below the new length the new element, past it and below the old length the old element deleted, past both the old slot (`TVal.ovR`). `ovRS_rep` |
| — (Lean only: KeY's `save` and `delAt` are total, the interpreter's halt) | `SFun.ok`, the guard of each storage operation | Lean only | a write returns where the storage below does, its path and value return and the location is there (the `has` observation); a push where the array is not full (`maxLen`); an index checked where it is a key or below the length (`boundG`). `SFun.save_rep` (`Storage.write_isSome`), `SFun.push_rep` (`Storage.push_isSome`) |
| — (Lean only: a read the elimination cannot follow) | `ElimM.ofOrig`, `SFun.ofOrig` | Lean only | a storage term it has no reading for (a memory read, a path it cannot follow) is kept as it is and read as a term (`fbRd`): exact, left to the closer |

### The closer's memory clauses (`Calculus/MemRead.lean`)

The clauses `sol_decide` reads memory with.  Each row is one solkey taclet,
named as solkey names it — of `memoryRules.key`, `structMemoryRules.key`,
and the program rules of `solidityProgramRules.key` that write memory — or,
under "—", a guard only Lean has, because the interpreter's memory
operations halt where KeY's are total.  A memory term of the reduction is
the tree of its writes and allocations as the program built it
(`write(m, a, v)`, `addM(m, R)` with its root `alloc(m, R)`, `copySt(m, S)`
with its root `copy(m, S)`), and a read walks it from the newest node down
(`LTm.memRes`, `memReadN`, `memIReadN`, `lenAtN`), comparing addresses
without running anything.  Each rewrite is an equation of reads
(`LTm.memRes_eval`): the readers are proved on the typed heap directly, with
no agreement module of their own, and the Theory column is the law of
`Theory/Typed/Mem.lean` under its solkey name (section "The laws by solkey's
names"), with the lemma it restates.  A name is an identity term: KeY's
`idC(freshIdp, flds)` is the path `LTm.freshPath?` reads below the root
`alloc(m, R)` of `addM(m, R)`.

| KeY taclet | closer clause | soundness | Theory law | status |
| --- | --- | --- | --- | --- |
| `readOnWrite` | `memReadN`, `.write` arm: the address written (`LTm.beqR`) reads the word written | `memReadN_eval`, `LTm.read_write_same` | `Grown.readOnWrite` (`Grown.writeT_facts`) | used; an address neither the same term nor apart keeps the read, where KeY's is an if-then-else |
| `readOnWrite` at an `Identity` | `memIReadN`, `.write` arm | `memIReadN_eval`, `LTm.iread_write_same` | `Grown.readOnWrite` | used |
| `readOnWrite` `\else` | the `.write` arms: an address apart (`LTm.apart?`: two members, a member and an element, two literal indices of one identity) reads below | `LTm.read_write_apart`, `LTm.iread_write_apart'`, `LTm.apart?_resolve` | `Grown.readOnWriteFrame` (`Grown.writeT_facts`) | used |
| `readOnAddM` `\else` | the `.addM` arms: an address whose object is older than the allocation (`LTm.boundedIn`: allocated on the spine below it, or read out of a memory there) reads below | `LTm.read_addM_old`, `LTm.iread_addM_old`, `LTm.boundedIn_eval` | `Grown.readOnAddMFrame` (`Grown.read_then_old`, `SVal.keeps_copyStToM`) | used |
| `readOnAddM` `\then`, `initMember`, `defaultValueInt`, `defaultValueBool` | `memReadN`, `.addM` arm: an address at a member path of the fresh root (`LTm.freshPath?`, `Ty.memberTy`) of a primitive type reads its default (`PrimTy.dflt`) | `LTm.read_addM_fresh`, `LTm.freshPath_eval` | `Heap.initMember` | used |
| `initElement` | the same, at a literal index of a fixed-size array (`Op2.freshStepL`) | `LTm.read_addM_fresh` | — | used |
| `memoryArrayFreshAlloc`, `initElement`, `selectOnCopyMemPrim` | `copyNewArrayRd?`, the `.copySt` word-read arm: the same fresh primitive array copy reads a default exactly when its index is below the allocated size | `copyNewArrayRd?_eval`, `memReadN_eval` | `newArrT_copy_prim_index`, `SVec.copyStToM_prim_defaults` | used composition; typed absence beyond the size is retained; reference-element copies remain open |
| `memoryArrayFreshAlloc`, `initElement`, `initMember`, `initSize` | `newArrArrayRd`, `newArrRd`: a fresh array value has its written length and typed default elements | `newArrRd_rep`, `newArr_rep` | `newArrT_find_at` | used composition in the typed storage-value reader; preserves allocation definedness and absent elements |
| `initSize`, `sizeOfDyn` | `lenAtN`, `.addM` arm: a fresh dynamic array's length is `0` | `lenAtN_eval` (`Heap.allocDefault_array_len`) | `Heap.initSize` | used |
| `sizeOfFixed` | none: a fixed-size array's length is its type's `n` (`lenCond`) | `lenCond_iff` | — | subsumed |
| `sizeOfLeaf` | none: no well-typed program reads the length of a struct or a primitive | — | — | unreached |
| `defValResolve` | none built: a default is read at the type the path declares (`PrimTy.dflt`), so `cast(defVal)` never occurs | `LTm.read_addM_fresh` | — | subsumed |
| `idShapeDef`, `shapeAtNil`, `shapeAtFixed`, `shapeAtFixedMapElement`, `shapeAtDyn`, `shapeAtDynMapElement`, `shapeAtMember` | none: an allocation carries its type (`addM(m, R)`), read down the path by `Ty.memberTy` | `LTm.freshPath_eval` | — | subsumed |
| `shapeAtMap`, `shapeAtLeafElement`, `shapeAtLeafMapElement` | not reached: memory holds no mapping (`alloc`'s and `addM`'s `mapFree` premise), and no path goes below a primitive | — | — | unreached |
| `idCCDef` | an allocation's root is `alloc(m, R)`, at the empty path (`Op1.freshStepL`) | `LTm.freshPath_eval` | — | used |
| `initIdentity` | `LTm.freshPath?` (`Op2.freshStepL`): an identity read out of the fresh object, `iread(addM(m, R), a)`, is named by `a`'s path, KeY's `idC` one segment longer | `LTm.freshPath_eval` | not restated: a reference member is allocated with its parent | used |
| `readFromEmptyMemory`, `newFromEmptyMemory` | none: the bottom of a leaf's memory is the global part's heap (`memory`), not `mtMem` | — | not restated | unreached |
| `readREmpty`, `readRCons` | none: a path is read one address at a time (`mfield`, `mat`), each a read of its own | — | not restated | subsumed |
| `newFromAdd` | `LTm.identApart?`: two identities differ where one is fresh over a memory (`LTm.freshOver?`) the other is older than (`LTm.boundedIn`) | `LTm.identApart?_ne`, `LTm.freshOver?_eval` | `Grown.alloc_fresh` (`Grown.alloc_id_ge`, Lean only) | deviation: no `new` term |
| `newFromWrite` | none, likewise: a memory on the spine below another grows to it (`LTm.onSpine_grows`) | — | — | deviation |
| `newFromCopySt` (solkey `473da8944c`) | none, likewise: a copy is an allocation on the spine (`copySt(m, S)`, `Grown`), and the identities fresh over it are apart from the older ones (`LTm.identApart?`) | — | — | deviation: no `new` term |
| `readFromCopyToStorage` `\then` | `copyFieldRd?`: a member of a copy's root reads the storage it copied there (`find(st, q.f)`), which the elimination then reads (`LFml.closeMem`) | `copyFieldRd?_eval` | `SVal.readFromCopyToStorage` (`SVal.copyStToM_field`) | used |
| `readFromCopyToStorage` `\else`, `readFromCopyToStorageIdentity` `\else` | the `.copySt` arms: an address whose object is older reads below | `LTm.read_copySt_old`, `LTm.iread_copySt_old` | `Grown.readFromCopyToStorageFrame` (`Grown.read_then_old`, `SVal.keeps_copyStToM`) | used; the premise is the object older than the copy, where KeY's is `idp1 ≠ idp2` |
| `readFromCopyToStorageIdentity` `\then` | `copyObjN`: an identity member of a copy's object, read at the copy, is kept as that read (`iread(copySt(m, S), o.f)`, KeY's `idC(idp1, consr(fxs, a))`) and holds `sfind(st, q.f)` where `o` holds `sfind(st, q)`; such an object is fresh over `m` (`LTm.copyFresh?`, `LTm.freshOverC?`, read by `LTm.identApart?`) | `copyObjN_eval`, `LTm.copyFresh?_eval` | `SVal.mirrors_copyStToM`, `SFields.Mirrors.get` (`Theory/Typed/MemMirror.lean`) | used |
| `readFromCopyToStorage` `\then` at `idC(idp2, fxs)`, `fxs` not empty | `copyPathRd?`, the `.copySt` word-read arm after `copyFieldRd?`: a word member of an object `copyObjN` reads (`find(st, q.f)`), and, Lean only (solkey copies no storage array to memory), an element of a copied dynamic array (`if (i < len(st, q)) then find(st, q[i]) else err`) | `copyPathRd?_eval`, `LTm.findField_eval`, `LTm.findIndex_eval` | `SVal.Mirrors.prim`, `SVec.Mirrors.getElem` | used |
| — (Lean only: a guard of an address) | `LTm.hoistA`, `LTm.peel`, `wrapG` (`Op2.memRes`'s `.read`, `.iread`, `.mlen` arms; `LTm.apart?` and the `.write` arms compare addresses with them out): a read at `(if (c) then o else err).f` is `if (c) then read(…, o.f) else err`, a guard the term already has left out; `guardL` leaves out a guard its term has, and `guardQ`, `memCondStep` read a guarded identity's guards as words (`framesCond?`) | `LTm.app2_hoistA`, `LTm.hoistA_some`, `wrapG_eval`, `framesCond?_iff` | — | used |
| `findDefinitionSize` (`structRules.key`) on a copy | `lenAtN`, `.copySt` arm: a copy of `new T[](n)` has length `n`; a copy of `sfind(s, p)` at an array path has `len(s, p)` (`LTm.sfindLen?`, Lean only: solkey copies no storage array to memory) | `lenAtN_eval` (`newArrT_copy_len`, `SVal.copyStToM_array_len`) | — | used; an element of a copy of a storage array is read back by `copyPathRd?` (above) |
| `findOnCopy`, `selectOnCopyMemPrim`, `selectOnCopyMemRef` | `copyMemRd`, `memRd` (`Calculus/Decide.lean`): a memory object read as the stored value it copies to, down the segments (a member's address, an element within its array's length, an object's identity read there) | `memRd_rep`, `copyMem_rep` (`Calculus/DecideEval.lean`) | `MVal.findOnCopy` (`MVal.copyMToSt_field`) | used |
| `memoryToStorageStoreRoot`, `memoryToStorageFieldCopyRoot`, `memoryToStorageFieldCopyField`, `memoryToStorageIndexMappingCopyRoot`, `memoryToStorageIndexArrayCopyRoot` | `save(storage, p, copyMem(m, i))` eliminated as any `save` (`SFun.save`, `ovRS`), its value read by `copyMemRd` | `SFun.save_rep`, `copyMem_rep` | `MVal.findOnCopy` | used |
| `memoryReferenceDeclFreshAlloc`, `memoryRootDeleteFreshRebind`, `memoryArrayFreshAlloc`, `memoryStorageCopy` (after `memoryStorageCopyUnfold`) | the pair `{x := alloc(m, R) ‖ memory := addM(m, R)}` (a copy: `copy(m, S)`, `copySt(m, S)`), both elements read in the update's pre-state (`UpdElem.toLS`): `x` names the root the allocation takes | `Upd.toLS_sound` | — | deviation: KeY's two sequential updates over one Skolem `freshIdp` (`\skolemTerm`, `\sameUpdateLevel`) |
| `memoryFieldDeleteReference`, `memoryIndexDeleteReference` | the reference written is a fresh root's identity, read back by `memIReadN` and compared by `LTm.identApart?` | `memIReadN_eval` | — | used |
| — (Lean only: KeY's memory operations are total, the interpreter's halt) | `MemQ`, `memCondN`: a memory term returns where each write lands (a member of an object of the memory, an element within its array's bounds: `lenCond`, the program rules' `\add(0 <= ie & ie < read(memory, mv, size))`) and each copy's source returns (`svConds`) | `memCondN_sound`, `lenCond_iff` | — | used |
| — (Lean only: a guard of a memory) | `guardQ`, `guardL`, `seqMemL`: a guard `d; a` read as the words its memory's returning comes to, a word the closer folds to `true` dropped | `guardQ_sound`, `guardL_eval`, `seqMemL_eval` | — | used |
| — (Lean only: solkey names a copy's root by a Skolem `freshIdp`) | `copyRes` (`Op2.memRes`'s `.copy` arm, applied at formation by `foldRead2`): a copy's root `copy(M, S)` read as `copy(stripW(M), S)`, the memory without its writes (`LTm.stripW`), guarded by the words `M`'s writes land on (`seqMemL`); the copy's laws read such a root at the node that copies it (`LTm.onSpineS`, `LTm.base_eval`, `LTm.unstripAddr`), and a memory's own landing guard is read as its words (`UpdElem.toLS`) | `copyRes_eval`, `LTm.stripW_eval`, `SVal.copyStToM_id_eq`, `LTm.read_unstrip` | — | used |
| — (solkey's `keccak256` is uninterpreted) | `keccakRes`, `keccakAt` (`Op2.memRes`'s `.keccak` arm): a byte string whose length (`lenAtN`) and every byte (`memReadN` at `t[i]`) read down the memory to literals (`LTm.litIn?`), at most `keccakMaxBytes` (64), hashes to `keccakBytes` of them, evaluated by the kernel; `orElse` the symbol where the memory does not return | `keccakAt_eval` (`keccakWords_spec`, `eval_read_mat`, `eval_mlen_some`) | — | Lean only: a locally built byte string's hash under `⟨⟩`, two allocations of the same literal bytes hash equal (`Examples/Tactics/Hashing.lean`, `hashTwiceDiamond`, `abcHash`, `twoAllocations`) |
| — (Lean only: a read walks every write) | `memFuel`: a read walks at most 256 writes and allocations down, then is kept | — | — | used |

## The data-structure theories

The rows above are the *program* calculus. Its updates are written over
symbols — `find`, `save`, `selectSt`, `read`, `write`, `addM` — that solkey
declares in `structHeader.key`/`memoryHeader.key` and defines nowhere; their
meaning is the taclet sets of `structRules.key`, `memoryRules.key` and
`structMemoryRules.key`. `Solidity/Theory/` is that meaning on typed values,
each taclet a law stated under its solkey name: a storage is its
observations at typed locations (`Theory/Typed/Obs.lean`), a memory a heap
grown from the global part's (`Theory/Typed/Mem.lean`).  Paths are typed
(`Path T U`): a member is `.field`, `at(i)` an index, `size` the live
length, read as its own observation; `listRules.key` needs no module, it is
`List`.  The side conditions on two paths of segments (`Theory.diverges`,
`Theory.lengthSeg`) are `Theory/Segs.lean`'s.

**The storage copy fold is followed eagerly.** solkey folded `copyAt` into
`save`: `save(st, nil, v)` is an irreducible leaf that the eight copy rules
write and `selectOnSaveEmpty*` read through (`c80a54494c`, `8c5c69ca25`).
Here a copy is one `save` too (`Obs.copyTo`), of the new value laid over the
old one, computed from the type (`TVal.overlay`, one component at a time:
`TVal.ovR`): no lazy leaf, so the `selectOnSaveEmpty*` rows are the reads of
that overlay.  `docs/solkey-feedback.md` carries the request that solkey drop
the fold.

### The update vocabulary (`Solidity/Update.lean`)

The sorts are KeY's, renamed to plain Lean identifiers; an element's
right-hand side is a term read in the pre-state, and a rule's premise nests
them as KeY's `\replacewith` updates do.

| KeY sort | Here | Notes |
| --- | --- | --- |
| a value | `Term` | a constant, a stack local, `a ⊕ b`, `find(s, p)` (`Term.find`; `select(s, r)` reads the same, and is how a value read prints as a `save`'s value, where `find` is the copy `SValT.find`; KeY writes `find` there, and has no `select`: the spelling is Lean's, also under `pp.sol.key`, and is told from `STerm.select` by its sort), `read(m, a)`, an array's length (`Term.len`, printed `p.length` at `storage` and `find(s, p.length)` elsewhere; `Term.mlen`), `c ? a : b`, `selectSt(net, at(a))` (`Term.net`), `selectSt(oldNet, at(a))` (`Term.netOf`), `delValue(t)` (`Term.delValue`, the default of a word; solkey replaced its `delValue<[α]>` by `delField<[α]>(st, a)`, which is `delValue(selectSt(st, a))` here), `wt(s)` (`Term.wt`/`Op1.wt`, KeY's `wellFormed(heap)`: `true` on a storage the contract can be in, stated `wt(storage)`, the premise of an obligation); `cleanTail(s)` (`Op1.cleanTail`, Lean only: solkey has no shadow slots; `true` on a storage whose arrays keep only ordinary defaults past their live ends, `Storage.cleanTailB`, undefined on any other, and in the Theory what the observations show, `TSto.CleanTails`; the premise of `ValidTail .clean`, `docs/options.md` O6); `Op1.toInt`, a `uint` read as a KeY `int` (total: solkey writes nothing, its `msgValue` and ledger entries being `int`s, `netHeader.key`; inserted by the reader where a term of fixed type `uint` meets a KeY `int`, `NTm.widen`/`resolvePairV`, and printed bare where the other operand shows the sort, `toInt(…)` where none does) |
| KeY's `int` | `Srt.kint` (Lean's `Int`) | the ledger's entries (`net(a)`, `x[a]`: `Op1.net`, `Tm.netOf`), `toInt`, a literal (`Op0.zlit`), a logical variable (`Tm.pvZ`, a formula's parameter read only at the sort: `RawFml.kintParams`), `+`, `-`, `*` (`Op2.zbin`, unbounded) and the comparisons (`Op2.zcmp`, to `bool`; an equation `a = b` on KeY `int`s is `a == b = true`, `NRead.eqK`).  Apart from Solidity's `int256` (`val .int`); `sol_decide` leaves it outside its fragment, as the ledger |
| `Path[storage]` | `PTerm` | a state variable (`.root`), an alias (`.pv`), `.field`/`.at`; `p[i]@S` (`.atIn`) and `p[p.length]@S` (`.nextIn`) for an index check or a push slot merged under a storage write, their check performed in `S` (no KeY counterpart: KeY's `at(i)` is unchecked) |
| `Storage` | `STerm` | `.storage`, `.mtSt` (KeY's `mtSt`, a deployment's storage: Lean-only reading, every root of the contract present at its default, where KeY's has none and `selectOnEmptyStorage` answers the default; reads agree), `.save`, `.delAt`; `.push`/`.pushSlot`/`.pop`/`.shrink`/`.extend` for the array writes; `.select` for `selectSt<[Struct]>(s, r)`, the struct at a member, written `select(s, r)` |
| what a storage `save` writes | `SValT` | a value (`.val`), a subtree read from a storage (`.find`, printed `find(s, p)`; a value read there prints `select(s, p)`), a memory object copied back (`.copyMem`, KeY's `copyMem(mtSt, m, i)`), or a fresh array (`.newArr`; a concrete one prints `newArr(T, n)`, `T` the array type) |
| `Identity` | `ITerm` | a memory local (`.pv`), a reference read out of memory (`.read`), `freshId(addM(m))` (`.alloc`, carrying the `RefTy`; a concrete one prints it, `freshId(addM(m, Person))`, `freshId(addM(m, uint[]))`), `freshId(copySt(m, v))` (`.copy`) |
| a member or element of a memory object | `MAddr` | `.field`/`.at` |
| `Memory` | `MTerm` | `.memory`, `.write(m, a, v)`, `.addM` (eager: the type rides along; a concrete one prints `addM(m, T)`, `T` a struct `Person` or an array type `uint[]`, `Token[3]`, where KeY writes `addM(mem, shaped(idp, #shapeOf(mv)))`: the type in place of its shape), `.copySt(m, v)` |
| what a memory `write` writes | `MValT` | a value (`.val`) or a reference (`.ref`) |
| one elementary update | `UpdElem` | `.val`, `.path`, `.mref`, `.storage`, `.memory`; `.store` for `old := storage`; `.pay` for a transfer's booking (and a taken send's) `pay(r, a)`; `.net` for `net := store(net, at(r), net(r) ± a)`, with `.selfBalance` for a `payable` function's booking of `msg.value` (`selfBalance := selfBalance + a`); `.saveNet` for `oldNet := net`; a deployment's (`Problem.deployUpd`, `spec!{constructor}`): `.netMt` for solkey's `net := storeSt(mtSt, at(r), selectSt<[int]>(mtSt, at(r)) + a)`, printed `storeSt(mtSt, at(r), a)` (Lean-only shortening: the read of `mtSt` is `0`, `selectOnEmptyStorage`), `.setBalance` for `selfBalance := a`, `.saveNetMt` for `oldNet := mtSt`; `.unset` for `lsv := unset`, an alias bound to no path (Lean only, `storageLocalDeclSkip`) |

### `structRules.key` → `Theory/Typed/Obs.lean`

The laws are stated once over any location family (`ObsLoc`: a state
variable's path, a dangling one, a path below a value), and each is total:
a location not there reads the default word, length `0`, and `has = false`.
Each operation of the interpreter is, read by its observations, the
operation here (`Storage.obs_save`, `obs_write`, `obs_delete`, `obs_push`,
`obs_pop`, `SVal.obs_overlay`, …).

| KeY taclet | Lean | Status |
| --- | --- | --- |
| `findDefinition*`, `selectOnSaveCons` (`a1 = a2`), `saveOnEmptyPrim` | `Obs.findOnSave`, `Obs.findOnSavePrefix` (`find_save_same`, `find_save_below`) | done: a word written reads back; a read above a save sees the save made below it |
| `selectOnSaveCons` (`a1 ≠ a2`) | `Obs.findOnSaveFrame`, `Obs.lenOnSaveFrame` (`find_save_frame`) | done, the frame's premise the decidable `(ObsLoc.strip? p q).isNone` |
| `selectOnSaveCons` (`\if (a1 = a2)`, a word at a symbolic index) | `CloseS.copyTo_word_ite` (`Calculus/CloseScoped.lean`), the closer's `sol_close_save_cases` | done: the read split on `(ObsLoc.strip? p q).isSome`, the paths compared from their root (`CloseS.strip?_ref_append`); Lean-only as a closer step (the quantified fallback's last alternative) |
| `selectOnDelAtCons`, `delField*`, `selectStDelNode*`, `selectStDelNodeFixed*` | `Obs.delAt` (`TVal.del`, `TVal.delR`), `Obs.findOnDelAt`, `Obs.findOnDelAtFrame`, `Obs.lenOnDelAtFrame`, `Obs.delAt_word_below` | done: the reset is computed from the type, a mapping's entries and an array's slots past its live end kept; no premise on the node's kind |
| `selectOnSaveEmpty*` (the copy fold) | `Obs.copyTo` (`TVal.overlay`, `TVal.ovR`) | done eagerly (above) |
| `storagePushValueSave`, `storagePopSave` (two `save`s each) | `Obs.push` (`TVal.pushA`), `Obs.pop` (`TVal.popA`), `Obs.extend` (`TVal.extendA`); `Obs.findOnPushFrame`, `Obs.findOnPopFrame` | done: a push or a pop is one operation, its frame `save`'s |
| `selectSt<[Struct]>(s, r)` | `Obs.select`, `Obs.select_save`, `Obs.select_copyTo`, `Obs.select_delAt` and their `_ne` | done: the struct at a root as a storage of its members |
| `selectOnEmptyStorage`, `saveOnEmptyStorage`, `defaultValue*` | `Storage.obs` of the typed empty storage (`Storage.init`) | done: a location reads its type's default |
| `selectOnEmptyStorage`, `saveOnEmptyStorage` in the closer | `sol_close_mt` (`Calculus/Close.lean`, `Calculus/CloseScoped.lean`) | Lean only: `mtSt` evaluates to the roots at their defaults (`CloseS.eval_mtSt`) |
| `selectOnEmptyStorage`, `fixedEmpty`, `selectOnShapeSize` in `sol_decide` (`structRules.key`) | `SFun.mt`, `mtRd`, `TSegs.mtHas` (`Calculus/Decide.lean`) | done: the elimination reads `mtSt` as `Storage.init`: a word its type's default, a dynamic array's length `0`, a location there below a member, a key or a fixed index in range, never below a dynamic index (`SFun.mt_rep`, `SVal.findM_dflt`, `TSegs.mtHas_eval`, `Calculus/DecideEval.lean`); a `save` on it is the ordinary write over this reader, so `saveOnEmptyStorage` needs no clause of its own |
| `selectOnShape*`, `wf*`, `fixed*`, `wfFixedIsFixed`, `wfDynIsNotFixed`, `fieldShapeDef` | the typed storage (`Storage C`, `Semantics/Storage.lean`) | **not modelled as taclets**: a typed storage is in its contract's shape, clause for clause |
| `sizeNotNegative` | — | **arch**: a length is a `uint`, at least `0` by its type (the closer's `Facts.range`) |

### `memoryRules.key`, `structMemoryRules.key` → `Theory/Typed/Mem.lean`

A memory is a heap grown from the global part's (`Grown H`), an address an
identity with a member or an element (`MAddrT T`); each law is a statement
about `Grown.readT`, `writeT` and the allocations, generic in the types it
is read at.  The section "The laws by solkey's taclets" restates each by its
solkey taclet's name (a `\else` as the name with `Frame`), proved by the
lemma beside it.

| KeY taclet | Lean theorem | Status |
| --- | --- | --- |
| `readOnWrite` `\then` | `Grown.readOnWrite` (`Grown.writeT_facts`) | done |
| `readOnWrite` `\else` | `Grown.readOnWriteFrame` (`Grown.writeT_facts`) | done |
| `readOnAddM` `\else` | `Grown.readOnAddMFrame` (`Grown.readId_then_old`) | done |
| — (the freshness behind `newFromAdd`) | `Grown.alloc_fresh` (`Grown.alloc_id_ge`) | Lean only: an allocation's identity is past every older one |
| `readOnAddM` `\then`, then `initMember` | `Heap.initMember` | done: a member of a fresh struct reads its type's default |
| `initSize`, `sizeOfDyn` | `Heap.initSize` (`Heap.allocDefault_array_len`) | done |
| `readFromCopyToStorage` `\then` | `SVal.readFromCopyToStorage` (`SVal.copyStToM_field`) | done |
| `readFromCopyToStorage` `\then` and `readFromCopyToStorageIdentity` `\then` below the root (`idC(idp, fxs)`) | `SVal.mirrors_copyStToM` (`Theory/Typed/MemMirror.lean`: every object of a copy holds what the storage value held there, past the heap the copy grew) | done |
| `readFromCopyToStorage` `\else`, `readFromCopyToStorageIdentity` `\else` | `Grown.readFromCopyToStorageFrame` (`Grown.readId_then_old`) | done: the premise is the object older than the copy, where KeY's is `idp1 ≠ idp2` |
| `findOnCopy` (a one-member path), `selectOnCopyMemPrim` | `MVal.findOnCopy` (`MVal.copyMToSt_field`) | done |
| `readFromEmptyMemory`, `newFromEmptyMemory` | — | not restated: memory grows from the global part's heap, never from an empty one |
| `readREmpty`, `readRCons` | — | not restated: a path is read one address at a time |
| `initIdentity` | — | not restated: a reference member is allocated with its parent, so it is a member read like a word |
| `defaultValueInt`, `defaultValueBool`, `defValResolve`, `idShapeDef`, `shapeAt*`, `sizeOf*`, `idCCDef` | — | not restated: an allocation carries its type, and a default is read at the type the path declares |

### The Theory's laws as term taclets (`Calculus/TermLib.lean`)

A rule on terms is a constructor of `TermTaclet` (W9.1), on scoped terms
`Tm C Γ .val`, applied on a sequent by name (`rw [findOnSave]`,
`Proves.rewrite`); `TermTaclet.sound` reads its two terms through the scoped
`Tm.denote` and closes the case by the Theory lemma below (`Tm.Theq`).
Side conditions are syntactic `Bool`s on scoped paths, closed by `rfl`
(`Tm.hasSeg`, `Tm.diverges`, `Tm.sameSegs`, `Tm.shift?`, `Tm.findLit?`),
or a hypothesis of the chain (`Tm.KindFreeAt`); `SCtxS` is a storage
context. solkey has none of these as a taclet: they are Lean-only rules
stated on terms, each sound by the typed law it cites.

| Term taclet | Lean (`TermTaclet`) | Theory lemma | Printed rule (the untyped Theory's, deleted at W10.4) | Notes |
| --- | --- | --- | --- | --- |
| `findOnSave` | `TermTaclet.findOnSave` | `Obs.findOnSave` (`Theory/Typed/Obs.lean`) | `findOnSave` | `find(save(s, p, v), q) = v` for a literal word `v`, `q` the path `p` its checks aside (`Tm.sameSegs`: `p[i]@S` is `p[i]`): a copy reads back the new value laid over the old, which is `v` only for a word |
| `findOnSaveFrame` | `TermTaclet.findOnSaveFrame` | `Obs.findOnSaveFrame` | `findOnSaveDifferent` | any written value, `p` diverging from `q` |
| `findMemberCons` | `TermTaclet.findMemberCons` | `Obs.select` (by definition: `select(s, r)` reads below `r`) | — | solkey's `consRcons`, `consRnil`, `findDefinitionMemberCons`/`Prim`: `find(s, r.p) = find(select(s, r), p)`, the path read from its head (`Tm.shift?`), at any depth |
| `findOnSave` in a storage of members | `TermTaclet.findOnSaveIn` | `Obs.findOnSave` | `findOnSave` | `findIn(saveIn(s, p, v), p) = v` for a word `v`, under a `select` (`sts`): the same law at `Contract.ofStruct` |
| `findMemberCons` in a storage of members | `TermTaclet.findMemberConsIn` | `Obs.select` | — | `findIn(s, f.p) = findIn(select(s, f), p)` under a `select` (`Tm.shiftIn?`) |
| `selectOnSaveMember` | `TermTaclet.selectOnSaveMember` | `Obs.select_copyTo` | — | solkey's `selectOnSaveCons` at `a1 = a2`: `find(select(save(s, r.p, v), r), q) = find(save(select(s, r), p, v), q)` |
| `selectOnSaveFrame` | `TermTaclet.selectOnSaveFrame` | `Obs.select_copyTo_ne` | — | solkey's `selectOnSaveCons` at `a1 ≠ a2`: a write under another root is not seen from `r` |
| `selectOnDelAtMember`, `selectOnDelAtFrame` | `TermTaclet.selectOnDelAtMember`, `TermTaclet.selectOnDelAtFrame` | `Obs.select_delAt`, `Obs.select_delAt_ne` | — | the same for a delete, `delAt(s, p)` being `save(s, p, delValue(find(s, p)))` |
| `selectOnSaveMemberIn`, `selectOnSaveFrameIn`, `selectOnDelAtMemberIn`, `selectOnDelAtFrameIn` | `TermTaclet.selectOnSaveMemberIn`, `TermTaclet.selectOnSaveFrameIn`, `TermTaclet.selectOnDelAtMemberIn`, `TermTaclet.selectOnDelAtFrameIn` | the same, `SCtxS.fill_denote` | — | the four in a storage context `K` of saves, deletes and selects (`SCtxS`), which the arrow finds: solkey rewrites a storage term wherever it stands |
| `selectOnSaveMember`, `selectOnSaveFrame`, `selectOnDelAtMember`, `selectOnDelAtFrame` at a member | `TermTaclet.selectOnSaveMemberAt`, `TermTaclet.selectOnSaveFrameAt`, `TermTaclet.selectOnDelAtMemberAt`, `TermTaclet.selectOnDelAtFrameAt` | `Obs.select_copyTo`, `Obs.select_delAt` and their `_ne` (`Tm.selectOnSaveMemberAt_denote`, …) | — | the four one `select` down, in a storage of members: `selectIn(saveIn(s, f.p, v), f)` is `saveIn(selectIn(s, f), p, v)`, a write under another member `f' ≠ f` unseen; in a storage context `K` |
| `findOnDelAt` | `TermTaclet.findOnDelAt` | `Obs.findOnDelAt` | `findDelAt` | where `find(s, p) = w` for a word `w`, the delete reads its default at `p` (`sameSegs`) |
| `findOnDelAtSave` | `TermTaclet.findOnDelAtSave` | `findOnDelAt` over `findOnSave` | `findDelAt` | a delete over a written word, the three paths one path their checks aside |
| `findOnDelAtValue` | `TermTaclet.findOnDelAtValue` | `Obs.findOnDelAt` | `findDelAt` | `find(delAt(s, p), q) = delValue(find(s, q))`, `q` the path `p` its checks aside: the delete's effect at its own path, the value left for a later law (`delValueLit`, or a read below a mapping member) |
| `delValueLit` | `TermTaclet.delValueLit` | by definition (`Op1.denote` of `delValue`) | `delValueDefault` | `delValue(w) = default(w)` for a literal word |
| `findOnDelAtBelow` | `TermTaclet.findOnDelAtBelow` | `Obs.delAt_word_below` (`TVal.delR`) | `findDelAtFields` | a word at or below a deleted node reads its default, where the deleted storage writes the word there (`Tm.findLit?`) and the delete resets every word below `p` (`Tm.KindFreeAt`, a premise of the chain: a mapping's entries and an array's slots past its end are kept, `TVal.delR`) |
| `findOnDelAtBelow` in a storage of members | `TermTaclet.findOnDelAtBelowIn` | `Obs.delAt_word_below` | `findDelAtFields` | `findIn(delAtIn(s, p), q) = defVal` under a `select`: `q` below the member path `p` by members (`Tm.extendsIn`), `s`'s member-wise writes giving the word there (`Tm.findLitIn?`), the node no mapping (`Tm.KindFreeAt`, at a storage of members and a member path, `Srt.pathAt`); a chain's `~[findOnDelAtBelow]~>` names both.  Past the program it is covered where the update holds the delete (`Upd.coversLit`, `Tm.findDelBelowAt`: a read by members below a delete returns) |
| `findOnDelAtFrame` | `TermTaclet.findOnDelAtFrame` | `Obs.findOnDelAtFrame` | `findDelAtOutside` | |
| `findOnPushFrame`, `findOnPopFrame` | `TermTaclet.findOnPushFrame`, `TermTaclet.findOnPopFrame` | `Obs.findOnPushFrame`, `Obs.findOnPopFrame` | — | a push or pop is one term here, not two saves.  Past the program they do not rewrite inside an update's right-hand sides (a law rewrite there asks both sides push-free, `Tm.pushFree`, W9.8.5), only in its equations' sides |
| `selectOnSaveEmptySize`, a fixed array copied to a dynamic one | `TermTaclet.lenOnSaveFixedCopy` | `Obs.copyTo_len_same`, `FixedCopy.observe_len` | — | `len(save(s, q, fixedCopy(E[], v)), p) = n` for an `E[n]` source, `q` the path `p` its checks aside: the `\else` of solkey's taclet, the destination no `fixed` array by its type (Lean only in its shape: `fixedCopy` is Lean's).  Past the program it is covered where the update holds the save and `q` is `p` as written (`Upd.coversLit`, `beqR`: a length read at a save's path returns, `Storage.find_save_same`) |
| `lenOnSaveFrame`, `lenOnDelAtFrame` | `TermTaclet.lenOnSaveFrame`, `TermTaclet.lenOnDelAtFrame` | `Obs.lenOnSaveFrame`, `Obs.lenOnDelAtFrame` | `findOnSaveDifferent`, `findDelAtOutside` at `p.size` | `len(save(s, q, v), p) = len(s, p)`, `len(delAt(s, q), p) = len(s, p)` where `q` leaves `p.length` (`Tm.divergesLen`): a length is a read at `p.length`, one term here (`Term.len`) |

### The laws of memory reads (`EvalLaw`, `Calculus/TermLaws.lean`)

A memory read (`read`, `copyMem`, `copySt`) denotes its run, so a law of one
is no Theory equation but a refinement of the interpreter: where the read
returns, its replacement returns the same (`EvalLaw.sound`,
`Tm.EvalRefinesAt`).  A chain's line past the program applies one in an
update's right-hand side under any modality where the update holds the
write the law reads back (`Upd.coversEval`, `LawCov.eval`, `FmlRw.lawUpdS`).

| Law | Interpreter lemma | KeY taclet | Notes |
| --- | --- | --- | --- |
| `readOnWrite` | `Heap.readAddr_writeAddr_same` (`Theory/Typed/Mem.lean`) | `readOnWrite` `\then` | `read(write(m, a, v), a) ⇝ v` for a literal `v` |
| `findOnCopy` | `MVal.copyMToSt_field`, `SVal.find_overlay_field` | `findOnCopy` over `findOnSave` | `find(save(s, p, copyMem(mtSt, m, i)), p.f) ⇝ read(m, i.f)`: the printed trace's one step from the `find` into memory |
| `readFromCopyToStorage` | `SVal.copyStToM_field` | `readFromCopyToStorage` `\then` | `read(copySt(m, find(s, p)), freshId(copySt(m, find(s, p))).f) ⇝ find(s, p.f)` |
| `readOnAddM` | `Heap.dflt_allocDefault`, `Srt.FreshRead.read_prim` (`Theory/Typed/Mem.lean`, `Calculus/TermLaws.lean`) | `readOnAddM` `\then`, then `initMember`, `initElement` | `read(addM(m, R), a) ⇝ default` for a primitive member or fixed element at a fresh path of the allocation (`Tm.freshPath?`, `Ty.memberTy`) |
| `readOnAddMFrame` | `Heap.Keeps.readAddr`, `SVal.keeps_copyStToM` (`Grown.read_then_old`) | `readOnAddM` `\else` | `read(addM(m, R), a) ⇝ read(m, a)` where `a`'s identity is allocated strictly earlier on `m`'s spine (`Tm.boundedIn`) |
| `readOnAddMFrameIdentity` | the same | `readOnAddM` `\else` at `Identity` | the twin at the identity sort |
| `readOnWriteFrame` | `Heap.readAddr_writeAddr_apart` | `readOnWrite` `\else` | `read(write(m, a, v), b) ⇝ read(m, b)` where `a` and `b` never meet (`Tm.apart?`: different members, a member and an element, one object at different literal indices) |
| `readOnWriteFrameIdentity` | the same | `readOnWrite` `\else` at `Identity` | the twin at the identity sort |
| `readOnWriteIdentity` | `Heap.readAddr_writeAddr_same` | `readOnWrite` `\then` at `Identity` | `read(write(m, a, ref(i)), a) ⇝ i` |
| — | — | `idC(ρ, [account])` | no law: a reference member of a fresh root, `read(addM(m, R), freshId(addM(m, R)).account)`, is the normal form, since KeY's `idC` has no `ITerm` counterpart |

The scoped reducer also applies these same proved memory clauses when a
`read`, `size` or identity read is formed (`foldMem2`, `foldRead2`,
`Calculus/DecideScoped.lean`), before later writes duplicate the observation.
Inputs are bounded by `normalizationSize`; a result is retained only when
its node count does not exceed the original's. `foldMem2_eval`
(`Calculus/DecideTyped.lean`) preserves the complete optional result,
including definedness guards; no additional semantic rule is trusted.

The merges that feed them (`Calculus/StatePartsScoped.lean`):
`{memory := M}{V}` substitutes `M` for `memory` in `V` (`Upd.mergeMem?`,
`Tm.withMemS`; with the locals of a
`{carol := freshId(copySt(…)) ‖ memory := copySt(…)}`, `Upd.mergeMemL?`),
and `{L ‖ storage := s}{V}` substitutes the locals and `s` in one pass, into
memory reads too (`Upd.mergeSt?`, `Tm.substStS`); past the program a
storage write a later one shadows is dropped (`Upd.dropSh`).  A law is
stated at the value or the identity sort (`EvalLaw : Tm C Γ u → Tm C Γ u →
Prop`) and rewrites at that sort inside every right-hand side, memory reads
included (`holds_upd_rwG`, `Calculus/RewriteLaws.lean`).

### The literal laws (`LitLaw`, `Calculus/TermLaws.lean`)

KeY's `*_literals` taclets (`integerSimplificationRules.key`) fold an
operation on two literals.  Each is a constructor of `LitLaw`, stated as the
interpreter computes it, and exact (`LitLaw.exact`): its left side returns
the literal on the right in every state.  So a chain applies one anywhere,
under any modality.  While the program is open: in an update's right-hand
sides, with no premise on the update (`FmlRw.lit`,
`Calculus/RewriteScoped.lean`: `holds_upd_rwC_iff`), and in the equations
and `wt(…)`s of the line's propositional skeleton (`FmlRw.litEq`, an
equivalence: `Fml.lawAlongS_holds`), where a term taclet rewrites a whole
side too (`FmlRw.lawEq`).  Past the program: in an update's right-hand
sides (`FmlRw.lawUpdS`, `Calculus/RewriteLaws.lean`).

| Law | KeY taclet | Notes |
| --- | --- | --- |
| `add_literals` | `add_literals` | `a + b ⇝ a + b` folded, where the sum is in `uint` range (`PrimTy.ofInt?`; out of range the sum reverts and is its own normal form) |
| `sub_literals` | `sub_literals` | `a - b ⇝ a - b` folded, in `uint` range |
| `leq_literals` | `leq_literals` | `a <= b ⇝ true`/`false` |
| `less_literals` | `less_literals` | `a < b ⇝ true`/`false` |
| `equal_literals` | `equal_literals` | `a == b ⇝ true`/`false` |

### The names

The typed laws keep solkey's names (`Grown.readOnWrite`, `MVal.findOnCopy`,
…; a taclet's `\else` as its name with `Frame`, and the storage laws
`Obs.findOnSave`/`findOnSaveFrame` name `selectOnSaveCons`'s two
branches), which is what makes this file a map; a law with no
solkey counterpart is marked Lean only at its row.  The untyped Theory's
enumeration of its printed rules (`TheoryRule`, `lemmaNames`) was deleted
with it at W10.4.

### Deviations

Where the theory or a taclet differs from KeY, each stated once at its row:

- **Eager against lazy.** `addM(m, R)` carries the allocated `RefTy` (KeY's
  `readOnAddM` resolves a fresh object's slot to `init<[α]>` at the
  reader's sort; `Semantics.allocDefault` materializes the object), and a
  default is read at the type its path declares; a copy is computed from
  the type (`TVal.overlay`), not a lazy leaf.
- **An index check is explicit after a merge.** KeY's `at(i)` is unchecked
  and `p[p.length]` reads the length in the state; here `p[i]` and
  `p[p.length]` check against the storage of the state they run in, so merged
  under `{storage := S}` they become `p[i]@S` and `p[p.length]@S`
  (`Tm.substStS`), the check performed in `S`.  The laws read them as `p[i]`
  (`Tm.sameSegs`, `Tm.diverges` on shapes); `p[p.length]@S` is its own
  path.
- **A push is one term.** `STerm.push s p v` *is* `save(save(s, p[p.length], v),
  p.length, p.length + 1)`, where KeY writes two parallel `save`s: a program
  can perform neither write alone. The slot it lands on is recycled or a
  fresh default (`Storage.push`, `pushSlot`); a mapping nested in a popped element
  survives into the next push either way (`storagePush*`/`storagePop*` rows).
- **Deletes are computed from the type** (`TVal.delR`): a mapping's entries
  and an array's slots past its live end are kept, with no premise on the
  node's kind; `delete` through a fixed-size array element is open in KeY
  and sound here ("Storage delete").
- **Memory paths are sources as they stand**, so KeY's four memory capture taclets are
  unclaimed and the `MemRef` index captures are `find same` (see their rows).
- **Shapes are types.** An allocation carries its type and a path is
  typed, so `fieldShape`, `shapeAt` and the `wf` taclets are not modelled:
  a typed storage and heap are in the shape their types declare.
- **Scope ends and hidden binders are Lean only and print as nothing**: the
  capture pop after a rule's fresh locals (`Frames.pop .capture`), a block's
  and a call frame's end, and the binder a declaration with an initializer
  puts in front of its assignment (`Premise.bind`).  KeY's program variables
  are global and need neither (their rows above).
- **Unset locals**: `T storage lsv;` binds `lsv := unset` (`storageLocalDeclSkip`),
  and the hidden binder of `memoryLocalDeclInitDrop` ranges over an unset
  memory local too (decision 17'); a read through either reverts.
- **`typed` is not modelled**, and the storage copy fold is not followed (top
  of this section).

The Lean payment update prints `pay(receiver, amount)`: it combines the
ledger booking of KeY's payment rule with the typed balance debit. This
Lean extension is explicit in printed and LaTeX derivations.

### Rigid conditions during a split (M19)

`Calculus/Rigid.lean` reuses `applyOnRigidFormula`'s scoped substitution
(`Fml.substU`, `Fml.substU_holds`) and binder thinning to read only a
literal-local branch condition before the context's updates. The combination
with a live sibling derivation (`Seq.refuteLanded_sound`) is Lean-only:
it preserves the shared prefix's diamond landing and exhaustion obligations.
It adds no taclet or `Proves` constructor. Both the condition and each update
are capped at 512 syntax nodes before substitution; the final condition is
also capped. Non-ground conditions use the existing `Seq.refuteS` clauses.
A rigid refusal or failed check conservatively walks both branches, even if
contradictory unused premises could have closed one in the previous path.
