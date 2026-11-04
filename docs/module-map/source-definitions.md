# Independent source definitions

| Module | What it defines |
|---|---|
| `Source/Syntax.lean` | S00: the pinned solc 0.8.38 grammar as intrinsic syntax `Syn : Cat → Type`, indexed by category and by statement context (`SCtx`: loop, `unchecked`), excluded syntax (assembly/Yul, `layout at`, `>>>`, `years`) included. |
| `Source/Ctor.lean` | S00: the constructor index `Ctor` (`Ctor.mem_all`), `Syn.nodes`/`Syn.children`, the syntax-level exclusions `Excl` and precise rejection (`Syn.rejections_of_sub`). |
| `Source/Upstream.lean` | S00: the explicit mapping from grammar rules/labels and manifest features to constructors (`grammarCtors`, `featureCtors`; `Ctor.grammar_covers`), checked by `scripts/check-source-grammar.mjs`. |
| `Source/Decls.lean` | S00: the typed declaration graph (`Decl`, `Syn.decls`, `Decl.refs`, `Syn.decls_ctor`). |
| `Source/Examples.lean` | S00 controls: an in-profile counter and rejected assembly, `layout at`, `>>>` and `years` programs. |
| `Source/Const.lean` | S01: compile-time constants: exact rationals `Q`, literal values and units, `Syn.const` (folding `+ - * / % **`, shifts and two's-complement bitwise operations), the implicit and explicit conversions of constants to integer and fixed-point types. |
| `Source/Types.lean` | S01: static types `STy`, elaboration of elementary types, implicit and explicit conversions (fixed point per the second-round decisions) with `implicit_int_range` and `FixTy.subsumes_inRange`. |
| `Source/Resolve.lean` | S01: name resolution: C3 linearization, scoped lookup, builtins classified against the profile (`Builtin.status`, member and call-option status), the `Resolves` judgment with `resolve_iff` and `Resolves.unique`. |
| `Source/Typing.lean` | S01: type-name elaboration (`Syn.tys`), typing contexts, expression typing as data (`Typed`, `HasType`) and statement typing in a fixed body context (`StmtD`/`ItemsD`, `StmtOK`/`ItemsOK`). |
| `Source/Resolved.lean` | S01: the intrinsic resolved form (`RExpr`/`RStmt` over local types, de Bruijn `Idx`, explicit implicit-conversion evidence) and the elaboration of derivations into it (`Typed.toR`, `StmtD.toR`). |
| `Source/WellFormed.lean` | S01: settings over solc's two pipelines (`Settings.coder`), resolutions, body frames (`Decl.frame?`), and well-formedness of a resolved unit (bases, clashes and overloads, pragmas, declared types, placement, constants, bodies). |
| `Source/TypingExamples.lean` | S01 controls: a derivation per typed expression constructor (`exprCoverage_typed`, `exprCoverage_total`, `stmtCoverage_total`), the counter well formed, C3 on a diamond, refuted ill-typed, `msg.value`, clashing, same-signature, interface-body and unknown-pragma programs. |
| `Source/State.lean` | S04.01: source values `Val` over a declaration `Layout` (ranges, enum bounds and reference locations intrinsic), contents `Data` (recursive aggregates, content-keyed mappings), typed `memory` (`Heap`, copy and alias laws), read-only `Calldata`, `Storage` typed by its layout, defaults. |
| `Source/Observe.lean` | S04.02: ABI words and bytes of values (`Val.word`, `Val.word_int`), selectors, `Panic`/`Error` revert data (`panicData_code`, `panic_distinct`) and `revertOutcome`. |
| `Source/World.lean` | S04.03: instance accounts, the world, transient storage cleared per transaction, transaction configuration, a journal of operations, call frames with journal rollback (`rollback_run`), value transfers. |
| `Source/Units.lean` | G12: source units of a compilation input (`UnitSet`), solc's import path resolution and remappings (`Path.absolute`, `Remapping.apply`), declaration identities (`DeclId`), the file-level scope across imports (`Sees`) and G12's judgment `UnitsOK`. |
| `Source/Overloads.lean` | G12: overload sets across a contract's bases (`InheritedFn`: hidden only by a more derived function with the same parameter types). |
| `Source/ConstCheck.lean` | G13: compile-time constants: purity of constant initializers (`PureS`, `ConstInitsPure`, solc error 8349), solc's typed constant evaluation (`TEval`, `NamedConst`, `ConstVal`), array lengths through it (`ArrayLenOK`) and acyclic constants (`ConstsAcyclic`). |
| `Source/UserOps.lean` | G13: user-defined value types: operator bindings of global `using {f as op} for T` directives (`opBindings`, well formed: `UsingOpsOK`), and the typing of operators, `wrap` and `unwrap` (`UdvtTyped`). |
| `Source/Inheritance.lean` | G14: solc's contract-level checks as relations: overrides (`FnOverrideOK`, `OverridesOK`), required overrides (`MustOverride`), implementations (`ImplOK`), base-constructor arguments (`CtorArgsOK`), modifier invocations (`ModInvOK`), `using for` libraries (`UsingLibOK`), constructor order and callable identity; `InheritanceOK`. |
| `Source/StateExamples.lean` | S04.01–S04.03 controls: nested memory aliasing, an independent memory copy, storage round trips, distinct panic outcomes, transfers, a reverted call undoing its writes. |
| `Frontend/Checked/Token.lean` | G08: the tokens of the checked frontend (`Tok`, keywords, punctuation, Yul keywords), pieces with their exact bytes (`Piece`), located tokens and errors. |
| `Frontend/Checked/Tables.lean` | G08: byte-literal keyword, word and punctuation tables, generated by `scripts/checked-lexer-tables.py`. |
| `Frontend/Checked/Lexer.lean` | G08: the checked lexer over bytes: per-lexeme classification (`classify`, the lexical classes of `SolidityLexer.g4`), maximal-munch splitting with modes, the certificate `Lexed` (`lex_sound`, `lex_reprint`, `lex_locate`, `lex_error_pos`). |
| `Frontend/Checked/LexExamples.lean` | G08 controls: every lexer rule's sample classified (`lexRules_classified`, `lexRules_cover`), tables against spellings, accepted inputs and located refusals. |
| `Frontend/Checked/Print.lean` | G09–G11: the token yield `Syn.yield` of S00's syntax under a layout (attribute orders, string fragments): the grammar derivation `Syn.Derives`. |
| `Frontend/Checked/Prec.lean` | G10/G11: the precedence, associativity and dangling-`else` predicate `Syn.prec`, with refusal where the grammar and solc disagree. |
| `Frontend/Checked/Parser.lean` | G09–G11: the untrusted recursive-descent parser from located tokens to `Syn .unit` and its layout (`parseTokens`), fuel-structural. |
| `Frontend/Checked/Check.lean` | G11: whole-source parsing checked against the yield and precedence (`parse`, `parse_sound`, `parse_derives`). |
| `Frontend/Checked/Render.lean` | G09: canonical token spellings and the source printer `Syn.print`. |
| `Frontend/Checked/TypeCorpusAcceptance.lean` | G09 `declCorpus_accepted`, composed from the two per-member constructor certificates. |
| `Frontend/Checked/TypeCorpusCoverage.lean` | G09 `declCtors_covered`, composed from the two per-member constructor certificates. |
| `Frontend/Checked/TypeCorpusExamples.lean` | Re-export of the G09 corpus modules (acceptance, coverage, profile); no declarations. |
| `Frontend/Checked/TypeCorpusFirst.lean` | Kernel-certified constructor list for the first original corpus member. |
| `Frontend/Checked/TypeCorpusMembers.lean` | Exact original two-member corpus equation. |
| `Frontend/Checked/TypeCorpusObservations.lean` | Named copies of the original profile and round-trip predicates. |
| `Frontend/Checked/TypeCorpusProfile.lean` | G09 `declCorpus_in_profile`, composed from the per-member profile certificates. |
| `Frontend/Checked/TypeCorpusProfileFirst.lean` | Per-member certificate (`TypeCorpusCertificates.first_profile`): the first corpus member parses with no rejections. |
| `Frontend/Checked/TypeCorpusProfileSecond.lean` | Per-member certificate (`TypeCorpusCertificates.second_profile`): the second corpus member parses with no rejections. |
| `Frontend/Checked/TypeCorpusRoundtripFirst.lean` | Per-member certificate (`TypeCorpusCertificates.first_roundtrip`): the first corpus member reprints to the same tree. |
| `Frontend/Checked/TypeCorpusRoundtripSecond.lean` | Per-member certificate (`TypeCorpusCertificates.second_roundtrip`): the second corpus member reprints to the same tree. |
| `Frontend/Checked/TypeCorpusSecond.lean` | Kernel-certified constructor list for the second original corpus member. |
| `Frontend/Checked/TypeDeclarationExamples.lean` | G09 declaration controls: recursive and mutual structs, attribute order, transient, refusals. |
| `Frontend/Checked/TypeExampleCore.lean` | Original G09 shared helpers and unchanged corpus data. |
| `Frontend/Checked/TypeNameExamples.lean` | G09 type-name controls: arrays, mappings, function types, attribute layouts, refusals. |
| `Frontend/Checked/TypePrintChecksum.lean` | G09 `print_checksum_flag`. |
| `Frontend/Checked/TypePrintExamples.lean` | Re-export of the G09 printing modules (text, round trip, checksum); no declarations. |
| `Frontend/Checked/TypePrintRoundtrip.lean` | G09 `print_roundtrip`, composed from the per-member round-trip certificates. |
| `Frontend/Checked/TypePrintText.lean` | G09 `print_text`. |
| `Frontend/Checked/TypeExamples.lean` | Entry point re-exporting the split G09 modules, with the two axiom guards. The controls: type-name trees, attribute layouts, recursive declaration references, printing round trips, type and declaration constructor coverage (`declCtors_covered`), refusals. |
| `Frontend/Checked/ExprExamples.lean` | G10 controls: precedence and associativity lemmas over `Syn.precNode`, every operator, expression trees, refused ambiguous forms, expression constructor coverage (`exprCtors_covered`). |
| `Frontend/Checked/Certificate.lean` | G11: G05's parse-stage instance: `Units`, `Parses`, `parseChecker` (`checkUnits_sound`), the producer (`produce_accepted`), `FrontendSpec.ofParse`. |
| `Frontend/Checked/UnitExamples.lean` | G11 controls: statements, definitions and units, every S00 constructor covered (`allCtors_covered`, `profileCtors_covered`), out-of-profile refusals, the G05 checker on a two-unit input. |
| `Source/Value.lean` | S02: run-time values `RVal`, `Halt`, decidable `STy` equality, wrapping (`wrapBits_mem`), checked/unchecked integer and fixed-point arithmetic, shifts, powers, comparisons, value conversions. |
| `Source/Elaborated.lean` | S02 prerequisite: resolved bodies, modifier invocations, initializers and base arguments (`Program`), and `Elaborated` (a resolution carrying its program, every part tied to a derivation). |
| `Source/Unique.lean` | Q1: uniqueness of meaning (`Typed.unique`, `StmtD.unique`, `ItemsD.unique`, `RBody.ofDerivation_unique`), solc's literal typing (`Typed.constShape`), `0.length` refused, literal-gap controls. |
| `Source/Machine.lean` | S02: the logical storage layout (`Env.cellTy`), `Locals`, the machine state `St`, frames `Fr`, `Glob`, the monad `EM`, storage/memory reads, writes, copies and deletion. |
| `Source/Eval.lean` | S02/S03: the interpreter of resolved expressions, lvalues, statements, modifiers, internal and external calls, dispatch and environment moves, at a horizon. |
| `Source/Semantics.lean` | S03.02/S03.04/S04.04/S05: constructor order per pipeline, deployment, transactions, least-horizon completion (`firstDone_mono`), sessions as G01 prefixes (`sessionAt_consistent`, `sourceLang`). |
| `Source/Ledger.lean` | S05: the semantic status of every expression and statement constructor against S01's coverage (`semExprCoverage_of_typed`, `semExprGaps_spec`). |
| `Source/SemanticsExamples.lean` | S02–S05 controls: overflow, division by zero, evaluation order per pipeline, short circuit, two placeholders, constructor order, revert rollback of storage and transient storage, a reentrant callback. |
| `Source/Infer.lean` | S02 item 1b: type inference computing derivations (`Typed.infer`, `StmtD.infer`, `ItemsD.infer`), sound by construction. |
| `Source/Elaborate.lean` | S02 item 1b: the elaborator `elaborate : Resolution → Option Elaborated` (bodies, modifiers, initializers, constants, base arguments), coherent by construction. |
| `Source/ElaborateExamples.lean` | Controls of the elaborator: a unit with inheritance, a base argument, a modifier and an initializer elaborated from syntax and run. |
| `Source/Horizon.lean` | S05 item 2: the interpreter is monotone in its horizon (`belowAt`, horizon independence `runTx_stable`, `firstDone_runTx`), only appends events (`growAt`), and a timed-out run's events are a prefix of a larger horizon's (`approxAt`, `runTx_events_mono`). |
| `Source/HorizonDeploy.lean` | S05 item 2: a deployment not completed at a horizon shows a prefix of its events at every larger one (`deploy_events_mono`). |
| `Source/Session.lean`, `Source/SessionExamples.lean` | Sessions showing the events of unfinished transactions (`sessionAtEvents`, `sourceLangEvents`), consistent, and their controls. |
| `Source/Hoare.lean` | V04b: Hoare triples over the interpreter monad `EM` (`Hoare`, `NotStuck`), with a rule per combinator (`bind`, `sub'`, `attempt'`, `lift'`, …). |
| `Source/WellTyped.lean` | V04b preservation: references agree with the heap typing and the layout (`Val.RefOK`, `DataOK`, `RValOK`, `LocalsOK`, `HeapOK`, `StOK`, `EMOK`); memory operations keep it (`alloc_ok`, `allocRef_ok`, `heapPut_ok`, `heapAt_ok`). |
| `Source/Decode.lean` | FU2-B `abi.decode`: the decoder keeps `MemOK` and is never stuck at the types it reads (`decodeArg_ok`, `decodeArgs_ok`, `abiDecodeData_ok`); the evaluation arm relative to its data (`evalE_abiDecode_ok`, `evalE_abiDecode_lit_ok`). |
| `Source/DecodeExamples.lean` | FU2-B controls: `abi.decode` elaborated from syntax and run, malformed payloads reverting as solc's decoder (empty revert, Panic `0x41`), named refusals. |
| `Source/Calldata.lean` | FU2-B `calldata` references: entry decoding, element/byte reads, slices and copies are never stuck and keep `MemOK` (`decodeArgs_entry_ok`, `readLoc_cd_ok`, `sliceR_ok`, `cdToMem_ok`); the `x.length`, `x[j]`, `x[s:e]` arms on locals (`evalE_cdLength_ok`, `evalE_cdIndex_ok`, `evalE_cdSlice_ok`). |
| `Source/CalldataExamples.lean` | FU2-B controls: `calldata` parameters elaborated and run, elements validated at the read, entry checks, slices and copies reverting as solc's. |
| `Source/InlineExamples.lean` | FU2-B controls: inline arrays elaborated and run at solc's common type, an index past the length panicking, refusals without a common type or with reference elements; `new T[](n)`, `new bytes(n)`, `new string(n)` zeroed, panicking `0x41` at `2^64`. |
| `Source/TryExamples.lean` | FU2-B controls: `try`/`catch` between two deployed contracts, success with returns bound, a caught revert (plain and `bytes memory` clauses), no code at the target not caught. |
| `Source/ValueProgress.lean` | V04b progress, value layer: `binVal`/`cmpVal`/`shiftVal`/`unaryVal`/`incDecVal`/`convVal`/`constVal` are never stuck in their domains (`NotStuckR`); every elaborated term is in them (`RExpr.OpsOK`, `Typed.toR_opsOK`, `Elaborated.body_opsOK`). |
| `Source/ExprProgress.lean` | V04b progress, expressions: `NS`/`NSP`; the value fragment (`RExpr.ValFrag`, `RExpr.MapRef`, `RLVal.IsSimple`: locals, value-type state variables, mappings) is never stuck (`exprNSAt`, `evalE_valFrag_ns`; `readAt_ns`, `writeAt_ns`, `keyStep_nsp`, `convRV_ns`); the fragment parameterized by allowed callees (`RExpr.ValFragC`, `CallNS`, `exprNSAt_step`) |
| `Source/StmtProgress.lean` | V04b progress, statements: the statement value fragment in a body frame is never stuck (`stmtNSAt`, `stmtNS`, `itemsNS`, `ItemsD.toR_ns`; `RStmt.ext`, `Locals.restore_ok`, `BodyFrame`); calls inside expressions by the joint induction `FragAt`/`fragAt` under `CallsOK` (`evalE_callFrag_ns`); elaborated frames (`Elaborated.body_locals`, `Glob.dispatchFn_params`) |
| `Source/SoundnessExamples.lean` | V04b controls: value-layer witnesses and stuck negative controls; fragment witnesses evaluated in the kernel (a loop, a storage update), an unframed `return` stuck; call witnesses (`callF_ns`, `recF_ns`, `callF_badFrame_stuck`) |
| `Source/FailureMachine.lean` | Explicit-plan Source frame operations (H16 execution leaf) These operations run in the actual Source EM and use its existing event emitter. |
| `Source/FailureMachineControls.lean` | Independent expected actual-EM controls. |
| `Source/FailurePrimitives.lean` | Shared actual-EM failure primitives below Eval. |
| `Source/Monetary.lean` | Balances are exact naturals, including values outside the EVM word range. |
| `Source/FailureEventControls.lean` | Independently fixed complete states for actual Source.emitEvent, with nonempty caller journal/event prefix and byte-memory alias. |
| `Source/FailureEventLaws.lean` | Full-state law for the actual Source event emitter. |
| `Source/FailureRuntimeControls.lean` | Actual explicit-plan Source execution through existing registered code. |

| `Source/MonetaryLaws.lean` | H19 primitive credit-produced and debit-preserved range facts; constructive out-of-range successful debit control. No Account/ledger migration or execution reachability claim. |

| `Source/FailureRequest.lean` | Actual EM request-budget scope: dropped/scheduled requests, exact Nat balance argument, zero-cut and active-owner refusal, halt/local retention and sequential ordinal controls. Session funding, rollback and consistency not claimed. |

| `Source/Funds.lean` | Actual request-boundary funds validation, invalid whole-state identity, exact valid execution, stable completed horizons and both session-driver drop laws. |
| `Source/FundsControls.lean` | Actual Source payable requests in both pipelines: stress-state drop, following valid request, timeout/revert distinction, prior debit/credit controls. |

| `Source/FailureConstructorControls.lean` | H16 actual initializer/body CALL event cuts, rollback and seeded parent/request owner propagation; default-None horizon proofs retained. Root/session indexing and full adequacy remain open. |

| `Source/FailureTransactionControls.lean` | H16 actual root dispatch plan, own-frame reverts versus outer-stop/timeout propagation, transient/journal finalization and complete state controls; request fate/funding/P8 adequacy remain open. |

| `Source/FailureFrameHorizon.lean` | H16 actual frame/check/event Grow and frame Approx transport; explicit real body relations and rethrow-timeout continuation, not full planned evaluator consistency. |
| `Source/FailureFrameHorizonControls.lean` | Inhabited event-prefix/heap/caller full-state frames, timeout/outer-cut controls and counterexample to blanket attempt approximation. |

| `Source/FailureRequestAdmission.lean` | Exact post-fee Nat value admission around unchanged requestScope; current effective-fate normalization, other-request/frame preservation, arbitrary-body drop/admitted laws, complete state/byte/cut/timeout/ordinal controls; no balance installation/session/P8 claim. |

| `Source/FailureNoCuts.lean` | Structural CutFree over the actual typed cursor; no-stop, NoFail entry, cleanup/tick preservation and full-state check identity. No full evaluator coherence/NoFail claim. |
| `Source/FailureNoCutsEffects.lean` | Actual enabled emitter: complete event append, exact live-budget tick, retained remaining locals/state under CutFree. |
| `Source/FailureNoCutsControls.lean` | Constructed nested request/frame no-cut budgets, full-state events/heap bytes and counterexample to NoFail-plan-alone reasoning on arbitrary cursors. |
