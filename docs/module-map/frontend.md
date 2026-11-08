<!-- Generated from docs/module-map/frontend.d/ by scripts/coord-tools/fragments.sh; edit the fragments there, not this file. -->
# The solc front end

`SolkeyTestSuite` (`lake build SolkeyTestSuite`): solkey's `TestSuite.sol` from
the AST the pinned soljson writes (`scripts/solc-ast.mjs` makes
`tests/solc/TestSuite.ast.json`; `./scripts/check-solc-ast.sh` re-derives and
diffs it).  `docs/testsuite-proofs.md` has the counts and timings.

| Module | What it defines |
|---|---|
| `Frontend/SolcJson.lean` | solc's JSON AST (`Lean.Json`) printed as `sol` text per function: `readContract`, `Gap`, `Tag`; a struct the table's when its members are, else the contract's own, declared (`readStructs`, `ownStructMembers`), struct constructors printed; the functions called by name as `contract!` members, callees first; the constructor (`ctor`, a root of the calls) and the state variables' initializers (`initMembers`, `initGap`).  Split by topic into the pieces below (`docs/parallelism.md`), this module the umbrella. |
| `Frontend/SolcJson/Body.lean` | What is left out, reading the JSON, types, expressions and statements; declaration-ID metadata and lazy selector receiver helpers. |
| `Frontend/SolcJson/Contract.lean` | JSON contract/dependency reading; callable-only source/native finite-dispatch signatures with source identity; inherited empty-data receive/payable fallback registration with direct missing-identity refusal; inherited constructor initialization follows verified legacy/viaIR provenance. |
| `Frontend/SolcJson/Getters.lean` | Source ABI identities and record-paired, nonempty getter plans, lowered through ordinary function members; primitive/UDVT/enum/contract values, nominal mapping keys, conservative nominal dispatch signatures, reference/function-result refusal and empty-data array bounds. |
| `Frontend/SourceUnits.lean` | Original compilation-unit ASTs, per-source provenance and checked compiler import identities; explicit specification/mixed-legacy-ABI refusals. |
| `Frontend/Static/Closure.lean` | G12–G14: reachability by saturation over a finite graph (`iter_sound`, `iter_complete`), shared by the static checkers. |
| `Frontend/Static/Units.lean` | G12: the import resolver `UnitSet.globals` (sound and complete for `Sees`, through cycles), the program check `UnitSet.unitsOK` (`unitsOK_iff`), identities (`Sees.decl_exists`) and agreement with S01's lookup (`globals_lookup`). |
| `Frontend/Static/Overloads.lean` | G12: the inherited overload set `Env.inheritedFns` (`mem_inheritedFns`, extends S01's lookup) and overload selection (`selectOverload`). |
| `Frontend/Static/UnitsExamples.lean` | G12 controls: an import cycle, a diamond (one identity), a clash, aliases, a missing unit, remappings, shadowing, an ambiguous overload and overloads across bases. |
| `Frontend/Static/Infer.lean` | G13: type inference `infer` over every category, returning S01 derivations (`Typed`, `LVal`, `TypedArgs`, `TypedSlots`): sound by construction. |
| `Frontend/Static/InferComplete.lean` | G13: completeness of `infer` for every S01 expression rule (`typed_complete`, `lval_complete`, `args_complete`, `slots_complete`). |
| `Frontend/Static/InferStmt.lean` | G13: statement and block checking `inferS`, returning `StmtD`/`ItemsD` derivations, including H125/H157 typed library/Error enumeration via `tryLibraryRes`. |
| `Frontend/Static/InferStmtComplete.lean` | G13: completeness of `inferS` (`stmt_complete`, `items_complete`); `stmtOK_iff`, `itemsOK_iff`; additive H125/H157 library/Error proof case with unchanged theorem statements. |
| `Frontend/Static/WellFormedCheck.lean` | G13: `wellFormedB` decides S01's `WellFormed` (`wellFormed_iff`), every body and initializer typed by the checkers. |
| `Frontend/Static/Consts.lean` | G13: purity checker (`pureB_iff`, `constInitsB_iff`), typed constant evaluation (`tevalP`, `nconstP`; `teval_complete`, `nconst_complete`), `evalConst`, `arrayLenB`, the cycle check (`acyclic_iff`). |
| `Frontend/Static/UserOps.lean` | G13: the user-defined value type checker `udvtTys` (`udvt_iff`) and the binding check (`usingOpsB_iff`). |
| `Frontend/Static/Standalone.lean` | G13, backfill item 5: the type a constant stands alone at (`STy.standalone`: a fractional constant at its mobile fixed-point type), the relations `StandaloneTyped`/`AbiArgTyped` decided by `standaloneTys` (`standalone_iff`, `abiArg_iff`), and the value from `Fx.mobileConst?`/`Fx.abiConst?` in `Language/FixedPoint/Literals.lean` (`standalone_value`). |
| `Frontend/Static/InferExamples.lean` | G13 controls: S01's examples checked by computation, ill-typed and ill-formed refusals, named constants, a cyclic constant, a non-compile-time constant, UDVT operators and conversions. |
| `Frontend/Static/Inheritance.lean` | G14: checkers deciding each inheritance relation (`fnOverrideB_iff` … `usingLibB_iff`, `inheritance_iff`) and callable identity (`callable_unique`). |
| `Frontend/Static/C3.lean` | G14: the C3 specification `C3Lin`, the merge laws and soundness of S01's `Env.linearize` (`linearize_sound`); constructor order (`ctorOrder_spec`). |
| `Frontend/Static/InheritanceExamples.lean` | G14 controls transcribing solc 0.8.38's `inheritance/` and `nameAndTypeResolution/` syntax tests, with their verdicts. |
| `Frontend/Static/Certificates.lean` | The static checkers as G05 `Checker` values (`unitsChecker`, `metadataChecker`, `strictMetadataChecker`, `inheritanceChecker`) and the program's library declarations. |
| `Frontend/Source.lean` | Compiler/pragma/settings validation, derived compilation-mode observations, static compiler-code artifacts and an admission result certifying its extracted feature list. |
| `Frontend/SolcJson/Admission.lean` | Bounded AST scope classification and declaration-header closure over resolved execution roots; structured policy, upstream and implementation diagnostics. |
| `Examples/Tactics/SourceUnitsImport.lean` | Both pinned compilers and pipelines: module calls, lexical error aliases, exact entry error bytes, receiver/condition effects and nonvacuity controls. |
| `Examples/Tactics/SourceUnitsMetadata.lean` | Missing, duplicate and foreign source metadata, lexical-specification refusal and real compiler remapping controls. |
| `Examples/Tactics/SourceLiteralsImport.lean` | Pinned literal, byte, address and constant execution, universal remainder correctness and a false-property counterexample. |
| `Examples/Tactics/SourceIdentifiersImport.lean` | Raw source names, builtin shadowing, address fields and specifications with dollar names. |
| `Examples/Tactics/SourceAdmissionImport.lean` | Scope roots, metadata-only references, ABI modes, malformed AST metadata and provenance regressions. |
| `Examples/Tactics/OperatorAliasesImport.lean` | Modern resolved UDVT aliases: all unary/binary signatures, nominal validation, lazy branches, both pipeline schedules, callee arithmetic scope and concrete false properties. |
| `Examples/Tactics/DeclarationMetadata.lean` | Compiled declaration metadata: interface IDs, receiver evaluation/laziness and rejection of malformed or anonymous selectors. |
| `Examples/Tactics/PublicGetters.lean` | Imported primitive scalar/mapping/array getters, interface overrides, struct omissions, ABI identities, bounds/helper freshness; box safety plus concrete success/panic controls at self address 7, with external-try diamond automation still limited. |
| `Frontend/Testing.lean` | `#solkey_test`: kernel-checked function and specification tests with checkpointed JSON results, imported-closure axiom-policy memoization and opt-in phase timers ([measurements](../browser-simple-benchmarks.md)); `scripts/test-solidity.mjs` compiles and tests `.sol` files/directories ([solidity-testing.md](../solidity-testing.md)). |
| `Frontend/Import.lean` | `solc_import "f.json" hash 0x… as N renaming A => B`: `N : Contract`, `N.f : Prog N Γ Γ'` per function (read in its parameters' context, quoted hash-consed and checked by the kernel), `N.constructor : Prog N Γ Γ'` (a deployment, `constructor(x̄);`), `N.report : List ImportRow`; native evaluation of the imported contract and the legacy `EvalOrder` override (two `evalExpr` sites), with the selected order quoted back as data. Large contract tables compile in list segments, with a kernel-checked equality to the original literal. |
| `Frontend/WorldImport.lean` | Strict hash-checked source creation/creation-try and linked mutation commands with explicit premises, executed operation certificates and funded reachability bridges. |
| `Solkey/TestSuite.lean` | `Solkey.TestSuite`, its source function rows and pinned import report (counts in the module and `TestSuite/Report.lean`). |
| `Solkey/ComputedRevert.lean` | Pinned solc computed reasons/raw rethrows, with public self-call bodies retained; rejected assembly shapes and word-array buffers. |
| `Solkey/Constructors.lean` | solkey's `Counter.sol` and `EtherWallet.sol` imported (`tests/solc/Counter.ast.json`, `tests/solc/EtherWallet.ast.json`): their constructors and initializers, and `EtherWallet`'s constructor obligation derived; `tests/solc/CtorGap.sol` and `tests/solc/InitGap.sol` pin what the import leaves out. |
| `Solkey/ScopedFlip.lean` | `tests/solc/ScopedFlip.sol` (one box function) through the TestSuite's commands, pinned: `solc_scoped_problems … decl`, `#solkey_problem`, `#solkey_derive?` and `#solkey_obligations`. |
| `Frontend/Problems.lean` | `obligation` (a function's statement written on its program `N.f`: `∀x̄. wt(storage) → [m] N.f`, a constructor's from `Problem.deployUpd`); `solc_scoped_problems N [decl]` (`N.f.problem : Fml N []` per program, the entries of one kernel-checked table `N.problems`), `#solkey_problem`, `#solkey_scan` (`N.f.problem`, or the statement `obligation` writes), `#solkey_derive?` (`scopedSearch` on `⊢ N.f.problem`; the replays to paste, when they fit `maxHeartbeats`), `#solkey_obligations` (derived, checked against `⊢ N.f.problem` and Lean's three axioms / pending). |
| `TestSuite/Problems.lean` | Two of `Solkey.TestSuite`'s obligations pinned in solkey's syntax (`#solkey_problem`), `initState_wt`. |
| `TestSuite/ScopedProblems.lean` | The pinned scoped obligations, `Solkey.TestSuite.f.problem : Fml Solkey.TestSuite []`, by `solc_scoped_problems … decl` (entries of one table, declared, not compiled), each on its program `Solkey.TestSuite.f`; what the `Derived` modules prove. |
| `TestSuite/Derived1.lean`, `TestSuite/Derived2.lean`, `TestSuite/Derived3.lean`, `TestSuite/Derived4.lean`, `TestSuite/Derived5.lean`, `TestSuite/Derived6.lean`, `TestSuite/Derived7.lean`, `TestSuite/Derived8.lean`, `TestSuite/Derived9.lean`, `TestSuite/Derived10.lean`, `TestSuite/Derived11.lean`, `TestSuite/Derived12.lean` | `Solkey.TestSuite.f.proved : ⊢ Solkey.TestSuite.f.problem`, the scoped sequent (`open scoped Solidity.Scoped`, `Calculus/ProvesDerive.lean`), 40, 40, 40, 40, 40, 37, 41, 23, 40, 40, 11 and 20 (412 in all), by `sol_prove` and explicit leaf tactics; 7 and 8 are what pushes, pops and storage copies added, 9 to 11 what memory added, 12 what copies between memory and storage added. |
| `TestSuite/Derived13.lean` | `testArrayCopyClearsOldElements`, by `sol_prove`; four resurrection claims, upstream's `solc/StorageDangling.sol`, are proved in `Examples/Tactics/StorageDangling.lean`. |
| `TestSuite/Derived14.lean` | The twenty obligations added at solkey `1b4341a303` (`send`, internal calls, `return`, tuples), each by `sol_prove`; ground splits are pruned (`Seq.refuteS`, closed by `Proves.closeFalse`). |
| `TestSuite/Derived15.lean` | 53 migration derivations for returns, overloads, modifiers, helpers, storage shapes, fresh arrays and push operands; the report counts only kernel-checked declarations. |
| `TestSuite/Derived16.lean` | Native push compound, DIV/MOD, increment and signed three-push derivations; demanded primitive reads close the signed case within the existing bounds. |
| `Calculus/MemoryLoopReplay.lean` | Typed symbolic aliases and kernel-checked one-layer equations for the unchanged 1024-step walk; untrusted native proposals, exact callback/result accounting, fail-closed checkpoints and empty-residue-only refusal boundary. |
| `TestSuite/MemoryLoopReplay/*.lean`, `TestSuite/Derived17MemoryLoop.lean` | Twenty shared replay stages for the original nested-return theorem; incomplete, missing-state, wrong-root and residual-leaf refusal controls. |
| `TestSuite/Derived17.lean` | Unannotated upstream loop derivations, including storage-dependent bounds, break/continue and nested returns; fixed-budget kernel-checked replay. |
| `TestSuite/Derived18.lean` | The imported native modular arithmetic obligation, proved with explicit Lean-only assignment rules. |
| `TestSuite/Derived19.lean` | Obligations new at solkey `473da8944c`: `&`'s operand order, a `continue` under an invariant, modifier continuations, the four dangling-storage claims (a length-only push) and shifts, by `sol_prove`. |
| `TestSuite/Derived20.lean` | Obligations whose leaves close each but not together in one declaration's heartbeats, and the quantified-prefix invariant: `sol_auto_theorem` (`Calculus/Closers.lean`). |
| `TestSuite/Derived21.lean` | The three `memoryIndexWrite*` obligations: memory read through a storage copy below its root, by `sol_prove`. |
| `TestSuite/Refuted.lean` | The obligations false in the model, `Solkey.TestSuite.f.refuted : ¬ (⊢ Solkey.TestSuite.f.problem)`, each by `sol_refute` (a certified counterexample, `Tools/Counterexample.lean`). |
| `Calculus/KeyValues.lean` | Recursive exclusion of native modular arithmetic from upstream-only programs, including path indices; weakening preserves the check. |
| `Examples/Tactics/ModularArithmetic.lean` | Kernel-checked modular arithmetic, intermediate overflow, dynamic zero, short circuiting, argument effects, function shadowing and fragment boundaries. |
| `Examples/Tactics/EvaluationOrder.lean` | Legacy and via-IR expression schedules: captures, inlined calls, modular arguments, failure priority, conditional evaluation and import configuration. |
| `Examples/Tactics/AuditRepairs.lean` | Strict Spec equations and proof bridges; constant arithmetic, unchecked parentheses, argument and receiver capture regressions. |
| `Examples/Tactics/RunnerAudit.lean` | Imported bare and specified external-call rows retain the callback reading and cannot prove storage preservation. |
| `TestSuite/Report.lean` | The pinned count: derived, pending (named), and rows without statements (excluded, skipped, unsupported and internal helpers). |
| `TestSuite/Suggestions.lean` | `#solkey_derive?` suggestions pinned by name, off the `Derived` modules' import path; `returnEarly` and `tupleReturnDiscardsComponents` pinned as derived since ground splits are pruned. |
| `Frontend/QualifiedUnits/Relation.lean` | Bounded qualified-units checkpoint; typed scope and retained premises are in the module. |
| `Frontend/OverrideValidation/Identity.lean` | Bounded override-validation checkpoint; typed scope and retained premises are in the module. |
| `Frontend/QualifiedUnits/Controls.lean` | Bounded qualified-units checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/QualifiedUnits/Lookup.lean` | Bounded qualified-units checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/SolcJson/CallMetadata.lean` | Bounded readonly-external checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/SolcJson/CallMetadataControls.lean` | Bounded readonly-external checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/SolcJson/CallMetadataData.lean` | Bounded readonly-external checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/OverrideValidation/Attributes.lean` | Bounded override-validation checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/OverrideValidation/Graph.lean` | Bounded override-validation checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/OverrideValidation/Routes.lean` | Bounded override-validation checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/PrimitivePackets/SignedSub/Controls.lean` | Bounded readonly-external checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/PrimitivePackets/SignedSub/Execution.lean` | Bounded readonly-external checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/OverrideValidation/OverrideFrontier.lean` | Bounded override-validation checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/OverrideValidation/Pruning.lean` | Bounded override-validation checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/QualifiedUnits/Checked.lean` | Bounded qualified-units checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/QualifiedUnits/CheckedControls.lean` | Bounded qualified-units checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/QualifiedUnits/Inheritance.lean` | Bounded qualified-units checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/QualifiedUnits/Specification.lean` | Bounded qualified-units checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/QualifiedUnits/UnitPaths.lean` | Bounded qualified-units checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/SolcJson/CallMetadataPath.lean` | Bounded readonly-external checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/SolcJson/CallMetadataPathControls.lean` | Bounded readonly-external checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/SolcJson/CallMetadataSound.lean` | Bounded readonly-external checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/QualifiedUnits/ReferenceControls.lean` | Bounded qualified-units checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/QualifiedUnits/References.lean` | Bounded qualified-units checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/OverrideValidation/Compatibility.lean` | Bounded override-validation checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/OverrideValidation/OverrideLists.lean` | Bounded override-validation checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/NumericLiteralProofs/WordTable/Part01.lean` | Bounded numeric-literals checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/NumericLiteralProofs/WordTable/Part02.lean` | Bounded numeric-literals checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/ConstantDepth/Complete.lean` | Bounded constant-depth checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/ConstantDepth/Lookup.lean` | Bounded constant-depth checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/C3Exactness/Admission.lean` | Bounded c3-exactness checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/C3Exactness/Linearization.lean` | Bounded c3-exactness checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/StatementGrammarH28/ElsePosition.lean` | Bounded statement-grammar checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/StatementGrammarH28/NearestElse.lean` | Bounded statement-grammar checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/TypeGrammarH28/Counterexamples.lean` | Bounded type-grammar checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/TypeGrammarH28/Layouts.lean` | Bounded type-grammar checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/ExecutableAst/Shared/Boundary.lean` | Bounded shared-translator checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/ExecutableAst/Shared/Translate.lean` | Bounded shared-translator checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/LiteralGrammarH28/Hex.lean` | Bounded hexadecimal-body grammar and encoding checkpoint; full literal parsing remains open. |
| `Frontend/LiteralGrammarH28/HexEncoding.lean` | Bounded hexadecimal-body grammar and encoding checkpoint; full literal parsing remains open. |
| `Frontend/NumericLiteralProofs/WordTable/Part03.lean` | Bounded numeric-literals checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/NumericLiteralProofs/WordTable/Part04.lean` | Bounded numeric-literals checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/QualifiedUnits/DifferentialControls.lean` | Bounded qualified-units checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/QualifiedUnits/SignatureGap.lean` | Bounded qualified-units checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/OverrideValidation/Selection.lean` | Bounded override-validation checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/OverrideValidation/Validity.lean` | Bounded override-validation checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/C3Exactness/GraphControls.lean` | Bounded c3-exactness checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/C3Exactness/Identity.lean` | Bounded c3-exactness checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/C3Exactness/OrderObstruction.lean` | Bounded c3-exactness checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/C3Exactness/Renaming.lean` | Bounded c3-exactness checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/ExecutableAst/Memory/Reader.lean` | Bounded memory-references checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/LiteralGrammarH28/Body.lean` | Bounded literal-grammar checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/LiteralGrammarH28/BodyControls.lean` | Bounded literal-grammar checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/ExecutableAst/ControlTuple/Adapter.lean` | Bounded control-tuples checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/ExecutableAst/ControlTuple/AdmissionControls.lean` | Bounded control-tuples checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/TypeGrammarH28/ParserBasics.lean` | Bounded type-grammar checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/TypeGrammarH28/ParserChecks.lean` | Bounded type-grammar checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/ExecutableAst/Shared/Intrinsic.lean` | Bounded shared-translator checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/ExpressionUniqueness/Statement.lean` | Bounded expression-uniqueness checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/OverrideValidation/Extraction.lean` | Bounded override-validation checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/OverrideValidation/Validator.lean` | Bounded override-validation checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/NumericLiteralProofs/WordTable/Part05.lean` | Bounded numeric-literals checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/NumericLiteralProofs/WordTable/Part06.lean` | Bounded numeric-literals checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/ExpressionUniqueness/Fixtures.lean` | Bounded expression-uniqueness checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/StatementGrammarH28/FixtureControls/Case00.lean` | Bounded statement-grammar checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/StatementGrammarH28/FixtureData.lean` | Bounded statement-grammar checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/StatementGrammarH28/G0List.lean` | Bounded statement-grammar checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/TypeGrammarH28/Composition.lean` | Bounded type-grammar checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/LiteralGrammarH28/BoundaryControls.lean` | Bounded literal-grammar checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/LiteralGrammarH28/Quoted.lean` | Bounded literal-grammar checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/LiteralGrammarH28/Scanner.lean` | Bounded literal-grammar checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/ExecutableAst/Shared/Scope.lean` | Bounded shared-translator checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/ExecutableAst/ControlTuple/IntrinsicControls.lean` | Bounded control-tuples checkpoint; typed scope and retained obligations are stated in the module. |
| `SolcValidation/Dialect.lean` | Bounded vt1-solc-validation checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/QualifiedUnits/NormalizationControls.lean` | Bounded qualified-units checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/QualifiedUnits/SignatureHiding.lean` | Bounded qualified-units checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/QualifiedUnits/SignatureNormalization.lean` | Bounded qualified-units checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/QualifiedUnits/TypePaths.lean` | Bounded qualified-units checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/C3Exactness/Audit.lean` | Bounded c3-exactness checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/C3Exactness/Controls.lean` | Bounded c3-exactness checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/OverrideValidation/Memoized.lean` | Materialized typed relation tables, proved equivalent to the original candidate. |
| `Frontend/NumericLiteralProofs/WordTable/Part07.lean` | Generated direct structural word-table proof. |
| `Frontend/NumericLiteralProofs/WordTable/Part08.lean` | Generated direct structural word-table proof. |
| `Frontend/ExpressionUniqueness/SeparatorSplit.lean` | Comma-separated token span reconstruction The result allows empty component words, as intrinsic tuple holes require. |
| `Frontend/ExpressionUniqueness/TokenSplit.lean` | Delimiter execution and token splitting for expression uniqueness The machine reads the existing checked tokens. |
| `Frontend/StatementGrammarH28/Balance.lean` | Balanced brace boundaries and intrinsic block witnesses BraceBalanced is a token predicate, not an AST. |
| `Frontend/StatementGrammarH28/YieldSplit.lean` | Exact block/list yield decomposition These lemmas expose the actual state-threaded yield of existing Syn lists and blocks, including the intermediate layout. |
| `Frontend/TypeGrammarH28/ParserArrays.lean` | Array spine parser composition. |
| `Frontend/TypeGrammarH28/ParserPaths.lean` | Independent qualified-name parsing contracts, with arbitrary locations. |
| `Frontend/LiteralGrammarH28/HexControls.lean` | Hex body kernel controls Rows are enumerated independently from the decoder recursion: empty; every pair digit category and case; adjacent and separated groups; odd counts;. |
| `Frontend/LiteralGrammarH28/HexPins.lean` | Exact hex theorem signatures and transitive axiom reports. |
| `SolcValidation/DataLayout.lean` | Checked object-data references into assembled artifact bytes This is the label-resolution/data-size boundary of the solc dialect adapter. |
| `SolcValidation/DataResolution.lean` | Unique object-data resolution A checked per-object table resolves a present label to its exact reference, not merely to some reference. |
| `Frontend/QualifiedUnits/SignatureMemberControls.lean` | Kernel controls for executed collection, not an assumed owner order or supplied collection result. |
| `Frontend/QualifiedUnits/SignatureMembers.lean` | Identity-based inherited overload collection. |
| `Frontend/ExecutableAst/Shared/Compose.lean` | One executable callback composition for producer-owned memory and control packets. |
| `Backend/PrimitivePackets/UnsignedCast/Boundaries.lean` | Bounded qualified-units checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/PrimitivePackets/UnsignedCast/Compiler.lean` | Bounded qualified-units checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/PrimitivePackets/UnsignedCast/Controls.lean` | Bounded qualified-units checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/PrimitivePackets/UnsignedCast/Semantics.lean` | Bounded qualified-units checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/PrimitivePackets/UnsignedCast/Transport.lean` | Bounded qualified-units checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/PrimitivePackets/Constants/Selected.lean` | Bounded numeric-literals checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/PrimitivePackets/Constants/Source.lean` | Bounded numeric-literals checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/PrimitivePackets/Constants/Agreement.lean` | Bounded numeric-literals checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/PrimitivePackets/Constants/Target.lean` | Bounded numeric-literals checkpoint; typed scope and retained obligations are stated in the module. |
| `Frontend/SolcJson/TryPanicCallMetadata.lean` | Typed H22 call metadata from the retained whole-source resolution. |
| `Frontend/ConstantDepth/Controls.lean` | SOL-CB controls, decided on the real `evalConst`/`nconstP`/`rank`/`acyclicB`: a chain whose rank is the declaration count and one just below it (one level fewer refuses), a shared diamond, contract scopes with inheritance and shadowing, duplicates, used and unused cycles, a qualified member reference and `uint8` overflow; clash-free acyclic units are tied to `TEval` through `evalConst_iff`/`evalConst_none_iff`. Ends with the lane's exact axiom pins. |
| `Frontend/ConstantDepth/Correspondence.lean` | SOL-CB backfill: a declared constant's graph edges are exactly the resolved constant paths of its initializer; rank decreases on each and along every path; typed evaluation, named constants and array lengths are functional under the clash-free acyclic contract. |
| `Frontend/ConstantDepth/Determinism.lean` | SOL-CB backfill: `TEval`, `NamedConst` and `ArrayLenOK` are deterministic in every environment (no clash-freedom or acyclicity premise), by mutual recursion on the derivations. |
| Module | Role |
| --- | --- |
| `Frontend/SpecOriginsV1.lean` | Additive source-pinned NatSpec directive origins, exact legacy clause-field agreement and forget lemmas; unsupported layouts have no origin. |
| `Frontend/CounterexampleMetadataV1.lean` | Opt-in exact-fixture importer companion and no-second-search retained-certificate ingress; canonical failed-clause attribution remains unimplemented. |
| `Frontend/Admission/DeclarationOccurrences.lean` | Canonical enumeration of every carried Source declaration and intrinsic syntax descendant, with exact membership and resolver-selected target coverage. Includes a generic intrinsic metadata-field collector with exact field/site witnesses, collector-to-unit subterm coverage, pragma-erasure and source-unit nonrecoverability laws. Root identity does not assert lexical scope; feature classification and operational admission remain separate. |
| `Frontend/Admission/ElementaryFeatures.lean` | Elementary catalog features from all explicit intrinsic `Elem` fields, including mapping-key and value-type metadata, composed with canonical declaration traversal. Exact occurrence and original-unit field witnesses; this subset does not certify full feature extraction or admission. |
| `Frontend/ExpressionUniqueness/Accepted.lean` | Accepted expression trees equal every certified tree of their actual tokens The original parseCat_sound certificate supplies the lexical tokens, complete layout witness and precedence. |
| `Frontend/ExpressionUniqueness/AddControls.lean` | Inhabited arbitrary prefix and additive-root controls The old raw-marker countercontrol is handled by the new unfinished-state scan. |
| `Frontend/ExpressionUniqueness/AddFreeAlgebra.lean` | Operand-sensitive additive algebra Expression freedom starts unfinished. |
| `Frontend/ExpressionUniqueness/AddRoot.lean` | Certified additive roots use operand-sensitive last markers This closes the raw-rank-ten marker gap without excluding prefix minus. |
| `Frontend/ExpressionUniqueness/AddScan.lean` | Operand-sensitive additive scans A top-level subtraction is selected only after a completed operand. |
| `Frontend/ExpressionUniqueness/AllRootLevels.lean` | Reconstruct every certified expression precedence level The final level-15/16 boundary follows from the primary spine and the actual primary prefix cut. |
| `Frontend/ExpressionUniqueness/ArgumentIdentity.lean` | Intrinsic argument identity induction steps Actual word-vector and name cuts are derived by the existing span theorems. |
| `Frontend/ExpressionUniqueness/ArgumentSpans.lean` | Positional and named argument constructors reconstruct their word vectors Actual execution supplies comma freedom, nonempty components and the first-token boundary separating positional lists from named braces. |
| `Frontend/ExpressionUniqueness/ArgumentWords.lean` | Actual argument vectors preserve nonempty words and comma boundaries Empty vectors are permitted; empty expression/named-argument component words are not. |
| `Frontend/ExpressionUniqueness/AttributeBalance.lean` | Function-type attribute layout preserves delimiter balance Only the existing token-layout combinators are analyzed. |
| `Frontend/ExpressionUniqueness/AttributeFieldIdentity.lean` | Actual attribute words determine existing function-type fields Arbitrary successful orders reduce to the exact field run. |
| `Frontend/ExpressionUniqueness/AttributeOrderIdentity.lean` | Successful two-field attribute orders are exhaustive Arbitrary layout lists are inverted, not bounded by an assumed length or canonical order. |
| `Frontend/ExpressionUniqueness/AttributeTokens.lean` | Actual function-type attribute tokens belong to their keyword run The original arbitrary layout order is retained. |
| `Frontend/ExpressionUniqueness/AxiomPins.lean` | Exact kernel-reported axiom pins for every source declaration in this lane. |
| `Frontend/ExpressionUniqueness/BinaryControls.lean` | Rank-ten raw-marker limitation is an inhabited arbitrary-family control This is a countercontrol to applying the raw-marker helper at prefix minus, not an ambiguity of certified expression trees. |
| `Frontend/ExpressionUniqueness/BinaryFreeAlgebra.lean` | Parameterized binary marker algebra Marker levels follow the existing Syn.level values. |
| `Frontend/ExpressionUniqueness/BinaryIdentity.lean` | Binary expression identity structural steps Actual certificates determine the root level, constructor and operator. |
| `Frontend/ExpressionUniqueness/BinaryRank.lean` | Certified binary marker classes distinguish lower roots from higher roots The existing root level is classified by exhaustive intrinsic constructors. |
| `Frontend/ExpressionUniqueness/BinaryRoot.lean` | Certified binary root markers follow their associativity Left-associative roots select the last marker of their exact rank; exponentiation selects the first. |
| `Frontend/ExpressionUniqueness/BinarySpans.lean` | Recover binary child words from actual certified printer executions Layouts may differ independently, and may have unconsumed suffixes. |
| `Frontend/ExpressionUniqueness/BoundaryIdentity.lean` | Unary and conditional expression identity steps Certified root levels and actual child-word cuts identify the original constructors/operators. |
| `Frontend/ExpressionUniqueness/Certified.lean` | Certified expression yield uniqueness over the original intrinsic syntax Exhaustive structural induction discharges every actual-child identity premise, including recursive expression/type/parameter/list/optional/argument cycles. |
| `Frontend/ExpressionUniqueness/CertifiedControls.lean` | Inhabited arbitrary-family controls for the complete theorem Arbitrary array depth, parameter counts, optional returns and both attribute orders inhabit a meta-type expression through an array wrapper. |
| `Frontend/ExpressionUniqueness/CommaFreeAlgebra.lean` | Comma-free token algebra for expression spans Every comma-free word below is balanced. |
| `Frontend/ExpressionUniqueness/ConditionalAlgebra.lean` | Conditional balance algebra for successful intrinsic yields Neutral punctuation preserves the question depth. |
| `Frontend/ExpressionUniqueness/ConditionalBalance.lean` | Top-level conditional punctuation balance A delimiter stack hides bracket interiors. |
| `Frontend/ExpressionUniqueness/ConditionalControls.lean` | Arbitrarily nested conditional middle controls Nested true branches contain earlier top-level colons. |
| `Frontend/ExpressionUniqueness/ConditionalSpans.lean` | Recover all three conditional child words from original certificates The first joint low marker reconstructs the condition boundary. |
| `Frontend/ExpressionUniqueness/ContainerControls.lean` | Arbitrary optional-hole vector identity and flattened collision control Full item vectors determine these intrinsic lists against any certified list. |
| `Frontend/ExpressionUniqueness/ContainerIdentity.lean` | Intrinsic list and optional-expression identity steps The only recursive premises are the structural induction predicates for actual children. |
| `Frontend/ExpressionUniqueness/DelimiterReconstruction.lean` | Reconstruct enclosing delimiter boundaries from certified expression tokens The closing delimiter scanner's skip facts are derived from successful balanced execution. |
| `Frontend/ExpressionUniqueness/ElementaryPathPrefix.lean` | Elementary type and path words have maximal prefix cuts The concrete type-atom boundary rejects payable and period continuations. |
| `Frontend/ExpressionUniqueness/ExpressionAddFree.lean` | Certified roots above addition are additively free from an unfinished state The entry bit is false for expressions. |
| `Frontend/ExpressionUniqueness/ExpressionBalance.lean` | Intrinsic expression yields are delimiter-balanced The proof follows the existing indexed syntax through expressions, types, parameters and argument syntax, including their lists and options. |
| `Frontend/ExpressionUniqueness/ExpressionBinaryFree.lean` | Certified higher roots avoid each lower binary marker family The invariant is uniform over binary ranks at least two other than ten. |
| `Frontend/ExpressionUniqueness/ExpressionCommaFree.lean` | Intrinsic expression certificates exclude top-level commas The existing expression/type/argument category closure supplies the separator invariant directly. |
| `Frontend/ExpressionUniqueness/ExpressionConditional.lean` | Existing expression yields pair top-level questions and colons All expression constructors and their type/parameter/call-argument closure are covered without precedence premises. |
| `Frontend/ExpressionUniqueness/ExpressionLowFree.lean` | Certified high-precedence expressions avoid loose-root markers Types and call argument syntax are loose-root-free at their outer level. |
| `Frontend/ExpressionUniqueness/ExpressionMode.lean` | Every successful intrinsic expression yield finishes an operand The completion bit starts arbitrarily. |
| `Frontend/ExpressionUniqueness/ExpressionStart.lean` | Actual expression-category yields never begin with an opening brace All 29 expression constructors and type/parameter/argument closure are covered. |
| `Frontend/ExpressionUniqueness/ExpressionUnaryFree.lean` | Original certified roots above unary operators exclude their outer markers All six prefix and both suffix tokens are absent at delimiter depth zero for roots of level at least15. |
| `Frontend/ExpressionUniqueness/FnTypePrefix.lean` | Function-type words have maximal parameter, attribute and returns cuts The helpers use concrete keyword-run and follower conditions, supplied by actual printer execution and surrounding syntax in the final certificate results. |
| `Frontend/ExpressionUniqueness/FunctionTypeIdentity.lean` | Actual function-type vectors and field identity Successful original printers supply parameter nonemptiness, comma freedom, attribute fields and optional returns boundaries. |
| `Frontend/ExpressionUniqueness/Grouping.lean` | Grouping yield inversion and arbitrary-depth certified controls Parentheses remain the existing one-component tuple. |
| `Frontend/ExpressionUniqueness/LastEnclosure.lean` | Trailing balanced enclosures reconstruct their prefix and payload Mirror the existing token word, use the established first enclosing cut, and mirror back. |
| `Frontend/ExpressionUniqueness/LayoutBoundary.lean` | Successful expression layouts extend and trim The existing printer only pops explicit layout choices. |
| `Frontend/ExpressionUniqueness/LiteralPrefix.lean` | Literal primary words reconstruct their maximal prefix Arbitrary string fragments form a maximal same-kind token run. |
| `Frontend/ExpressionUniqueness/LowControls.lean` | Inhabited loose-root controls with arbitrary conditional middle assignments Every assignment operator and arbitrary prefix depth occurs in the middle of a certified conditional. |
| `Frontend/ExpressionUniqueness/LowFreeAlgebra.lean` | Joint assignment and conditional marker algebra The first loose-root selector includes every assignment operator and question mark. |
| `Frontend/ExpressionUniqueness/LowRoot.lean` | Recover assignment and conditional root marker classes from certificates The first joint loose-root marker is derived from existing recursive precedence and printer certificates. |
| `Frontend/ExpressionUniqueness/MappingIdentity.lean` | Actual intrinsic mapping identity induction step The actual key-name/arrow and value-name fields derive their own maximal-prefix boundaries. |
| `Frontend/ExpressionUniqueness/MappingKeyIdentity.lean` | Existing intrinsic mapping key word reconstruction MapKey is the existing unindexed intrinsic sum. |
| `Frontend/ExpressionUniqueness/MemberSpans.lean` | Member and named-argument names and child words reconstruct The existing special member spelling for address is injective, including all arbitrary identifier strings. |
| `Frontend/ExpressionUniqueness/OperandMode.lean` | Delimiter-aware operand completion state The state contains only the existing delimiter stack and one completion bit. |
| `Frontend/ExpressionUniqueness/OperandModeAlgebra.lean` | Operand-mode algebra for literal fragments, types and attribute layouts Completion is forced by every atom and outer enclosure. |
| `Frontend/ExpressionUniqueness/ParameterIdentity.lean` | Actual parameter fields and recursive identity step The concrete parameter suffix supplies the type-prefix follower boundary internally. |
| `Frontend/ExpressionUniqueness/ParameterWords.lean` | Actual parameter words are nonempty at arbitrary list lengths An empty type word cannot finish an operand from an unfinished state. |
| `Frontend/ExpressionUniqueness/PostfixControls.lean` | Inhabited arbitrary-depth mixed postfix controls Each step includes index, slice, member, options and call. |
| `Frontend/ExpressionUniqueness/PostfixFollowers.lean` | Concrete followers of an existing primary expression The flag is the original primary node's isNew value. |
| `Frontend/ExpressionUniqueness/PostfixIdentity.lean` | Postfix expression identity structural steps Actual certified words identify all five root families and actual child spans. |
| `Frontend/ExpressionUniqueness/PostfixRootKind.lean` | The five postfix constructor families reconstruct from actual words Trailing punctuation separates calls, options, members and square postfixes. |
| `Frontend/ExpressionUniqueness/PostfixSpans.lean` | Actual bracketed postfix children have unique token spans Balanced trailing enclosures reconstruct the existing base and payload words. |
| `Frontend/ExpressionUniqueness/PostfixYieldSplit.lean` | Actual postfix and call-argument printer inversion Recover existing intrinsic children and their successful state executions. |
| `Frontend/ExpressionUniqueness/Primary.lean` | Reconstruction of deterministic primary token yields These results use existing intrinsic constructors and fully consumed layouts. |
| `Frontend/ExpressionUniqueness/PrimaryChildIdentity.lean` | Recursive primary expression identity steps Keyword/enclosure shapes and comma vectors come from actual original yields. |
| `Frontend/ExpressionUniqueness/PrimaryLeafIdentity.lean` | Primary expression leaf identity against every certified competitor Actual certified root levels and token heads derive the family internally. |
| `Frontend/ExpressionUniqueness/PrimaryPrefix.lean` | Reconstruct the complete primary token prefix The certificate supplies the follower through PrimarySpine. |
| `Frontend/ExpressionUniqueness/PrimaryPrefixParts.lean` | Primary word-prefix cuts from actual intrinsic executions Keyword and enclosure boundaries come from successful existing printers. |
| `Frontend/ExpressionUniqueness/PrimarySpine.lean` | Certified high expressions expose an existing primary and actual postfix word The primary is an existing Syn.expr node with level16, never a second AST. |
| `Frontend/ExpressionUniqueness/PrimaryStart.lean` | Actual primary first-token classes The existing unindexed constructor enumeration distinguishes primary families. |
| `Frontend/ExpressionUniqueness/PrimaryYieldSplit.lean` | Actual primary printer components and balanced enclosures Existing intrinsic child nodes and their layout executions are recovered from successful yields. |
| `Frontend/ExpressionUniqueness/RecursiveProperty.lean` | Structural induction predicates over existing intrinsic syntax Word comparison is appropriate for individual expressions/types/arguments. |
| `Frontend/ExpressionUniqueness/ReverseSplit.lean` | Reverse delimiter scanning and last-marker reconstruction Mirroring swaps delimiter directions and reverses token words, preserving the existing token alphabet. |
| `Frontend/ExpressionUniqueness/RootLevelControls.lean` | Arbitrary primary/postfix boundary controls These inhabited families use the original certificates. |
| `Frontend/ExpressionUniqueness/RootLevels.lean` | Original certified root levels agree through unary precedence This combines loose, binary and unary root reconstruction. |
| `Frontend/ExpressionUniqueness/SpanControls.lean` | Arbitrary-family controls for recovered operand spans The additive certificate may contain arbitrarily many unary-minus tokens in its right child. |
| `Frontend/ExpressionUniqueness/StartAlgebra.lean` | Balanced words which do not begin with an opening brace This is a first-token invariant only. |
| `Frontend/ExpressionUniqueness/TypeArrayIdentity.lean` | Reconstruct intrinsic array type roots and recursive identity Balanced dimension words and maximal actual atom prefixes separate arrays from all non-array types, even mapping/function atoms with arbitrary descendants. |
| `Frontend/ExpressionUniqueness/TypeAtomPrefix.lean` | Existing non-array type words reconstruct their maximal prefix Every root and payload property is derived from actual type executions. |
| `Frontend/ExpressionUniqueness/TypeAtomStart.lean` | Non-array type roots distinguish their first token classes The classifiers inspect existing intrinsic nodes and tokens only. |
| `Frontend/ExpressionUniqueness/TypeIdentityControls.lean` | Unconditional identity controls for arbitrary intrinsic type families Structural induction discharges every recursive premise for arbitrary array depths. |
| `Frontend/ExpressionUniqueness/TypeLeafIdentity.lean` | Actual type atom classification and intrinsic leaf identity Array disjointness and actual token heads reconstruct atom families internally. |
| `Frontend/ExpressionUniqueness/TypePrefix.lean` | Arbitrary intrinsic type words reconstruct their maximal prefix Actual execution derives the existing type atom and balanced array spine. |
| `Frontend/ExpressionUniqueness/TypePrefixAlgebra.lean` | Maximal token runs and array-bracket spines These are token boundary lemmas, not a second AST or a producer interface. |
| `Frontend/ExpressionUniqueness/TypePrefixControls.lean` | Type-prefix inhabited families and necessary-boundary countercontrols The raw new-array/direct-new-index token collision is rejected by the ORIGINAL certificate. |
| `Frontend/ExpressionUniqueness/TypeSpine.lean` | Actual type yields decompose into an existing atom and square payload words The atom is an existing intrinsic typeName node. |
| `Frontend/ExpressionUniqueness/TypeYieldSplit.lean` | Invert actual type printer executions All existing fields and layout choices are retained. |
| `Frontend/ExpressionUniqueness/UnaryControls.lean` | Inhabited arbitrary unary-chain controls Every prefix operator has arbitrary direct nesting. |
| `Frontend/ExpressionUniqueness/UnaryFreeAlgebra.lean` | Unary-marker freedom above unary expression roots The selector includes all six prefix tokens and both suffix tokens. |
| `Frontend/ExpressionUniqueness/UnaryRoot.lean` | Unary root reconstruction and actual child spans Prefix tokens select position zero. |
| `Frontend/ExpressionUniqueness/YieldBalance.lean` | Balance algebra for the intrinsic expression printer These token and success-predicate lemmas support the recursive expression/type/ argument category closure. |
| `Frontend/ExpressionUniqueness/YieldShape.lean` | Structural facts about successful intrinsic expression yields A small success-predicate calculus for the existing state printer proves facts about arbitrary inputs and arbitrary remaining layouts. |
| `Frontend/ExpressionUniqueness/YieldSplit.lean` | Invert actual printer executions into successful child executions These are state-printer inversion facts. |
| `Frontend/LiteralGrammarH28/BodyPins.lean` | String-body theorem signatures and axiom reports. |
| `Frontend/LiteralGrammarH28/BoundaryPins.lean` | Quote/scanner theorem signatures and axiom reports. |
| `Frontend/LiteralGrammarH28/Classification.lean` | Hex/unicode literal relations and exact classification/refusal boundaries; keeps the raw unicode line/bidi guards. |
| `Frontend/LiteralGrammarH28/EncodingValue.lean` | `CodepointBytes`: independent `\u` escape byte arithmetic (surrogates included); hex pair/quad value bounds. |
| `Frontend/LiteralGrammarH28/FragmentCompleteness.lean` | Classification inversions extended to arbitrary fragment lists of every kind. |
| `Frontend/LiteralGrammarH28/Fragments.lean` | `Fragments`/`FragmentValue`: fragment sequences, byte concatenation and per-fragment splitting. |
| `Frontend/LiteralGrammarH28/FullControls.lean` | Kernel controls for every nonnumeric classification arm and fragment sequence, independent of compiler outcomes. |
| `Frontend/LiteralGrammarH28/FullPins.lean` | All public lane theorem signatures and axiom reports (the audit's pin source). |
| `Frontend/LiteralGrammarH28/Global.lean` | Literal classification inversion over unrestricted raw input. |
| `Frontend/LiteralGrammarH28/Lengths.lean` | Scanner split uniqueness and strictly shorter suffix; byte-length bounds for plain, hex and unicode literals and fragment sequences. |
| `Frontend/LiteralGrammarH28/ModeGrammar.lean` | All-mode (sol/yul/asm/pragma) literal and fragment grammar relation. |
| `Frontend/LiteralGrammarH28/ProofSafety.lean` | Safety report for the word-table proof tactic's generated declarations. |
| `Frontend/LiteralGrammarH28/Roundtrips.lean` | Constructive encode/classify round trips in every literal-bearing mode. |
| `Frontend/LiteralGrammarH28/Split.lean` | Exact literal splitting in each admitted lexer mode, any suffix kept. |
| `Frontend/LiteralGrammarH28/TaggedEncoding.lean` | Constructive hex/unicode literal encodings passing the line/bidi guards. |
| `Frontend/LiteralGrammarH28/Utf8Shape.lean` | `\u` escape byte shape (lead/continuation, non-overlong) and code-point recovery; no scalar check. |
| `Frontend/LiteralGrammarH28/WordTable.lean` | Exhaustive word-table return classes, proved by a checked proof-producing tactic. |

### SOL-QN final target, C3 and normalization adequacy

| Module | Purpose |
|---|---|
| `Frontend/QualifiedUnits/Linearization.lean` | Independent C3 hierarchy judgment on original declaration identities; `order_iff` (the `idUniverse` bound never refuses a hierarchy), precedence and acyclicity. |
| `Frontend/QualifiedUnits/Target.lean` | The final SOL-QN target relation, including inherited overloads; `target_iff` against the public signature-aware resolver. |
| `Frontend/QualifiedUnits/NormalizationAdequacy.lean` | Structural adequacy of signature normalization against Source elaboration on every supported signature category. |
| `Frontend/QualifiedUnits/TargetControls.lean` | Kernel controls for the independent C3 judgment, the final target relation and normalization adequacy. |
| `Frontend/QualifiedUnits/ConstructorFixtures.lean` | One typed specimen and literal expected traversal per existing Source constructor (all 112). |
| `Frontend/QualifiedUnits/Layout.lean` | Original owner-body layout: universal frozen source-layout theorem and actual owner-body member correspondence. |
| `Frontend/QualifiedUnits/MergeSpecification.lean` | Independent deterministic C3 merge judgment on original declaration identities; `merge_iff` against `mergeOwners`. |
| `Frontend/QualifiedUnits/ReferenceCoverage.lean` | Universal preservation of frozen explicit references and all finite identifier/member paths. |
| `Frontend/QualifiedUnits/SignatureResolution.lean` | Signature-aware declaration resolution over original Source identities (the public consumer `resolve`). |
| `Frontend/QualifiedUnits/SignatureResolutionControls.lean` | Kernel observations for the actual signature-aware resolver, paired with each main compiler query. |
| `Frontend/StatementGrammarH28/G0Nodes.lean` | Gate G0 twin of `Syn.nodes` constructors (`g0NodeCtors`, `Syn.casesOn` with structural recursion) read by the fixture observers, linked by `g0NodeCtors_eq_nodes`. |
| `Frontend/StatementGrammarH28/AtomConditional.lean` | Statement-grammar `if`/`while`/`do`/empty-`for` coverage with arbitrary expression conditions under the exposed atom premise `ExprAtomRparen`; nearest else and token uniqueness inside the fragment. |
| `Frontend/StatementGrammarH28/AtomNested.lean` | Mutual `AtomStmt`/`AtomItems`/`AtomCatch`/`AtomCatches` fragment: arbitrarily nested blocks, control leaves, `return e;`, `unchecked` items, atom-condition `if`/`while`/`do`/`for`, `for` initialisers, simple statements, `emit`/`revert`, contextual `revert` expression statements, `try`/`catch` and `assembly` (stated sub-parser premises); coverage by mutual structural recursion with syntax-derived budgets under the else and catch frames, nearest else, token and prefix uniqueness. |
| `Frontend/StatementGrammarH28/G0Rejections.lean` | Gate G0 twins of the profile observation: `Syn.nodes` with exclusions, `Syn.placeholders`, `isLiteralBase` and `Syn.rejections` (`g0Rejections`), each linked to Source (`g0Rejections_eq`), and `g0IsRethrow`, the twin of `isRethrow` linked by `g0IsRethrow_eq`. |
| `Frontend/StatementGrammarH28/AtomSimple.lean` | Simple statements through the stated `simple`-parser premise `SimpleAtom`: the parser-equation dispatch lemma for `simpleHead` tokens without generated match names, `simpleStmt` coverage, block-loop step and the `for`-header prefix with an initialiser. |
| `Frontend/StatementGrammarH28/AtomCall.lean` | `emit`/`revert` statement steps under the stated path and argument premises `PathAtom`, `ArgsAtom`. |
| `Frontend/StatementGrammarH28/AtomYield.lean` | Printer premise `AtomYield`, the yield relation `AtomYields` for the atom-condition fragment, `Derives` characterisation and yield uniqueness (`atom_statements_yield_unique`). |
| `Frontend/StatementGrammarH28/AtomTry.lean` | `try`/catch premises `ExprAtomBrace`, `ExprAtomReturns`, `RetsAtom`, `ParamsAtom`; the catch-open spine `catchOpen` and `CatchFrame`; the actual `try` and catch-signature step equations. |
| `Frontend/StatementGrammarH28/AtomAsm.lean` | `assembly` premises `YulBodyAtom` (on `yulBody`) and `FlagsAtom` (on the flag list); the actual `assembly` step `asm_step`; the canonical rethrow body `rethrow_yul_body` by composed parser steps. |
| `Frontend/StatementGrammarH28/AtomDerives.lean` | Printer premises `Prints`/`PrintsTo`, the print relations `AtomStmtP`/`AtomItemsP`/`AtomCatchP`/`AtomCatchesP`, layout-free yields, `Derives` characterisation and yield uniqueness for the mutual fragment. |
| `SolcValidation/IrSyntax.lean`, `SolcValidation/IrParse.lean` | Intrinsic object-dialect Yul syntax of solc `--ir` text and its certifying parser: a result carries proof that printing it reproduces the lexed tokens ([VT1](../feature-work/fullscope-vt1.md)). |
| `SolcValidation/IrCensus.lean` | Function definitions and operation uses per object, read off the parsed tree. |
| `SolcValidation/IrEval.lean`, `SolcValidation/IrEvalFuel.lean` | Fuelled interpreter of the parsed IR over a consumer-supplied EVM `Machine`: object operations through the checked data table, immutables and links; adapter laws and fuel stability. |
| `SolcValidation/IrHelpers.lean`, `SolcValidation/IrHelperSim.lean`, `SolcValidation/IrHelperSource.lean` | Real solc checked-arithmetic helpers as certified terms; their simulation on any machine and match to the source operators `BinOp.evalNum` (T02 helper level). |
| `SolcValidation/IrHelperSteps.lean` | Statement-level steps of the helpers (cleanup and panic calls, pure operations, `if` with a panic) composed by `rw`; kernel proofs of `checked_sub_t_uint256`/`checked_div_t_int256` and call-site forms. |
| `SolcValidation/IrExpHelpers.lean`, `SolcValidation/IrExpModel.lean`, `SolcValidation/IrExpSim.lean` | solc's `checked_exp_t_uint256_t_uint256` group as a certified term, its arithmetic model (exact below `2^256`, panic otherwise) and its simulation on any machine. |
| `SolcValidation/IrAbiHelpers.lean`, `SolcValidation/IrAbiSim.lean`, `SolcValidation/IrPushHelpers.lean`, `SolcValidation/IrPushSim.lean` | solc's `uint256` calldata decoder and storage-array push as certified terms, and their exact machine-effect sequences on any machine. |
| `SolcValidation/IrRename.lean` | Renaming of call positions between function environments and its simulation: renamed IR code evaluates in the target environment exactly as the original (`evalExpr_ren`, `evalBlock_ren`, `Sim.flat`). |
| `SolcValidation/IrCensusCreation.lean`, `SolcValidation/IrCensusDeployed.lean`, `SolcValidation/IrLinkedCode.lean`, `SolcValidation/IrCensusTree.lean` | The parsed `Census` and `LinkedMath` `--ir` trees as generated terms, certified against the quoted fixture texts by kernel evaluation (`census_certified`, `linked_certified`). |
| `SolcValidation/IrCensusMaps.lean`, `SolcValidation/IrCensusTransfer.lean` | Each extracted helper group located in the parsed objects' groups; the lookup lemmas, environment simulations and the helper theorems restated for the parsed programs. |
| `SolcValidation/IrCensusUnique.lean` | One definition per function name in every scope of the parsed Census/LinkedMath trees; name lookup lands on the transferred helpers; duplicate-definition negative controls. |
| `SolcValidation/IrExpEvm.lean` | `checked_exp`'s model and imported IR body against this compiler's checked `**` code (`Evm/Exp.lean`'s `exp_tail`) and the EVM `EXP` value. |
| `SolcValidation/IrErase.lean`, `SolcValidation/IrCensusParse.lean` | An injective, decidable erasure of the intrinsic IR tree; the parser's own result for the LinkedMath fixture pinned by kernel evaluation. |
