# Module map

One line per module: what it defines. The module's own `/-!` docstring has
the detail; this file only says where to look.

**Start at `Theorems.lean`**: the main theorems on one page, in notation
(`⊢ φ → ⊨ φ`, `(P, σ) ⇓ σ'`, `⟦P⟧`), each proved by the original's name.

```
Solidity/  KeySort  AST  Syntax  Semantics  Update  SpecSyntax  Theorems
           Semantics/         the interpreter's satellites
           Calculus/          the taclets and everything proved about them
           Theory/            solkey's data-structure theories as free-term algebras
           Typing/            value typing, reachability
           SortCheck/         solkey's sort annotations, checked
           Counterexamples/   refutations that pin a design decision
           Evm/               the compiler and its simulation proof
           Tools/             the `#run`, `#wp`, `#verify`, … commands
           Corpus/            solkey's example suites (own target)
           Examples/          the worked examples, in the default build
```

Layering: types and names (`AST`), the typed syntax (`Syntax`), the
interpreter (`Semantics`), terms and formulas (`Update`), the taclets
(`Calculus/Rules`), then what is proved about them. Imports are acyclic; a new
module goes in `Solidity.lean` (`scripts/check-orphans.mjs` fails on a module
nothing imports).

**Formulas read storage through the Theory.** Programs and updates run in the
interpreter, but `a ≐ b` (`Fml.eq`) compares `Tm.denote`s over `State.abs`,
the state as a Theory term, and is total as KeY's `=` is. A program comparison
`a == b` is `Fml.eqD`, `defined(a) ∧ defined(b) ∧ a ≐ b`. `Theory/Bridge/`
proves once that the interpreter's reads and writes are the Theory's on `abs`
(up to `StValue.Equiv`). A derivation rewrites terms by named term taclets
(`Calculus/TermTaclets.lean`, `Proves.rewrite`), each sound by its Theory
lemma (`TermTaclet.sound`).

## The language

| Module | What it defines |
|---|---|
| `KeySort.lean` | solkey's sort lattice as one type. Imports nothing. |
| `AST.lean` | Types (`PrimTy`/`Ty`/`RefTy`, `RefTy.fixed`), the struct table, operators, `Var`. |
| `Syntax.lean` | The typed syntax (`Val C p`, `SPath`, `Loc`, `MPath`, `Stmt C`), `Contract`/`FunDecl`, and the elaborator behind `sol[C]{…}` and `contract!{…}`. |
| `FreshNames.lean` | `FreshNames.ofTable`: the examples' names for the rules' fresh variables, one table per example; `FreshNames.clashes`. |
| `SpecSyntax.lean` | The specification language (`SolSpec.g4`: `SpecExpr`, `spec!(…)`) and a function's clauses (`FunSpec`). |
| `Semantics.lean` | The interpreter `Stmt.run`, following solc where KeY is more liberal (`docs/solc-alignment.md`). |
| `Semantics/Properties.lean` | Read-after-write, frame and result-monad lemmas about the state operations, shared by every later layer. |
| `Semantics/Agree.lean` | `EnvAgreeExcept`: states agreeing off scratch names, and a frame lemma per evaluator. |
| `Semantics/DecEq.lean` | `DecidableEq SVal`. |
| `Semantics/Callback.lean` | The callback reading of `transfer` and `try`: `ExecS`/`ExecP`, `holdsC`, `TransferSem`. |
| `TermSimp.lean` | The simp sets `tm_eval` and `tm_denote` of the generic term functions. |
| `Update.lean` | Terms as one signature (`Srt`, `Op0`…`Op3`, `Tm`; `Term`, `STerm`, … are its sorts, the old constructors abbreviations), their reading (`Tm.eval`, `Tm.denote`) and frame lemmas, parallel updates, formulas with both modalities (`Fml`, `holds`, `Valid`), lowering of program expressions to terms. |
| `Theorems.lean` | The headline theorems in notation. |

## The calculus

| Module | What it defines |
|---|---|
| `Calculus/RuleSyntax.lean` | The `dl{ … }` notation: schemas and the printers for taclets, premises, goals. |
| `Calculus/Rules.lean` | `Taclet` (solkey's rules), `LeanTaclet` (rules solkey lacks), `Rule`, `CallbackTaclet`. |
| `Calculus/KeyTaclets.lean` | The 313 taclets of `solidityProgramRules.key` as one type, with `KeyOrigin`. |
| `Calculus/RuleShapes.lean` | Which solkey taclets each constructor transcribes, checked (`taclets_partitioned`). |
| `Calculus/PrintedRules.lean` | The printed rules and the constructor for each. |
| `Calculus/Completeness.lean` | `Stmt.step`, the rule for every statement, and `Stmt.complete`. |
| `Calculus/Uniqueness.lean` | One rule per statement: every derivation's premise is `Stmt.step`'s. |
| `Calculus/Progress.lean` | A formula with a modality always steps. |
| `Calculus/Termination.lean` | Weights, `Fml.measure`, `symex_normalizes`. |
| `Calculus/SoundKit.lean` | `SameOk`, `Premise.Correct` and the tactics the soundness proofs use. |
| `Calculus/SoundUpdate.lean` | Every taclet with an update premise has the statement's effect. |
| `Calculus/SoundUnfold.lean` | Every unfolding taclet runs like its statement off the fresh names. |
| `Calculus/RuleSoundness.lean` | `Taclet.sound`, `LeanTaclet.sound`, `Rule.sound`. |
| `Calculus/Logic.lean` | The sequent calculus `Proves` (`⊢` all rules, `⊢ₖ` solkey's) and `Proves.sound`; the update, rewrite and close rules. |
| `Calculus/Callback.lean` | `CallbackTaclet.sound`, `ProvesC` and `ProvesC.sound`. |
| `Calculus/SolkeyFragment.lean` | `Stmt.inSolkey`, where solkey's rules alone are the calculus; and where they fall short. |
| `Calculus/Symex.lean` | `Fml.step`, `symex`, `symex_sound`; `sol_step`, `sol_symex`, `sol_derive`. |
| `Calculus/Close.lean` | `sol_close`: first-order goals by weakest preconditions. Its docstring lists what it does not close. |
| `Calculus/CloseTests.lean` | What `sol_close` closes, pinned. |
| `Calculus/ReadWrite.lean` | Reads after writes: the four-way path comparison; the simp sets `close_rw`, `decide_eval`. |
| `Calculus/Decide.lean` | `sol_decide`: reads of writes as case trees on key equalities, over the live storage. |
| `Calculus/DecideComplete.lean` | The starting storage's reads are realizable; `Fml.valid_iff_cons`. |
| `Calculus/Spec.lean` | Specifications compiled to dynamic logic as solkey's `SpecCompiler` does; `spec[C]{f}`, `sol_spec`. |
| `Calculus/Notation.lean` | `dl[C]{ … }` and `dl!{ … }`: concrete formulas read against a contract; `dl![m]{ … }`, `⟨[ ]⟩` at a modality `m`; a Lean formula where a formula stands; `Γ ⟹ φ` lines. |
| `Calculus/Quote.lean` | Quoters from formulas back to terms, so the kernel re-checks a computed goal. |
| `Calculus/Chains.lean` | Derivations as values: `~>`, `~*>`, `calc` chains, `sol_chain`, `#derivation`; lines at a modality `m` over a postcondition `φ : Post C`; rewrite links (`~[sequentialToParallel]~>`, `~[findOnSave]~>`). |
| `Calculus/Sequents.lean` | `sequent!{ Γ ⟹ φ }`: the goals of a `⊢` walk (`Proves`) read back, for checked `show` lines; a chain under a context (`Fml.Steps.valid_in`). |
| `Calculus/ProofTree.lean` | solkey's proof tree of a goal `Γ ⊢ φ` (`ProofTree.build`, `Tree.rows`, `Tree.toJson`); `sol_derive?`, the walk it is, and `sol_chain?`, a derivation as its `calc`. |
| `Calculus/UpdateRules.lean` | KeY's update simplification as `UpdRule`s, and the semantics of the update constructors. |
| `Calculus/ChainRewrites.lean` | The lines after a chain's program as rewrites of the line with their soundness (`LineRw`): update merges, update rules, Theory laws. |
| `Calculus/TermRules.lean` | Theory equations as rewrite rules: `Term.Theq`, `Fml.rwEq` and its soundness. |
| `Calculus/TermTaclets.lean` | `TermTaclet`: the Theory's read-back rules on terms, their side conditions, and `TermTaclet.sound`. |
| `Calculus/TheoryRewrite.lean` | A Theory lemma as a rewrite rule (`theoryRewrite`, `sol_rw`). |
| `Calculus/Rewrite.lean` | The steps after the program: `rw [h]`, `eqDSplit`, `andSplit`, `sol_apply_upd`, `sol_upd`, `sol_merge`. |

## The data-structure theories

solkey's `find`/`save`/`read`/`write` are uninterpreted symbols whose meaning is
a taclet set. These modules are that theory as terms, each taclet a theorem.
The map from taclet to theorem is `docs/lean-key-rule-map.md`.

| Module | What it defines |
|---|---|
| `Theory/Terms.lean` | The mutual sorts `Struct`/`StValue`/`Memory`, the readers, `StValue.Equiv`. |
| `Theory/Storage.lean` | `structRules.key`'s taclets: `save`, `storeAt`, the delete family, `diverges`. |
| `Theory/Copy.lean` | The copying write `copyTo` and the array writes (`pushT`, `popT`, …). |
| `Theory/Memory.lean` | `memoryRules.key`'s taclets and `new`. |
| `Theory/CrossDomain.lean` | `structMemoryRules.key`'s four taclets. |
| `Theory/Observe.lean` | Congruence for `StValue.Equiv`: every operation respects it. |
| `Theory/Abs.lean` | The interpreter's storage as a Theory term (`SVal.abs`, `State.abs`). |
| `Theory/Bridge/Find.lean`, `Save.lean` | The interpreter's read and save against `findSt` and `save` on `abs`. |
| `Theory/Bridge/Delete.lean` | `defaultOf` and `delete` against `delValue` and `delAt`. |
| `Theory/Bridge/Copy.lean`, `CopyArray.lean` | `overlay`, `strip` and assignment against `copyVal`, `stripVal`, `copyTo`. |
| `Theory/Bridge/Push.lean` | `push`/`pop` against `pushT`/`shrinkT`/`popT`. |
| `Theory/Bridge/Denote.lean` | `Term.denote_eval`, `holds_eqD_iff`. The one Theory module that imports `Update`. |
| `Theory/Rewrite.lean` | `TheoryRule`: a constructor per printed rewrite rule, and the lemma behind each. |

## Typing and sort faithfulness

| Module | What it defines |
|---|---|
| `Typing/Storage.lean` | `Layout`, `SVal.hasTy`, read typing, write inversions, runtime sorts. |
| `Typing/StoragePreservation.lean` | `save` keeps a value's type. |
| `Typing/State.lean` | `StateWT`, the full-state invariant. |
| `Typing/Soundness.lean` | Type soundness: `Stmt.run_wt`, `Prog.run_wt`. |
| `Typing/Reachability.lean` | Every reachable storage is canonical. |
| `Typing/Constructibility.lean` | The converse: reachable ⇔ canonical ∧ tight. |
| `SortCheck/Annotations.lean` | The taclets' read-sort annotations, transcribed from the `.key` file. |
| `SortCheck/Parser.lean` | Token-level `.key` scanner and the `conforms` cross-check. |
| `SortCheck/Faithfulness.lean` | Each annotation holds of what a well-typed run reads. |
| `SolkeyCheck.lean` (root) | `lake exe solkeycheck`. |
| `Counterexamples/*.lean` | Four refutations pinning a design decision: `DeleteFamilyGenericOverlap`, `StaticRuntimeSort`, `PreFixSortAnnotations`, `WellTypedNecessity`. |

## The EVM compiler

`docs/compiler-verification.md` has the theorem, the fragment and what is out.

| Module | What it defines |
|---|---|
| `Evm/Machine.lean` | A straight-line EVM: slots as terms, wrapping words, relative forward jumps. |
| `Evm/Compile.lean` | The compiler for the fragment `wtStmt`, with solc's guards. |
| `Evm/Repr.lean` | The storage layout and the representation relation. |
| `Evm/Signed.lean` | The signed guard sequences, exact on two's complement. |
| `Evm/Exp.lean` | `**`: solc's `checked_exp_unsigned`, unrolled. |
| `Evm/Correctness.lean` | `compile_correct`, `compile_storage`, `not_stuck`. |
| `Evm/Examples.lean` | Compiled programs run by `decide`. |

## Tools

Commands for people; they prove nothing beyond the certificates they check.
`Examples/Tools.lean` and `Examples/Verify.lean` pin their output.

| Module | What it defines |
|---|---|
| `Tools/Show.lean` | Printers for storage values, states, transactions, clauses. |
| `Tools/Common.lean` | Shared plumbing: resolving `C` / `C.f`, evaluating terms, report layout. |
| `Tools/Run.lean` | `#run C.f(args) [from σ] [with msg.sender := n, …]`: the interpreter from a fresh state. |
| `Tools/Inspect.lean` | `#wp φ`, `#step φ`, `#taclet r`. |
| `Tools/DiffTest.lean` | `#difftest C[.f]`: interpreter against compiled EVM code on random storages. |
| `Tools/Counterexample.lean` | `Fml.eval3`, witness search and shrinking, `#counterexample`. |
| `Tools/Verify.lean` | `#verify C[.f]`: each spec'd function proved, refuted or stuck. |
| `Tools/ProofTree.lean` | `#proof_tree φ`, `#proof_node n φ`, `#proof_tree_json φ`: solkey's view of the tree of `⊢ φ`. |

## The solkey corpus

`SolidityCorpus` (`lake build SolidityCorpus`): each function of solkey's `.sol`
suites, generated by `scripts/solkey-port.mjs` into `Solidity/Corpus/`, stated
at the contract's initial store and decided by the kernel.
`./scripts/check-corpus.sh` checks the verdicts against
`tests/solkey/expected.tsv`; `docs/corpus-parity.md` is the scoreboard.

## Examples

Two directories, by proof style (`.claude/rules/derivations.md`).

`Examples/Chains/` — the calculus's worked examples, one file per section in
its order, each example a chain in its printed lines and fresh names:

| Module | Its examples |
|---|---|
| `Examples/Chains/Storage.lean` | Storage writes and reads, roots, rebinding, index, `push`/`pop`, nonsimple paths, side effects in receiver and index. |
| `Examples/Chains/StorageArrays.lean`, `StorageDelete.lean` | The further storage array cases; storage `delete`. |
| `Examples/Chains/StorageCoverage.lean` | One step per storage rule. |
| `Examples/Chains/Arithmetic.lean` | The compound storage update. |
| `Examples/Chains/Memory.lean`, `MemoryDelete.lean`, `MemoryArrays.lean` | Memory aliasing, writes and reads; memory `delete`; memory arrays. |
| `Examples/Chains/MemoryCoverage.lean` | One step per memory rule. |
| `Examples/Chains/StorageToMemory.lean`, `MemoryToStorage.lean` | The copies between the two, with lazy reads. |
| `Examples/Chains/Payment.lean` | `transfer`: funded, nonsimple amount, storage receiver, unfunded. |
| `Examples/Chains/CheckedArithmetic.lean`, `EvaluationOrder.lean` | Overflow reverts; the evaluation order of an indexed write. |

`Examples/Tactics/` — theorems `⊨ dl!{ … }` proved by `sol_symex; sol_close`
or `sol_decide`, derivations `⊢ φ` built one `apply` per taclet, and runs:

| Module | What it shows |
|---|---|
| `Examples/Tactics/Tour.lean` | The running example end to end. |
| `Examples/Tactics/StorageSteps.lean` | One storage statement form at a time, as `apply` walks. |
| `Examples/Tactics/StorageSuite.lean`, `StorageDelete.lean`, `LedgerDelete.lean` | solkey's taclet suite on storage; `delete`; a struct holding a mapping deleted. |
| `Examples/Tactics/Branch.lean`, `Revert.lean` | Two-goal splits; box and diamond on `revert`, `require`, `assert`. |
| `Examples/Tactics/Payment.lean`, `Net.lean` | `transfer` as `⊢` walks with checked sequents; its frame and the ledger's runs. |
| `Examples/Tactics/Values.lean`, `Operators.lean`, `Checked.lean` | Operators, checked arithmetic, `−−`, bitwise, shifts, `unchecked`, `uint8` … `int248`, casts. |
| `Examples/Tactics/Calls.lean`, `CallOperands.lean`, `Callback.lean`, `TryCatch.lean` | Internal calls, call-valued operands, callbacks (`ProvesC`), `try`/`catch`. |
| `Examples/Tactics/Memory.lean`, `CrossDomain.lean`, `Theory.lean` | Memory, storage↔memory copies, the theory's rewriting. |
| `Examples/Tactics/SelectOnSaveConsr.lean` | Reading a write back through a `consr` path, by hand and in solkey's order. |
| `Examples/Tactics/ApplySteps.lean`, `UpdateRules.lean`, `Decide.lean`, `TermTaclets.lean` | The proof style, update simplification, `sol_decide`, term taclets. |
| `Examples/Tactics/Specs.lean` | Clauses as obligations (`spec!{f}`, `sol_spec`) beyond the benchmarks. |

At the root, the notation's own tests:

| Module | What it shows |
|---|---|
| `Examples/ChainNotation.lean`, `ChainRewrites.lean`, `ExampleNames.lean` | How a chain is written and checked, its rewrite links, the printed names of fresh variables. |
| `Examples/Notation.lean` | What taclets, premises and sequents print, pinned. |
| `Examples/Verify.lean`, `Tools.lean` | `#verify`, `#counterexample` and the other commands, pinned. |
| `Examples/ProofTree.lean` | The proof tree's commands, `sol_derive?` and `sol_chain?`, pinned. |
| `Examples/Benchmark/*.lean` | solkey's benchmark contracts with their `@custom:key` clauses proved (`Counter`, `SimpleStorage`, `Mapping`, `Purchase`, `Coin`, `EtherWallet`, `ERC20`), and `Syntax`, which pins what elaborates away (units, casts, events, errors, enums, struct constructors, modifiers). |
