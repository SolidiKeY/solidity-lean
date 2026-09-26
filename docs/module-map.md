# Module map

One line per module: what it defines and why it exists. Open the module's
own `/-!` docstring for the detail; this file is the index, not a summary of
them.

```
Solidity/  KeySort.lean  AST.lean  Syntax.lean  Semantics.lean  Update.lean
           Semantics/   the interpreter's satellites: properties, the frame kit
           Calculus/    the taclets and everything proved about them
           Theory/      the data-structure theories as free-term algebras
           Typing/      value typing: storage layouts, state invariants
           SortCheck/   the annotation table and the `.key` scanner
           Counterexamples/  refutations that pin a design decision
           Examples/    the worked examples, in the default build
```

The layering: types and names (`AST.lean`), the typed syntax
(`Syntax.lean`), the interpreter (`Semantics.lean`), terms and formulas
(`Update.lean`), the taclets (`Calculus/Rules.lean`), then what is proved
about them. New modules go in `Solidity.lean`; `scripts/check-orphans.mjs`
fails on a module nothing imports.

## The language

| Module | What it is |
|---|---|
| `KeySort.lean` | solkey's sort lattice as one Lean type: `parents`, `ancestors`, `KeySort.le`, KeY spellings. Imports nothing. |
| `AST.lean` | The static vocabulary: `PrimTy`/`Ty`/`RefTy` and their KeY sorts, the struct table `structDef`, operators typed at the primitive type they accept, and `Var` (a program name, or a fresh one a rule declares). |
| `Syntax.lean` | The typed syntax, indexed by contract and type: `Val C p`, `SPath C T`, `Loc`, `MPath`, `Stmt C`. A statement no rule can run cannot be written. `Contract`, the named example contracts, and `sol[C]{…}`: the elaborator, run at compile time and re-checked by the kernel. |
| `Semantics.lean` | The interpreter, `Stmt.run`, by structural recursion on the typed syntax. KeY's state (storage tree, identity heap, locals, `net`), following solc where KeY was more liberal (`docs/solc-alignment.md`). |
| `Semantics/Properties.lean` | Association-list, read-after-write, frame and allocation lemmas about the interpreter's state operations. |
| `Semantics/Agree.lean` | `EnvAgreeExcept ns`: states that agree off a few scratch names, and a frame lemma per evaluator. What every unfolding rule's soundness composes. |
| `Semantics/DecEq.lean` | The hand-written `DecidableEq SVal`. |
| `Update.lean` | Terms (`Term`, `PTerm`, `STerm`, `ITerm`, `MTerm`, …) read by the interpreter's own functions, parallel updates, formulas with both modalities (`Fml`, `holds`, `Valid`), and lowering program expressions to terms. |

## The calculus

| Module | What it is |
|---|---|
| `Calculus/RuleSyntax.lean` | The notation `dl{ … }`: schemas whose names carry their kind, and the delaborators that print taclets, premises and goals back in it. |
| `Calculus/Rules.lean` | The taclets: `Taclet C k m s p`, one constructor per rule, named as solkey names it, written in `dl{ ⟨[ s; ]⟩ ⇝ p }`. |
| `Calculus/KeyTaclets.lean` | The 310 taclets of `solidityProgramRules.key` as one type, their `\heuristics`, and `KeyOrigin`. Regenerate with the recipe in its docstring. |
| `Calculus/Completeness.lean` | `Stmt.step`: the rule for every statement, a total function; `Stmt.complete`. |
| `Calculus/RuleShapes.lean` | Which solkey taclets each constructor transcribes (`tacletOrigins`), checked against the constructor list, and `taclets_partitioned`. |
| `Calculus/PrintedRules.lean` | The printed rules as a type and which constructor each is. |
| `Calculus/SoundKit.lean` | `SameOk`, `Premise.Correct`, and the lemmas and tactics the soundness proofs are made of. |
| `Calculus/SoundUpdate.lean` | Every taclet with an update premise has the statement's effect. |
| `Calculus/SoundUnfold.lean` | Every unfolding taclet runs like its statement off the fresh names. |
| `Calculus/RuleSoundness.lean` | `Taclet.sound`: every taclet, no hypothesis but freshness. |
| `Calculus/Logic.lean` | `Premise.fml`, the sequent calculus `Proves Γ φ` (`Γ ⊢ φ`) and `Proves.sound`; sequents print as `dl{ Γ ⟹ φ }`. |
| `Calculus/Quote.lean` | Quoters from formulas back to terms, so a computed goal is re-checked by the kernel. |
| `Calculus/Symex.lean` | Symbolic execution: `Fml.step` fires `Stmt.step`'s rule, `symex`, `symex_sound`; tactics `sol_step`, `sol_symex`. |
| `Calculus/Notation.lean` | `dl[C]{ … }` and `dl!{ … }`: concrete formulas read against a contract. |
| `Calculus/ReadWrite.lean` | What a state reads after a write: the four-way path comparison, memory addresses, copies member by member. |
| `Calculus/Close.lean` | `sol_close`: a first-order goal in an arbitrary state, by weakest preconditions and `ReadWrite.lean`'s facts. Its docstring lists what it does not close. |
| `Calculus/CloseTests.lean` | What `sol_close` closes, pinned. |

## The data-structure theories

solkey's `find`/`save`/`read`/`write` are uninterpreted symbols whose meaning
is a taclet set. These modules are that theory as terms, each taclet a
theorem.

| Module | What it is |
|---|---|
| `Theory/Storage.lean` | `structRules.key`'s taclets, over `Theory/Terms.lean`'s sorts. Stated about **`findSt`**, the read that does not cross into memory, because that is the reader `structRules.key` has — `copyMem` is declared in `structMemoryRules.key`. `save`, `storeAt`, the delete family and `diverges` are here. Every taclet a theorem, in the *pre-fold* shape: the leaf of a write collapses (`saveOnEmpty`, `saveOnStoreCons` with its `isEmpty(flds)` split, `selectOnSaveEmpty`), because the copy on which solkey's non-collapsing leaf differs — a storage-to-storage copy of a mapping-carrying type — is not a statement (`TypedStmt.Assign.mk`). `storeAt` is the one-segment walk; `selectOnSaveCons` with no well-formedness hypothesis; the four `find`-over-`save` laws (`find_save_same`/`_extends`/`_prefix`/`_frame`) plus `find_append` — `Semantics` had only the first. The delete family is eager (`delNode`/`delValue`/`delAt`) and states every `selectStDelNode*` rule but `Map`: a `Seg` carries no `MapField`, so the mapping-preserving `delete` is the interpreter's alone. `findDelAtFields` carries a read through the fields of a deleted node. Still a theory over free terms, as upstream's is: the pre-state leaf `Struct.cur` is a view like `copyMem`, and what it denotes is `Update.lean`'s lowering business. |
| `Theory/Memory.lean` | `memoryRules.key`'s taclets, over `Theory/Terms.lean`'s sorts, plus the `new` predicate. Every taclet a theorem, including the chain-walking family (`readREmpty`, `readRCons`, `idCCDef`, `defaultDefIdentity`) and `newFromAdd`/`readOnAddM` in KeY's branching form. `copySt`/`copyMem` are `Theory/CrossDomain.lean`. |
| `Theory/Terms.lean` | The sorts, because `structMemoryRules.key` ties the other two files together: `copyMem` is a `Struct` constructor and `copySt` a `Memory` one, as KeY declares them, so `Struct`/`StValue`/`Memory` are one mutual inductive. With them the readers that are mutual for the same reason — `selectSt`, `findSt` (the storage read that stops at a view), `find` (the one that crosses into `readR`), `readIn`/`readId`/`readR`/`readRId`, and the path-identity resolver. All structural: the cycle is cut by `readIn` reading its copied struct with `findSt`, so every equation stays `rfl` and a closed term reduces in the kernel, which is how half the taclets are checked. `Struct.inductionOn`/`Memory.inductionOn` are the one-sort recursors a mutual inductive does not give. `Struct.cur p` is the storage a derivation line started from, below `p`: the leaf a read is lowered onto. |
| `Theory/CrossDomain.lean` | `structMemoryRules.key`'s four taclets on those sorts: `findCopyMem`, `readCopySt`, `readCopyStIdentity`, `readCopyStOther`. `readCopyStIdentity` falls out of `defaultDefIdentity` because a copied struct member reads as `dflt`. Not modelled: a view nested in a view — `StValue.find_eq_findSt` is where that is stated, and no worked example nests one. |
| `Theory/Rewrite.lean` | The theory layer's answer to `Calculus/Rules.lean`: `TheoryRule`, one constructor per rewrite rule of the printed signature, under **its printed** name rather than KeY's, and `lemmaNames` saying which theorem each one is at each sort. `#theory_rules` prints the table. |

## Typing

| Module | What it is |
|---|---|
| `Typing/Storage.lean` | `Layout`, `SVal.hasTy`, read-typing lemmas, and the runtime sorts `SVal.keySort`/`MVal.keySort`. |
| `Typing/StoragePreservation.lean` | The write-side twin: `save` keeps a value's type. |
| `Typing/State.lean` | `StateWT`, the full-state invariant, and cross-domain copy typing. That the interpreter keeps it is to be ported (`docs/kernel-port.md`). |

## Sort faithfulness (the solkey cross-check)

| Module | What it is |
|---|---|
| `SortCheck/Annotations.lean` | Proof-free table of the taclets' read-sort annotations, transcribed from the `.key` file. |
| `SortCheck/Parser.lean` | Token-level `.key` scanner plus the `conforms` cross-check. |
| `SolkeyCheck.lean` (root) | `lake exe solkeycheck`. |

## Counterexamples

- `DeleteFamilyGenericOverlap.lean` — the first-order inconsistency of solkey's pre-`e67a0d7c48` delete fallthroughs.
- `StaticRuntimeSort.lean` — the static sort of an array/mapping type is not its value's runtime sort.

## Examples

Every example is a theorem `⊨ dl!{ … }` proved by `sol_symex; sol_close`, or
a derivation `⊢ φ` built one `apply` per taclet (`Calculus/Logic.lean`).
`docs/examples-port.md` says where each example of the removed untyped layer
went.

| Module | What it is |
|---|---|
| `Examples/Tour.lean` | The running example end to end. |
| `Examples/StorageSteps.lean` | One example per storage statement form, the worked derivations as `apply` walks. |
| `Examples/StorageSuite.lean` | solkey's taclet suite on storage, deduplicated. |
| `Examples/StorageDelete.lean`, `Examples/LedgerDelete.lean` | `delete`, and a struct holding a mapping deleted. |
| `Examples/Branch.lean`, `Examples/Revert.lean` | The two-goal split; box and diamond on `revert`, `require`, `assert`, `transfer`. |
| `Examples/Values.lean` | Operators, short-circuits, checked arithmetic. |
| `Examples/Memory.lean`, `Examples/CrossDomain.lean`, `Examples/Net.lean`, `Examples/Theory.lean` | Memory, copies between storage and memory, `transfer`, the theory's rewriting. |
| `Examples/Notation.lean` | What taclets, premises and sequents print, pinned. |
| `Examples/ApplySteps.lean` | The proof style: every `Proves` constructor once, and a refused rule. |
