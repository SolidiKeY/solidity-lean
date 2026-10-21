# Porting mini-solkey into solidity-lean

For anyone editing the calculus, the syntax or the semantics: where each part
of mini-solkey (`~/projects/side-projects/lean/mini-solkey`) landed, what is
still open, the Lean pitfalls that shaped the design, and the design
decisions a change must respect.  mini-solkey is a small readable copy of the
storage calculus (typed syntax, one inductive taclet judgement, completeness
with no residue, a sound sequent calculus) and stays the reference for the
shape of each declaration.  The port was done in place, so there is no
parallel layer.  `docs/module-map.md` says what each module holds and
`docs/lean-key-rule-map.md` maps the rules to solkey's taclets.

## Where each chapter landed

| mini-solkey | here |
|---|---|
| `Ch01_Syntax`, `Ch02_Elab` | `AST.lean`, `Scope.lean`, `Syntax/Scoped.lean` (`Stmt C Γ Γ'`), `Syntax.lean` (the grammar), `Syntax/Elab.lean` (`sol[C]{}`, its output `Prog C Γ Γ'`) |
| `Ch03_Theory` | `Theory/` |
| `Ch04_Semantics` | `Semantics/Run.lean` (`Stmt.run`, typed), `Semantics/State.lean`, `Semantics/Storage.lean`, `Semantics/Heap.lean` |
| `Ch05_Logic` | `Calculus/Fml.lean` (`Fml C Γ`, both modalities), `Calculus/Logic.lean` (`holds`), `Update.lean` (terms, updates) |
| `Notation` | `Calculus/RuleSyntax.lean` (schemas, printers), `Calculus/SurfaceNotation.lean` (`dl[C]{}`) |
| `Ch06_Taclets` | `Calculus/Rules.lean`, `Calculus/Taclet.lean` (`Taclet.toStep`), `Calculus/Sound*.lean` (`Stmt.sound`), `Calculus/Proves.lean` (`Proves`) |
| `Ch07_Symex` | `Calculus/Step.lean`, `Calculus/Symex.lean`, `Calculus/Close.lean`, `Calculus/CloseScoped.lean` |
| `Ch08_EVM`-`Ch10_Correctness` | `Evm/` (`docs/compiler-verification.md`) |
| `Ch11_Completeness` | `Calculus/Step.lean` (`Stmt.step`), `Calculus/RuleExists.lean` (`Stmt.rule_exists`); progress (`Fml.active_iff_step`) retired at W4 `calc-del` of `docs/intrinsic.md` |
| `Ch12_Termination` | retired at W4 `calc-del` (the scoped strategy is fuelled) |
| `Ch13_Chains` | `Calculus/Chains.lean` |
| `Ch14_Updates` | `Calculus/UpdRuleScoped.lean`, `Calculus/UpdateRules.lean` |
| `Ch15_Decide` | `Calculus/Decide.lean` (storage reduction), `Calculus/DecideComplete.lean` (the bounded scoped closer); current typed read realization and its exact fragment are in `Calculus/ReadRealization.lean` and `Calculus/QueryReduction.lean`; `Calculus/ReadTrace.lean` and `Calculus/QueryReadBounds.lean` add bounded typed occurrence replay and no-loss witnesses |
| `Ch19_Arith` | `Calculus/LinearDecision.lean`: complete local decision of Boolean combinations of linear equations and inequalities over natural assignments; `Calculus/ScalarCode.lean` and `Calculus/TypedLinear.lean` add exact bounded primitive contexts without dependencies. |
| `Ch20_Decision`, `Ch21_NoLoss` | `Calculus/ExactReduction.lean` and `Calculus/QueryReduction.lean` prove exact reduction and read abstraction for their recognized leaf fragment; `Calculus/StaticLinear.lean` completes arithmetic compilation and both verdicts for static primitive equalities. `Calculus/CheckedLinear.lean` adds exact checked addition/subtraction, comparisons and Boolean expressions. `Calculus/ExactUpdates.lean` adds push-free update equivalence without memory-local destinations. `Calculus/ParameterReduction.lean` adds complete typed universal prefixes through that shared compiler. `Calculus/ProgramReduction.lean` adds exact assignments, primitive declarations, deletion, blocks, branches, require/assert/revert and primitive-result calls before that compiler. `Calculus/InputReduction.lean` reconstructs observed transaction fields, parameters and storage together; `Tools/CompleteVerification.lean` connects both original-function verdicts to `#verify`. `Calculus/TraceReduction.lean` adds exact original-source validity over consistent occurrence traces, with syntax-derived bounds; `Calculus/QueryArithmetic.lean` completes arithmetic extraction from explicit fixed-layout dependent-query certificates. `Calculus/AliasConstraints.lean` generates symbolic path-alias constraints through the existing comparison and checked compiler. `Calculus/DependentReduction.lean` adds automatic fresh occurrence flattening, guarded alias arithmetic and original-source proof/counterstate transport, including universal parameters and the public exact verifier. Broader arithmetic, interior quantifiers and remaining updates stay open. See `docs/complete-verification.md`. |
| `Ch25_DeclarationFacts` | `Calculus/DeclarationFacts.lean`, integrated into specification-candidate certification by `Tools/Counterexample.lean`; `Calculus/DeclarationReduction.lean` removes certified facts by exact equivalence before read-query recognition |
| `Ch27_Certificates` | Arithmetic finite-graph certificates are not ported; the declaration certificates above prove a different family of facts |
| `Ch28_Countermodels` | `Calculus/LinearCountermodel.lean` extracts guaranteed arithmetic counterassignments from traced derivative graphs. `Calculus/ReadRealization.lean`, `Calculus/ReadQuery.lean`, `Calculus/QueryReduction.lean` reconstruct actual typed counterstates from supplied assignments; `Calculus/StaticLinear.lean` connects complete model extraction to original-source counterstates for static primitive equalities. `Calculus/CheckedLinear.lean` extends it to checked addition/subtraction, comparisons and Boolean expressions. `Calculus/ParameterReduction.lean` reconstructs typed universal parameter instances alongside storage. `Calculus/ProgramReduction.lean` transports both verdicts through supported source programs. `Calculus/InputReduction.lean` adds actual transaction-input reconstruction, and `Tools/CompleteVerification.lean` connects both verdicts to `#verify`. `Calculus/TraceReduction.lean` reconstructs original-source counterstates from supplied finite dependent-read values, rejecting conflicting aliases. `Calculus/QueryArithmetic.lean` adds complete value selection and actual counterstores from explicit alias-aware query certificates. `Calculus/AliasConstraints.lean` generates path-alias formulas and their arithmetic encodings. `Calculus/DependentReduction.lean` automatically compiles dependent mapping reads and reconstructs original-source counterstates through universal prefixes; interior quantifiers and broader source arithmetic remain open. |
| `Ch29_StorageModels` | The separate Mathlib first-order storage-model packaging is not ported; this repository keeps its typed interpreter and Theory laws without external dependencies |
| `Examples/` | `Solidity/Examples/` |

Beyond mini-solkey: type soundness and reachability (`Typing/`), sort
faithfulness (`SortCheck/Faithfulness.lean`), the callback semantics
(`Semantics/Callback.lean`, `Calculus/Callback.lean`), function
specifications (`Calculus/SurfaceSpec.lean`), the solkey corpus (`SolidityCorpus`,
`docs/corpus-parity.md`), and the `SolKey` reader's correspondence against
`Taclet` (`~/projects/side-projects/lean/solkey`).  The intrinsic refactor
(`docs/intrinsic.md`, 2026-10-07 to 10-11) scoped the syntax, typed the state
and the run, and moved the calculus onto both.

## Still open

- **The bridge: closed (2026-10-07 to 2026-10-09, W4 and W5 of
  `docs/intrinsic.md`).** The scoped syntax (`Scope.lean`,
  `Syntax/Scoped.lean`) replaced `Syntax.lean`'s `Stmt C` in every
  semantics, rule and proof: the untyped run, its calculus and the bridge
  theorems (`run_erase`) are deleted.  The untyped statement went at W8
  (decision 11): the elaborator emits the scoped syntax
  (`Syntax/Elab.lean`) and the printers print it
  (`Calculus/PrintStmt.lean`).  The terms read the typed state itself,
  its global part (`State.glob`, `Semantics/State.lean`) and its locals:
  nothing is erased.
- **The closer (M6c; its IR deleted at W9.5a).** `sol_decide` reduces and closes
  the scoped leaf by position (`Calculus/DecideScoped.lean`,
  `Calculus/DecideTyped.lean`: `Valid.of_reduceS`, sound over the typed
  state), `sol_close` reads a leaf's parameters at their types,
  `sol_prove` walks scoped sequents, the update rules rewrite the scoped
  leaf, and a chain's links are scoped, while the program is open and
  past it.  No leaf is erased any more: decision 7's untyped formula IR and
  the erasure to it went at W9.5a (`docs/intrinsic.md`); what the reduction
  compiles a leaf to is `LFml` (`Calculus/DecideLang.lean`).

- **Calls.** Parameters and return values of reference type (`Person storage
  p`, `uint[] memory xs`) are elaboration errors (`Syntax.lean`).  An external
  call is a `try` only (`Stmt.tryCall`): a bare `I(a).f();`, `try new C()`,
  `{value: v}`, an `Error`'s message and a catch-all's `bytes` are not
  modelled, and a `try` is outside the EVM fragment.  A diamond `try` closes
  to `false` (`tryCallDiamond`), and so does a diamond payment
  (`transferDiamond`): solkey's diamond transfer rules are not ported.
- **Callbacks.** The ordinary taclets lift to `ProvesC` only on a statement
  that pays nothing and runs no other (`Stmt.forks = false`).  A branch or a
  call around a transfer, and the capture rules of a transfer
  (`transfer_unfold_*`), have no `ProvesC` rule, so their soundness under the
  callback reading is unproved.  `ProvesC` has no strategy: `sol_symex` is the
  no-callback reading's.  The corpus's `net/*-withcallback.key` problems stay
  unported (`docs/corpus-parity.md`).
- **The hand-written `TestSuite`** declares neither `boolKeyed` (the
  interpreter reads keys as `Int`) nor `tree` (a struct recursive through a
  mapping, which `structRank` forbids).  The corpus's `TestSuite` rows come
  from the imported contract, which has `boolKeyed` (`Corpus/Imported.lean`).
- **Complete decision and countermodels.** The scoped closer is sound but
  bounded (`Calculus/DecideComplete.lean`); failure is not a refutation.
  Exact reduction and typed read realization now cover a recognized leaf
  fragment, and complete automatic model extraction covers static primitive
  read/literal equalities, checked addition/subtraction, comparisons and Boolean
  expressions, also after supported push-free updates with no memory locals
  in their output context. Exact source-program reduction now covers assignments,
  primitive declarations, deletion, blocks, branches, require/assert/revert and
  primitive-result calls. Observed transaction inputs are reconstructed exactly
  by `Calculus/InputReduction.lean`, with both verdicts connected to `#verify`.
  Dependent-key traces now have bounded no-loss witnesses and original-source
  counterstate replay (`Calculus/TraceReduction.lean`), with values supplied
  externally; `Calculus/QueryArithmetic.lean` also provides complete arithmetic
  selection from explicit fixed-layout query certificates.
  `Calculus/DependentReduction.lean` now supplies automatic occurrence
  flattening, guarded aliases and original-function proof/counterstates through
  universal parameters, connected to `sol_exact` and `#verify`. Broader source
  arithmetic and remaining updates stay open (`docs/complete-verification.md`). Memory the updates
  allocate is read
  by solkey's `memoryRules.key`/`structMemoryRules.key` taclets
  (`Calculus/MemRead.lean`; `docs/lean-key-rule-map.md`, "The closer's
  memory clauses"), copies between memory and storage included; a `push`
  of a memory object is outside the fragment.
- **Reachability of an ill-defaulted root** (an array of a struct
  `defaultOkS` refuses; the table has none since `BadDup` was refused,
  `refusedStructs`): that such an array
  stays empty is unproved, so `reachable_iff` asks `Ty.okDeep` of every root
  (`Typing/Constructibility.lean`).
- **The EVM fragment**: memory, copies of dynamic arrays, `push()` of a struct,
  fragile aliases after `pop`/`delete`, mappings keyed by `bool`/`int`
  (`docs/compiler-verification.md`).

## Port later

- **The `SolKey` reader** (separate repository, `lean/solkey`).  Ported to
  the scoped `Taclet` on its branch `intrinsic` (`docs/intrinsic.md`, "W5
  reader"); it requires `../../../solidity-lean-intrinsic` until `intrinsic`
  merges into `master`, when its require goes back and the branch merges.
- **The `Rules` corpus** (34 `.key` problems hand-written in the removed
  untyped layer): to be re-derived over the typed syntax
  (`tests/solkey/expected.tsv`).
- **The `PreservationNecessity` counterexample** (a duplicated layout root
  checks one stored value against two types, so `nodupKeysB` is necessary),
  removed with the untyped layer; the typed storage has one value per root
  by construction (W10.5.2).

## Sharp edges

- **`Meta.reduce` through indexed families is about 100 times slower.**
  Closed goals are evaluated as compiled code (`evalExpr`) and quoted back by
  hand-written quoters (`Calculus/Quote.lean`, `Syntax/Quote.lean`); the kernel re-checks.  This
  works only for a contract that is a named constant, and every new syntax
  constructor needs an arm in every quoter.
- **`deriving ToExpr` fails on constructors with proof fields.**  Quote the
  contract as its constant and the proofs as `Eq.refl`.
- **A big overlapping `match` is unusable in proofs** (`simp` and `whnf` time
  out), which is why `Stmt.step` is a total dispatcher.
- **An inner `match` does not refine an index.**  Dispatcher arms need
  top-level patterns, and `if h : ...` rather than `if ...`, so the branch
  fact reaches the proof obligations.
- **Kernel-evaluated code takes a context-indexed family apart by
  `casesOn`**, never by `match`: the equation compiler casts every index and
  the kernel pays a context comparison per cast (11–13× on symex; Gate G0 of
  `docs/intrinsic.md`, condition 1).  `cases` itself works on `Prog C Γ Γ'`
  without generalising.
- **Notation.**  The concrete `dl{}` needs `priority := high` over the
  schematic one; the chain macro builds applications with `Syntax.mkApp` (in a
  quotation `$a $b` reads `$b` as an arrow); `dl_fml`/`dl_term` need category
  parenthesizers, or `dl{ a = b } ~> psi` prints with parentheses.

## Decisions

Design rationale a change must respect.  Rows cited from other documents keep
their names.

### Syntax and elaboration

| Question | Decision |
|---|---|
| Unknown names | An error: parameters are declared locals.  mini-solkey reads an unknown name as a `uint` parameter. |
| Struct bodies | The package-wide `Semantics.structDef`, which the interpreter reads; a `Contract` is its storage roots only (`Contract.fieldType` reads the table).  A per-contract table would let a contract disagree with what runs. |
| Conditions | `if`, `require` and `assert` test a `Simple` value; the elaborator captures any other condition into a fresh `bool` first, in the scope the condition stands in (a nested `else if` inside its branch). |
| `T storage x;` | Binds `x` to no path (`Rhs.unset`, an alias local at `none`, since 2026-10-07): a read through it reverts, where solc 0.5 and later reject it statically.  A conditional of references declares its alias so, before the branches. |
| Effects inside expressions | `++`/`--` in an expression and a conditional of references are captured by the elaborator before the statement (`hoist`), so `Val` stays effect-free and no rule sees them.  The order is solc's (right operand before left, right-hand side before target, base before index), pinned by `TestSuite.sol`'s evaluation-order functions.  A call in an expression (`x = f(a) + 1;`) is captured the same way, counting as an effect.  An effect or call under `&&`/`\|\|` runs only where solc evaluates it (`bool se = a; if (se) { se = b; }`, solkey's `logicalAndShortCircuitRhs`), and one in a conditional's branch only in that branch (`T se; if (c) { se = a; } else { se = b; }`, solkey's `ternaryToIf`); a conditional callee `(c ? f : g)(x̄)` is imported as `c ? f(x̄) : g(x̄)` where neither `c` nor the arguments have an effect (solc's legacy pipeline evaluates the arguments before the callee; otherwise the function is unsupported).  A decrement is spelled `x--`/`--x` with two U+2212, since `--` opens a Lean comment. |
| What elaborates away | `event`/`error` declarations, visibility and mutability words, ether and time units, `payable(e)`/`address(e)`, `uint256`/`int256` and enums are read by `sol{}`/`contract!{}` and gone before any `Stmt`: no constructor, no rule. |
| `emit`, `require(c, Err(a))` | The log and the error data are dropped, the arguments are not: one that may revert or has an effect is evaluated (captured left to right).  `revert Err(a)` is `revert()`.  Struct constructors lower to a `T memory` local plus member writes. |
| Named arguments | `f({q: b, p: a})` is `f(a, b)`, put in the callee's parameters' order before the statement is elaborated (`RawExpr.orderNamed`), as solkey's parser does; an argument with an effect out of that order is an elaboration error, as in a struct constructor. |
| Modifiers | Inlined around each function that applies them (`wrapMods`), the first listed outermost, each parameter a fresh local bound when the modifier is entered.  A `_;` may stand anywhere, several times (the body runs again in the same locals, its parameters and return variable not reset: solc's legacy pipeline), not inside `unchecked`; a `return` in a modifier ends that modifier (`lowerReturns`, before its `_;` is filled), so the code after the `_;` of the modifiers outside it still runs; a modifier without one and a reference-typed parameter are elaboration errors. |
| Constructors | `constructor(…) { … }` is `Contract.ctor`, not a function, and `uint x = 5;` a root with an initializer (`Contract.inits`).  A deployment is the program `constructor(args);`, a top-level statement only, not in a function's body, a branch, a loop or a block (the reader's `top` flag, cleared by `elabBranch`): the elaborator inlines the constructor as any call (`elabCtor`, `functionBodyExpand`'s `CallRet.rets []`), the initializers prepended after its parameters are bound and before its modifiers, as solkey's `ExpandFunctionBody` does.  No new `Taclet`: the start is an update, solkey's `{storage := mtSt ‖ net := storeSt(mtSt, at(msgSender), msgValue) ‖ selfBalance := msgValue}` (`Problem.deployUpd`, the term `mtSt`), and `Contract.deployT` runs the elaborated program from `State.deploy` (it takes the program, which the elaborator builds: `ctorProgS`, `Syntax/Splice.lean`).  The obligation owes no `wt(storage)` (`deploy_wt` would be a theorem of its own).  `constant`/`immutable` with an initializer follow solkey in `contract!` (a root with an initializer); the solc import inlines a `constant` and an `immutable` nothing writes, and keeps one the constructor writes a root (`docs/solc-alignment.md`). |
| `unchecked { ... }` | No `Stmt` constructor: the wrapping `BinOp`s `+% -% *% **%`, which the elaborator (`uncheckStmts`) writes in place of the block's checked ones, so every rule over `op` covers them.  A function called from the block stays checked, as in solc.  On the EVM they are `ADD`/`SUB`/`MUL`/`EXP` with no guard.  Signed `+ - *` wrap on the operands' words through the conversions `UnOp.toInt`/`toUint` (`int(u)`, `uint(i)`; no code on the EVM), which casts between `uint` and `int` elaborate through too (`castCapture`); no solkey taclet. |
| `**`, bitwise, shifts | `**` is checked `uint` exponentiation (`int ** k` is not ported).  `BinOp.band`/`bor`/`bxor`/`shl`/`shr` and `UnOp.bnot` are solc's at `uint256` (a shift by 256 or more is `0`), `uint` only: two's-complement `int` is not modelled.  No solkey taclet exists and none is added; the rules over `op` cover them.  Their compound forms elaborate to `l = l op e;`. |
| Environment values | `msg.sender`, `msg.value`, `block.timestamp`, `address(this).balance` and `address(this)` (`this` in a formula, the ledger's own account) are a simple value `Simple.env k` (term `Term.env k`), as solkey's `netHeader.key` declares them as program variables; no taclet reads them.  `msg.*` and `block.timestamp` are the state's `tx : TTx`, kept by every statement and replaced by a callback (a re-entrant call is its own transaction); the balance is `State.selfBalance`, the funds the transaction found, which `transfer` leaves (it books `net` only, and not at `this`).  On the EVM: `CALLER`, `CALLVALUE`, `TIMESTAMP`, `ADDRESS`, tied to the state by `EnvSim`; `address(this).balance` is not compiled, since `SELFBALANCE` reads the account a `CALL` debits. |

### Semantics

| Question | Decision |
|---|---|
| Modalities | The box is partial correctness (it holds unless the run ends normally in a bad state); the diamond needs a normal end; both accept a run that is `exhausted` (a push at the bound, decision 15 of `docs/intrinsic.md`).  The typed run is never stuck.  An unfolding rule owes its statement the same outcome up to the halt (`TRes.Sim`, `Calculus/SoundKit.lean`), which the order-changing rules meet without side conditions. |
| Array bounds | An index is checked where the program takes the path (`checkIndex`), so an update fails as its statement does and a failing update reads as a revert.  `SVal.find`/`save` address slots past the end: an alias checked when bound writes the slot a later `pop` left, as solc does. |
| Memory `delete` of a reference | The location gets a fresh default object (KeY's `memoryFieldDeleteReference`, solc), not a reset of the old one: an alias keeps it. |
| Fixed-size arrays | One `RefTy.fixed E n`, not a length index on `.array`; array rules take an `ArrTy R E` (`dyn`/`fixed`) so one rule covers both, as solkey's `Path[...,array]` does.  `delete` keeps a fixed array's `n` elements (reset) and empties a dynamic one; a fixed array has no `length` slot, and its `.length` is the literal `n`; a literal index `>= n` is an elaboration error.  solkey's delete/`pop` taclets exclude fixed elements; the Lean rules do not, and are sound for them. |

### Calculus and rules

| Question | Decision |
|---|---|
| One rule per statement | Rules carry solkey's taclet names (an operator family is one constructor, not one per operator).  `Taclet` is a `Prop`; uniqueness is stated through `Stmt.step` (`Stmt.rule_exists`, `Rule.iff_step`, `Rule.premise_unique`).  A constructor carries as hypotheses exactly the facts its `Stmt.step` arm establishes, read off its schema variables by name and position (`RuleSyntax.sideConds`, `autoParam`ed with `side_cond`, hidden by the printers), so a taclet is still one `dl{ }` line.  Where solkey leaves two taclets open and its strategy picks, the side condition keeps the one `Stmt.step` picks (`Val.notTernary`, `Loc.isTarget`, `MPath.isBindable`). |
| Where the kernel follows KeY over the old table | A state variable operand is captured (`binopUnfoldLeft`), since it is a path, not a `SimpleExpression`.  A compound target is an `OpLoc` at a simple index (`values[i + 1] += 1;` captures the index first; `Upd.opSave` reads the source first, as `Stmt.run` does).  A `y = nsp.f++;` receiver is captured by KeY's `storageLocalDeclInitDrop`, not a Lean-only alias rule.  A memory reference from a member is `memoryFieldWriteCopy` from any bindable source: solkey's `..._rightSndResult` captures first, which is incorrect where the slot holds a reference.  Per-rule detail is in `docs/lean-key-rule-map.md`. |

### Calls and callbacks

| Question | Decision |
|---|---|
| Where a callee's body lives | In the call (`Stmt.call f args ret body`), closed over a frame of its own (its returns on its parameters, `rs ++ ps`), not looked up in the contract: a contract holding `Stmt` bodies indexed by itself is an inductive-inductive type Lean lacks.  The contract keeps the body as read (`FunDecl.body`); the elaborator inlines it at each call with every callee local renamed fresh (`renameStmts`, `ElabScope.inlined`) and builds the closed frame directly (`elabCallRet`, `Syntax/Elab.lean`).  `Stmt.run` is structural with no rank certificate, and the elaborator is the only author of a call's body.  A function calls only the functions declared before it, so inlining ends.  A recursive function is the exception ("Recursion", below): its call is `Stmt.callRec`, its body behind a thunk, unrolled frame by frame. |
| Binding arguments | The arguments are read in the caller's context and bound as the frame's parameters, as solc reads every argument before the call, so `internalCallExpand` and `functionBodyExpand` are exact with no condition (the untyped side's `Arg.separatedFrom` is gone with its run).  The capture rule (`functionCallArgCapture`) takes the leftmost argument that is not simple: a criterion the capture could re-trigger would loop. |
| `return` | Anywhere in a body, lowered away by the elaborator (`lowerReturns`, run on a callee's body after its locals are renamed) rather than as an abrupt completion in `Stmt.run`.  What follows a `return` is dead; the statements after an `if` with a returning branch move into the other branch.  A moved statement naming a branch's own declaration is an elaboration error.  A callee's `return` ends the callee only. |
| Callback semantics | A relation over `Stmt.run` (`ExecS`/`ExecP`), not a second interpreter: every statement but a transfer, a branch and a call is `Stmt.run`'s, so the relation cannot drift.  A transfer halts, leaves the invariant broken (an outcome no formula accepts), or resumes in `State.havoc` (storage and ledger replaced; locals, memory and funds kept, as solkey `0b885c229d` keeps `selfBalance`) satisfying it. |
| Callback taclets | A second inductive `CallbackTaclet`, not `Taclet` constructors: `Stmt.sound` is against `holds` (the deterministic run), and one-rule-per-statement would break.  The box constructor as in solkey (the diamond is not ported); the resume premise is a second sequent under `{havoc}` (KeY's anonymising update). |
| The invariant | An `Invariant C` is a formula with no local and no transfer (solkey's `CInv(storage, net)`); the frame lemmas need it closed.  It may read the ledger, which a callback havocs, and `address(this).balance`, which it keeps (`State.havoc`). |
| `ProvesC` | The ordinary taclets lift on a statement that pays nothing and runs no other, and whose premise pays nothing; a goal with no transfer left is `Proves`'s (`holdsC_iff_holds`).  Validity with callbacks implies validity without (`valid_of_validC`). |
| External calls (`try`) | The callee is never run.  Without callbacks how a call ends is the transaction's (`TTx.ext`, a table read by `Stmt.run`, which no formula reads); a call with no entry reaches an address with no code and reverts in the caller, and so does data that does not decode (`Binders.decodeT`).  `tryCallNoCallbackBox` has a goal per clause, for every value of the locals it binds (`Premise.branches`, `Fml.alls`), so a proof holds whatever the table says.  With callbacks a `try` is a point where control leaves (`Stmt.hasTransfer`), and `ExecS` runs it nondeterministically, its success from a `havoc`ked state keeping the invariant. |
| Function contracts | A derived rule over `Stmt.run`, not a `Proves` constructor (`Calculus/FunContract.lean`): `useContract` has KeY's goals "pre" (`[ params := args ] requires`) and "post" (`[ params := args ] {old := storage ‖ oldNet := net} {havoc} ∀ T r. (ensures → [ res = r; ..ω ] φ)`), box only, its conclusion `⊨`, so it applies at the first statement of a goal.  A contract is a fact about the callee's block from any state (`FunContract`), proved from its obligation `requires → {old := storage ‖ oldNet := net} [ T r; body ] (ensures ∧ typed(r))` (solkey's planned `requires -> [g(args)@C] ensures`, no invariant); it owes the result's type (`rangeFml`), as `∀ T r` ranges over the type.  The mutability is read off the inlined body, since `FunDecl` keeps no `pure`/`view` (only `payable`) (`Calculus/Blocks.lean`'s `Stmt.within`): `pure` (a `view` body that reads no state, with the same frame) and `view` keep storage and ledger, so "post" has no `{havoc}`; `nonpayable` (storage writes, `transfer`) gets `State.havoc`'s.  A body with memory, a push, a pop, an alias or a `catch` that binds data has no mutability, hence no contract (a `try` is `nonpayable`): "post" havocs no heap.  The callee's parameters are the call's fresh names, so a contract is stated at a call.  A recursive call by its contract is `useRecContract` (`Calculus/Recursion.lean`), the contract proved by induction over the unrolling ("Recursion", below). |

### Recursion

Status: implemented on branches `open-recursion` and `open-rec2`: the
countdown (box and diamond), a recursive sum, mutually recursive
`even`/`odd` and a recursive `divmod` of two returns proved
(`Examples/Tactics/Recursion.lean`); the runner proves
`functionsRecursiveUnbounded` unannotated and `tests/solc/Recursion.sol`'s
rows by their `/// @custom:key` contracts (`rec_auto`); under the callback
reading (`ValidT`) on branch `open-reccb` (`rec_auto_c`, row "Callbacks
(O7)").

| Question | Decision |
|---|---|
| Where a recursive callee's body lives | In the call, behind a thunk: `Stmt.callRec f d args ret (body : Unit → Prog C (rs ++ ps) (rs ++ ps))`, the body a block (so its frame is `rs ++ ps` on both sides).  A `Unit →` field is strictly positive, so `Stmt` stays an ordinary inductive and `Stmt.run` structural (the recursor's hypothesis for the field is `∀ u, motive (body u)`): the run is `TRun.call` of `body ()` (`Stmt.run_callRec`, by `rfl`).  No printer, quoter or analysis forces the thunk but where it must (below), so a body that calls itself costs one frame, not the unrolling. |
| What the body is | `recUnroll Prog.recBase step recDepth` (`Syntax/Scoped.lean`): `recDepth` frames, frame `n + 1` the body with its own recursive calls `callRec f n args' ret' (fun _ => frame n)`, the bottom one `assume(false);` (exhausted).  The EVM's stack holds 1024 words and every internal call's frame at least its return address, so no run nests deeper than 1024: a deeper one overflows the stack and halts, which the model reads as the bottom frame's `exhausted`, and both modalities accept exhaustion (decision 15).  So the unrolling over-approximates the EVM soundly (below the bound the run is exact; the EVM may overflow earlier, every frame holding more than its return address, and a mutually recursive callee's count starts again at each frame of its caller, which only makes the bound looser), and nothing about a fixed point is needed.  **The diamond of a recursive call is no termination claim**: it accepts the exhausted bottom frame, so `⟨ f(); ⟩ false` holds of `function f() { f(); }`; it says the call neither reverts nor panics (where a loop that does not end is `diverge`, which the diamond rejects).  KeY's diamond would need a `decreases`.  `d` is the frames left; only the quoters read it. |
| Elaboration | `elabCallRet` (`Syntax/Elab.lean`): a function is recursive when its body (or a modifier's) reaches a call of itself (`isRecursive`, over the contract's functions).  Its call allocates the frame's names once, and the body is elaborated per frame, lazily: `frame n bt` elaborates the raw body under `ElabScope.recs`, where a call of the same function (or of one mutually recursive with it) is `callRec f n … bt` with the frame's own names (`RecFrame`; the thunk's contract erased, `RecThunk`), its errors read once at the call.  A recursive body may call the functions declared before it and the ones mutually recursive with it (`recPartners`).  Every frame of the unrolling is one context, `rs ++ ps`, at every call: a call of several returns returns to a tuple's targets (`CallRet.rets`, the targets fresh at each call, since they are declared in the caller's context too), and is refused as a statement (`f(a);` would declare the returns inside the frame, another context); a reference return is `CallRet.mem`/`CallRet.storage` with the frame `[.mem R] ++ ps`/`[.alias R] ++ ps`.  Such a call runs (the unrolling is the same); a storage return has a contract (its alias rebound to a path, within `view`), a memory return none (a body with memory has no mutability, `Stmt.within` is false on `declMem`, …): "What is left" below. |
| Quoting | A thunk is not data, so both quoters (`Syntax/Quote.lean`, `Calculus/Quote.lean`) quote a `callRec` by forcing its body once and writing `fun _ => recUnroll Prog.recBase (fun n bt => Q) d`, where `Q` is the forced body with every call of the same function written `callRec f n … bt` (`hs`, the functions whose unrolling is being quoted, by de Bruijn index).  Mutual recursion nests: the inner function's unrolling is under the outer's binders.  The kernel re-checks every quoted term. |
| The strategy | `recursiveCallUnfold` (Lean only): `callRec` is the call of its body's next frame, which `internalCallExpand`/`functionBodyExpand` expand as any call.  It is exact, so sound, but it does not end with a symbolic argument: it splits every `if` whatever its condition, and with concrete arguments it is just as deep (the closer prunes branches only at the leaves).  So the strategy the tactics run does not fire it: `Fml.stepS`/`symexS` (`Calculus/Symex.lean`) are `Fml.step`/`symex` but at a box whose first statement is a recursive call, which they leave and go on with the rest of the formula.  `sol_step` there fails ("no modality left, or a recursive call at the head of each"), and `sol_symex` fails naming the call (`the strategy stops at the recursive call `f``): it is proved by its contract.  The rule stays (`Stmt.step`, a walk's `unfold`, `#step`). |
| Proofs | KeY's way: `useRecContract` (`useContract` at a `callRec`, `Calculus/Recursion.lean`) with a `RecContract` (the `FunContract` at every call that returns `rs`, the body within its mutability, the parameters unwritten), proved for every frame by `RecContract.unroll`: the bottom frame meets every contract, and a frame meets it where the frame below does.  `FunContract` and its rule take the modality (`m`, the box by default), so a diamond contract is one too.  No `decreases`, under either modality: both accept the exhausted bottom frame, and the unrolling is finite, so the induction is over the frames, not a measure (a diamond `⟨ f(); ⟩ true` of a countdown from any `a` holds: below 1024 frames it ends, above them it is exhausted, as on the EVM).  In the step the frame below is a free thunk `t`; `sol_symex_rec` runs the strategy up to each call of it (conjunctions split) and `rec_contract ih` proves the call by the hypothesis.  A contract from the source: `recSpecContract` reads a function's `requires`/`ensures` (`FunDecl.spec`, `spec!{f}`'s compiler) as `req` over the parameters and `ens` over the return variables (`\result`, `result_<name>`), `old`/`oldNet` and the parameters; it assumes no range, layout or invariant (a contract holds from every typed state of the frame).  A call that returns to targets (`CallRet.rets`) is one of every call: `FunContract.forall_val`, `FunContract.forall_rets` (its targets' names do not matter, `Binders.defaultsT_eq`).  Mutual recursion: `odd`'s unrolling sits in each frame of `even`'s, its own calls of `even` the outer frame below, so `even`'s step proves the call of `odd` by `odd`'s contract by an induction of its own, whose step's call of `even` is the outer hypothesis; the body's mutability goes through the nested unrolling by `Prog.within_recUnroll`. |  The compiled strategy runs a goal with a free thunk at a placeholder body (`Prog.recSentinel`, `Symex.placeholders`), quoted back as the variable: `Meta.reduce` is far too slow for it. |
| Analyses that do not force the thunk | `Stmt.maxIdx` (the body's names are read when it is unfolded), `Stmt.size`, the solkey fragment (`inSolkey`, `keyStep`: false), `Stmt.asserts`, `forks`/`forksIn` (a recursive call runs as a call, which forks), the EVM's fragment (outside it), all conservative.  `Stmt.within`, `Stmt.hasTransfer` and `Stmt.callsBack` force it (the frame of a contract needs the first, the callback reading the others): they read the body's frames, exactly, but are proved by one frame, the recursive site a hole (`Prog.within_recUnroll`, `Prog.callsBack_recUnroll`, `Prog.hasTransfer_recUnroll`; `sol_no_callback`), never by evaluation: linear in the unrolling for one recursive call per body, exponential for several, so a loop's frame (`Prog.frame`) over a body with a doubly recursive call is not computable, and the walk of `ProvesC` does not try `plain` (`rfl`) on a sequent with a recursive call. |
| Callbacks | `ExecS.callRec`: a recursive call runs as the call of its body (`Stmt.exec_run`, `CallbackWk.callRec_wk`, `CallbackUnwk.callRec_unwk`). |
| The import | `SolcJson.reach` orders the functions callees first, a call back into the path adding nothing, so each function of a cycle comes after every function it calls outside it. |
| Through function values | A call through a value is a call of each function it may reach (`FunDecl.valueCallees`), so recursion through a value is recursion (`isRecursiveC`, `recPartnersC`), the dispatch's candidates among the partners (`docs/semantic-gaps.md`, "Function types"). |

| The runner | An obligation with a recursive call (`Frontend/Testing.lean`), plain or a specification's (`cspec`), is stated as `Valid` and proved by `rec_auto` (`Calculus/Recursion.lean`): the strategy up to each recursive call (`sol_symex_rec`), each call by a hypothesis about its body (an induction step's frame below), else by its callee's contract from the source (`recSpecContract`), else by `true`/`true`; a contract by induction over the frames at the first of `pure`, `view`, `nonpayable` the body is within (a failure past that is final: a more permissive mutability only weakens "post"); the leaves by `sol_close`, else the specification closer, with `Int.tmod` read as `%` at a nonnegative dividend and `bool` locals split.  Every step has its own heartbeats (`Recursion.tryOn`: the option's `maxHeartbeats`, counted from the step's start), the driver between steps none (it does no search of its own), and the nesting is bounded (fuel 32).  The search (`⊢`) is not run on it: it does no induction.  `functionsRecursiveUnbounded` (`⟨ f(); ⟩ true`) proves unannotated, `tests/solc/Recursion.sol` by its clauses. |
| Callbacks (O7) | `Calculus/RecursionCallback.lean`.  **A recursion that does not call back**: `callsBack` of a `callRec` is its body's, read off one frame (`sol_no_callback`), so `validT_noCallback_iff` applies and `rec_auto` proves it; past a callee that calls back, `ProvesC.recValid` reads the sequent at a recursive call without callbacks where nothing in it calls back (`holdsC_iff_holds`).  **A recursion that calls back**: `RecContractC` is `RecContract` over the callback runs (`FunContractC`: every `ExecP` run of the body from a frame where `requires` holds keeps the invariant, does not panic and ends where `ensures` holds), proved by the same induction (`RecContractC.unroll`), each frame's obligation by `ProvesC` (`FunContractC.ofProvesC`, through `Prog.exec_wk` under the snapshots); `ProvesC.recContract` (Lean only) proves the call by it, its goals "pre" and "post", sound by `holdsC_callRecContract` with the frame of a callback run (`ExecS.frame`: a callback only replaces the storage and the ledger, which a `nonpayable` body may write).  Both are `ProvesC.recCall`, a recursive call at the head of the box by a lemma about its readings; `ProvesC.havocIntro` takes "post"'s `{havoc}` into the context, and `sol_leaf` closes a leaf that mentions the induction's free frame (`Symex.placeholders`).  `rec_auto_c` is `rec_auto`'s twin on `ValidT`: the walk of `ProvesC` (`sol_prove`), each recursive call it stops at by `recValid`, else by a hypothesis, the source's contract or `true`/`true` at the first of `pure`, `view`, `nonpayable` (`Examples/Tactics/Recursion.lean`: `callThenCount`, `payDownNoPanic`, `payDownAuto`).  The runner proves a recursive row read with callbacks by `rec_auto_c` (`tests/solc/Recursion.sol`'s `callThenCount`, `payDown`). |

**What is left.** A contract of a memory return, and of a storage return
under the callback reading (`CallRet.isValues`, below).  (A recursive body whose `if` has a condition
that is not a local and a branch that calls back is closed: the capture is
`ProvesC.capture`, `docs/options.md` O3, and `tests/solc/Recursion.sol`'s
`payDown` reads `if (a > 0)` directly; `payDownDirect`,
`Examples/Tactics/Recursion.lean`.)  **A storage return** has a contract
(lane `open-refret`): its body binds the alias to a path (`r = xs;`, `r =
f(n - 1);` to the frame below's), and `Stmt.within` admits `rebind` and
`declStorage` of a path (`ARhs.pathIn`: `view` and `nonpayable`, not a
push), their frame the alias written (`Stmt.writesAt`, `Stmt.run_frame`'s
cases: the storage unchanged, one local set); "post" binds the returned
alias (`Fml.callResult`'s `.storage`, `holds_callStorage`), a contract at
one storage call is one at all (`FunContract.forall_storage`), and
`rec_auto` tries it.  `Examples/Tactics/Recursion.lean`'s `pickNoPanic`
proves `pick` by its contract; an `ensures` that reads the alias
(`r.length`) is past the closers, which read no alias local in a leaf
(`cdlIn![…, uint[] storage r]` writes one), and a source `ensures` over a
reference return is refused (`recSpecContract`).  **A memory return** runs
but has no contract, with callbacks or without: a body that allocates
(`declMem`, `assignMem`, a recursive call's `CallRet.noMem`) is within no
mutability, and the frame keeps the heap and its typing (`TGFrame.H`,
`TGFrame.heap`).  Its "post" would need a heap frame, which is a design of
its own: (1) a run invariant that every memory reference in the callee's
frame points into the objects it allocated (no memory parameter, or the
caller's objects reachable from one, so its writes reach no caller object),
an induction over every statement's run like `Stmt.run_frame`'s; (2)
`TGFrame` over a grown heap (`σ.H <+: τ.H`, the caller's objects' contents
unchanged, `HRef.wk`) in place of `τ.H = σ.H`; (3) "post" binding the
returned object as `Fml.allocAll` does (a fresh object of any contents,
`ens` over it), and a proof that the caller's goal does not see the other
objects the callee allocated (unreachable garbage), which no lemma of
`holds` states today (a formula is read at one typed heap); (4) the callback
reading's `ExecS.frame` alike.  The call rule (`holds_callMem`) is there for
a callee that allocates nothing.  A contract assumes no invariant
of the contract (`invariant`), so a clause that needs one past a recursive
call stays open.  `Stmt.within` of a body with two recursive calls of
itself is exponential in compiled code (`rec_auto` proves it by `simp`,
frame by frame, so `fib` is linear there).

### `send`

| Question | Decision |
|---|---|
| How a send ends | Asked of the transaction, as a `try`'s ending is: `TRun.send` (`Semantics/Run.lean`) reads `TTx.ext` at `sendKey a v` (empty calldata, the amount as the one word).  No entry or `ok` books the payment as `transfer` does and sets `pv` true; any other entry books nothing and sets `pv` false.  No new field: the oracle a `try` already reads.  Always-succeeding would prove `ok == true`, false on the EVM. |
| The statement | `Stmt.send pv r a`, `pv` a `bool` local, beside `Stmt.transfer`.  `bool ok = r.send(a);` elaborates as `bool ok; ok = r.send(a);`: `valueDeclSkip` where solkey fires `localValueDeclInitDrop` (same node count; the default is set, then overwritten by the send); a bare `r.send(a);` does not parse, as solkey has no rule for it. |
| Labelled goals | `Premise.cases fs us`: each formula of `fs`, then `{U} ⟨[ ..ω ]⟩ φ` for each update, read as one conjunction (`Premise.fml`) and as `Proves.cases`'s two hypotheses.  `Premise.Sound` asks that the run be one of the updates; the formulas are extra goals.  The scoped walk lists them with `Seq.premise` (`Calculus/ProvesDerive.lean`), a goal per element (`Seq.each`). |
| The diamond | Ported (`sendNoCallbackDiamond`), unlike `transfer`'s: a refusal is an outcome of the run.  Its "non-negative amount" goal is solkey's and not needed for soundness (the booking halts on a negative amount). |
| With callbacks | A send is a point where control leaves (`Stmt.forks`, `Stmt.hasTransfer`).  `ExecS` books it as the transfer of its amount and then halts where that does, leaves the invariant broken, resumes in a `havoc`ked state keeping it with `pv` true, or fails with nothing booked and `pv` false (`sendFailed`), the last whatever the oracle says: a callee may always revert.  `ProvesC.send` reads `CallbackTaclet.sendWithCallbackBox`'s premise as solkey's three goals, sound by `holdsC_sendCb`; the ordinary send rules do not lift (the statement forks), except under `ProvesC I false` for a gas-limited send (`Stmt.forksIn`, `docs/options.md`).  `Examples/Tactics/Callback.lean`'s `callToKeepsInv` is `PiggyBankNet.callTo` under a storage invariant. |
| Cost | `Stmt.run` and the proofs by cases on it grow by one arm; `TestSuite/Derived1.lean` re-checks in 7.7 s on a fresh worker on this branch and on master alike. |
| A ledger read past a storage write | `Modality.wp_box_saveStorage` (untyped, gone at W10.5.1; the typed `CloseS.wp_box_write` keeps the ledger as well) also hands the closer `τ.net = σ.net`, so `net-send-simple.key`'s `sendTo`, which stores the outcome (`sent = ok;`), closes as solkey states it (`Net.netSendSimple`), and so does `[ to.transfer(5); total = 1; ] net(to) = 2` (`Net.netTransferThenStore`).  Re-checks after it, on fresh workers: `Examples/Tactics/CrossDomain.lean` 54 s and `Memory.lean` 52 s (the `lean-verify` skill lists 75–90 s for each), `StorageSuite.lean` 21 s.  The `TestSuite/Derived*` replays close their leaves inside the residue and do not use the lemma. |
| Review (2026-10-06) | Fixed: sort rows for the four send taclets that read `net` (`SortCheck/Annotations.lean`, 119 rows; `solkeycheck`'s check, run as an `#eval` of `conforms`, is at zero against `1b4341a303`, and four rows ahead of the `100f7f24c3` pin); the corpus rows `net_send_simple` (proved) and `net_call_withcallback_simple` (unsupported: no tuples yet) in `tests/solkey/expected.tsv` and `docs/corpus-parity.md`, from `1b4341a303`'s `net/` (the header stays at `78f42fde33` until the TestSuite fixture is re-imported); `PiggySend.sendTo` keeps `sent = ok;`; `sol_derive?` prints a send's goal split on its `apply` line (`apply cases … <;> (try simp only […]) <;> (try and_intros)`), so a replay touches only the rule's goals, pinned with `sol_prove?` in `Examples/ProofTree.lean`; `#taclet` cites `upd_send_cases`, pinned in `Examples/Tools.lean`; the unfold rules pinned in `Payment.lean`; bare `simp`s of the lane replaced by `simp only`. `(bool ok, ) = a.call{value: v}("")` waits for tuples. |

### Specifications

| Question | Decision |
|---|---|
| Specifications | Compiled as solkey compiles them (`Calculus/SurfaceSpec.lean`): a clause reads a storage term, `\old(count)` is `find(old, count)` with `old` a storage variable bound by `{old := storage}`, and `\forall T x; e` is `Fml.all` over a local of type `T`.  Lean adds two premises solkey's total typed reads need not: each parameter's range and the layout of the state the clauses read (`layoutFmls`).  `sol_decide` keeps `find(old, p)` and reads `\forall` as a quantifier of its language (`LFml.all`). |

### Several returns, tuples and blocks

| Question | Decision |
|---|---|
| Several returns | `FunDecl.rets`, a list (unnamed returns are `_ret`, or `_ret0`, `_ret1`, …, where solkey's `ExpandFunctionBody` names every unnamed return `ret{i}`, a single one `ret0`; `FunDecl.ret` is the one return of a function that has one).  A call with targets (a tuple assignment's, an obligation's) carries `CallRet.rets`: each return variable declared at its type's default on entry (solc zeroes them; KeyTaclets' `R ri;` leaves them unconstrained), nothing assigned on leaving; a bare `f(a);` carries `CallRet.none` and declares the returns at the head of its body.  The targets are ordinary statements after the call, `t = r;`, solkey's `function-frame{…} t0 = r0;` without the frame; the printers write the call and them as the tuple assignment (`Stmt.tupleCallStr?`).  Only value types: `memory` on a return of several is an elaboration error.  `Stmt.run` is unchanged (`CallRet.enterT`/`leaveT`). |
| Tuples | Desugared by the elaborator as `ParserUtils.tupleAssignment` does (`elabTuple`): from a call, the call then the targets left to right; from a tuple, each component with a target into a fresh temporary, then the targets, so `(a, b) = (b, a);` swaps; a declaration `(uint a, , bool b) = …` declares its variables first and assigns them directly.  A component left out is dropped when it can neither revert nor have an effect, and evaluated otherwise (solc; solkey keeps only a call and drops the rest).  Targets that may alias (the same name twice, two that are not stack locals, one that reads another) are refused until solc's order of their writes is checked. |
| `return (e₀, e₁)` | `lowerReturn`: each return variable assigned in order, or, when a component reads a return variable (solkey's `ReturnLowering`, `returnSwapped`), the tuple assignment `(r₀, r₁) = (e₀, e₁);`, which reads every component first.  **Lean only:** `return g();` of several values is the tuple assignment `(r₀, r₁) = g();`, which solkey's `ReturnLowering` refuses (one value for several returns). |
| Blocks | `{ … }` is `RawStmt.block`, elaborated as a branch (its declarations scoped to it); in the scoped syntax it is `Stmt.block`, its locals popped at its end, and `blockEmpty` steps into it (claimed since the intrinsic refactor).  A block with a `return` inside is spliced into the statements after it before `lowerReturns` moves them (solkey's `blockReturn`), under the same guard as an `if`: a statement after it may not name one of its declarations.  There is no `return` left in `Stmt`: `blockReturn` and `functionFrameReturn` have nothing to rewrite; a call's frame ends with its expansion (`functionFrameEmpty`, claimed with `internalCallExpand`/`functionBodyExpand`). |
| `return` inside a loop | Lowered through a flag local, as solkey's `LoopLowering` does (`lowerLoops`, `docs/loops.md`): `r = e; ret = true;`, the loops' conditions and the rest of their bodies guarded by `!ret`, and `if (ret) return;` after the outermost loop, which `lowerReturns` lowers as any early `return`.  `lowerReturns` alone cannot: inside a loop the rest of the body and the remaining iterations would have to move, which no rewrite of the body can do.  Not an early-exit outcome in `Stmt.run` (rejected: Frame rules, below). |
| Recursion | A call of a recursive function is `Stmt.callRec` ("Recursion", below); every other call is inlined as before. |
| Two call rules | solkey `671f6762a9` splits KeY's call into `InternalCall` (`f(a);`, `y = f(a);`: `internalCallExpand`) and `FunctionBodyStatement` with targets (a tuple assignment's call, a synthesized obligation's `result = f(x̄)@C;`: `functionBodyExpand`).  Lean keys the split on the call's `CallRet`: `CallRet.rets` (the call returns to targets after it) is `fbs`, anything else `ic` (`CallRet.isRets`, a side condition of each; `callStep` picks by it, so `Rule.premise_unique` stays one rule per statement; a memory return is `ic`, decision 19 of `docs/intrinsic.md`).  A bare call of a function of several returns, `f(a);`, is an `InternalCall` in solkey; here it declares the returns at the head of its body and carries `CallRet.none` (`elabCallRet`), so it is `ic` too.  Both rules have the same premise, `expand_function_body`, and the same soundness (`Stmt.sound_call`).  Like `functionBodyExpand`, `internalCallExpand` waits for simple arguments (`functionCallArgCapture` first, decision D3), where KeY's binds `T p = arg` as written. |
| Specification obligations | Elaborated as solkey's synthesized `result = f(x̄)@C;` (decision D1): `T result;` then a call that returns to `result` (`CallRet.rets`; a void function's `f(x̄)@C;` returns to no target, `CallRet.rets []`), so the obligation fires `functionBodyExpand` as solkey's does.  **Lean only:** `T result;` is a statement of the box (one more node, `valueDeclSkip`), where solkey declares `result` among the problem's program variables; the sequent prints it `result = f(x̄);`.  A function of several returns returns to `result_<name>` (`SpecCompiler.resultVariable`), printed `(result_lo, result_hi) = f(x̄);`, and an `ensures` names a return by its name after the locals and before the state variables (`SpecCompiler.visitIdent`); `\result` needs one return.  **Lean only:** a function with an unnamed return has an obligation (its return is `result`, or `result__ret0`, … of several), where solkey refuses one (`SolidityOutline.unsupportedReason`). The tree has the same nodes as before but for the rule's name: `result = r;` was the call's own last statement (`CallRet.result`) and is now the statement after it. |
| Printing a call with targets | `ppTupleCallS` (`Calculus/PrintStmt.lean`) prints a `CallRet.rets` call and the target assignments after it as the tuple assignment, as `Stmt.tupleCallStr?` (`Syntax/Scoped.lean`) does for `Prog.toStr`.  With two targets or more the printed tuple re-elaborates to the same call (up to the elaborator's fresh names, which a chain line cannot pin; no chain runs a tuple call); `y = f(x̄);` and `f(x̄);` print an `fbs` as the `ic` they re-elaborate to (solkey tells the two apart by `@C`). |
| Frame rules | `blockReturn` and `functionFrameReturn` are architectural: returns are lowered at elaboration (`lowerReturns`), so there is no `return` to rewrite.  A faithful `function-frame` (an abrupt `return` completion in `Stmt.run`) would undo decision `978083b` and rewrite `Res`/`Halt` and every soundness, Typing, NoPanic, Callback and Evm proof.  **User decision (2026-10-06): an early-exit outcome in `Stmt.run` is rejected** in favour of lowering (`lowerReturns`) plus flags (a `return` that cannot be moved, as in a loop, lowered through a flag local); `RuleShapes.unclaimedTaclets` lists `blockReturn` and `functionFrameReturn`; `blockEmpty` and `functionFrameEmpty` are claimed since the scoped calculus (`docs/lean-key-rule-map.md`). |
