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
| `Ch01_Syntax`, `Ch02_Elab` | `AST.lean`, `Syntax.lean` (`Stmt C`, `sol[C]{}`) |
| `Ch03_Theory` | `Theory/` |
| `Ch04_Semantics` | `Semantics.lean` (`Stmt.run`), `Semantics/Agree.lean` |
| `Ch05_Logic` | `Update.lean` (terms, updates, `Fml`, both modalities) |
| `Notation` | `Calculus/RuleSyntax.lean` (schemas, printers), `Calculus/Notation.lean` (`dl[C]{}`) |
| `Ch06_Taclets` | `Calculus/Rules.lean`, `Calculus/Sound*.lean`, `Calculus/RuleSoundness.lean` (`Taclet.sound`), `Calculus/Logic.lean` (`Proves`), `Calculus/Uniqueness.lean` |
| `Ch07_Symex` | `Calculus/Symex.lean`, `Calculus/Close.lean` |
| `Ch08_EVM`-`Ch10_Correctness` | `Evm/` (`docs/compiler-verification.md`) |
| `Ch11_Completeness` | `Calculus/Completeness.lean` (`Stmt.step`, `Stmt.complete`), `Calculus/Progress.lean` |
| `Ch12_Termination` | `Calculus/Termination.lean` |
| `Ch13_Chains` | `Calculus/Chains.lean` |
| `Ch14_Updates` | `Calculus/UpdateRules.lean` |
| `Ch15_Decide` | `Calculus/Decide.lean` (the storage fragment), `Calculus/DecideComplete.lean` (realizability, `Fml.valid_iff_cons`) |
| `Examples/` | `Solidity/Examples/` |

Beyond mini-solkey: type soundness and reachability (`Typing/`), sort
faithfulness (`SortCheck/Faithfulness.lean`), the callback semantics
(`Semantics/Callback.lean`, `Calculus/Callback.lean`), function
specifications (`Calculus/Spec.lean`), the solkey corpus (`SolidityCorpus`,
`docs/corpus-parity.md`), and the `SolKey` reader's correspondence against
`Taclet` (`~/projects/side-projects/lean/solkey`).

## Still open

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
- **`sol_decide`, past realizability.**  A write or `delete` through a member
  named `length` falls back to `sol_decide_heuristic`, and `omega`/`grind` are
  not proved complete on the statement realizability leaves
  (`Calculus/DecideComplete.lean`).  Memory the updates allocate is read
  by solkey's `memoryRules.key`/`structMemoryRules.key` taclets
  (`Calculus/MemRead.lean`; `docs/lean-key-rule-map.md`, "The closer's
  memory clauses"), copies between memory and storage included; a `push`
  of a memory object is outside the fragment.
- **Reachability of an ill-defaulted root** (a `BadDup[]`): that such an array
  stays empty is unproved, so `reachable_iff` asks `Ty.okDeep` of every root
  (`Typing/Constructibility.lean`).
- **The EVM fragment**: memory, copies of dynamic arrays, `push()` of a struct,
  fragile aliases after `pop`/`delete`, mappings keyed by `bool`/`int`
  (`docs/compiler-verification.md`).

## Port later

- **The `SolKey` reader** (separate repository).  It imports only
  `Solidity.Calculus.Rules` and `Solidity.Calculus.KeyTaclets` and still names
  the old `RuleName` table; its correspondence proofs are to be migrated to
  `Taclet`.  `AGENTS.md` and `scripts/solkey-port.mjs` cite this section.
- **The `Rules` corpus** (34 `.key` problems hand-written in the removed
  untyped layer): to be re-derived over the typed syntax
  (`tests/solkey/expected.tsv`).
- **The `PreservationNecessity` counterexample** (a duplicated layout root
  checks one stored value against two types, so `nodupKeysB` is necessary),
  removed with the untyped layer; `Typing/StoragePreservation.lean` cites it.

## Sharp edges

- **`Meta.reduce` through indexed families is about 100 times slower.**
  Closed goals are evaluated as compiled code (`evalExpr`) and quoted back by
  hand-written quoters (`Calculus/Quote.lean`); the kernel re-checks.  This
  works only for a contract that is a named constant, and every new syntax
  constructor needs an arm in every quoter.
- **`deriving ToExpr` fails on constructors with proof fields.**  Quote the
  contract as its constant and the proofs as `Eq.refl`.
- **A big overlapping `match` is unusable in proofs** (`simp` and `whnf` time
  out), which is why `Stmt.step` is a total dispatcher.
- **An inner `match` does not refine an index.**  Dispatcher arms need
  top-level patterns, and `if h : ...` rather than `if ...`, so the branch
  fact reaches the proof obligations.
- **`cases` on the indexed syntax** fails with "dependent elimination
  failed" unless the index is generalised first.
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
| Conditions | `if`, `require` and `assert` test a `Simple` value; the elaborator captures any other condition into a fresh `bool` first.  A branch may not declare, so a complex condition nested in a branch is an elaboration error. |
| `T storage x;` | Not a statement: solc 0.5 and later reject an uninitialised storage pointer. |
| Effects inside expressions | `++`/`--` in an expression and a conditional of references are captured by the elaborator before the statement (`hoist`), so `Val` stays effect-free and no rule sees them.  The order is solc's (right operand before left, right-hand side before target, base before index), pinned by `TestSuite.sol`'s evaluation-order functions.  A call in an expression (`x = f(a) + 1;`) is captured the same way, counting as an effect.  An effect or call under `&&`/`\|\|` or in a conditional's branch is an elaboration error.  A decrement is spelled `x--`/`--x` with two U+2212, since `--` opens a Lean comment. |
| What elaborates away | `event`/`error` declarations, visibility and mutability words, ether and time units, `payable(e)`/`address(e)`, `uint256`/`int256` and enums are read by `sol{}`/`contract!{}` and gone before any `Stmt`: no constructor, no rule. |
| `emit`, `require(c, Err(a))` | The log and the error data are dropped, the arguments are not: one that may revert or has an effect is evaluated (captured left to right).  `revert Err(a)` is `revert()`.  Struct constructors lower to a `T memory` local plus member writes. |
| Modifiers | Inlined around each function that applies them (`wrapMods`), the first listed outermost, each parameter a fresh local bound when the modifier is entered.  A `_;` may stand anywhere, several times (the body runs again in the same locals, its parameters and return variable not reset: solc's legacy pipeline), not inside `unchecked`; a modifier without one, a `return` in a modifier and a reference-typed parameter are elaboration errors. |
| Constructors | `constructor(…) { … }` is `Contract.ctor`, not a function, and `uint x = 5;` a root with an initializer (`Contract.inits`).  A deployment is the program `constructor(args);`, a top-level statement only, not in a function's body, a branch, a loop or a block (the reader's `top` flag, cleared by `elabBranch`): the elaborator inlines the constructor as any call (`elabCtor`, `functionBodyExpand`'s `CallRet.rets []`), the initializers prepended after its parameters are bound and before its modifiers, as solkey's `ExpandFunctionBody` does.  No new `Taclet`: the start is an update, solkey's `{storage := mtSt ‖ net := storeSt(mtSt, at(msgSender), msgValue) ‖ selfBalance := msgValue}` (`Problem.deployUpd`, the term `mtSt`), and `Contract.deploy` runs the elaborated program from `Contract.deployState` (it takes the program, since `elabStmts` is `partial` and could not be unfolded inside it).  The obligation owes no `wt(storage)` (`deploy_wt` would be a theorem of its own).  `constant`/`immutable` with an initializer follow solkey in `contract!` (a root with an initializer), and stay a `Gap` in the solc import. |
| `unchecked { ... }` | No `Stmt` constructor: the wrapping `BinOp`s `+% -% *% **%`, which the elaborator (`uncheckStmts`) writes in place of the block's checked ones, so every rule over `op` covers them.  A function called from the block stays checked, as in solc.  On the EVM they are `ADD`/`SUB`/`MUL`/`EXP` with no guard. |
| `**`, bitwise, shifts | `**` is checked `uint` exponentiation (`int ** k` is not ported).  `BinOp.band`/`bor`/`bxor`/`shl`/`shr` and `UnOp.bnot` are solc's at `uint256` (a shift by 256 or more is `0`), `uint` only: two's-complement `int` is not modelled.  No solkey taclet exists and none is added; the rules over `op` cover them.  Their compound forms elaborate to `l = l op e;`. |
| Environment values | `msg.sender`, `msg.value`, `block.timestamp`, `address(this).balance` and `address(this)` (`this` in a formula, the ledger's own account) are a simple value `Simple.env k` (term `Term.env k`), as solkey's `netHeader.key` declares them as program variables; no taclet reads them.  `msg.*` and `block.timestamp` are the state's `tx : TxEnv`, kept by every statement and replaced by a callback (a re-entrant call is its own transaction); the balance is `State.selfBalance`, the funds the transaction found, which `transfer` leaves (it books `net` only, and not at `this`).  On the EVM: `CALLER`, `CALLVALUE`, `TIMESTAMP`, `ADDRESS`, tied to the state by `EnvSim`; `address(this).balance` is not compiled, since `SELFBALANCE` reads the account a `CALL` debits. |

### Semantics

| Question | Decision |
|---|---|
| Modalities | The box is partial correctness (it holds unless the run ends normally in a bad state); the diamond needs a normal end.  Neither tells a revert from a stuck run, so an unfolding rule owes its statement the same successful outcome (`SameOk`), which the order-changing rules meet without side conditions.  `SolidityJudgment.Holds` differs on stuck runs. |
| Array bounds | An index is checked where the program takes the path (`State.checkIndex`), so an update fails as its statement does and a failing update reads as a revert.  `SVal.find`/`save` address slots past the end: an alias checked when bound writes the slot a later `pop` left, as solc does. |
| Memory `delete` of a reference | The location gets a fresh default object (KeY's `memoryFieldDeleteReference`, solc), not a reset of the old one: an alias keeps it. |
| Fixed-size arrays | One `RefTy.fixed E n`, not a length index on `.array`; array rules take an `ArrTy R E` (`dyn`/`fixed`) so one rule covers both, as solkey's `Path[...,array]` does.  `delete` keeps a fixed array's `n` elements (reset) and empties a dynamic one; a fixed array has no `length` slot, and its `.length` is the literal `n`; a literal index `>= n` is an elaboration error.  solkey's delete/`pop` taclets exclude fixed elements; the Lean rules do not, and are sound for them. |

### Calculus and rules

| Question | Decision |
|---|---|
| One rule per statement | Rules carry solkey's taclet names (an operator family is one constructor, not one per operator).  `Taclet` is a `Prop`; uniqueness is stated through `Stmt.step` (`Stmt.complete`, `Rule.eq_step`, `Rule.premise_unique`).  A constructor carries as hypotheses exactly the facts its `Stmt.step` arm establishes, read off its schema variables by name and position (`RuleSyntax.sideConds`, `autoParam`ed with `side_cond`, hidden by the printers), so a taclet is still one `dl{ }` line.  Where solkey leaves two taclets open and its strategy picks, the side condition keeps the one `Stmt.step` picks (`Val.notTernary`, `Loc.isTarget`, `MPath.isBindable`). |
| Where the kernel follows KeY over the old table | A state variable operand is captured (`binopUnfoldLeft`), since it is a path, not a `SimpleExpression`.  A compound target is an `OpLoc` at a simple index (`values[i + 1] += 1;` captures the index first; `Upd.opSave` reads the source first, as `Stmt.run` does).  A `y = nsp.f++;` receiver is captured by KeY's `storageLocalDeclInitDrop`, not a Lean-only alias rule.  A memory reference from a member is `memoryFieldWriteCopy` from any bindable source: solkey's `..._rightSndResult` captures first, which is incorrect where the slot holds a reference.  Per-rule detail is in `docs/lean-key-rule-map.md`. |

### Calls and callbacks

| Question | Decision |
|---|---|
| Where a callee's body lives | In the call (`Stmt.call ... body`), with every callee local renamed fresh (`renameStmts`), not looked up in the contract: a contract holding `Stmt` bodies indexed by itself is an inductive-inductive type Lean lacks.  The contract keeps the body as read (`FunDecl.body`); the elaborator types and inlines it at each call.  `Stmt.run` is structural with no rank certificate, and the elaborator is the only author of a call's body.  A function calls only the functions declared before it, so inlining ends; a recursive call is an elaboration error. |
| Binding arguments | One after another (`Arg.bindSeq`), so `internalCallExpand` and `functionBodyExpand` are exact.  solc reads every argument before the call; the two agree because a call is separated (`Arg.separatedFrom [] args`), which the elaborator's fresh parameters guarantee.  The capture rule takes the leftmost argument that is not simple: a criterion the capture could re-trigger would loop at an index that is not fresh, and `Fml.step_decreases` holds at every index. |
| `return` | Anywhere in a body, lowered away by the elaborator (`lowerReturns`, run on a callee's body after its locals are renamed) rather than as an abrupt completion in `Stmt.run`.  What follows a `return` is dead; the statements after an `if` with a returning branch move into the other branch.  A moved statement naming a branch's own declaration is an elaboration error.  A callee's `return` ends the callee only. |
| Callback semantics | A relation over `Stmt.run` (`ExecS`/`ExecP`), not a second interpreter: every statement but a transfer, a branch and a call is `Stmt.run`'s, so the relation cannot drift.  A transfer halts, leaves the invariant broken (an outcome no formula accepts), or resumes in `State.havoc` (storage and ledger replaced; locals, memory and funds kept, as solkey `0b885c229d` keeps `selfBalance`) satisfying it. |
| Callback taclets | A second inductive `CallbackTaclet`, not `Taclet` constructors: `Taclet.sound` is against `Stmt.run`, and one-rule-per-statement would break.  The box constructor as in solkey (the diamond is not ported); the resume premise is a second sequent under `{havoc}` (KeY's anonymising update). |
| The invariant | An `Invariant C` is a formula with no local and no transfer (solkey's `CInv(storage, net)`); the frame lemmas need it closed.  It may read the ledger, which a callback havocs, and `address(this).balance`, which it keeps (`State.havoc`). |
| `ProvesC` | The ordinary taclets lift on a statement that pays nothing and runs no other, and whose premise pays nothing; a goal with no transfer left is `Proves`'s (`holdsC_iff_holds`).  Validity with callbacks implies validity without (`valid_of_validC`). |
| External calls (`try`) | The callee is never run.  Without callbacks how a call ends is the transaction's (`TxEnv.ext`, a table read by `Stmt.run`, which no formula reads); a call with no entry reaches an address with no code and reverts in the caller, and so does data that does not decode (`bindData`).  `tryCallNoCallbackBox` has a goal per clause, for every value of the locals it binds (`Premise.branches`, `Fml.alls`), so a proof holds whatever the table says.  With callbacks a `try` is a point where control leaves (`Stmt.hasTransfer`), and `ExecS` runs it nondeterministically, its success from a `havoc`ked state keeping the invariant. |
| Function contracts | A derived rule over `Stmt.run`, not a `Proves` constructor (`Calculus/Contracts.lean`): `useContract` has KeY's goals "pre" (`[ params := args ] requires`) and "post" (`[ params := args ] {old := storage ‖ oldNet := net} {havoc} ∀ T r. (ensures → [ res = r; ..ω ] φ)`), box only, its conclusion `⊨`, so it applies at the first statement of a goal.  A contract is a fact about the callee's block from any state (`FunContract`), proved from its obligation `requires → {old := storage ‖ oldNet := net} [ T r; body ] (ensures ∧ typed(r))` (solkey's planned `requires -> [g(args)@C] ensures`, no invariant); it owes the result's type (`rangeFml`), as `∀ T r` ranges over the type.  The mutability is read off the inlined body, since `FunDecl` keeps no `pure`/`view` (only `payable`) (`Semantics/Mutability.lean`): `pure` (a `view` body that reads no state, with the same frame) and `view` keep storage and ledger, so "post" has no `{havoc}`; `nonpayable` (storage writes, `transfer`) gets `State.havoc`'s.  A body with memory, a push, a pop, an alias or a `try` has no mutability, hence no contract: "post" havocs no heap.  The callee's parameters are the call's fresh names, so a contract is stated at a call; recursion stays out. |

### `send`

| Question | Decision |
|---|---|
| How a send ends | Asked of the transaction, as a `try`'s ending is: `Semantics.sendAt` reads `TxEnv.ext` at `sendKey a v` (empty calldata, the amount as the one word).  No entry or `ok` books the payment as `transfer` does and sets `pv` true; any other entry books nothing and sets `pv` false.  No new field: the oracle a `try` already reads.  Always-succeeding would prove `ok == true`, false on the EVM. |
| The statement | `Stmt.send pv r a`, `pv` a `bool` local, beside `Stmt.transfer`.  `bool ok = r.send(a);` elaborates as `bool ok; ok = r.send(a);`: `valueDeclSkip` where solkey fires `localValueDeclInitDrop` (same node count; the default is set, then overwritten by the send); a bare `r.send(a);` does not parse, as solkey has no rule for it. |
| Labelled goals | `Premise.cases fs us`: each formula of `fs`, then `{U} ⟨[ ..ω ]⟩ φ` for each update, read as one conjunction (`Premise.fml`) and as `Proves.cases`'s two hypotheses.  `Premise.Correct` asks that the run be one of the updates; the formulas are extra goals.  `Derive.casesGoals` lists the goals by recursion, with no `List.append` for `decide +kernel`. |
| The diamond | Ported (`sendNoCallbackDiamond`), unlike `transfer`'s: a refusal is an outcome of the run.  Its "non-negative amount" goal is solkey's and not needed for soundness (the booking halts on a negative amount). |
| With callbacks | A send is a point where control leaves (`Stmt.forks`, `Stmt.hasTransfer`).  `ExecS` books it as the transfer of its amount and then halts where that does, leaves the invariant broken, resumes in a `havoc`ked state keeping it with `pv` true, or fails with nothing booked and `pv` false (`sendFailed`), the last whatever the oracle says: a callee may always revert.  `ProvesC.send` reads `CallbackTaclet.sendWithCallbackBox`'s premise as solkey's three goals, sound by `CallbackTaclet.sound_send`; the ordinary send rules do not lift (the statement forks).  `Examples/Tactics/Callback.lean`'s `callToKeepsInv` is `PiggyBankNet.callTo` under a storage invariant. |
| Cost | `Stmt.run` and the proofs by cases on it grow by one arm; `TestSuite/Derived1.lean` re-checks in 7.7 s on a fresh worker on this branch and on master alike. |
| A ledger read past a storage write | `Modality.wp_box_saveStorage` also hands the closer `τ.net = σ.net`, so `net-send-simple.key`'s `sendTo`, which stores the outcome (`sent = ok;`), closes as solkey states it (`Net.netSendSimple`), and so does `[ to.transfer(5); total = 1; ] net(to) = 2` (`Net.netTransferThenStore`).  Re-checks after it, on fresh workers: `Examples/Tactics/CrossDomain.lean` 54 s and `Memory.lean` 52 s (the `lean-verify` skill lists 75–90 s for each), `StorageSuite.lean` 21 s.  The `TestSuite/Derived*` replays close their leaves inside the residue and do not use the lemma. |
| Review (2026-10-06) | Fixed: sort rows for the four send taclets that read `net` (`SortCheck/Annotations.lean`, 119 rows; `solkeycheck`'s check, run as an `#eval` of `conforms`, is at zero against `1b4341a303`, and four rows ahead of the `100f7f24c3` pin); the corpus rows `net_send_simple` (proved) and `net_call_withcallback_simple` (unsupported: no tuples yet) in `tests/solkey/expected.tsv` and `docs/corpus-parity.md`, from `1b4341a303`'s `net/` (the header stays at `78f42fde33` until the TestSuite fixture is re-imported); `PiggySend.sendTo` keeps `sent = ok;`; `sol_derive?` prints a send's goal split on its `apply` line (`apply cases … <;> (try simp only […]) <;> (try and_intros)`), so a replay touches only the rule's goals, pinned with `sol_prove?` in `Examples/ProofTree.lean`; `#taclet` cites `upd_send_cases`, pinned in `Examples/Tools.lean`; the unfold rules pinned in `Payment.lean`; bare `simp`s of the lane replaced by `simp only`. `(bool ok, ) = a.call{value: v}("")` waits for tuples. |

### Specifications

| Question | Decision |
|---|---|
| Specifications | Compiled as solkey compiles them (`Calculus/Spec.lean`): a clause reads a storage term, `\old(count)` is `find(old, count)` with `old` a storage variable bound by `{old := storage}`, and `\forall T x; e` is `Fml.all` over `PrimTy.admits` (so a quantified invariant is not `closed`).  Lean adds two premises solkey's total typed reads need not: each parameter's range and the layout of the state the clauses read (`layoutFmls`).  `sol_decide` keeps `find(old, p)` and leaves `\forall` outside its fragment. |

### Several returns, tuples and blocks

| Question | Decision |
|---|---|
| Several returns | `FunDecl.rets`, a list (unnamed returns are `_ret`, or `_ret0`, `_ret1`, …, where solkey's `ExpandFunctionBody` names every unnamed return `ret{i}`, a single one `ret0`; `FunDecl.ret` is the one return of a function that has one).  A call with targets (a tuple assignment's, an obligation's) carries `CallRet.rets`: each return variable declared at its type's default on entry (solc zeroes them; KeyTaclets' `R ri;` leaves them unconstrained), nothing assigned on leaving; a bare `f(a);` carries `CallRet.none` and declares the returns at the head of its body.  The targets are ordinary statements after the call, `t = r;`, solkey's `function-frame{…} t0 = r0;` without the frame; the printers write the call and them as the tuple assignment (`Stmt.tupleCallStr?`).  Only value types: `memory` on a return of several is an elaboration error.  `Stmt.run` is unchanged (`CallRet.enter`/`leave`). |
| Tuples | Desugared by the elaborator as `ParserUtils.tupleAssignment` does (`elabTuple`): from a call, the call then the targets left to right; from a tuple, each component with a target into a fresh temporary, then the targets, so `(a, b) = (b, a);` swaps; a declaration `(uint a, , bool b) = …` declares its variables first and assigns them directly.  A component left out is dropped when it can neither revert nor have an effect, and evaluated otherwise (solc; solkey keeps only a call and drops the rest).  Targets that may alias (the same name twice, two that are not stack locals, one that reads another) are refused until solc's order of their writes is checked. |
| `return (e₀, e₁)` | `lowerReturn`: each return variable assigned in order, or, when a component reads a return variable (solkey's `ReturnLowering`, `returnSwapped`), the tuple assignment `(r₀, r₁) = (e₀, e₁);`, which reads every component first.  **Lean only:** `return g();` of several values is the tuple assignment `(r₀, r₁) = g();`, which solkey's `ReturnLowering` refuses (one value for several returns). |
| Blocks | `{ … }` is `RawStmt.block`, elaborated as a branch (its declarations scoped to it) and spliced flat.  A block with a `return` inside is spliced into the statements after it before `lowerReturns` moves them (solkey's `blockReturn`), under the same guard as an `if`: a statement after it may not name one of its declarations.  There is no block, frame or `return` left in `Stmt`: `blockReturn`, `functionFrameReturn` and `functionFrameEmpty` have nothing to rewrite. |
| `return` inside a loop | Lowered through a flag local, as solkey's `LoopLowering` does (`lowerLoops`, `docs/loops.md`): `r = e; ret = true;`, the loops' conditions and the rest of their bodies guarded by `!ret`, and `if (ret) return;` after the outermost loop, which `lowerReturns` lowers as any early `return`.  `lowerReturns` alone cannot: inside a loop the rest of the body and the remaining iterations would have to move, which no rewrite of the body can do.  Not an early-exit outcome in `Stmt.run` (rejected: Frame rules, below). |
| No recursion | A function calls only the functions declared before it, so inlining ends; this lane adds none. |
| Two call rules | solkey `671f6762a9` splits KeY's call into `InternalCall` (`f(a);`, `y = f(a);`: `internalCallExpand`) and `FunctionBodyStatement` with targets (a tuple assignment's call, a synthesized obligation's `result = f(x̄)@C;`: `functionBodyExpand`).  Lean keys the split on the call's `CallRet`: `CallRet.rets` (the call returns to targets after it) is `fbs`, anything else `ic` (`CallRet.isRets`, a side condition of each; `callStep` picks by it, so `Uniqueness` stays one rule per statement).  A bare call of a function of several returns, `f(a);`, is an `InternalCall` in solkey; here it declares the returns at the head of its body and carries `CallRet.none` (`elabCallRet`), so it is `ic` too.  Both rules have the same premise, `expand_function_body`, and the same soundness (`Stmt.run_call_expand`).  Like `functionBodyExpand`, `internalCallExpand` waits for simple arguments (`functionCallArgCapture` first, decision D3), where KeY's binds `T p = arg` as written. |
| Specification obligations | Elaborated as solkey's synthesized `result = f(x̄)@C;` (decision D1): `T result;` then a call that returns to `result` (`CallRet.rets`; a void function's `f(x̄)@C;` returns to no target, `CallRet.rets []`), so the obligation fires `functionBodyExpand` as solkey's does.  **Lean only:** `T result;` is a statement of the box (one more node, `valueDeclSkip`), where solkey declares `result` among the problem's program variables; the sequent prints it `result = f(x̄);`.  A function of several returns returns to `result_<name>` (`SpecCompiler.resultVariable`), printed `(result_lo, result_hi) = f(x̄);`, and an `ensures` names a return by its name after the locals and before the state variables (`SpecCompiler.visitIdent`); `\result` needs one return.  **Lean only:** a function with an unnamed return has an obligation (its return is `result`, or `result__ret0`, … of several), where solkey refuses one (`SolidityOutline.unsupportedReason`). The tree has the same nodes as before but for the rule's name: `result = r;` was the call's own last statement (`CallRet.result`) and is now the statement after it. |
| Printing a call with targets | `ppTupleCall?` (`Calculus/RuleSyntax.lean`) prints a `CallRet.rets` call and the target assignments after it as the tuple assignment, as `Stmt.tupleCallStr?` does for `Prog.toStr`.  With two targets or more the printed tuple re-elaborates to the same call (up to the elaborator's fresh names, which a chain line cannot pin; no chain runs a tuple call); `y = f(x̄);` and `f(x̄);` print an `fbs` as the `ic` they re-elaborate to (solkey tells the two apart by `@C`). |
| Frame rules | `blockReturn`, `functionFrameReturn`, `functionFrameEmpty` are architectural, like `blockEmpty`: returns are lowered at elaboration (`lowerReturns`), and a call's body is spliced flat, so there is no block and no frame to rewrite.  A faithful `function-frame` (an abrupt `return` completion in `Stmt.run`) would undo decision `978083b` and rewrite `Res`/`Halt` and every soundness, Typing, NoPanic, Callback and Evm proof.  **User decision (2026-10-06): an early-exit outcome in `Stmt.run` is rejected** in favour of lowering (`lowerReturns`) plus flags (a `return` that cannot be moved, as in a loop, lowered through a flag local); `RuleShapes.unclaimedTaclets` lists the three beside `blockEmpty`. |
