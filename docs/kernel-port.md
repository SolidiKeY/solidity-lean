# Porting mini-solkey into solidity-lean

mini-solkey (`~/projects/side-projects/lean/mini-solkey`) is a readable copy
of the storage part of this package that got guarantees this package did not
have: typed syntax, one inductive rule judgement, completeness with no
residue, a sound sequent calculus.  Its design was ported **in place**: the
typed syntax replaced the untyped AST, the taclet judgement replaced the
`sol_rule` table, and the old layer (the untyped interpreter, `RuleName`,
the `⇝` block rewriting, `sol_derivation`, `seq!`, `sol_wp`, the EVM
compiler, the type-soundness theory) was removed.  An earlier parallel
`Solidity/Kernel/` was the staging area; it is gone.  mini-solkey stays the
reference for the shape of every declaration.

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
| `Ch08_EVM`–`Ch10_Correctness` | `Evm/` (`docs/compiler-verification.md`) |
| `Ch11_Completeness` | `Calculus/Completeness.lean` (`Stmt.step`, `Stmt.complete`), `Calculus/Progress.lean` |
| `Ch12_Termination` | `Calculus/Termination.lean` |
| `Ch13_Chains` | `Calculus/Chains.lean` |
| `Ch14_Updates` | `Calculus/UpdateRules.lean` |
| `Ch15_Decide` | `Calculus/Decide.lean` (the storage fragment) |
| `Examples/` | `Solidity/Examples/` |

Beyond mini-solkey: type soundness and reachability (`Typing/`), sort
faithfulness (`SortCheck/Faithfulness.lean`), the solkey corpus
(`SolidityCorpus`, `docs/corpus-parity.md`), and the `SolKey` reader's
correspondence against `Taclet` (`~/projects/side-projects/lean/solkey`).

## Still open

- **Calls, beyond the fragment**: parameters and return values of reference
  type (`Person storage p`, `uint[] memory xs`), an early `return` (only the
  body's last statement, or the last of each branch of a last `if`, may
  return), a call inside an expression (`x = f(a) + 1`; KeY writes a call as
  a statement or a whole right-hand side, `res = f(a)@C;`), external calls,
  `msg.*`.
- **Callbacks, beyond the invariant**: an invariant over the ledger `net`
  (no term reads it, nor `selfBalance`), so solkey's `net/*-withcallback.key`
  problems stay unported; the capture rules of a transfer
  (`transfer_unfold_*`), a branch or a call around a transfer have no rule of
  `ProvesC` (their soundness under the callback reading is not proved), and
  `ProvesC` has no strategy (`sol_symex` is the no-callback reading's).
- **The corpus is not regenerated** since the syntax gaps below closed:
  `scripts/solkey-port.mjs` no longer refuses `--`, `.length`, `new`, an
  `++` inside an expression, `**` and `T[n]`, and `docs/corpus-parity.md`
  counts the old verdicts until `--probe` re-pins them.  `TestSuite`'s
  `boolKeyed` (a `bool`-keyed mapping: the interpreter reads keys as `Int`)
  and `tree` (a struct recursive through a mapping, which `structRank`
  forbids) are still not declared.
- **`Ch15`'s realizability**: `sol_decide` is sound, not proved complete —
  constraints between reads of the starting storage (shapes, bounds,
  `length`) are not stated; memory, copies, `push`/`pop` are outside its
  fragment.
- **The converse of reachability** (every canonical storage is reachable).
- **The EVM fragment**: `int`, `**` (needs a loop), memory,
  storage-to-storage copies, `push`, `v = x++;`
  (`docs/compiler-verification.md`).

### Closed: calls and the callback semantics of `transfer` (2026-09-27)

- A `Contract` declares its internal functions (`contract!{ function f(uint x)
  returns (uint r) { … } }`, `FunDecl`): typed parameters, an optional return,
  the body as read.  A call (`f(a, b);`, `y = f(a);`, `uint y = f(a);`) is
  `Stmt.call`, which carries the callee **inlined**, as KeY's
  `FunctionBodyStatement` carries its declaration: the parameters bound to the
  arguments, the return variable and where its value lands, the body — every
  callee local renamed fresh by the elaborator, its tail `return e` an
  assignment to the return variable.  `Stmt.run` recurses into the body
  structurally.
- Taclets `functionCallArgCapture` (`unfoldArgument`, Lean-only)
  and `functionBodyExpand` (KeY's `expand_function_body`), with `Stmt.step`,
  `eq_step`, termination (`Arg.weight`), soundness, typing, reachability, the
  EVM (a call compiled inlined, `argsCode`) and `Examples/Calls.lean`.
- The callback semantics: `Semantics/Callback.lean` (`ExecS`/`ExecP`, a
  relation over `Stmt.run` through branches and calls; `holdsC`; `TransferSem`
  and `holdsT`), `CallbackTaclet` with `transferWithCallbackBox`/`Diamond`
  (claimed by `RuleShapes.callbackOrigins`, `PrintedRules.callbackPrintedOrigins`),
  `CallbackTaclet.sound`, the judgement `ProvesC` and `ProvesC.sound`
  (`Calculus/Callback.lean`), and `Examples/Callback.lean`.

### Closed: the syntax gaps of the corpus (2026-09-27)

- `.length` of a storage or memory array is a value (`Val.len`, `Val.mlen`,
  carrying `p = .uint` so that no match refines an index): KeY's member reads
  at `length`, `storageLengthRead`/`memoryLengthRead` and their unfolds.
- A decrement is spelled `x−−`/`−−x` (two U+2212), `IncDec.preDec/postDec`.
- `++`/`−−` inside an expression, and a conditional of references, are
  captured by the elaborator before their statement, in solc's order
  (`hoist`, `captureExpr` in `Syntax.lean`): values stay effect-free.
- A negative literal takes the type it is checked at (`int e = -5;`).
- Memory `delete` (`Stmt.deleteMem`) with KeY's eight taclets; `new T[](n)`
  (`MRhs.newArr`, `Stmt.assignNew`) with `memoryArrayFreshAlloc` and
  `newArrayCapture`.

### Closed: fixed-size arrays and `**` (2026-09-27)

- `RefTy.fixed E n` (`T[n]`), in storage and memory, through typing,
  reachability, the sort check, the calculus, `sol_decide` and the compiler.
  The array rules cover both kinds through `ArrTy` (`IndexTy.arr ak`), as
  solkey's `Path[…,array]` sorts do; `push`/`pop` stay at `.array`.
- `**` is checked `uint` exponentiation (`BinOp.pow`), right-associative and
  tighter than `*`, as in solc; its taclets are the `binopAssignment` family's.

## Sharp edges

- **`Meta.reduce` through indexed families is about 100× slower.** mini-solkey
  evaluates closed goals with `evalExpr` and quotes them back with hand-written
  quoters; the kernel re-checks. This only works for a contract that is a
  named constant, and every new syntax constructor needs an arm in every
  quoter.
- **`deriving ToExpr` fails on constructors with proof fields.** Quote the
  contract as its constant and proofs as `Eq.refl`.
- **A big overlapping `match` is unusable in proofs**: `simp` and `whnf` time
  out. That is why `Stmt.step` is a total dispatcher.
- **An inner `match` does not refine an index.** Dispatcher arms need
  top-level patterns, and `if h : …` rather than `if …` so the branch fact
  reaches the proof obligations.
- **`cases` on the indexed syntax** fails with "dependent elimination failed"
  unless the index is generalised first.
- **Notation**: the concrete `dl{}` needs `priority := high` over the schematic
  one; the chain macro builds applications with `Syntax.mkApp` (in a quotation
  `$a $b` reads `$b` as an arrow); `dl_fml`/`dl_term` need category
  parenthesizers, or `dl{ a = b } ~> ψ` prints with parentheses.
- **Shape blow-up.** Storage × memory × stack × arrays multiplies the shapes.
  The `Kind`-indexed classes (`EClass`, `LClass`, `PClass`) are what kept
  mini-solkey's `decide` small; `decide +kernel` over thousands of shapes may
  still be slow, so measure before committing to one `Shape.all`.
- **Broken builds hidden by pipes.** A commit was once pushed while the build
  was red because `lake build | tail` hid the failure. Check the exit code.

## Decisions

| Question | Decision | Date |
|---|---|---|
| Rule names | solkey's taclet names (§5) | 2026-09-25 |
| `native_decide` | forbidden in `Solidity/Kernel/`; old files keep their count | 2026-09-25 |
| Struct bodies | stay the package-wide `Semantics.structDef`, which the interpreter reads; a `Contract` is its storage roots only, and `Contract.fieldType` reads the table. A per-contract table would let a contract disagree with what runs. Revisit in phase 7, if the interpreter is made contract-parametric | 2026-09-25 |
| Context index | a statement is `Stmt C Γ Γ'`, indexed by the local context `stmtWt` threads, and each name carries its `Γ` binding (a root, `lookupBy r Γ = none` too). That is what makes `Prog.erase_wt` hypothesis-free: without the index a typed term could use `x` at two types, and only a predicate could rule it out | 2026-09-25 |
| Declarations | a declaration introduces a fresh name (`isFresh`: neither a local nor a state variable), so contexts only grow and a name fresh at `Γ` occurs in no term typed at `Γ`. That is the freshness the untyped rules assume per rule (`stmtUsesVar … = false`); here it is typing | 2026-09-25 |
| Scratch names | a taclet takes its scratch names as parameters with freshness proofs; the elaborator and `Stmt.step` pick `se`, `sp`, `ie` first, so on a program that does not use them the residual erases to the rule table's own | 2026-09-25 |
| Conditions | `if`, `require` and `assert` test a `Simple` value; `ksol` captures any other condition into a fresh `bool` first (`ifElseUnfold`, `requireConditionCapture` are the elaborator's). A branch still may not declare, so a complex condition nested in a branch is an elaboration error | 2026-09-25 |
| `T storage x;` | not a kernel statement: solc ≥ 0.5 rejects an uninitialised storage pointer (`storageLocalDeclSkip` has no kernel counterpart) | 2026-09-25 |
| Semantics | kernel terms get a structural denotation, proved to be the interpreter's (`Prog.run_eq`); taclets are proved sound over it, not through the untyped `*_sound` theorems, whose scratch names are fixed strings | 2026-09-25 |
| Array bounds | no `inBounds` split: an index is checked where the program takes the path (`State.checkIndex`, from `Loc.resolve` and `PTerm.at`), so the kernel's update fails as the statement does, and a failing update is read like a revert by the modalities. `SVal.find`/`SVal.save` address slots, past the end included: an alias checked when bound writes the slot a later `pop` left (solc, solkey `f2eb3d98eb`) | 2026-09-27 |
| Typed states | not needed: `Premise.Correct` is over every state. The short-circuit rules re-apply the operator to the value they read (`v = nse; v = v && true;`), so a non-boolean read is stuck in the premise as in the original. `Kernel.Typed` and `Val.eval_bool` stay for later use | 2026-09-25 |
| Operator families | a rule over an operator is one constructor (`binopAssignment op`), as in `Calculus/Rules.lean`; solkey's taclet is per operator | 2026-09-25 |
| Continuations | an unfolding rule's residual binds scratch names fresh at the statement's context; to retype the rest of the program past them, the names must also avoid what the rest declares. The formula-level step picks them avoiding both, and `Prog` weakens along an extension that names its new bindings | 2026-09-25 |
| Goals | a goal is `H ⊢ k`: hypotheses (path conditions and updates, a predicate transformer) and a continuation (`⟨P⟩ k`, `up h k`, a postcondition). An unfolding rule's premise is `⟨P⟩ up ⟨ω⟩ k`; the frame lemmas make that sound, and the scratch names need not avoid what `ω` declares. A diamond split also owes the condition's definedness (`c || !c`), and a closed box owes `H ⊢ true`: an update that fails under a diamond hypothesis is false | 2026-09-25 |
| `Taclet` in `Type` | a derivation is data: `Taclet.rule`/`Taclet.origin` read its constructor. In `Prop` they could not, and proof irrelevance would identify two rules deriving the same premise. `Stmt.complete` is `∃ pr, Nonempty (Taclet …)` | 2026-09-25 |
| State-variable operand | `x = total + 1;` captures `total` (`binopUnfoldLeft`), as KeY's `addition_unfold_left` does: a state variable is a `Path[storage,simple,primitive]`, not a `SimpleExpression` (literal or program variable). The old table's `s` admits it and fires `binopAssignment`; the kernel follows KeY | 2026-09-26 |
| Storage declaration, unbindable path | `Person storage r = persons[x + 1];` captures the index first (`Hole.decl`). KeY's `storageLocalDeclInitDrop` drops any initializer to an assignment, and so does the old table; the kernel has no `T storage x;` to drop to, so it fuses the drop with the rebind and needs the path bindable | 2026-09-26 |
| Compound target | `OpLoc`: a local, a state variable, a member, or an entry at a *simple* index. The old table is stuck on `values[i + 1] += 1;` and solkey has no taclet for it; `ksol` captures the index into `ie` first, as it does a condition. The update `Upd.opSave` reads the source first, as `execStmt` does, so the terminal rules are exact; no `?=` freeze in the unfolds, a kernel value having no effects | 2026-09-26 |
| `y = nsp.f++;` | the assignment form takes a target whose receiver is simple (`OpLoc.recvSimple`): neither solkey nor the old table has an unfold for it. `ksol` captures the receiver into a scratch `sp`, which the old table would bind by its Lean-only `storagePlaceAlias` and the kernel binds, as KeY does, by `storageLocalDeclInitDrop` (the bridge tour's fourth disagreement) | 2026-09-26 |
| Memory reference from a member | `mp.account = mq.account;` is `memoryFieldWriteCopy` from any *bindable* source. The old table (and solkey's `memoryFieldRead_unfold_rightSndResult`) first captures the member into a scratch `T memory se = mq.account;`, which requires the slot to hold a reference; the interpreter copies a reference slot as it is, so over every state the capture is not correct. The two `…_rightSndResult` memory rules are not kernel rules (the bridge tour's memory disagreements) | 2026-09-26 |
| Overlapping taclets | where solkey leaves two taclets open on one statement and its strategy picks, the kernel adds the side condition that makes `Stmt.step`'s choice the only one (the removed staging area's Unique.lean): `sp.f = c ? a : b;` is lowered, never captured (`Val.notTernary`); `folks[1].account = folks[2].account;` unfolds its target first (`Loc.isTarget` on the source unfolds); a memory reference unfolds its target first too, and is written as it is only from a bindable source (`MLoc.isTarget` on the source unfolds, `MPath.isBindable` on `memoryFieldWriteCopy`/`memoryIndexWriteCopy`) | 2026-09-26 |
| One rule per statement | every statement has exactly one rule (`Stmt.complete`, `Taclet.eq_step`, `Taclet.premise_unique`). Each constructor carries as hypotheses exactly the facts its `Stmt.step` arm establishes: read off its schema variables by `RuleSyntax.sideConds` — by name (`nsp`/`nse`/`nadr`/`nmp` not simple, `sp`/`map`/`arr` simple, `loc` a member or entry at a target) and by position (a hole `lhs` lands in a target, a value written to storage or memory is not a conditional, a memory reference written is bindable) — `autoParam`ed with `side_cond` and hidden by the printers, so a taclet is still its one `dl{ }` line and `apply unfold .r` discharges them. A copy source that need not be simple is spelled `path` (the `StorageRef` unfolds, `storagePushValueCopySource`); `binopUnfoldRight`'s `hsc` is one of them. `pop` and a memory element write name their element type (`E`, `p`) so that the premise's scratch alias or value has it: two derivations cannot differ in a type the statement does not fix | 2026-09-27 |
| Modalities | the kernel's box is partial correctness (it holds unless the run ends normally in a bad state) and its diamond needs a normal end; neither tells a revert from a stuck run. An unfolding rule then owes its statement the same *successful* outcome (`SameOk`), which the order-changing rules (`*StorageRef_unfold_leftFst`, `*NonSimpleIndexCapture`) meet without the side conditions the untyped `*_sound` theorems carry. `SolidityJudgment.Holds` differs on stuck runs ("a stuck execution validates nothing"); the phase-7 bridge must say so | 2026-09-25 |
| Unknown names | an error: parameters are declared locals. mini-solkey reads an unknown name as a `uint` parameter | 2026-09-25 |
| Ported contracts | one named constant per interpreter store, `initStorage_*` checks roots, order and defaults against the store by `simp` | 2026-09-25 |
| Decrement spelling | `x−−`, `−−x` (two U+2212 MINUS SIGN): `--` opens a Lean comment, and `x -= 1` is another statement (`opAssign`, other taclets). The printers write it back the same way | 2026-09-27 |
| Effects inside expressions | `++`/`−−` in an expression and a conditional of references are captured by the elaborator before the statement (`uint se1; se1 = i++;`, a branch binding a fresh alias), so `Val` stays effect-free and no rule sees them. The capture order is solc's (right operand before left, right-hand side before target, base before index), which `TestSuite.sol`'s evaluation-order functions pin; an effect under `&&`/`||` or in a conditional's branch is an elaboration error | 2026-09-27 |
| Fixed-size arrays | one `RefTy.fixed E n`, not a length index on `.array`; the array rules take an `ArrTy R E` (`dyn`/`fixed`), so one rule covers both kinds, as solkey's `Path[…,array]` does. `SVal.array`/`MObj.array` carry a `fixed` flag: `defaultOf`/`delete` keeps a fixed array's `n` elements (reset) and empties a dynamic one; `overlay` takes the new value's flag; a fixed array has no `length` slot (`find` of `length` is stuck). `.length` of one is the literal `n` the elaborator writes (an indexed base is captured first); a literal index `≥ n` is an elaboration error. solkey's delete/`pop` taclets exclude fixed elements (`noFixedArrayElement`); the Lean rules do not, and are sound for them | 2026-09-27 |
| `sol_decide` and fixed arrays | a delete below a key is exact three ways (`KShape`: a mapping keeps its entries, a fixed array keeps its length, anything else resets), `delBelow` guarding on the read shape with `LTerm.orElse`; `sol_decide_reads` splits the storage reads a residual still depends on | 2026-09-27 |
| Fixed arrays on the EVM | solc's inline layout: `n · size E` slots, element `i` at `slot + i·size E`, no length slot, constant bound check (`fixedCheck`). `tyRank (T[n]) = tyRank T + 1` so that `size` recurses | 2026-09-27 |
| `**` | `uint` only (`BinOp.accepts`), checked with the other arithmetic; `int ** k` is not ported. Not compiled: solc's `checked_exp` is a loop | 2026-09-27 |
| `TestSuite` state | `Triple` is `FixedTriple` in Lean (`solkey-port.mjs`'s `STRUCT_RENAMES`); `boolKeyed` and `tree` are not declared | 2026-09-27 |
| `.length` | a `Val` (`len`, `mlen`) whose result type is carried as a proof `p = .uint`, not an index: a constructor fixing the index would have to be refined in every inner `match` of `Stmt.step` | 2026-09-27 |
| Memory `delete` of a reference | the location gets a fresh default object (KeY's `memoryFieldDeleteReference`, solc), not a reset of the old one: an alias keeps it | 2026-09-27 |
| Where a callee's body lives | in the call (`Stmt.call … body`), not looked up in the contract: a contract holding `Stmt` bodies indexed by itself is an inductive-inductive type Lean does not have. The contract keeps the body as read (`FunDecl.body : List RawStmt`); the elaborator types and inlines it at each call. So `Stmt.run` is structural with no rank certificate, and nothing in the kernel ties a call's body to the declaration (the elaborator is its only author) | 2026-09-27 |
| Recursion | a function calls only the functions declared before it (`ElabM` reads the visible ones): the declaration order is the rank, as `structRank` is the struct table's, and inlining ends. A recursive call is an elaboration error | 2026-09-27 |
| A callee's locals | renamed fresh at each call (`renameStmts`, numbered as captures are: `se`, `sp`, `mv`), so running the inlined body in the caller's locals is running it in a frame of its own, and a printed goal reads back | 2026-09-27 |
| Binding arguments | one after another (`Arg.bindSeq`), exactly as the inlining declares them, so `functionBodyExpand` is exact; solc reads every argument before the call, and the two agree because a call is **separated** (`Stmt.call`'s proof `Arg.separatedFrom [] args`: no argument that is not simple reads a parameter bound before it), which the elaborator's fresh parameters always are. That also makes the capture of an argument before the call sound | 2026-09-27 |
| Capture of an argument | the leftmost argument that is not *simple* (not "ready": a simple local named like a parameter is bound as it is). Capturing by any criterion the capture itself could re-trigger would loop at an index that is not fresh; `Fml.step_decreases` is proved at every index | 2026-09-27 |
| `return` | a function's body may end in `return e;` (or end in an `if` each branch of which ends so), lowered to an assignment to the return variable (named `_ret` when the declaration does not name it): KeY's named return, and no abrupt completion in `Stmt.run`. An earlier `return` is an elaboration error | 2026-09-27 |
| Calls on the EVM | compiled inlined: arguments stored in their parameters' cells, the return variable zeroed, the body, the result copied (`argsCode`, `retEnterCode`, `retLeaveCode`); `stmt_sim`'s case is proved | 2026-09-27 |
| Callback semantics | a relation over `Stmt.run` (`ExecS`/`ExecP`), not a second interpreter: every statement but a transfer, a branch and a call is `Stmt.run`'s (`det`), so the relation cannot drift from the interpreter. A transfer halts, leaves `I` broken (`violated`, an outcome no formula accepts), or resumes in `State.havoc` (storage, ledger, funds replaced; locals and memory kept) satisfying `I` | 2026-09-27 |
| The contract invariant | an `Invariant C`: a formula with no local and no transfer (solkey's `CInv(storage, net)`); the frame lemmas need it closed. It cannot read the ledger: no term does | 2026-09-27 |
| Callback taclets | a second inductive `CallbackTaclet`, not `Taclet` constructors: `Taclet.sound` is against `Stmt.run`, and `Stmt.complete`/`eq_step` say one rule per statement; with callbacks a transfer's rule is the callback one. Two constructors, as solkey's, each premise the booking update read twice: `{U} I` (under the diamond the booking must succeed: "sufficient funds") and `CbResume`, the rest from every havocked state satisfying `I` — a proposition, as KeY's skolem symbols are, since the havoc is no term | 2026-09-27 |
| `ProvesC` | the ordinary taclets lift to the callback reading on a statement that pays nothing and runs no other (`s.forks = false`), and whose premise pays nothing; a goal with no transfer left is `Proves`'s (`holdsC_iff_holds`). Validity with callbacks implies validity without (`valid_of_validC`) | 2026-09-27 |

## `ResidueShape` verdicts (history)

One row per constructor of `Coverage.ResidueShape`, filled in phase 2:
*unrepresentable* (the typed syntax cannot write it, and why) or *rule* (the
`Taclet` constructor that runs it).

| Shape | Verdict |
|---|---|
| `iteSymbolicCond` | *rule*: `ifElseSplit`, a `split` premise (phase 3), on a `Simple` condition; a complex one is captured by `ksol` |
| `incDecStmt` | storage and stack *unrepresentable*: `Stmt.incDec` takes an `OpLoc` (a local, a state variable, a member, an entry at a simple index; `ksol` captures a complex index). Memory targets open |
| `assignMemFieldFromStorage` | a storage *value* into a memory member is a rule (`memoryFieldWriteUnfoldSource` captures the read); a storage *reference* into one is *unrepresentable*: `MSrc` is a value or a memory reference, no copy form |
| `assignMemIndexFromStorage` | as `assignMemFieldFromStorage`, with `memoryIndexWriteUnfoldSource` |
| `assignStackRefUnfoldTarget` | *unrepresentable*: a stack local has a primitive type (`Val.local`) |
| `assignPushPlaceLhsNonStorage` | *unrepresentable* once push places exist: as `deletePushPlaceNonStorage` |
| `assignStorageLocalRootFromStack` | *unrepresentable*: an alias has a reference type, a stack local a primitive one |
| `assignMemoryRootFromStack` | *unrepresentable*: a memory local names an object; a stack local holds a primitive |
| `assignStackVarFromMemory` | *unrepresentable*: as `assignMemoryRootFromStack`, the other way |
| `assignStackPlace` | *unrepresentable*: a member or index access has its base's location, and a stack local has no members |
| `assignPushRhsNonStorage` | *unrepresentable* once push places exist: as `deletePushPlaceNonStorage` |
| `assignPushRhsNonLocalLhs` | open |
| `assignOperatorRhsBadLhs` | storage slice *unrepresentable* (local root: reference type; stack place: none); memory root and push place open |
| `assignOperatorRhsRefTyped` | *unrepresentable*: an operator is applied at a primitive type (`Val.binop`) |
| `assignIncDecBadTarget` | storage and stack *unrepresentable*: `Stmt.assignIncDec` writes a stack local, from an `OpLoc` with a simple receiver (`ksol` captures another). Memory targets open |
| `assignTernaryBadLhs` | *unrepresentable*: a conditional is a `Val`, and a value is written only to a local or a storage `Loc` (`VHole`) |
| `assignCallRhs` | *rule*: `y = f(a);` is a `Stmt.call` whose result lands in the local `y` (`functionBodyExpand`, after `functionCallArgCapture`); a call's value to anything but a local is captured into one by the elaborator |
| `assignStackPlaceRhs` | *unrepresentable*: as `assignStackPlace` |
| `compoundAssignPow` | *unrepresentable*: `Stmt.opAssign` carries `op.hasCompoundAssign`, which `**` fails (solkey has no `powAssign` taclet) |
| `compoundAssignBadTarget` | storage and stack *unrepresentable*: an `OpLoc` target. Memory targets open |
| `memoryDeclBadInit` | *unrepresentable*: `MRhs` is a memory path (aliased) or a storage path (copied) at the declared type |
| `deleteStorageLocalRoot` | *unrepresentable*: `delete` takes a `Loc`, never an alias |
| `deletePushPlaceNonStorage` | *unrepresentable* once push places exist: they will be over a storage `SPath` |
| `pushNonStorageTarget` | *unrepresentable*: `Stmt.push` takes a storage `SPath` (solc has no `push` on a memory array) |
| `pushMemoryValue` | *unrepresentable*: `Stmt.push` takes a storage `Src`; a memory argument is a copy the calculus has no rule for |
| `popNonStorageTarget` | *unrepresentable*: as `pushNonStorageTarget` |
