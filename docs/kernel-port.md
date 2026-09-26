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
| `Ch06_Taclets` | `Calculus/Rules.lean`, `Calculus/Sound*.lean`, `Calculus/RuleSoundness.lean` (`Taclet.sound`), `Calculus/Logic.lean` (`Proves`) |
| `Ch07_Symex` | `Calculus/Symex.lean`, `Calculus/Close.lean` |
| `Ch11_Completeness` | `Calculus/Completeness.lean` (`Stmt.step`, `Stmt.complete`) |
| `Examples/` | `Solidity/Examples/` |

## Port later

Each was removed with the untyped layer and is to be ported over `Stmt C` /
`Stmt.run`; git history before `59fa352` has the old versions.

- **Termination** (`Ch12`): a measure on formulas, `symex` normalizes.
- **Uniqueness**: at most one rule per statement (`Taclet` is a `Prop`, so it
  is stated about premises; the old `Kernel/Unique.lean` did it with `Taclet`
  in `Type`).
- **Progress** (`Ch11`): a formula with a modality always steps.
- **Chains** (`Ch13`), **update simplification** (`Ch14`), **the decision
  procedure** (`Ch15`: the four-way path comparison; `Close.lean` has the
  "apart" case).
- **The EVM compiler** (`Ch08`–`Ch10`), `docs/compiler-verification.md`.
- **Type soundness**: the interpreter keeps `StateWT`; tightness
  (`reachable ⇒ canonical`); the sort-faithfulness proof of the taclet
  annotations (`SortCheck/Faithfulness`).
- **Calls** and the **callback semantics** of `transfer`
  (`transferSemantics:withCallback`): the typed syntax has neither.
- **Memory `delete`**, `new T[](n)`.
- **The solkey corpus** (`scripts/solkey-port.mjs`), regenerated as
  `sol[C]{}` programs proved by `sol_symex`.
- **The `SolKey` reader** (`~/projects/side-projects/lean/solkey`) names
  `RuleName`/`ruleEffect`/`StepEffect`; it is to be re-targeted at `Taclet`.

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
| Array bounds | no `inBounds` split: `SVal.find`/`SVal.save` revert out of range, so the kernel's update fails as the statement does. A failing update is read like a revert by the modalities | 2026-09-25 |
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
| Overlapping taclets | where solkey leaves two taclets open on one statement and its strategy picks, the kernel adds the side condition that makes `Stmt.step`'s choice the only one (`Kernel/Unique.lean`): `sp.f = c ? a : b;` is lowered, never captured (`Val.notTernary`); `folks[1].account = folks[2].account;` unfolds its target first (`Loc.isTarget` on the source unfolds); a memory reference unfolds its source first (`MPath.isBindable` on the target unfolds) | 2026-09-26 |
| Modalities | the kernel's box is partial correctness (it holds unless the run ends normally in a bad state) and its diamond needs a normal end; neither tells a revert from a stuck run. An unfolding rule then owes its statement the same *successful* outcome (`SameOk`), which the order-changing rules (`*StorageRef_unfold_leftFst`, `*NonSimpleIndexCapture`) meet without the side conditions the untyped `*_sound` theorems carry. `SolidityJudgment.Holds` differs on stuck runs ("a stuck execution validates nothing"); the phase-7 bridge must say so | 2026-09-25 |
| Unknown names | an error: parameters are declared locals. mini-solkey reads an unknown name as a `uint` parameter | 2026-09-25 |
| Ported contracts | one named constant per interpreter store, `initStorage_*` checks roots, order and defaults against the store by `simp` | 2026-09-25 |

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
| `assignCallRhs` | open |
| `assignStackPlaceRhs` | *unrepresentable*: as `assignStackPlace` |
| `compoundAssignPow` | *unrepresentable*: `Stmt.opAssign` carries `op.hasCompoundAssign`, which `**` fails (solkey has no `powAssign` taclet) |
| `compoundAssignBadTarget` | storage and stack *unrepresentable*: an `OpLoc` target. Memory targets open |
| `memoryDeclBadInit` | *unrepresentable*: `MRhs` is a memory path (aliased) or a storage path (copied) at the declared type |
| `deleteStorageLocalRoot` | *unrepresentable*: `delete` takes a `Loc`, never an alias |
| `deletePushPlaceNonStorage` | *unrepresentable* once push places exist: they will be over a storage `SPath` |
| `pushNonStorageTarget` | *unrepresentable*: `Stmt.push` takes a storage `SPath` (solc has no `push` on a memory array) |
| `pushMemoryValue` | *unrepresentable*: `Stmt.push` takes a storage `Src`; a memory argument is a copy the calculus has no rule for |
| `popNonStorageTarget` | *unrepresentable*: as `pushNonStorageTarget` |
