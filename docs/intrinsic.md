# Making the model intrinsic

Plan of record for branch `intrinsic` (started 2026-10-07): locals scoped in
the syntax (`Stmt C Γ Γ'`, positional `Idx`), a state typed by its context,
an interpreter with no `stuck`, a compiler total on typed syntax, and the
calculus and closer over typed formulas. Trimmed to a module-map entry at M7.

## Decisions (user, 2026-10-07: "implement all of them")

1. If a speed gate (G0, M6a) fails, the calculus takes Church-typed program
   variables (KeY's `\programVariables`); every other layer stays intrinsic.
2. Locals are block-scoped (popped at the end of `if`/loop/`try`/block), as
   solc; each changed behaviour gets a `docs/solc-alignment.md` row.
3. `uint` values are `{n : Int // p.admits n}` (keeps 56642ee's kernel path).
4. Storage is typed (`SVal : Ty → Type` over `structDef`, M4b).
5. The SolKey reader (side-projects `lean/solkey`) is regenerated on a branch
   there when M6a breaks it.
6. The closer and Decide are ported (M6c); `Fml.erase` is a bridge only.
7. All milestones run; a failed gate takes its stated fallback, not a stop.
8. The bridge (typed `Core` beside the untyped `Stmt`) ends at M4, not M7.
9. (lead, 2026-10-07) The M6a speed gate counts as **passed**: aggregate
   symex is 1.1–3× faster on the larger programs; the 1.45× of the 10 ms
   straight-line e2 is a few ms, to be reduced, not a fallback trigger.
10. (lead, 2026-10-07) A `bool` mapping key follows solc: it is hashed as
    `0`/`1`, so the typed path (M4b) takes the `Int` `0`/`1` for it
    (`docs/solc-alignment.md`).

Decided by the lead since (2026-10-07):

9. **The M6a gate counts as passed.**  The scoped symex is about 2.9×
   faster on e1×5 and e3×10 (3.2 s against 9.0 s in total); it is outside
   the 20% gate on e2 (1.42×), e4 (1.27×) and e2×10 (1.23×), each by
   3–23 ms, a cost to reduce (the kernel's comparison of contexts) rather
   than a trigger for Decision 1's fallback.  The calculus stays
   positional.
10. **A `bool` mapping key follows solc**: it is hashed as the word `0`/`1`,
   so the typed path takes the key as the `Int` `0`/`1`
   (`docs/solc-alignment.md`, "`bool` mapping keys").

## Milestones

| # | Status | Work |
|---|---|---|
| M0 | done 2026-10-07: G0 passes under the conditions below | baselines + scratch spike, gate G0 |
| M1 | done | stuck causes that need no index; the elaborator runs the locals check (`wtCheck`) |
| M2 | done 2026-10-07: every import and `sol{}` site resolves, the scoped form kernel-checked; elaboration within 10% (below) | `Ctx`/`Idx`/`Thin`, typed `Core` syntax, `resolve`, quoter, lint |
| M3 | done 2026-10-07: typed run, `run_erase`, Typing over `Core`, locals checker deleted (no shim left); Typing elaboration 10% faster (below) | `Env Γ`, `State C Γ`, typed run; delete the locals checker |
| M4 | | typed values, storage, heap; delete `stuck`; retire old `Stmt` |
| M5 | | EVM on typed syntax; delete `wtStmt`, `not_stuck` |
| M6a | lane: every `Stmt.step` arm and `Premise` ported; gate passed (Decision 9) | calculus: `Fml C Γ`, `Frames`, `Premise`, symex, chains, ProofTree |
| M6b | | `dl!{}`, specs, callbacks |
| M6c | | closer and Decide on typed `Fml` |
| M7 | | cleanup, docs, rule-map rows, review pass |

### M1 notes

- (a) `**` with a negative exponent, and `transfer`/`send` (and the update
  element `.pay`) of a negative amount, revert.  `Simple.lit` carries
  `PrimTy.inRange` (`AST.lean`; `PrimTy.admits` was taken, a `Value`
  predicate in `Update.lean`), discharged by `rfl` in quotes and by
  `litAt` in the elaborator; `Evm.wtSimple` admits every literal.  The
  storage builder writes literals now, so `canon_reachable`/`reachable_iff`
  (`Typing/Constructibility.lean`) and `shape_iff_reachable`/
  `wt_iff_reachable` (`Calculus/Problem.lean`) take `FitsStorage` (every
  word, key and slot in range); `reachable_shape`, `shape_of_reachable`
  and `wt_of_reachable` are the unconditional directions.
  `uint_negative_reachable` is gone (its program no longer elaborates).
- (b) `R.memOk` is `(Ty.ref R).mapFree`, as `MRhs.copy` already used:
  `MPath.var` and `Stmt.declMem` carry it; `deleteMem` needs no field,
  since `MPath.mapFree` derives it for every memory path.  `allocDefault`
  keeps its stuck arm: the closer's `.alloc R`/`.addM R` terms reach it at
  an untyped `R` (to go at M4c).  In the `dl{}` macro a memory local's
  proof is the auto-bound `hmv` (`proofIdent`), a declared one's
  `MRhs.mapFree r`; this moves a struct name before the member name in some
  taclets' implicit binders (`Examples/Notation.lean` pins,
  `SortCheck/Faithfulness.lean`), which the SolKey reader's `GenProved`
  must be regenerated for.
- (c) The seven captures that did not declare their local now do
  (`captureAs`): `elabOpTarget`'s `ie` (two), `elabIncTarget`'s `sp`/`mv`
  (four), `elabSize`'s `se`.  The rest declare it already: `hoist`'s call
  captures after the call, a callee's renamed locals, loop flags and
  modifier parameters when their raw declaration is elaborated, a call's
  arguments and return variables in the callee's own context (`Γf`).
- (d) A storage conditional of references is
  `T storage sp1; if (c) { sp1 = a; } else { sp1 = b; }` (`hoist`; the
  `Syntax.lean` pin).  A memory one still declares its `mv` in each branch:
  `T memory mv1;` would allocate, so it waits for M2's scoped branches.
- (e) `Binding.unset`: `declStorage R x none` binds it, `aliasPath` reverts
  on it.  `storageLocalDeclSkip` is `T storage lsv; ⇝ {lsv := unset} ⟨[ ]⟩`
  (`UpdElem.unset`, printed and read as `lsv := unset`, a keyword in
  `dl!{}`; rule-map deviation row, solc-alignment row).  `Stmt.wt` adds
  `x` at its alias type (`BTy.matchesB` accepts `unset`), the EVM forgets
  it (`Sim.unbind`), and Decide carries it as `SymB.unset`, a read through
  it outside the fragment.  Pins changed: the `Syntax.lean` conditional
  pin and the `StorageCoverage.storageLocalDeclSkip` chain's last line
  (`{ acc := unset } φ`); no `#guard_msgs` output changed.
- (f) `BTy`, `Ctx` and the locals check (`Stmt.wt`, `Prog.wt`, each part's
  `wt`) moved from `Typing/State.lean`/`Typing/Soundness.lean` into
  `Syntax.lean`, below the printer; `Soundness.lean` keeps the theorems.
  `wtCheck` (`Prog.wtFirst`, an error naming the statement) runs in
  `elabProg`/`elabProgAt` (so `sol[C]{}`, `solc_import`, `ctorProg`,
  `Tools/Run`), at a spec's and a constructor problem's call
  (`specPieces`, `Problem.ctor`) and per statement in a `dl!{}` modality,
  from the elaborator's locals (`ECtx.toCtx`).  An `if` now leaves
  `Ctx.join`: the fresh locals both branches declare alike, which the memory
  conditional of references' `mv1` needs (`Ctx.le_join_thn`/`_els` in the
  two `ite` cases, `Soundness.lean`, `Reachability.lean`).  All 449
  TestSuite functions, the corpus and every example pass.  A block's local
  retyped by a later branch (`{ bool x = true; } if (c) { uint x = 1; }`)
  is now an elaboration error (pinned in `Examples/Tactics/Branch.lean`),
  until M2's scoped locals.  Timing (profiler, before → after): the
  TestSuite `solc_import` 1.69 s → 1.71 s, `TestSuite/Derived3.lean`
  (cumulative type checking) 17.1 s → 17.0 s, `Examples/Tactics/Branch.lean` unchanged (each
  declaration within 10 ms).
- M1 review (2026-10-07), confirmed findings fixed:
  `Ctx.join` keeps only fresh locals (`Var.isFresh`), so a user local
  declared alike in both branches no longer blocks a later retyping.  The
  general rule until M2: a name declared in a block, a `for` init or one
  branch cannot be redeclared at another type later in the program (both
  shapes pinned in `Examples/Tactics/Branch.lean`).  `wtCheck` names the
  innermost rejected statement and, for a retyping, the local and both types
  (`Stmt.wtWhy`, `Ctx.retyped`); an empty block prints `{ }` (`braced`; six
  pins updated).  `check` folds `+ - *` and an exact `/` of two literals
  when an operand is out of range (`BinOp.foldLit?`; solc's constant
  folding, pinned in `Syntax.lean`).  `x := unset` in `dl!{}` accepts only
  an alias or an unbound name (and keeps `x` out of the `uint` parameters,
  `RawFml.unsets`); pins in `Notation.lean`.  The unset-alias revert has
  witnesses (`StorageSuite.unsetAliasWrite`/`Read` and a loop pin).
  Docstrings and solc-alignment rows no longer claim that no checked program
  has a negative exponent or amount (`TxEnv` fields are unconstrained);
  solc-alignment gains a "Block-scoped locals" row and delta, and its error
  classification and mappings-in-memory rows say what reverts and what stays
  stuck.  New bare `simp`s are `simp only` (or `rfl`).

### M2 notes

- M2.1 (2026-10-07): `Scope.lean` (`LTy`, `Ctx := List LTy`, `Idx`, `Ext`,
  `Thin`, `Binders`, `CodeBinder`) and `Syntax/Core.lean` (every family at
  `C Γ`, `Args`, `CallRet`, mutual `Stmt C Γ Γ'`/`Prog C Γ Γ'`, printers,
  `Stmt.wk`/`Prog.wk`), both in `Solidity.Core`.  Departures from the sketch
  below:
  - The contexts are in their own module, not `AST.lean`:
    `Solidity.Semantics.Ctx` (the locals check's `List (Var × BTy)`) would
    clash wherever `Semantics` is open, until M3 deletes it.
  - `Thin` is `refl | keep | drop` (the spike's), not `done | keep | drop`:
    the identity is one constructor.  `Ext`'s functions are `casesOn` +
    structural (`Ext.trans`, `Ext.depth`, `Idx.ext`), `Thin`'s `match`.
    `Ext` is a `Subsingleton`.
  - Constructors keep today's argument order (`declLocal p x init`), a use
    is an `Idx`, a binder a `Var`.  New: `Stmt.block`.  `call` has no `hsep`.
  - A call's frame is `rs ++ ps`: `Args` binds the parameters in order
    (`snoc`, the last innermost), and the frame declares the return
    variables `rs` at their defaults.  `CallRet Γ rs Γ'` (no `C`) is `none`,
    `val p r res` (`res : Option (Idx Γ (.val p))`), `rets bs` (left in the
    caller, `Γ' = rs ++ Γ`: the tuple's targets read them) and `mem R r hd
    hm` (`Γ' = .mem R :: Γ`).  The memory return's declaration moves from
    the body's head (`Person memory mv2;`) into the frame, so `erase` must
    put it back.
  - A `try`'s returned values are `Binders ρ` and its code a `CodeBinder κ`
    (`[]` or `[.val .uint]`).
  - Printers take the names of the context (`List Var`, innermost first) and
    write what `Syntax.lean`'s write; `Stmt.memCallStr?` and
    `Stmt.tupleCallStr?` compare names, as there.  Pinned by `example₁`
    (every scope) and two weakening `#guard`s at the end of the module.
- M2.2 (2026-10-07): `Syntax/Resolve.lean` (`erase`, `resolve`,
  `resolve_erase`, `Prog.resolveCheck`) and `Syntax/Splice.lean` (the entry
  points).  Departures and choices:
  - `resolve` returns the context it leaves as an `NCtx` (names beside
    types), `Σ Γ' : NCtx, Stmt C Γ.ctx Γ'.ctx`, not a bare `Ctx`: the next
    statement needs the names.  `erase` takes the names `ns` of its context
    (`Stmt.erase ns : Stmt C Γ Γ' → List (Solidity.Stmt C)`, a block its
    statements), so `resolve_erase` reads `s.erase Γ.names = [u]`.
  - Each `resolveX` returns its result with the proof that it erases to its
    input (a subtype), so `resolve_erase` holds by construction and needs no
    induction; the functions are structural, at elaboration time only.
  - A name is its newest declaration, which must be at the type its use
    needs (no fallback to an older one).  Branches of `if`/`try`, loop
    bodies and call bodies are scopes; the untyped programs have no block,
    so a block's locals stay in scope in its enclosing one (harmless: the
    elaborator's own scopes keep the program from reading them).
  - A call: each argument is read in the caller's context and may not read
    a parameter (a new check; the elaborator's parameters are fresh); the
    body sees only its frame.  `CallRet.none` with a body starting
    `T memory r;` is a memory return (`CallRet.mem`), the declaration moved
    into the frame and back by `erase` (`CallRet.pre`).  `erase` of a call
    whose arguments are not separated (never `resolve`'s output) binds them
    at the head of its body, since `Syntax.lean`'s call needs `hsep`.
  - The memory conditional of references: `T memory mv1 = a; if (c) { mv1 =
    a; } else { mv1 = b; }`, `mv1` bound first to a branch that indexes
    nothing (`MPath.indexFree`, a read that cannot revert), or, when both
    index, to a fresh default object (`T memory mv1;`, an object nothing
    reaches; a `solc-alignment.md` row).  With it, `Stmt.wt`'s `if` leaves
    `Γ`: `Ctx.join`, `Var.isFresh` and their lemmas are gone.
  - The entry points (`elabProg`, `elabProgAt`, `ctorProg`, `sol[C]{}`,
    `solc_import` through `elabProgAt.go`, `specPieces`, `Problem.ctor`,
    each statement of a `dl!{}` modality) run `Prog.resolveCheck` from the
    elaborator's locals (`ECtx.toNCtx`, read under the file's
    `FreshNames`); `wtCheck`, `Prog.wtFirst`, `Stmt.wtWhy`, `Ctx.retyped`
    and `ECtx.toCtx` are gone.  The error names the innermost statement and
    the local: ``the locals check (`resolve`) rejects `x = 1;`: x is not
    declared``, `… b is declared as bool, used as uint`.  `contract!{}` checks
    no body: a body is checked where it is inlined.
  - `elabProg` and the rest moved out of `Syntax.lean` into
    `Syntax/Splice.lean`, which imports `Resolve` (itself above
    `Syntax/Core.lean`, above `Syntax.lean`); `Semantics.lean`,
    `Frontend/Import.lean` and `Examples/Benchmark/Syntax.lean` import it.
  - The lint: the TestSuite import (`Solkey/TestSuite.lean`, 449
    elaborated, 0 unsupported), every module of `Solidity`,
    `SolidityCorpus` and `SolkeyTestSuite`, and so every `sol{}` site,
    elaborate under `resolve`.  The two `Branch.lean` retyping errors of M1
    now elaborate.  Not run here: `check-corpus.sh` and `solkeycheck` (need
    `lake`).
  - Timing (the gate: `sol{}` sites within 10%): on the TestSuite contract's
    12 functions, each called with its parameters in scope, 50 rounds by
    `IO.monoNanosNow` in a scratch module, elaboration takes 0.155 ms a
    call, `resolve` 0.045 ms and the old `Prog.wt` 0.030 ms: the check
    costs 0.015 ms more a block, against the quoting and kernel check that
    dominate a site (the TestSuite import, 449 blocks, is 10.4 s).
- M2.3 (2026-10-07): `Syntax/CoreQuote.lean`, `solc_scoped`, `Stmt.ext`.
  - `Core.Prog.quote` takes the term of its context and conses what a
    statement pushes onto it (`ctxFrom`), so a scope's context shares its
    enclosing one; `Prog.quoteShared` then hash-conses the whole term
    (`ShareCommon`, condition 7).  Over the 449 TestSuite programs the
    scoped terms have 95.5k objects against the untyped quoter's 144.6k
    (unshared), and quoting them takes 0.14 s with `resolve`.
    `Prog.defineCore` resolves, quotes and declares; `tour` and a block of
    calls are pinned in the module (declared, erased back by `rfl`).
  - The lint: `solc_scoped N` declares `N.f.core : Core.Prog N Γ Γ'` for each
    program of an import, resolved from its parameters, the kernel checking
    it, and errs on one that does not resolve; it pins the count
    (`Solkey/TestSuiteScoped.lean` 449, `Solkey/Constructors.lean` 2+2+1+1,
    `Examples/Tactics/LoopsImport.lean` 9).  Every `sol{}` site, and each
    import's elaboration, runs `resolve` already (M2.2), so a block that does
    not resolve fails the build.  The kernel's check of the scoped terms
    costs about the untyped ones' (3.0 s against 2.9 s over the 449,
    synchronously), so inside `solc_import` it made `Solkey/TestSuite` 30%
    slower: `solc_scoped` is a command of its own, and the TestSuite's is a
    module of its own (3.5 s, in parallel with the rest of
    `SolkeyTestSuite`).
  - `Stmt.ext`/`Prog.ext`/`CallRet.ext` (`Syntax/Core.lean`): what a
    statement pushes, in condition 1's form (`casesOn`, structural); the
    kernel reduces them (`decide` on `example₁`).
  - Timing (the gate: within 10% of M0): wall time from the worker's start
    to the end of a copy of the file after every kernel check (`#clock` in a
    scratch module, `/proc/self/stat` against `/proc/uptime`; M0's included
    the MCP call's overhead too).  `Examples/Benchmark/Syntax` 1.22 s (two
    runs; M0 1.2 s, +2%), `Solkey/TestSuite` 10.99/11.21/11.07 s (M0 10.4 s,
    +6%), `Examples/Chains/Storage` 7.21/7.34 s (M0 7.5 s, −3%).

### M3 notes

- M3.1 (2026-10-07): `Semantics/Core.lean`, the interpreter over
  `Core.Stmt`.
  - `LTy.Denote C` (reducible): `val p` a `Value`, `alias R` an
    `Option (Name × List Seg)` (`none` unset: a read reverts), `mem R` a heap
    identity, `old`/`oldNet` a storage/ledger.  Values, storage and heap stay
    `Semantics.lean`'s until M4, so `C` is not used yet.
  - `Env C Γ` is computed (`Unit`, `t.Denote C × Env C Γ`); `get`/`set` recurse
    on `Idx`, `drop` on `Ext`, by `casesOn` (condition 1); `append`/`take` (a
    call's frame, a `try`'s returned values) on the list `ρ`.
  - `State C Γ` has today's fields with `env : Env C Γ`; `State.glob` is the
    global part as a `Semantics.State` (no locals), so every storage, heap
    and ledger operation of `Semantics.lean` is called as it is, and
    `withGlob`/`withEnv` put the result back.
  - One function per statement (`Run.assign` … `Run.block`, `Run.seq`), given
    its sub-programs' runs and their `Prog.ext`.  `Stmt.runR`/`Prog.runR` are
    `Stmt.rec`/`Prog.rec` over them (`@[implemented_by]` the `match` twin
    `Stmt.runC`/`Prog.runC`, linked by `Stmt.runR_eq`/`Prog.runR_eq`, a
    mutual structural proof); `Stmt.run σ s`/`Prog.run σ P` are abbreviations
    with today's argument order.  The twin is a `match`, not `casesOn`: it is
    compiled code only, never kernel-evaluated.
  - Scopes: `ite`, `block`, `loop` (each iteration) and the `try` clauses pop
    by `State.drop` of the sub-program's `Prog.ext` (a `try` clause also pops
    its `ρ`/`κ`, `Ext.append`).  A call evaluates the arguments in the caller
    (`Args.eval`, in order), enters the frame `rs ++ ps` (`CallRet.enter`:
    defaults, a memory return allocated after the arguments are read, as
    today's first body statement did), runs the body, and leaves the caller
    its locals plus what `CallRet.leave` exports (`val`'s assignment,
    `rets`' variables, `mem`'s identity).
  - The loop is `Core.Loop`, today's `Loop` over any state type (`step`,
    `iterN`, `run` with `run_of_iterN`), since today's is fixed to
    `Semantics.State`; it goes when M4 retires the untyped interpreter.
  - `stuck` now comes only from a value of the wrong shape (`asInt`/`asBool`,
    a condition that is an `int`: M4a) and from a storage or heap that does
    not fit (`findStorage`, `getObj`, `copyStToM`, `allocDefault`: M4b, M4c).
    No local lookup can fail: an unset alias reverts, as today.
  - Equations: `Prog.run_nil`, `run_cons`, `run_cons_ok`,
    `run_loop_of_iterN`, `Stmt.run_ite`/`run_block`/`run_loop`/`run_call`
    (by `rfl` or one rewrite); `Env.get_set`, `take_append`, `drop_append`.
  - Examples (kernel): a failing `require` reverts, a failing `assert`
    panics (`rfl`), two of `Semantics.lean`'s three `++`-order runs
    (`decide +kernel`), `CallsExample`'s `addTwo(3)`/`larger(5, 7)` read from
    the caller's locals (`rfl`), a loop declaring a local per iteration
    (`run_loop_of_iterN (n := 4) rfl`).  `aliasWrite` and the third
    `++`-order run do not reduce in the kernel with either interpreter
    (storage overlay / nested push), so `aliasWrite` is a `#guard_msgs`
    `#eval` (`runResolved`), as today.
  - Timing: kernel check of `Eq.refl` on `(run σ P).isOk`, best of five
    (`IO.monoNanosNow` around `addDeclCore`, a scratch module), the old
    interpreter on the untyped block, the new on its `defineCore` term, and
    the `match` twin `Prog.runC` on the same term:

    | Block | old | `Prog.run` (rec) | `Prog.runC` (match) |
    |---|---|---|---|
    | `require(age > 3)` | 2.8 ms | 2.6 ms | 3.2 ms |
    | `assert(age > 3)` | 2.8 ms | 2.6 ms | 3.2 ms |
    | `i++ + i` | 9.2 ms | 5.4 ms | 9.1 ms |
    | `values[++i] = ++i` | 18.9 ms | 16.5 ms | 21.7 ms |
    | `addTwo(3)`, `larger(y, 7)` | 22.3 ms | 11.7 ms | 18.0 ms |

- M3.2 (2026-10-07): `Semantics/RunErase.lean`, the bridge theorem.
  - `Prog.run_erase P hP hnd hlen σ : ResultsAgree (P.popped ns)
    (Solidity.Prog.run (σ.erase ns) (P.erase ns)) ((P.run σ).map (State.erase
    (P.outNames ns)))`, and `Stmt.run_erase` for a statement (its erasure a
    list).  `State.erase ns σ` names the locals by `ns` (`LTy.enc`: an unset
    alias `.unset`, a memory local `.mref`), and `popped` are the binders not
    in scope at the end, which the untyped run keeps.  `ResultsAgree` and
    `EnvAgreeExcept` are `Semantics/Agree.lean`'s; its frame lemmas
    (`Stmt.run_frame`) were not needed.
  - The hypothesis is `P.Fresh out ns`: no binder reuses a name in scope
    (`ns`) or of an enclosing call frame (`out`), a frame's names are
    distinct, and a call's arguments are separated (`erase` then writes
    `Syntax.lean`'s call, not the arguments-in-the-body fallback).  A name may
    be declared again after its scope ends (a loop body every iteration,
    sibling branches): the untyped run overwrites the stale binding.
    `callsCore_fresh` proves it for a resolved block by `simp only`.
  - The proof is one invariant, `Agree ns σ τ` (equal global parts, every
    local of `σ` bound under its name in `τ`), and `RunRel`: the same halt,
    or agreeing states that bind every name off `ns ++ binders` as before
    (what a call's caller needs of its body).  The global operations are
    natural in the locals (`saveStorage_nat` … `memClear_nat`, each by
    unfolding; `copyMem` through `Agree.lean`'s `copyMem_congr`), so the
    scoped run's operations on `σ.glob` and the untyped run's on `τ` agree.
    One lemma per statement (`Stmt.erases_*`), the IH passed in, and a
    mutual structural `Stmt.erasesAt`/`Prog.erasesAt` that dispatches;
    loops by `Loop.run_rel₂`, `Loop.run_rel` across the two state types.
  - Not true in general (M2–M3 review): `resolve`'s output from the
    elaborator is not always `Fresh`.  A raw block, a `for` init and a
    modifier's `_` are elaborated by `elabBranch`, which pops their locals
    from `ECtx` but emits them flat, so a later declaration of the same name
    passes `checkFresh` and `resolve` stacks a second binder in one scope:
    `for (uint i=0;…){} for (uint i=0;…){}`, `Branch.lean`'s pins
    `{ bool x = true; } if (c) { uint x = 1; }` and
    `for (int i…){} if (c) { uint i = 1; }`, a modifier applied twice.
    `run_erase` does not cover these.  Not done either: deriving `Stmt.wt`/`Prog.wt`/`Ctx.has`/`EnvWT` from `resolve`
    plus `run_erase`.  Applying `Prog.run_erase` to `callsCore` and a state
    times out in the elaborator at `whnf` (the partial application without the
    state checks); not yet diagnosed.  (M3.3 did not need the derivation of
    the locals check: the typing proofs moved to `Core` instead.)

- M3.3 (2026-10-07): Typing over `Core`; the locals checker deleted.
  - `Typing/State.lean`: `StateWT H L s` is the global part only (layout
    and store typing unique, storage, heap, `heapWf`; `ofB` decides it).
    `BTy`, `envTypedB` and the stray-binding ban went with the untyped
    locals.
  - `Typing/Soundness.lean`: `Core.RunWT C H σ` is `StateWT H C.layout
    σ.glob` and `Env.All (LTy.WT C H) σ.env`.  The locals part stays a
    predicate (a local of type `val p` holds a `Value`, an alias a path the
    layout must type, a memory local an identity `H` must claim) until M4
    types values, storage and heap; env typing by construction is M4's.
    `Core.Stmt.run_wt`/`Prog.run_wt` need no locals hypothesis.  The global
    lemmas (`StateWT.save`/`write`/`ofCopyOut`/`setObj`/`pay`/`transferAt`,
    `pushAt_wt` … `bumpMem_wt`) are on `Semantics.State`; the evaluator
    lemmas (`Core.Val.eval_wt` …) on the scoped syntax.
  - `Invariant C` (glob part, per-local part monotone in `H`, blind to the
    locals): `keeps_seq`/`ite`/`block`/`loop`/`call`/`tryCall`/`require`/
    `assert`/`revert` are proved once; each invariant gives its leaves and
    four hooks (arguments, `CallRet.enter`, `Binders.decode`,
    `CodeBinder.decode`).  `wtInv`, `canonInv` (`Reachability.lean`,
    `Canon` on the glob part) and `tightInv` (`Constructibility.lean`, the
    untyped `Tight` now storage-only, plus `LTy.Keys` on aliases) are its
    three instances; a tight leaf is its canonical leaf plus a tightness
    lemma (`keepsT_of`).  `Core.Loop.run_induct` is the loop's induction.
  - `Reachable C st := ∃ Γ' (P : Core.Prog C [] Γ') σ, P.run (State.ofSem
    C.initState) = .ok σ ∧ σ.storage = st`: reachability by the scoped
    interpreter, where it was the untyped run of a checked program.
    `Problem.lean`'s statements keep their text (`initStorage_wt`'s witness
    is `.nil`) but now speak of the scoped run, while `wt(storage)` is read
    by `holds` over the untyped one.  Open gap: `ReachableU → Reachable`
    (resolve, `Fresh`, `run_erase`; M2–M3 review).
  - The builder (`Core.Build`) is a scoped program: `fill d T q v : Prog C
    Γ Γ` declares each alias in a block of its own (`bound`), so a fill
    leaves its context, and its caller's aliases (read by position) are
    untouched: `Keep`/`KeepΓ` and the builder's locals check are gone, the
    run lemmas carry `σ'.env = σ.env`.  A shadow slot's alias is a block
    holding its `pop` and the nested fill; `Prog.append`, `Prog.rep`,
    `Prog.run_append` are local to it.
  - Faithfulness reads `Agree` (`RunErase.lean`): a row is faithful when its
    read, the erasure of a scoped read (`Read.Typed ns Γ`), finds what the
    sort claims in every state agreeing with a `RunWT` state.  The
    counterexamples give the scoped state and its agreement.  The example
    of `Branch.lean` that ran `Prog.wt` runs `resolveCheck`.
  - Deleted: `Syntax.lean`'s locals check (`BTy`, `Semantics.Ctx`, `Ctx.le`,
    `Ctx.has`, every `.wt`, `Arg.wt`, `CallRet.ctx`/`wt`, `bindCtx`,
    `Stmt.wt`, `Prog.wt`), `EnvWT`, the untyped `RunWT` and every untyped
    run traversal (`run_wt`, `run_canon`, `run_tight`).  Shims left: none.
    `bindData_induct` (Reachability) stays: `Problem.lean` reads the untyped
    interpreter's parameter binding with it, until M6a.
  - Elaboration, CPU s of the module alone (`#clock` in a copy with
    `Elab.async false`, imports cached), before (6cc3fd2, measured in a
    worktree under the same load) and after:

    | Module | before | after |
    |---|---|---|
    | `Typing/State` | 1.60 | 1.59 |
    | `Typing/Soundness` | 6.40 | 5.98 |
    | `Typing/Reachability` | 4.55 | 4.34 |
    | `Typing/Constructibility` | 11.16 | 9.39 |
    | the four | 23.71 | 21.30 |
    | `SortCheck/Faithfulness` | 26.22 | 25.57 |

  - For M4: values typed (`LTy.Denote (.val p)` a `PrimTy.Denote`) make
    `LTy.WT`'s `val` case true by construction; the alias and memory cases
    go with typed storage and heap.  The untyped `Tight`, `SE` and the
    global lemmas are on `Semantics.State` and move with it.
  - MCP: "Lean did not finish" on `Calculus/Problem.lean` hid a real error
    (a deleted lemma it used); a scratch copy cut in halves found it.

### M2–M3 review

Read-only review of M2–M3, the confirmed findings (2026-10-07):

- `Prog.Fresh` fails for ordinary elaborated programs (a name redeclared
  after a raw block, a `for` init or a modifier's `_`, which `elabBranch`
  pops from `ECtx` but emits flat), so `run_erase` does not cover them and
  "`resolve`'s output is `Fresh`" is false, not unproved.  Docs corrected
  (`RunErase.lean`'s docstring, M3.2 above, `solc-validation.md`).  Open:
  make the output `Fresh`, by a per-function set of every name declared so
  far that `checkFresh` reads (refuse, or rename to a fresh capture), or by
  a scope marker `resolve` turns into `Core.Stmt.block`.
- `Reachable` is now reachability by the scoped interpreter, while `holds`
  reads `wt(storage)` over the untyped one; `reachable_canon`,
  `shape_iff_reachable`, `wt_iff_reachable` and `reachable_iff` say nothing
  yet about the untyped run.  Said in M3.3, `testsuite-proofs.md`,
  `solkey-feedback.md`, `Problem.lean`'s and `Reachability.lean`'s
  docstrings.  Open: `ReachableU C st := ∃ P σ, resolveCheck [] P = .ok _ ∧
  Prog.run C.initState P = .ok σ ∧ σ.storage = st` and `ReachableU →
  Reachable`, from `Prog.resolve_erase` and `run_erase` once `Fresh` holds.
- The memory conditional of references refuses `c ? a[i] : b[j]` when the
  default of the type is not well-formed (`hoist`'s `T memory mv;`): now in
  `solc-alignment.md`'s row.
- `Core.lean`'s docstring cited a missing `Stmt.run_eq_runC`; it names
  `Stmt.runR_eq`/`Prog.runR_eq`.

## Baselines (M0)

Measured 2026-10-07 on the `intrinsic-m0` worktree (master 74b89f3), Lean
4.24.0, a machine shared with other sessions (repeats differ by up to 25%).
Method: wall time of `lean_diagnostic_messages` on a freshly opened file
(imports from the Lake cache, so worker start and header load are included,
about 1 s), stamped by `date` before and after the call; `Derived10` was
re-elaborated after a docstring edit instead (imports already loaded).
`stmt_sim` by `set_option profiler true` on its declaration, and by the wall
time of re-elaborating the file from it.

| What | Time |
|---|---|
| `TestSuite/Derived9` | 7.0 s |
| `TestSuite/Derived10` | 9.3 s |
| `TestSuite/Derived11` | 2.8 s |
| the three (`testsuite-proofs.md`'s 20.2 s is the sum of `sol_prove` CPU) | 19.1 s |
| `TestSuite/Problems` | 1.2 s |
| `Solkey/TestSuite` (`solc_import` of `TestSuite.ast.json`) | 10.4 s |
| `Examples/Benchmark/Syntax` (a `sol{}`/`contract!{}` site) | 1.2 s |
| `Examples/ProofTree` | 10.1 s |
| `Examples/Chains/Storage` | 7.5 s |
| `Evm/Examples` | 9.5 s |
| `Evm/Correctness`, whole file | 25.6 s |
| `Evm/Correctness` from `stmt_sim` (:1996) to the end | 19.9 s |
| `stmt_sim` alone, profiler items over 100 ms (type checking 1.6 s, `simp` 2.6 s, pre-definitions 0.2 s) | 4.4 s |

Not measured: the whole `SolkeyTestSuite` and `check-corpus.sh` (both need
`lake` from the shell, which this lane may not run); take them at M1's start
from `./run-lean.sh`.

### M6a notes

- Lane `intrinsic-calculus`, round 1 (2026-10-07): `Calculus/Core/Fml.lean`
  and `Calculus/Core/Print.lean`.  Departures from the sketch below:
  - `Tm C Γ s` keeps `Update.lean`'s signature (`app0`…`app3` over `Op0`…`Op3`);
    the locals are `pvV`/`pvP`/`pvS`/`pvI` and `netOf` by position, and
    `app1` refuses `Op1.netOf` (`Op1.named`).
  - `Upd C Γ Δ` is a snoc list (`nil`, `snoc` an assigning `UpdElem C Γ Δ`,
    `decl x r` with `r : Rhs C Γ t`, `pop h`), right-hand sides in `Γ`,
    targets in `Δ`.  A pop is invisible; an update of pops only erases to
    its formula.
  - `Frames.pop` takes `Ext` (condition 5), not `Thin`; so do
    `Premise.unfold` and `Upd.pop`.  `Frames.exit` (round 2; the spike's
    `frameStep`, recursive) goes through every frame of a finished program,
    and `Fml.modalK` is a modality that exits at once when its program is
    empty: `Premise.fml` writes it, so no step is administrative.
  - `Premise.bind`'s binder is a formula, `Fml.bind x t φ` ("for every value
    of `x : t`"), printed as `φ`: the update sketch had no right-hand side
    for it.  `Premise.check` has no program (`assertSimple`'s is empty).
    `branches`, `cases`, `inv` came in round 3.
  - `Stmt.scopeExt`/`Prog.scopeExt` (named apart from M3's coming
    `Stmt.ext`/`Prog.ext`, which should replace them at the merge).
  - Printing: `Fml.show` walks the formula with the precedences of
    `RuleSyntax.lean`'s grammar and prints terms, updates and statements by
    the `dl{}` printers on the erased part, so the text is today's; pinned
    against `legacyShow` (the erasure printed).  It runs in `MetaM` on a
    concrete formula; the delaborator for formulas with schema variables
    (`#taclet`, `#wp`) is still to write.
- `Calculus/Core/Lower.lean`: `Val.lower` and the rest on `Core.Tm`, with
  `lower_erase`.
- Round 2 (2026-10-07): `Calculus/Core/Step.lean`, `Calculus/Core/Quote.lean`,
  `Calculus/Core/Taclet.lean`, `Examples/Tactics/CoreSymex.lean`.
  - `Core.Stmt.step k m s : Option (Premise C Γ Γ')`: one `Stmt.casesOn`
    (condition 1); the expression-level arms (`localStep`, `assignStep`, …)
    `match` on `Val`/`Loc`/`Src`, whose context is a parameter.  Ported:
    locals (simple, root and member reads, operators, `binopUnfoldLeft`/
    `Right`, `unopCapture`), root and member writes (with their captures
    and `storageFieldWrite_unfold_leftFst`), `rebind` to an alias or a root,
    the value and alias declarations, `if` (`ifElseSplit`, `ifElseUnfold`),
    `require`, `assert`, `revert`.  Every other arm was `none` (until round 3): the strategy
    stops in front of it.  A capture's schema variables are weakened by
    `Val.up` and its kin (`.local i ↦ .local i.there`, no `Thin`;
    `Val.up_eq` says each is `wk up`), except `ifElseUnfold`'s branches,
    weakened by `Prog.wk up`, which matches on `Stmt`/`Prog`/`Thin`/`Idx`
    and runs in the kernel on every captured condition (e4 below).
  - `Fml.stepR` is `Fml.rec`, `@[implemented_by Fml.stepAt]` (`casesOn` +
    structural), `Fml.stepR_eq` by induction (condition 2).  `Fml.fresh` is
    one above every binder label's index (`Fml.maxIdx`, `casesOn` +
    structural): the erased names are today's `se1`, `sp1`.
  - The quoter writes every context out and hash-conses the result with
    `ShareCommon` (condition 7); a per-context cache was not needed.
  - `Examples/Tactics/CoreSymex.lean`: three programs, each resolved, run by
    `Core.symex`, quoted, added as a theorem `symex n φ = ψ` by `Eq.refl`
    (kernel-checked), and its erasure compared with today's `symex` with the
    cover goals dropped (equal, same fresh names).
  - `Calculus/Core/Taclet.lean`: `Core.Taclet` with three constructors,
    `Taclet.step_eq` (the rule `Stmt.step` fires) and `Taclet.erase` (each
    erases to today's `Solidity.Taclet`).  Soundness against M3's run is
    stated below, not proved: `Core.Stmt.run` has not landed.
  - Review fixes (2026-10-07): `Premise.split` carries the `BlockKind` that
    ends its branches (`if`: `.block`, printed `}`; `require`: `.capture`,
    printed as nothing, as KeY's `⟨[ revert(); ω ]⟩`); the schema
    variables' shift is `Val.up` and its kin; `Taclet.erase` is stated as
    what it is, an instance of today's rule relation, not soundness of the
    cover-free split.

- Round 3 (2026-10-07): every arm of `Stmt.step`, `Calculus/Core/Shift.lean`,
  `Calculus/Core/Arms.lean`, `Calculus/Core/Blocks.lean`,
  `Examples/Tactics/CoreStep.lean`.
  - Every statement has a rule, each the one `Completeness.lean` fires and
    commented with its taclet: index reads and writes, copies, deletes,
    aliases (and `lsv = sp.push()`), the conditional (`ternaryToIf`,
    `ternaryCaptureCond`, into a local, storage or memory), `&&`/`||`,
    compound assignments and `++`/`--`, push/pop, transfer/send, every
    memory statement, `new T(n)`, calls, `try`, loops, a block.  Today's
    holes are kept (`SHole`, `MHole`, `VHole`, with `up`), so each unfold
    rule is written once.
  - `Premise` gains `branches` (a `try`, each clause a `Branch`: binders and
    block), `cases` (a `send`'s outcomes), `inv` (the invariant rules) and
    `inline` (a block whose end drops locals from under the ones it keeps).
    No cover goal anywhere.  `Frames.drop`/`Upd.drop` are the frame end by
    a `Thin`: a call that leaves its return variables (`CallRet.rets`, a
    memory return), or whose argument was captured first, leaves its frame
    (or the capture) *under* them, which no suffix (`Ext`) pops.  Printed as
    nothing; `Calculus/Core/Quote.lean` got `qThin` and the two cases,
    `Calculus/Core/Print.lean` the one case of `Frames.items` (the only
    edits there), and a fix to `qCallRet`/`qLoopAnn`, whose `return` inside
    a `match` returned the `Option` alone (a call with a result and a loop
    with `decreases` did not quote).
  - A call is inlined as `expand_function_body`: the parameters declared
    with the arguments (`Args.declsThen`, each argument shifted under the
    ones before), the return variables, the body as a block weakened once by
    `Prog.wk (Thin.keepAll rs (Thin.atop ps Γ))` (the design's one `wk` per
    call expansion), the result assigned; the frame is popped (`unfold`) or
    dropped under the returns (`inline`).  `whileUnwind` writes
    `if (c) { { body } while (c) body }`: the body a block, so the loop
    after it reads the loop's context and nothing is weakened; the erasure
    is today's (a block erases to its statements).  `whileInvariantDiamond`
    weakens the body once (`Prog.wk up`) under the variant's local; the
    box rule pops the condition's local before the body instead.
  - The invariant rule's frame (`Prog.frame`, `Stmt.within`, `writesAt`)
    anonymises the locals of the loop's context the body writes; the
    body's own locals, which `Prog.loopFrame` lists, are popped every
    iteration and are not in the context, so a loop that declares locals
    erases to today's `{anon(…)}` less those names (the only erasure that
    differs; the test's loops declare none).
  - `Stmt.scopeExt` is gone: M2's `Stmt.ext`/`Prog.ext` replaced it.
  - `Examples/Tactics/CoreStep.lean`: 22 programs, one or more per rule
    family, each resolved, run by `Core.symex`, its erasure equal to
    today's `symex` with the covers dropped, and kernel-checked
    (`Eq.refl`), over `StandardExample`, `TestSuite` (memory arrays,
    arrays of mapping-holding structs), `CallsExample` and two contracts
    of its own (a pair and a memory return; a `try`).  Each loop arm has
    its program, `whileNoVariantDiamond` among them.  Arms no program
    reaches are not pinned: the file's docstrings name the taclets each
    program fires.
  - For the calctools lane: its `Premise` quoter needs the four new
    constructors.
  - `Calculus/Core/Logic.lean` (M3 landed): `holds` on scoped formulas over
    `State C Γ`, terms read by position and `Update.lean`'s symbols on
    `State.glob`, `Upd.apply` (parallel; `decl` pushes, `pop`/`drop` drop),
    `Frames.run`, a hidden binder a universal.  The premise shapes are
    proved once (`Premise.sound_update`, `_unfold`, `_inline`, `_bind`,
    `_capture`, `_split`, `_check`, `_done`, each: what the statement's run
    must be for `p.fml m ω κ φ` to give `⟨ s; ω κ ⟩ φ`, no freshness
    premise), with `Val.eval_up` and its kin (a shifted part reads in the
    pushed state as before).  Proved arms: `localValueAssign`,
    `valueDeclSkip`, `storageLocalDeclSkip`, `revertBox`/`revertDiamond`,
    `localValueDeclInitDrop`, a block, `binopUnfoldLeft`, `unopCapture`,
    `requireConditionCapture`, `assertConditionCapture`, `ifElseSplit`,
    `requireSimple`, `assertSimple`.  A split is sound only where its
    condition holds a `bool` (`hb`): M3's values are untyped, so an `int`
    in a `bool` local would make both goals vacuous; M4a's typed values
    discharge it (it is the cover goal today's split proves).
  - Left: soundness of the other arms (the shapes are there; each needs
    its statement's run equation), `holds_erase` against today's `holds`
    (with M3's `Agree`, `Semantics/RunErase.lean`), and a
    `Premise.sound` over `Stmt.step` once every arm is proved.

### M6a lane: the speed gate (kernel, `Eq.refl` of `symex n φ = ψ`)

Measured with `Solidity/Scratch/CoreBench.lean` (not committed), median of 5
(3 for e1×5), fuel 5000 both sides, on a machine shared with three other Lean
agents (±20% noise between runs), after the schema variables' shift became
`Val.up` and its kin (no `Thin`; e2 was 1.45× with `.wk up`).  e1 is
`if (alice.age == 4) { total = 1; } else { total = 2; }; uint y = total;`,
e2 `uint x = alice.age; uint y = x + 1; alice.age = y;`, e3
`uint x; x = 4; uint y = x + 1; require(y > 3); total = y;`, e4
`uint x = alice.age; if (x + 1 == 4) { uint z = x; total = z; } else { total = 2; }`
(a captured condition: its branches weakened by `Prog.wk up`); ×n repeats
the program n times.

| program | steps today / Core | today | Core | ratio | symex then `fresh`: today / Core |
|---|---|---|---|---|---|
| e1 | 15 / 13 | 25.2 ms | 29.6 ms | 1.17 | 31.4 / 24.6 ms |
| e2 | 6 / 5 | 7.4 ms | 10.5 ms | 1.42 | 9.9 / 7.0 ms |
| e3 | 11 / 10 | 17.7 ms | 15.3 ms | 0.86 | 22.3 / 12.6 ms |
| e4 | 15 / 13 | 27.2 ms | 34.6 ms | 1.27 | |
| e1×5 | 435 / 403 | 7.6 s | 2.6 s | 0.34 | |
| e2×10 | 51 / 50 | 99 ms | 122 ms | 1.23 | 106 / 100 ms |
| e3×10 | 101 / 100 | 1267 ms | 440 ms | 0.35 | 1348 / 451 ms |

- Repeated branching programs (e1×5, e3×10) are about three times faster:
  a branch shares the rest of the program as a frame (`seq ω κ`) instead of
  copying `thn ++ ω` into each goal, and there is no cover goal.  A single
  branch is not (e1 1.17×, e4 1.27×).
- Every program reduces faster (last column: the symex projected to a
  number, no comparison of terms), but the `Eq.refl` check is up to 1.42×
  on the smallest (e2, 3.1 ms more): the kernel compares the result with
  the quote node by node, and every node carries its contexts (result DAG
  195 nodes against 114; its type check 0.58 ms against 0.06 ms).  The
  shift without `Thin` moved e2 from 1.45× to 1.42×, within the noise: the
  weakening was not the cost.
- Gate: within 20% on four of seven (e1, e3, e1×5, e3×10); outside on e2
  (1.42×), e4 (1.27×) and e2×10 (1.23×), by 3–23 ms each; in total 3.2 s
  against 9.0 s.
- **Verdict (Decision 9): passed.**  On a strict reading it failed on
  e2, e4 and e2×10, and passed on aggregate (3.2 s against 9.0 s); the lead
  ruled the aggregate the gate, the straight-line overhead a cost to
  reduce.
- Reducing it (round 3, `Solidity/Scratch/CoreBench.lean`, median of 7;
  e2 legacy 7.3 ms):
  - the reduction is not the cost: `Core.Fml.maxIdx (Core.symex n φ)`
    checked against its number, which evaluates the whole result, is
    7.3 ms, today's `Eq.refl` 7.4 ms; the `Eq.refl` against the quote is
    10.6 ms.  The comparison with the quote costs about 3 ms more than the
    evaluation, for today's formulas about nothing;
  - against the quote declared as a constant first (its type check out of
    the measurement): 10.0 ms, so typing the quote is 0.6 ms of it;
  - **contexts as named constants** (every context of `φ` and `ψ` declared
    once, `ctxᵢ := t :: ctxⱼ`, both sides written with them, a scratch
    pass over the quoted `Expr`): 10.6 ms on e2, 1.42–1.46× against 1.45×,
    e4 1.27× against 1.30×, e2×10 1.07–1.26× against 1.17–1.25×: within
    the noise.  The kernel's reduct carries the input's contexts along, so
    they were mostly shared already;
  - **a projection**, the erasure checked instead of the scoped result
    (`Core.Fml.erase [] (Core.symex n φ) = ψ'`, which `holds_erase` would
    make enough for the closer): 14.7 ms, slower, since `erase` names every
    position;
  - so the remaining cost is per node of the comparison: the kernel infers
    the type of both sides of every pair it compares that is not one
    object (proof irrelevance first), and a scoped node carries two to
    five context arguments more (result DAG 195 nodes against 114).  What
    would remove it is not to compare terms at all: a Boolean structural
    equality on `Core.Fml` evaluated by the kernel (`decide`), with its
    soundness lemma, or fewer nodes (`Idx` as a number with a proof).
    Neither is done; both are larger than this lane's round.
- **Verdict: the gate fails on a strict reading** (e2, e4, e2×10), and
  passes only on aggregate.  Under Decisions 1 and 7 that triggers the
  Church-typed fallback for the calculus.  Before taking it, two cheaper
  fixes aim at exactly the measured cost (the comparison of contexts, not
  the reduction): quote contexts as `let`-bound constants, or check a
  projection of the result instead of the whole term.  This lane has not
  taken the fallback; the call is the user's.
- **The lead's call (Decision 9): passed.**  The aggregate wins; e2's few
  milliseconds are to be reduced, not a fallback trigger.

### M6a lane: how `dl{ … }` will write a scoped taclet

The cutover (after M4) re-targets `Taclet` at `Core.Stmt C Γ Γ'`
(`Taclet C k m : Stmt C Γ Γ' → Premise C Γ Γ' → Prop`) without touching the
rule lines of `Calculus/Rules.lean`: the macro (`RuleSyntax.lean`,
`schemaAt`/`declVar`) inserts what scoping needs, and the printer hides it.

1. **Schema variables are positions or parts read in the `\find`'s context
   `Γ`.**  `v`, `lhs`, `lsv`, `mv` become `Idx Γ t`, expression schema
   variables (`se`, `nse`, `sp`, `nsp`, `e`, …) parts of `Γ`
   (`Simple C Γ p`, `SPath C Γ T`), program variables (`thenStm`, `ω`)
   `Prog C Γ Γ₁` with `Γ₁` a fresh implicit.
2. **A fresh declaration pushes.**  Reading the premise's statements left to
   right, the macro keeps a count `d` of the fresh locals declared so far
   (`T se = …`, `T storage sp = …`, `ie`, `mv`: `declVar`'s stems).  A
   fresh local is `.here` lifted by the declarations after it; every schema
   variable of the `\find` read after `d` declarations is weakened `d`
   times: an `Idx` by `.there`, a part by its `up` (`Val.up`, `SPath.up`, …,
   `Calculus/Core/Step.lean`; no `Thin`, Gate G0's condition 1).  The premise is `Premise.unfold P (Ext.push^d .refl)`: the pop
   `Premise.fml` puts after it (`pop .capture`), which prints as nothing.
3. **The statement's own declaration binds.**  `T v = e; ⇝ v = e;`
   (`localValueDeclInitDrop`, `storageLocalDeclInitDrop`,
   `memoryLocalDeclInitDrop`) is `Premise.bind v t [v = e↑]`: `v` is `.here`
   and `e` weakened once; the binder prints as nothing, so the line reads
   as solkey's `⟨[ v = e; ]⟩`.
4. **A declaration's update declares.**  `T v; ⇝ { v := defVal(T) } ⟨[ ]⟩`
   is `Upd.nil.decl v …`; an assignment's `{ v := se }` is
   `Upd.nil.snoc (.local v …)`, its right-hand side lowered as today
   (`Calculus/Core/Lower.lean`).
5. **A branch is a block.**  `⟨[ thenStm ]⟩` in a split's goal is the
   program variable as it is; `Premise.fml` adds the block's pop
   (`pop .block P.scopeExt`), printed `}` by `Core.Fml.show`.  Side
   conditions stay as today (`side_cond`), stated on the parts.
6. **The printer** (`#taclet`, `PrintedRules`) drops `↑`/`.there` on schema
   variables, the capture's pop and the hidden binder, so every printed
   rule line is unchanged; `Calculus/Core/Taclet.lean`'s three constructors
   are what the macro emits for `localValueAssign`,
   `storageFieldRead_unfold_rightFst` and `ifElseSplit`.

Soundness against M3's interpreter, to prove when `Core.Stmt.run` lands
(`holds σ φ` the scoped formulas' meaning over `State C Γ`):

    theorem Core.Premise.sound (h : Taclet C k m s p) (ω : Prog C Γ' Γ₁)
        (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) (σ : State C Γ) :
        holds σ (p.fml m ω κ φ) → holds σ (.modal m (.cons s ω) κ φ)

with no freshness premise: the fresh locals are positions pushed and popped
by the premise itself.  Until then `Taclet.erase` carries it over from
`Taclet.sound`, given `holds_erase`.

- Left for M6a: `holds_erase` (M3's `Agree`, `Semantics/RunErase.lean`), the
  soundness of the arms not proved in `Calculus/Core/Logic.lean`;
  the remaining taclets of `Core.Taclet` (by the macro, at the cutover);
  `Hyps`/`Proves`; a `sol_symex` on `Core` (`normValid` with
  `Core.Fml.quote`); chains, `Derive.residue` and ProofTree; the
  delaborator for formulas with schema variables (`#taclet`, `#wp`).
**The prototype** (`Calculus/Core/Schema.lean`, lane `intrinsic-calctools`)
does 1, 2, 5 and the side conditions for three lines, as `scoped
macro_rules` on the same `dl{ ⟨[ s; ]⟩ ⇝ p }` syntax, so the lines are
`Rules.lean`'s text (`storageFieldRead_unfold_rightFst` with `v` for `lhs`:
the scoped syntax has no holes yet); `Taclet.toCore`/`ofCore` check that they
write `Core.Taclet`'s hand-written constructors, and a pin shows the
insertions (`v.there`, `SPath.alias Idx.here`, `Ext.refl.push`, the
`autoParam` side condition).  How it carries over to `RuleSyntax.lean` at
the cutover:

- **One threaded list instead of `Scope`'s names.**  `schemaStmt`/
  `schemaProg` already thread a `Scope` left to right; it becomes the
  prototype's `Fresh` (the fresh locals, newest first, and their kinds).
  `declVar` pushes; `headOf` looks a name up there first (a fresh local is
  `Idx.there^j .here`, `j` its distance from the newest) and otherwise reads
  a `\find` schema variable weakened `Fresh.length` times (`idxAt`, the
  family's `up`).  `headAt` is unchanged: it picks the constructor by the
  position.
- **The witnesses stay auto-bound.**  The proofs a name carries (`hfld`,
  `hgsp`, `hmv`: `proofIdent`), the `rfl`s of literals and `hop`/`hq` are
  read in `Γ` and do not mention positions, so weakening never touches
  them; the side conditions (`sideConds`) are stated on the `\find`'s parts,
  in `Γ`, as today (`taclet_side%`).
- **The premise closes its scope.**  `schemaPremise`'s unfold arm wraps
  `progTerm`'s `Prog.cons` chain as `Premise.unfold P (Ext.push^d .refl)`
  with `d` the fresh locals the block declared; a `T v = e;` find whose
  premise drops the initializer (3. above) becomes `Premise.bind`, a
  `T v;` one `Upd.decl`; a split takes `BlockKind.block` when the `\find`
  is an `if`, `.capture` otherwise (`require`'s `revert();`).
- **Names resolve at the use site.**  The prototype writes `Taclet`
  unqualified (`mkIdent`), so a line means the `Taclet` in scope; today's
  quotations are hygienic and fix `Solidity.Stmt.*`.  At the cutover they
  name `Core.*` (or, after M7's rename, the same names again).
- **The printer is already there**: `Calculus/Core/Delab.lean` prints a
  scoped taclet's line as today's (`Examples/Tactics/CorePrint.lean` pins
  the three, `#taclet` included), so `PrintedRules`, `#taclet` and the
  ProofTree pins need no change for the frames, binders and weakenings.

- Left for M6a: `holds`/`holds_erase` (needs M3's `State C Γ`); the rest of
  `Stmt.step`'s arms (index reads and writes, copies, memory, calls, `try`,
  loops, compound assignments, `push`/`pop`, `transfer`/`send`, `&&`/`||`,
  the conditional) and the `Premise` constructors `branches`, `cases`,
  `inv`; the remaining taclets of `Core.Taclet` (by the macro, at the
  cutover); `Proves`' soundness and the rules for `branches`/`cases`/`inv`
  (`Calculus/Core/Proves.lean` states the rest); a `sol_symex` on `Core`
  (`normValid` with `Core.Fml.quote`); chains, `Derive.residue` and
  ProofTree; a `dl!{}` reader for `#wp`/`#step` on scoped formulas (M6b;
  their printing is `Core.Delab`'s).

### M6a lane: tooling (`intrinsic-calctools`, 2026-10-07)

- **Quoters** (`Calculus/Core/Quote.lean`): `Fml.quote`, `Tm.quote`,
  `Upd.quote`, `Frames.quote`, `Premise.quote`, each writing every context
  out and hash-consing the result (`ShareCommon`, condition 7).
- **Printing with schema variables** (`Calculus/Core/Delab.lean`): a scoped
  `Expr` is translated into its erasure's `Expr` (each free variable of a
  scoped type gets a twin of the erased type with its name; a position is
  the name the term declared, `.there` and `up` on a schema variable
  vanish; a constructor maps to the erased one of the same name, contexts
  dropped) and printed by `RuleSyntax.lean`'s printers, so the text is
  today's by construction.  What erasure loses: a capture's pop, an
  update's pop and the hidden binder print as nothing; a block's end in a
  formula prints `}`, through a printing-only production (`core_item`,
  written with at least one `}` so that no program today's grammar reads
  parses two ways).  Delaborators for `Core.Taclet` (with solkey's branch
  labels), `Core.Premise`, `Core.Fml`; `#taclet` resolves `Core.Taclet.*`
  (`Tools/Inspect.lean`: the solkey and printed lines of the rule of the
  same name; its soundness pending M3).  `Examples/Tactics/CorePrint.lean`
  pins the three taclets against `Rules.lean`'s lines and the strategy's
  formulas, from their quoted `Expr`, against `Core.Fml.show`.  Not
  covered yet: a call and a `try` (printed `‹…›`), and a sequent
  (`Core.Proves`).
- **`Hyps`/`Proves`** (`Calculus/Core/Proves.lean`): the telescope
  `Hyps C Γ₀ Γ` (`pre`, `upd`, `havoc`, `all`, `bind`, `anon`), `wrap`/
  `fresh`/`boxOnly` by `casesOn`, and `Proves` with `intro`, `allIntro`,
  `updIntro`, `bindIntro`, `update`, `unfold`, `bind`, `split` (two goals),
  `check`, `done`, `empty`, `closeTrue`; a derivation of
  `[ if (b) { } else { } ] true` checks.  Soundness waits for M3.

### M6a lane: soundness part B (`intrinsic-sound2`, 2026-10-07)

The arms of `Calculus/Core/Blocks.lean` against `Core.Stmt.run`, in
`Calculus/Core/SoundKit.lean`'s shape (`Stmt.StepSound`):

- `Calculus/Core/RunWk.lean`: a weakened program runs as the program
  (`Stmt.run_wk`, `Prog.run_wk`, by the mutual recursion, every statement).
  The state of the wider context is `τ.lift h d` (`Env.put`: `τ`'s locals
  where `h` keeps, `d`'s elsewhere); the locals `h` drops are kept
  (`WkRel`, `Env.off`), a scope's end pops alike on both sides
  (`Thin.Over`, `Prog.wk_over`), a loop whose every turn is lifted runs
  lifted (`Loop.run_map`).  It is what the call's `Prog.wk (Thin.atop …)`
  and the diamond's `Prog.wk up` need.
- `Calculus/Core/SoundCalls.lean`: `Stmt.stepSound_call`, for the four
  kinds of result, inlined (`expand_function_body`: the frame popped, or
  dropped from under the returns by `Premise.inline`) or with an argument
  captured (`functionCallArgCapture`, `Args.eval_capture`: the arguments
  before it are simple, so read without effect).
- `Calculus/Core/RunFrame.lean`: `Mutability.lean`'s `frame_of_within`
  on scoped syntax (`Stmt.run_frame`), positionally: of the locals at
  least `d` deep only the ones `writesAt d` lists change (`LocAgree`), the
  global part only in storage and ledger, and those only when
  `nonpayable` (`GFrame`).  `holds_anonHavoc` turns a state in the frame
  into one `{anon(xs)}` (`{havoc}`) covers.
- `Calculus/Core/SoundLoops.lean`: `whileInvariantBox`,
  `whileInvariantDiamond` (`Loop.run_variant`, ported to any state) and
  `Stmt.stepSound_loop` (with `SoundBlocks`' `whileUnwind`, `loopExit`,
  `whileClose`, `whileNoVariantDiamond`).
- **The anonymised list stays as it is.**  The body's own locals are popped
  at the end of every iteration (`Run.loop` drops `body.ext`), so the
  premise read under `{anon(xs)}` lives in the loop's context, where they do
  not exist: soundness does not need them listed (the erasure still differs
  from today's `{anon(…)}` by those names, M6a notes above).
- **One hypothesis left, under the diamond**: the condition reads as a
  `bool` wherever it returns (`Val.BoolValued`, `stepSound_loop`'s `hcb`,
  for `m = .diamond` only).  Today's rule proves it as a cover goal; M3's
  values are untyped (a `bool` storage read may hold an `int`), so it is
  M4a's typed values that discharge it, as `State.Typed` does a split's.
- Found on merging: `Semantics/RunErase.lean` (M3) and
  `Calculus/Core/Fml.lean` (this lane's calculus) both declare
  `Solidity.Core.Prog.outNames`, so a module importing both fails
  ("environment already contains `Prog.outNames.match_1`"), the root
  `Solidity.lean` among them.  One of the two needs renaming.

### Gate G0: passes, under conditions

The spike (`Solidity/Scratch/IntrinsicSpike.lean`, not committed) has seven
statements (`assignLocal`, `declLocal`, `declStorage`, `write`, scoped `ite`,
`loop`, `call` over a closed frame), `Prog Γ Γ'` with a variable output
index, `Frames` with `pop .capture`/`.block`, `storageFieldRead_unfold_rightFst`
as a capture and `ifElseSplit` into `pop .block`, a typed run, `resolve` from
the named toy, hand quoters, and a symex checked by the kernel (`Eq.refl` of
the compiled-and-quoted result, `Environment.addDeclCore`, timed). The program
has 43 top-level statements (five blocks; the symex variant drops the loop
and the call). U is today's shape: names, unscoped locals, `stuck`,
`thn ++ ω`.

| Variant | symex, kernel | run, kernel | result DAG (hash-consed) |
|---|---|---|---|
| U, names (reference) | 3.8–3.9 s (500 steps) | 164–184 ms | 1170 |
| I, `(Var × LTy)` contexts, `match` | 51.8 s | 380 ms | |
| J, `LTy` contexts, `match` | 45.1 s | 293 ms | |
| K, `LTy` contexts, `casesOn` + structural | 6.5 s (686 steps) | 44 ms | 1566 |
| **K, `Fml.rec` step + `implemented_by`** | **3.0–3.3 s (0.8×)** | **44 ms (0.25×)** | **1566 (1.34×)** |

- Kernel ≤ 1.3×: yes for K with the recursor step (0.8× symex, 0.25× run).
  The literal's own check is 0.8 ms against 0.15 ms (5×, negligible).
- Quoted size ≤ 2×: yes as a hash-consed DAG (result 1.34×, literal 1.96×);
  unshared trees are 26–37× larger, because every node carries its contexts.
- No `Meta.reduce` fallback: the quoter covers every constructor of the
  closed term, `Idx`/`Ext`/`Frames` included.
- `cases` with no generalisation: works on `Prog Γ Γ'`, `Prog Γ Γ`,
  `Prog [] [t]` and `Stmt Γ (t :: Γ)` (the cyclic index is closed by
  acyclicity); `induction` on `Idx` and a structural proof of `run_append`
  work too.

The named-scope retry was not needed. The conditions, which M2–M6 follow:

1. **No `match` on an indexed family in kernel-evaluated code.** The equation
   compiler casts every index (`x = a → x₁ ≍ x₃ → motive`, then `Eq.ndrec`)
   even for `_` patterns, and the kernel pays a context comparison per cast:
   11–13× on symex, 4× on a fold. Hot functions use `T.casesOn`/`T.rec` with
   the motive generalising the indices and the dependent arguments passed
   after it (`Prog.casesOn (motive_2 := fun Γ Γ₁ _ => Frames Γ₁ Γ₀ → …) P … κ`).
   `match` stays fine on parameter-only families (`Expr Γ`, `SPath Γ`) and on
   elaboration-time code (`resolve`, quoters).  `Stmt.wk`/`Prog.wk` are not
   elaboration-time only: `ifElseUnfold` runs `Prog.wk up` in the kernel
   (`Calculus/Core/Step.lean`); a rule's expression schema variables use
   `Val.up` and its kin instead, which match only on parameter-only
   families.
2. **The fastest form is `T.rec` + an `@[implemented_by]` twin** written with
   `casesOn` + structural recursion (the code generator rejects `T.rec`),
   linked by a theorem (`stepR_eq`, by induction, `show`/`rw`/`rfl`).
   `casesOn` + structural alone compiles and costs 1.7×.
3. **Labels stay out of the index**: `Ctx := List LTy`, the name on the
   binder (`declLocal x`, `Args.cons x`). With `(Var × LTy)` the literal is
   three times larger (tree 206k against 67k) and symex 15% slower.
   `resolve` and printers keep the names beside the context
   (`List (Var × LTy)` and its `map (·.2)`).
4. **`Env Γ` is computed from Γ** (`Unit`, `t.Denote × Env Γ`), not an
   inductive family: `get`/`set`/`drop` are recursions on `Idx`/`Ext` over
   projections, no casts. That is the 0.25× run.
5. **Scope ends are suffixes** (`Ext Γ Δ`: `refl`, `push`) rather than the
   general `Thin`; `Prog.ext` and `Ext.trans` recurse on one argument.
   `Thin` with `keep` is only for `Stmt.wk`/`Prog.wk`.
6. **No administrative steps**: `Premise.fml` takes the rest ω and the frames
   κ apart, so an update continues into `box ω κ φ`, not into
   `box nil (seq ω κ)` (that doubled the steps and cost 1.23×).
7. **The quoter hash-conses contexts** (`ShareCommon`, or a per-context cache).

Pitfalls met: a `casesOn`-style definition has no per-constructor equations
(`simp [f]` loops on `f.eq_1`), so the rule lemmas are stated by hand and
proved by `rfl`; mutual `casesOn` motives are `motive_1`/`motive_2`; Lean
promotes a uniform first index to a parameter (`Premise`, `Ext`), which
changes the motive and breaks structural recursion unless that argument is
bound before the colon; inside `if x = y then match u, t with …` the
fall-through arm loses the refinement of `t`, so compute it before the
`match`. `Stmt.wk` is stated as
`Thin Γ Δ → Stmt Γ Γ' → (Δ' : Ctx) × Thin Γ' Δ' × Stmt Δ Δ'` (mutual with
`Prog.wk`) and elaborates as is.

## Design (from the scoping review, design 3 "staged core")

END STATE (names after the final rename; during migration the typed families live in `namespace Solidity.Core`, and today's `Stmt C` stays as the elaborator's output IR plus the erasure target).

-- AST.lean, merging ECtx/LocalTy (Syntax.lean:2134-2145), BTy/Ctx (Syntax.lean, the locals check) and Evm LTy (Compile.lean:434)
inductive LTy | val (p : PrimTy) | alias (R : RefTy) | mem (R : RefTy) | old | oldNet
abbrev Ctx := List (Var × LTy)              -- innermost first; the Var is a printing label only
inductive Idx : Ctx → LTy → Type            -- data, positional (de Bruijn index)
  | here  : Idx ((x, t) :: Γ) t
  | there : Idx Γ t → Idx ((y, u) :: Γ) t
inductive Thin : Ctx → Ctx → Type           -- order-preserving embedding (scope end / weakening)
  | done : Thin [] []
  | keep : Thin Γ Δ → Thin (b :: Γ) (b :: Δ)
  | drop : Thin Γ Δ → Thin Γ (b :: Δ)
def Idx.name : Idx Γ t → Var                 -- for #wp, pins and FreshNames printing

-- Syntax.lean: every family threads Γ
inductive Simple (C) (Γ : Ctx) : PrimTy → Type
  | lit (n : Int) (h : p.admits n = true) | bool (b : Bool)
  | local (i : Idx Γ (.val p)) | env (k : EnvKey) (hp : p = .uint)
SPath C Γ T (.alias (i : Idx Γ (.alias R))), Loc C Γ T, MPath C Γ T (.var (i : Idx Γ (.mem R)) (hm : R.memOk = true)),
MLoc/Val/Src/ARhs/MRhs/NewLhs/MSrc/OpLoc/ExtCall/LoopAnn C Γ …   -- Γ threaded, nothing else changes
mutual
inductive Stmt (C) : Ctx → Ctx → Type
  | assignLocal (i : Idx Γ (.val p)) (r : Val C Γ p) : Stmt C Γ Γ
  | rebind (i : Idx Γ (.alias R)) (r : ARhs C Γ R) : Stmt C Γ Γ
  | declLocal (x : Var) (p : PrimTy) (init : Option (Val C Γ p)) : Stmt C Γ ((x, .val p) :: Γ)
  | declStorage (x : Var) (R : RefTy) (init : Option (ARhs C Γ R)) : Stmt C Γ ((x, .alias R) :: Γ)
  | declMem (x : Var) (R : RefTy) (hm : R.memOk = true) (init : Option (MRhs C Γ R)) (hd : …) : Stmt C Γ ((x, .mem R) :: Γ)
  | ite (c : Val C Γ .bool) (thn : Prog C Γ Γ₁) (els : Prog C Γ Γ₂) : Stmt C Γ Γ        -- branches scoped
  | loop (a : LoopAnn C Γ) (c : Val C Γ .bool) (body : Prog C Γ Γ₁) : Stmt C Γ Γ         -- popped per iteration
  | call (f : Name) (args : Args C Γ ps) (ret : CallRet C Γ rs Γ') (body : Prog C (rs ++ ps) Γf) : Stmt C Γ Γ'
      -- body closed over its own frame; no hsep/Arg.separatedFrom; ret exports CallRet.rets / mv into Γ'
  | tryCall (e : ExtCall C Γ) (rets : Binders ρ) (ok : Prog C (ρ ++ Γ) Γ₁) (err : Prog C Γ Γ₂)
      (code : Binders κ) (pnc : Prog C (κ ++ Γ) Γ₃) (other : Prog C Γ Γ₄) : Stmt C Γ Γ
  | … the other 20 constructors as today, at Stmt C Γ Γ, with Idx in place of Var
inductive Prog (C) : Ctx → Ctx → Type
  | nil : Prog C Γ Γ
  | cons (s : Stmt C Γ Γ₁) (P : Prog C Γ₁ Γ₂) : Prog C Γ Γ₂   -- output index always a variable: no `++` in constructor results
end
def Prog.thin : Prog C Γ Γ' → Thin Γ Γ'            -- structural, used to pop scopes
def Stmt.wk  : Thin Γ Δ → Stmt C Γ Γ' → Σ Δ', Stmt C Δ Δ'   -- used only on a found statement's own schema variables and once per call expansion

-- Semantics.lean
def LTy.Denote (C) : LTy → Type   -- val p ↦ p.Denote (Bool | {n : Int // p.admits n}); alias R ↦ Option (Path C (.ref R)); mem R ↦ HRef R; old ↦ Storage C; oldNet ↦ Ledger
inductive Env (C) : Ctx → Type | nil : Env C [] | cons (v : t.Denote C) (e : Env C Γ) : Env C ((x, t) :: Γ)
def Env.get : Env C Γ → Idx Γ t → t.Denote C ;  def Env.thin : Thin Γ Δ → Env C Δ → Env C Γ
structure State (C) (Γ : Ctx) where storage : Storage C; heap : Heap C; env : Env C Γ; net; selfBalance; tx
  -- Storage C: HList over C.vars of SVal T (mutual SVal/SFields indexed by Ty via structDef); Heap C: positional typed objects
inductive Halt | revert | panic | diverge          -- `stuck` deleted at M4
def Stmt.run : State C Γ → Stmt C Γ Γ' → Except Halt (State C Γ')
def Prog.run : State C Γ → Prog C Γ Γ' → Except Halt (State C Γ')

-- Calculus: solkey's `c# … #c` as data
inductive BlockKind | block | capture               -- `}` printed, or invisible (a Lean-only scope end for fresh se/sp/ie)
inductive Frames (C) : Ctx → Ctx → Type
  | nil : Frames C Γ Γ
  | seq (ω : Prog C Γ Γ₁) (k : Frames C Γ₁ Γ₀) : Frames C Γ Γ₀
  | pop (b : BlockKind) (h : Thin Γ Γ') (k : Frames C Γ Γ₀) : Frames C Γ' Γ₀
inductive Upd (C) : Ctx → Ctx → Type                 -- assigning elements Γ→Γ, declaring elements Γ→(x,t)::Γ
inductive Fml (C) : Ctx → Type
  | modal (m : Modality) (P : Prog C Γ Γ₁) (k : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) : Fml C Γ
  | upd (m) (U : Upd C Γ Γ') (φ : Fml C Γ') : Fml C Γ
  | all (x : Var) (p : PrimTy) (φ : Fml C ((x, .val p) :: Γ)) : Fml C Γ | anon (xs : List (Σ t, Idx Γ t)) (φ : Fml C Γ) | …
inductive Premise (C) (Γ Γ' : Ctx)
  | update (U : Upd C Γ Γ') | unfold (P : Prog C Γ Γ'') (h : Thin Γ' Γ'')   -- fresh captures dropped by `pop .capture h`
  | bind (x : Var) (t : LTy) (P : Prog C ((x,t)::Γ) Γ')                         -- `T v = e; ⇝ v = e;` (binder printed invisibly)
  | split (c c' : Fml C Γ) (P : Prog C Γ Γ₁) (Q : Prog C Γ Γ₂)                 -- no cover goal: conditions cannot be stuck
  | …
def Premise.fml : Premise C Γ Γ' → Frames C Γ' Γ₀ → Fml C Γ₀ → Fml C Γ
  -- .unfold P h, k, φ ↦ .modal m P (.pop .capture h k) φ   : ω is never re-typed
inductive Taclet (C) (k : Nat) : Modality → Stmt C Γ Γ' → Premise C Γ Γ' → Prop   -- k only names fresh vars (se1, sp1)
inductive Hyps (C) : Ctx → Ctx → Type                -- telescope: `{U}` and `∀` hypotheses extend scope
inductive Proves : RuleSet → Hyps C [] Γ → Fml C Γ → Prop

-- Evm
abbrev Machine.mem := Nat → Word                     -- local i at level Γ.length - 1 - i
def compileStmt : Stmt C Γ Γ' → List Instr           -- total; frame for a call at levels Γ.length…
def inFrag : Frag Γ → Stmt C Γ Γ' → Option (Frag Γ') -- fragment + fragile aliases only; no scoping conjuncts
theorem compile_correct : inFrag F P = some F' → Sim C F σ m → … (no `not_stuck`: Halt has no stuck)

-- Checker from the existing frontends (kept as the elaborator back end)
def Stmt.resolve (Γ : Ctx) : Syntax.Stmt C → Except String (Σ Γ', Core.Stmt C Γ Γ')   -- Var ↦ Idx by lookup, scopes explicit
theorem resolve_erase : resolve Γ u = .ok ⟨Γ', s⟩ → s.erase = u
theorem run_erase : (s.erase).run σ.erase = (s.run σ).map State.erase  -- modulo EnvAgreeExcept on popped locals; the M2–M6 bridge
---WHAT STAYS
These stay extrinsic, on purpose.

1. **The EVM fragment and fragile aliases** (`inFrag`, `Frag Γ`; Compile.lean:461-566, 449). This is a fact about the compiler target, not a typing fact:
   - `pop`/`delete` leave the Solidity context unchanged (Γ' = Γ) but kill aliases on the EVM side (Correctness.lean:736, 1154).
   - Literal ranges, `binInFrag`, `static`, `wtPush`, and "no memory/send/try/loop" would otherwise either restrict the source language for every layer or need a second copy of the syntax (`FStmt`) with an erasure proof.
   - `compileStmt` is already total. Only `compile_correct` keeps the fragment hypothesis.

2. **Function and modifier bodies in `Contract`** stay `RawStmt` (Syntax.lean:245-276). A typed body would make `Contract` contain `Stmt C`, which is indexed by `C`. The elaborator stays the only checker of declared bodies; each call site's `Stmt.call` body is typed.

3. **Taclet soundness and closer completeness** are theorems by nature (`Taclet.sound`, `Fml.valid_iff_reduce`). The closer's `LFml` is a decision-procedure IR reached by a sound reflection. It is ported last (M6c), and only if its gate passes.

4. **Storage canonicity beyond shape** stays a lemma: map-key uniqueness, a default being a default (Reachability `canon`), and `tight` (Constructibility). Making it intrinsic needs sorted or functional maps, which would undo what `decide +kernel` over association-list stores relies on (Semantics.lean:958-1100, 977-985).

5. **Definite assignment of `T storage p;`.**
   - `LTy.alias R` denotes `Option (Path …)`, and reading an unset alias reverts. solc rejects such reads statically, so no solc-accepted run reaches it.
   - A flow-sensitive "unset" index would need a context meet at every `ite` join. That collides with `ifElseSplit`, whose branches continue into the same ω.
   - It is listed as an optional refinement, not a milestone.

6. **The elaborator's narrow integer widths** (`LocalTy.val p bits`, `fitCheck`/`narrowPost`) stay elaborator-only until `PrimTy` gains widths. That is a language change, not a scoping one.

7. **Divergence** (`Loop.run` via `Classical.choose`, Semantics.lean:1620-1630) is semantics, not typing, and stays.

8. **Fresh-name numbering** (`Taclet C k`, `Hyp.fresh`/maxIdx, Logic.lean:311) is kept only to print `se1`/`sp1` the same way, so pins don't change. It carries no soundness obligation: names are labels on a positional context, so shadowing is harmless.

9. **Fallback if the M0 gate fails** for the calculus: the calculus stops at Church-typed program variables (`Var` carrying its `LTy`, a total typed env, KeY's `\programVariables`). Every other layer is still intrinsic, and only declare-before-use inside formulas stays extrinsic. This matches KeY, where program variables are global.
---
M0 (risk first, 3-5 days, nothing merged except a doc row). Record the baselines that every later milestone is gated on:
- `TestSuite/Derived9-11` (20.2 s, docs/testsuite-proofs.md:1400) and the whole `SolkeyTestSuite`;
- `Examples/ProofTree.lean` (50 `#guard_msgs`) and `Examples/Chains` (188 theorems, 623 links);
- `./scripts/check-corpus.sh`;
- `Evm/Correctness.lean` (stmt_sim at `maxHeartbeats 470000`, :1996) and `Evm/Examples.lean` (21 decide/rfl).

Then build a spike in `Solidity/Scratch/` (never committed): `Idx`/`Thin`/`Env`, six `Stmt C Γ Γ'` constructors, `Frames`, one capture taclet (`storageFieldRead_unfold_rightFst` with `pop .capture`), `ifElseSplit` with `pop .block`, a compiled `symex` with a hand quoter, and kernel `rfl` on a 40-statement program, against the same toy without indices.

Gate G0, to proceed with the positional Idx design:
- kernel check at most 1.3× and quoted Expr size at most 2×;
- no `Meta.reduce` fallback is hit;
- `cases` on `Prog C Γ Γ'` works without generalisation.

If G0 fails, retry with named `lookupBy` Bool witnesses (the c26d16e^ Kernel style). If that fails too, the calculus takes the Church-typed fallback.
M1 (semantic debt, current representation, 1-2 weeks, merge). Remove the stuck causes that need no index.
(a) A negative `**` exponent (Semantics.lean:802, 838) and a negative transfer/send amount (:1471, :1485) revert. `Simple.lit` gets `(h : p.admits n = true)`, the EVM's literal range moved into the syntax.
(b) `R.memOk` proof on `declMem`/`deleteMem`/`MPath.var`, keeping a mapping out of memory in the syntax (`allocDefault`'s stuck arms at :674-682 stay, reached by the closer's untyped terms, until M4c).
(c) In the elaborator, `declare` every `freshCapture` (Syntax.lean:2700, 2707, 2724-2729, 2752, 3627).
(d) Lower the reference ternary (hoist :3451-3463) to `T storage sp1; if (c) { sp1 = a; } else { sp1 = b; }`.
(e) Add `Binding.unset`: `declStorage R x none` binds it, and a read of it reverts. `storageLocalDeclSkip` (Rules.lean:336) gets a rule-map deviation row.
(f) The elaborator self-checks `Prog.wt Γparams P` at every `sol{}`/`solc_import`/`spec!` site. The two TestSuite programs (Derived3:69, Derived7:67) and Branch.lean:236-245 must pass.

Gate: pins unchanged except the deviation row, and TestSuite time within 5%.
M2 (typed syntax plus checker, 2-3 weeks, merge). Add `LTy`/`Ctx`/`Idx`/`Thin` to AST.lean and the `Core.*` families to a new `Syntax/Core.lean` (registered in Solidity.lean).
- `Core.Stmt.erase`, `Stmt.resolve`, `resolve_erase`.
- `Core.Prog.quote` (Idx as `.here`/`.there`, no proofs to synthesise except `admits`/`memOk`, which are `Eq.refl`).
- Typed `Stmt.call`, with args closed and the body at `rs ++ ps`. resolve un-inlines the renamed callee locals to frame positions, using `CallRet` and the elaborator's `Γf` at :3655.
- Scoped `ite`/`loop`/`tryCall`/block.

A lint test runs `resolve` on all 449 imported functions and on every `sol{}` site (compiled, through `#guard`).

The bridge rule: `Core.*` and the untyped `Stmt` coexist only until M7, with a dated row in docs/kernel-port.md. This is the one deliberate exception to 'replace in place'; the old Kernel/ was deleted because it lingered. Gate: elaboration time of the sol{} sites within 10%.
M3 (typed interpreter over the locals, 2-3 weeks, merge).
- `Core.State C Γ` with `Env C Γ` (storage and heap still untyped in this milestone), and `Core.Stmt.run`/`Prog.run` with scope pops via `Prog.thin`.
- `run_erase` against `Stmt.run`, modulo `EnvAgreeExcept` on popped locals, reusing Semantics/Agree.lean.
- `Stmt.wt`/`Prog.wt`/`Ctx.has`/`EnvWT` (Syntax.lean's locals check; Soundness.lean) become corollaries of resolve plus run_erase, then are deleted.
- `Stmt.run_wt` is restated as `Core.Stmt.run` preserving the RunWT remainder (storage, heap, heapWf).
- `Reachable` (Reachability.lean:1814) is redefined over `Core.Prog C [] Γ'`. Problem.lean:131/140/169 statements are unchanged.
- The Constructibility builder (:91-183) emits `Core.Prog` (`fill : … → Σ Γ', Core.Prog C Γ Γ'`), and KeepΓ (:990-1202) disappears.

Gate: the Typing build within 20%, and nothing on the calculus path changes.
M4 (typed values, storage and heap, 4-6 weeks, merge in three PRs).
- **4a: `PrimTy.Denote`.** This removes cause B (asInt/asBool, pickBranch, guardOk, the junk arms of checkArith :873-876). uint is `{n : Int // p.admits n}`, with arithmetic still on Int literals, so the kernel never unfolds `Nat.land` (keeps 56642ee).
- **4b: `SVal : Ty → Type`.** It is mutual with `SFields` over `structDef` (exact members by construction), `Storage C` is an HList over `C.vars`, and paths are `Path C T T'`. This removes cause C: find/save/checkIndex/arrayLen/push/pop/copyStToM's map arm. `defaultForTy` gets a structRank-structural definition so the kernel reduces it.
- **4c: a positional typed heap.** `HeapTy.Extends` becomes a returned `Thin`-like extension. `copyMToSt` recurses on Ty, which removes the cycle arm at :710. This removes cause D.

At the end of 4c, `Halt.stuck` is deleted from `Core`. The untyped side keeps its stuck through `run_erase`.

Gates: Corpus `decide +kernel` and the 8 concrete stores (Semantics.lean:958-1100) within 20%. No whnf timeouts on structDef: per-contract stores stay named constants.
M5 (EVM on Core, 2-3 weeks, merge).
- `Machine.mem : Nat → Word` is level-addressed; the 14 `mload`/`mstore` sites compute `Γ.length - 1 - i`.
- `Sim C F σ m` becomes `∀ i : Idx Γ (.val p), ReprV p (σ.env.get i) (m.mem (level i))`.
- `Sim.bindVal`/`bindAlias`/`bindFragile`/`weaken` (Correctness.lean:1052-1160) become `Env.cons` plus a `Thin` restriction.
- `wtStmt` loses its scoping conjuncts and becomes `inFrag : Frag Γ → Stmt C Γ Γ' → Option (Frag Γ')`.
- `not_stuck` (:2460) and `never_stuck` (Theorems.lean:236) are deleted, since the type proves them. The ReprV `_inv` lemmas (:182-200) go.

Gate: `stmt_sim` must pass at 470000 heartbeats or less (AGENTS forbids raising it), and the Evm/Examples decide examples within 20%.
M6a (calculus cutover at the modality boundary, 6-10 weeks, the largest milestone, its own worktree lane).

Typed `Upd C Γ Γ'`, `Fml C Γ` with `Frames`, `Hyps`, `Premise C Γ Γ'`, and `Taclet C k m (s : Core.Stmt C Γ Γ')`. The dl{} macro (RuleSyntax.lean `schemaAt`/`declVar` :600-657) inserts two things itself, so every rule line in Rules.lean stays textually the same:
- `↑` on the found statement's schema variables reused after a capture;
- `pop .capture` for the 54 fresh-declaring rules.

Other rule changes:
- `ifElseSplit` continues into `pop .block`, which lets the table claim solkey's `blockEmpty`. A call's frame claims `functionFrameEmpty`/`functionBodyExpand`, shrinking `RuleShapes.unclaimedTaclets` (:482).
- `localValueDeclInitDrop`/`storageLocalDeclInitDrop`/`memoryLocalDeclInitDrop` use `Premise.bind`, printed as solkey's `⟨[ v = e; ]⟩`.
- `Premise.coverFml` and the `cov` goal (Logic.lean:41, 67) are deleted, giving KeY's two goals.

In this milestone, `Stmt.step`, `Fml.stepAt`, `symex`, the quoters, chains (program links), `Derive.residue` and ProofTree move to Core. The post-modal closer keeps working through `Fml.erase : Fml C Γ → Legacy.Fml C` and one lemma, `holds_erase`.

The SolKey reader breaks here, because LeanShape matches `Stmt.*` arities. It needs the user's go-ahead before regenerating GenProved on a branch in side-projects.

Gate (hard stop): Derived9-11, the chains, and Examples/ProofTree within 20% of M0. Repin the pins once, for `cov` removal and block printing.
M6b (formula-level frontends, 2-3 weeks).
- The dl!{} reader (Notation.lean `elabUpd` :858, `scopeHints` :932-990) produces exact Γ, with default-uint free names as explicit outer `Fml.all`.
- `Post C Γ₀`, so no weakening of φ is ever needed.
- Problem.fml/Spec.lean:478/Frontend/Problems.lean bind parameters as the context.
- spec `old`/`oldNet` get `LTy.old`/`.oldNet`.
- Callbacks: `ExecS I : State C Γ → Stmt C Γ Γ' → COut Γ'`. `iteStuck`/`loopStuck` (Semantics/Callback.lean:168, 224) and the `hI : I.vars = []` hypotheses are deleted, replaced by `Invariant.fml : Fml C []`. `havoc` ranges over typed `Storage C`.
M6c (closer port, optional, behind a gate, 4-8 weeks). Move Close/ReadWrite/UpdateRules/StateParts/Decide*/Closer/ChainRewrites (about 25k lines, about 650 env-API references) from `Legacy.Fml` to typed `Fml C Γ`, module by module, keeping `Fml.erase` until the last module.

If any module is more than 20% slower, it stays on the erased form permanently, and the reflection is documented as the decision procedure's IR.
M7 (cut-over cleanup, 2-3 weeks).
- The elaborator emits Core directly, or keeps today's Stmt as a private IR feeding `resolve`. Pick whichever M2's timings favour.
- Delete untyped `Stmt.run`, `run_erase`, `Typing/Soundness` wt/run_wt, and Semantics/Agree's fresh-name lemmas, which have no users left now that freshness is positional.
- Rename `Core.Stmt` → `Stmt`.
- Run `check-orphans`, `check-doc-paths`, `solkeycheck` and `check-testsuite`.
- Update docs: module-map.md:148, loops.md:116/120/288, solc-validation.md:26/324 (whose 'not stuck' claim becomes true), lean-key-rule-map.md rows for blockEmpty/functionFrameEmpty/capture pop/unset alias.
- Run the read-only review pass (finder plus skeptic per area).
---RISKS
Speed (AGENTS warning, before any edit): this reverses the design choice of 6c174cc/c26d16e. Syntax.lean:17-21 and Typing/Soundness.lean:9-13 kept locals unscoped so that rules could declare se1/sp1 without re-typing ω. The old Γ-indexed port recorded that Meta.reduce through indexed families is about 100× slower, that `cases` fails with 'dependent elimination failed', and that an inner match does not refine indices (c26d16e^:docs/kernel-port.md:214-227). No commit removed the index for measured speed, but it does touch the paths made fast by 7541cad (quoted symex), 2ff6a0f (nospecialize, runCache) and 02f363b (sol_prove by one kernel evaluation). The `pop .capture` frame is the design's answer to the 6c174cc rationale, and M0 must confirm it before anything merges.
The bridge period (M2-M7) has a typed Core beside the untyped Stmt. That conflicts with the 'replace in place, not beside' memory, and the old Kernel/ was deleted for lingering. Mitigation: a dated deletion row, and `run_erase` as the only bridge theorem. If M6a stalls, two syntaxes live on.
Rule fidelity:
- `pop .capture` frames and the invisible binder of `Premise.bind` are Lean-only scope markers, so printers must hide them for `#taclet`/PrintedRules/ProofTree pins to keep solkey's `\find`/`\replacewith` shape. Each needs a rule-map row.
- `storageLocalDeclSkip` (`T storage lsv; ⇝ ⟨[]⟩`) becomes `{lsv := unset}`, a visible deviation.
- On the other side, `blockEmpty`/`functionFrameEmpty`/`functionBodyExpand` become claimed (RuleShapes.lean:450-482), and the `cov` goal (not in KeY) disappears.
The SolKey reader (side-projects lean/solkey) depends on Taclet constructor names and arities and on `Stmt.*` arity in LeanShape. M6a breaks its 590-reference generated `Corresp/Proved.lean`. Regenerating it requires the user's explicit go-ahead (memory: do not touch the side-projects reader unless asked).
Semantic change: scoped blocks and loops pop locals, and today they outlive the branch. This follows solc (≥0.5 C99 scoping) but changes `ifElseSplit`'s continuation (now through a pop frame), loop frames (`Prog.loopFrame`, `Fml.loopAnon`), modifier `_; _;` (commit 9ab7d94) and lowerReturns (Syntax.lean:3064-3110), where the continuation copied into branches may see branch locals. Each needs a solc-alignment.md row.
Dependent elimination: `Prog.cons`'s output stays a variable (no `Δ₂ ++ Δ₁`), but `Thin`/`Suffix` casts in `Env.thin`, `Frames.pop` and Stmt.step's dispatcher (Completeness.lean:531) can still produce 'motive is not type correct' in the about 387 match arms across 28 files. Dispatcher arms must use top-level patterns and `if h :`, as the old port learned.
Typed storage through `structDef` (a String match) may make the kernel whnf structDef in defeq checks. This risks whnf timeouts in Corpus `decide +kernel` and in concrete stores (Semantics.lean:977-985 already records one). uint as a subtype must not make the kernel unfold `Nat.land` (56642ee).
Callee frames: the typed `Stmt.call` body is closed over `rs ++ ps`, so expansion needs `Prog.wk` (O(|body|) once per call). Three return paths must be exported in the caller's output context: `CallRet.val`, `CallRet.rets` re-declared by elabTuple (:4129), and the memory return `mv` (elabMemCall :3583). Getting this wrong would break 449 imported functions at M2's lint.
Memory: Lean workers already use 3-4 GB on Decide.lean and Derived*. M6a touches both, inside the 32 GiB session cap, so at most two Lean agents can run, and only one during the M2/M4 low-module rebuilds.
Scope creep: M6c (about 25k closer lines) may not pay off. The plan allows it to stop at the `Fml.erase` reflection, which leaves the decision-procedure IR extrinsic. Users asking for 'everything intrinsic' should be told this before M6c starts.
