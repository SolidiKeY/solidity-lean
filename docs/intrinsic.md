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
| M4 | lane `intrinsic-values` merged 2026-10-07: typed values, storage, heap, typed run and `trun` erasure (M4 lane); left: the typed run on the interpreter's path, delete `stuck`, retire old `Stmt` | typed values, storage, heap; delete `stuck`; retire old `Stmt` |
| M5 | M5.1–M5.3 done and merged 2026-10-07 (compiler, `Sim`, `compile_correct` over `Core`, M5 lane); left: delete `wtStmt`, `not_stuck` and the untyped compiler, which wait for M4 to retire `Stmt` | EVM on typed syntax; delete `wtStmt`, `not_stuck` |
| M6a | lane: every `Stmt.step` arm and `Premise` ported; gate passed (Decision 9) | calculus: `Fml C Γ`, `Frames`, `Premise`, symex, chains, ProofTree |
| M6b | lane `intrinsic-frontend` 2026-10-07: reader, obligations, specs, callbacks (notes below) | `dl!{}`, specs, callbacks |
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
  - Not true in general before the M2–M3 freshness lane (below):
    `resolve`'s output from the elaborator was not always `Fresh`.  A raw block, a `for` init and a
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
  - `RunInv C` (glob part, per-local part monotone in `H`, blind to the
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
    by `holds` over the untyped one.  Closed by `ReachableU.reachable`
    (M2–M3 review, freshness lane).
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
- Done (freshness lane, 2026-10-08), the item above and the next one:
  - **Decision: rename apart, no scope marker.**  A marker `resolve` turns
    into `Core.Stmt.block` would need a block in `Syntax.lean`'s untyped
    `Stmt`, which every interpreter, rule and printer matches on, and which
    M4 retires.  Instead the elaborator renames a flat block's local apart
    before elaborating (`freshenBlocks`, `Syntax.lean`): a raw block,
    `unchecked`, a `for` init and the `_;` a modifier repeats are flat; a
    branch, a loop's body, a `try` clause and a call's body are `resolve`'s
    scopes.  A flat local whose name is declared later in the scope
    `resolve` reads it in is renamed `x_1` (KeY's `VariableNamer` spelling,
    the least index naming nothing in the program or the state variables),
    in its block only: Solidity's scope ends there, so no later statement,
    postcondition or caller sees it, and a redeclaration keeps its name.  A
    user-style name, not a capture (`se4`): `captureExpr` skips a fresh name
    as a capture holding its value, which a mutable local is not.  Applied
    at every entry: `elabProg`, `elabProgAt.go` (and `solc_import`), each
    inlined body after its modifiers (`elabCallRet`), a `dl!{}` modality and
    a `cdl!{}` one.  Shadowing a local in scope is still refused, with the
    elaborator's message.
  - **`resolve` checks `Fresh`** (`Syntax/Resolve.lean`; `Prog.Fresh` moved
    there from `RunErase.lean`): a binder of a name in scope or of an
    enclosing frame is refused, and `resolveStmt`/`resolveProg` return
    `Fresh` with the erasure, so `Prog.resolve_fresh` holds by construction.
    `strict := false` skips it for a formula's program (`cdl!{}`,
    `Fml.resolveN`), which may shadow a `∀` or an update binder
    (`CoreNotation.lean`'s `x = 1 → ⟨ uint x = 2; ⟩ x = 2`).
  - `ReachableU C st` (`Calculus/Problem.lean`): a block `resolveCheck [] us`
    accepts runs untyped from `C.initState` to `st`.  `ReachableU.reachable`
    by `Prog.resolve_of_resolveCheck`, `resolve_erase`, `resolve_fresh` and
    `run_erase` at `ns = []` (the erased initial state is `C.initState` by
    `rfl`); `wt_of_reachableU` follows.  `run_erase` applied to a resolved
    program and a state elaborates at once here (the `callsCore` timeout
    of M3.2 is not reproduced).
  - Pins: no existing pin changed (the four targets build, the corpus and
    `SolkeyTestSuite` included): `Branch.lean`'s two examples were
    `example`s, Loops' `ModifierRuns` body declares nothing, and
    `Benchmark/Syntax`'s `Twice` applies two modifiers, each renamed by the
    inliner.  New pins show the renaming: `Branch.lean` (`bool x_1`,
    `int i_1`, two loops of one index, shadowing refused),
    `Benchmark/Syntax.lean`'s `TwiceLocal` (`se3_1`, the first run of a body
    `_; _;` repeats).  `CoreNotation.lean`'s three shadowing pins failed
    under a strict `cdl!{}` until it read non-strict.
- `Reachable` is now reachability by the scoped interpreter, while `holds`
  reads `wt(storage)` over the untyped one; `reachable_canon`,
  `shape_iff_reachable`, `wt_iff_reachable` and `reachable_iff` say nothing
  yet about the untyped run.  Said in M3.3, `testsuite-proofs.md`,
  `solkey-feedback.md`, `Problem.lean`'s and `Reachability.lean`'s
  docstrings.  Closed: `ReachableU`, `ReachableU.reachable`, `wt_of_reachableU`
  (`Calculus/Problem.lean`).
- The memory conditional of references refuses `c ? a[i] : b[j]` when the
  default of the type is not well-formed (`hoist`'s `T memory mv;`): now in
  `solc-alignment.md`'s row.
- `Core.lean`'s docstring cited a missing `Stmt.run_eq_runC`; it names
  `Stmt.runR_eq`/`Prog.runR_eq`.

### M5 notes

- M5.1 (lane `intrinsic-evm`, 2026-10-07): `Evm/CoreCompile.lean` compiles
  `Core.Stmt`/`Core.Prog`, total, beside `Evm/Compile.lean`.
  - A local of `Γ` at position `i` lives at level `b + (Γ.length - 1 - i)`;
    `b` is the frame base, `0` for the program, the caller's next free level
    for a call's body (closed over `rs ++ ps`: parameters from the base, then
    the return variables).  `Machine.mem` stays `Var → Word` while the old
    compiler lives: a level `l` is the cell `cell l` (`.fresh "%" l`, printed
    `%l`), and `Machine.memAt` is the level-addressed view.  A scope's cells
    are not cleared at its end; every declaration but an unset
    `T storage x;` writes its cell; that alias is `dead` in `Frag` and not
    read until a rebind writes the cell.
  - `inFrag : Frag Γ → Stmt C Γ Γ' → Option (Frag Γ')`.  `Frag Γ` is one flag
    per local (`ok`, `fragile`, `dead`): the alias facts `TyCtx` kept beside
    the types.  An unset `T storage p;` is `dead`.  A branch's or block's
    result is restricted to `Γ` (`Frag.restrict`, a `drop` by lengths, so no
    `Prog.ext` is needed) and the branches met.  A call's body is checked from
    `Frag.init (rs ++ ps)`; the caller's fragile aliases are dropped when the
    body may shrink an array (`Stmt.shrinks`), which the shared `TyCtx` did
    implicitly.  Out, as before: memory, `send`, `try`, loops, a call of
    several returns (`CallRet.rets`, no code) or of a memory return; since
    W1 (lane `w1-evm`), also a struct copy at a type whose structs repeat a
    member name (`assignIn` needs `(Ty.ref R).nodupS`, so a copy at `BadDup`
    leaves the fragment): the typed run copies by position, the
    representation reads by name.
  - Every definition over `Stmt`/`Prog` lists all 27 constructors, with no
    catch-all, and nested shapes go to helpers (`assignCode`, `opLocCode`,
    `assignIn`, `declStorageIn`).  A catch-all arm made the equation compiler
    fail to build the splitter for an indexed `Stmt C Γ Γ'`, so no equation
    lemmas and no `simp [compileStmt]`.
  - `compileStmt_erase`/`compileProg_erase`: `⌊compileStmt b s⌋ =
    ⌊Evm.compileProg (s.erase ns)⌋` (`⌊·⌋` maps `Instr.forgetCell`, which
    forgets `mload`/`mstore` operands), for `s` with `Stmt.sepArgs ns s`.
    Axioms: `propext`.  Cells differ by design.  `sepArgs` is needed because
    `erase` of a call with unseparated arguments binds them in the body after
    the return variable is zeroed (same words, another order).
    `Stmt.pushes`/`Stmt.pays` are `Evm.pushesP`/`Evm.paysP` of the erasure
    for every statement (`pushes_erase`).
  - `Evm/CoreExamples.lean` ports the 45 compile `decide` examples of
    `Evm/Examples.lean` (not the four interpreter theorems, which need the M5
    `compile_correct` and are in `Evm/CoreInterpreter.lean`, M5.3), plus a scoped-branch run, a `pop` in a branch
    forgetting an outer fragile alias, and `sameCode` on 14 programs.
    Programs come from `sol{}` through `Prog.resolve`, which the
    elaborator's `whnf` does not reduce, so they run under `decide +kernel`
    (the kernel evaluates the resolution too).  Timing, the 44 non-`**`
    examples as one block (`Elab.async false`, two runs on a loaded machine):
    old `decide` 2.5–4.0 s, old `decide +kernel` 1.8–2.4 s, new 2.3–3.3 s
    (1.3–1.4× the old kernel run, 0.8–0.9× the committed `decide`; split
    by phase under "G0 condition 1" in the M5 lane);
    `pow_run` 3.5–5.5 s in all three.
- Left for M5 after M5.1: see "M5 lane" below.

### M5 lane

Lane `intrinsic-evm` (worktree `solidity-lean-i-evm`), beside M2.3/M3 on
`intrinsic`.  Status 2026-10-07, round 3 (after M3): the correctness
proof over `Core` is done, with no `sorry` and the axioms `propext`,
`Classical.choice`, `Quot.sound`; see "M5.3" below.

- M5.2 `Evm/CoreSim.lean`, done (no `sorry`):
  - `Look Γ := ∀ {t}, Idx Γ t → Binding`, the locals by position: what
    M3's `Env.get` will instantiate (the binding a denotation stands for).
    `Look.cons` is `Env.cons` (the pair), `Look.drop h` (along an `Ext`) a
    scope's end, `Look.set` an assignment.  Kept abstract so that M3's choice
    of `LTy.Denote` (untyped `Value` until M4a, `PrimTy.Denote` after) does
    not change the statements.
  - `Sim C L b F σ ρ m`: storage, ledger, bound and transaction as before
    (`σ.env` unread); `vals : ∀ i : Idx Γ (.val p), ∃ v, ρ i = .val v ∧
    ReprV p v (m.memAt (lvl b i))`; `aliases`/`fragile` by `F.get i`.  The
    design's `ReprV p (env.get i) (m.mem (level i))` once values are typed
    (M4a drops the `∃ v`).
  - Old → new: `bindVal`/`bindAlias`/`bindFragile`/`unbind` →
    `consVal`/`consAlias`/`consFragile`/`consDead`; `weaken` → `drop`
    (a scope's end, `Frag.restrict`) and `flags` (`meet`, `meet_right`,
    `storeDrop`); assignments `setVal`/`setAlias`/`setFragile`; `stack`,
    `push`, `book`, `mono`, `store'` as before; `congrMem` (memory changed
    above the frame only).  Each is a few lines: positions need no
    `TyCtx.set` case split, only `lvl_there`/`lvl_ext`/`lvl_eq_iff`.
  - A call's frame: `Sim.enter` (the callee's frame at base `b + Γ.length`)
    and `Sim.return`/`returnDrop` (the caller's locals back over the
    callee's machine).  Their memory side is static:
    `storesFrom_compileStmt` (code compiled at base `b` stores to no level
    below `b`), `storesFrom_callFrame` (arguments, return variable and body
    store at `b + Γ.length` and above), and `exec_mem`/`StoresFrom.exec`
    (code that does not store to a cell leaves it).  `NoStore` covers the
    expression and guard codes (`expLoop 255` is held opaque: unfolding it
    hits the recursion limit).
  - Check: the whole file re-elaborates in about 7 s (MCP wall time,
    machine shared with three other Lean agents).
- `resolve` returns separated calls (`Stmt.resolve_sepArgs`,
  `Prog.resolve_sepArgs`, `Syntax/Resolve.lean`): `Resolved` and
  `resolveProg`'s result carry `sepArgs`, which moved there from
  `Evm/CoreCompile.lean`.  So `compileProg_resolve`: a resolved program
  compiles as the block it was resolved from, up to cells, with no
  hypothesis.  (This edits a module below `Semantics.lean`; the merge into
  `intrinsic` rebuilds from there.)
- **G0 condition 1: the EVM compiler is exempt.**  `compileStmt`/`compileProg`,
  `inFrag`/`inFragP`, `Stmt.pushes`/`pays`/`shrinks`,
  `Stmt.asserts`/`Prog.asserts`, `argsCode` and
  `retEnterCode`/`retLeaveCode` `match` on `Stmt C Γ Γ'`, `Prog C Γ Γ'`,
  `Args C Γ ps` and `CallRet Γ rs Γ'`, and `Evm/CoreExamples.lean` and
  `Evm/CoreInterpreter.lean` evaluate them in the kernel.  They are kept as `match`: the calculus never
  evaluates them (no symex or closer step reaches the compiler), the only
  kernel evaluations are the example checks of `Evm/CoreExamples.lean` and
  the fragment, bound, `pays` and `asserts` checks of
  `Evm/CoreInterpreter.lean`, and every proof
  about them (`compileStmt_erase`, `storesFrom_compileStmt`, the `Sim`
  lemmas) is structural and uses their equation lemmas.  Timing (scratch
  module, `Elab.async false`, the same 44 non-`**` examples as one block
  each, two runs, the order of the two compilers swapped between them):
  elaboration alone (each program under `(fun _ => true) P`, warm)
  1.03–1.04 s; elaboration plus `Prog.resolve` (`(resolve [] P).toBool`)
  1.08–1.10 s, so `resolve` is 0.04–0.07 s; old compiler and run
  (`decide +kernel`) 1.77–1.89 s; new resolve, compiler, fragment check and
  run 2.25–2.47 s.  So the kernel cost of compiling and running is 0.73–0.85 s
  old against 1.15–1.36 s new (1.5–1.6×), and none of it is `resolve`; how
  much of it is the `match` casts against the level arithmetic and `inFrag`
  is not measured.  If the EVM examples ever join a speed gate, the fix is
  condition 1's: `Stmt.rec` with the motive over the indices for
  `compileStmt`/`inFrag`, the `match` versions kept as `implemented_by`
  twins and for the equation lemmas.
- M5.3, done (no `sorry`), over M3's `Core.Stmt.run`/`Core.Prog.run`.
  **Superseded in W1** (lane `w1-evm`, "W1 evm lane" below): the symbols
  these bullets name are gone; read `Look.ofTEnv` for `Look.ofEnv`,
  `TState.sem` for `σ.glob`, `ValOutT`/`LocOutT` for `ValOut`/`LocOut`,
  `Core.Prog.trun` from `freshT C 0 …` for `Core.Prog.run (State.ofSem
  (State.fresh C 0))`.  The structure and the timings below are M5.3's.
  - `Evm/CoreExpr.lean`: `Look.ofEnv σ.env` instantiates `Look` (each
    local's `LTy.enc` of `Env.get`; `Look.ofEnv_cons`/`_set`/`_drop` are
    `Look.cons`/`set`/`drop`), and the simulation is `Sim … σ.glob
    (Look.ofEnv σ.env) m`.  `simple_sim`, `spath_sim`, `loc_sim`,
    `val_sim` as the untyped ones, `ValOut`/`LocOut` on `σ.glob`.
  - `Evm/CoreStmt.lean`: one lemma per statement with no sub-program
    (`assign_sim` … `transfer_sim`).  `StmtOut` is the untyped dichotomy
    plus `Keeps` (the cells below the frame's base unchanged, and no
    array's length lowered unless the statement `shrinks`), which a call
    needs of its body; the panic case only for code that `asserts`.
  - `Evm/CoreCorrect.lean`: `stmt_sim`/`prog_sim` by mutual structural
    recursion, every arm one call: the families (`assign_family` …
    `assert_family`, what `inFrag` admits and the `CoreStmt` lemma),
    `ite_sim`, `block_sim` (`StmtOut.drop`: a scope's end pops the state's
    locals, the machine's cells stay) and `call_family` (`callNone_sim`,
    `callVal_sim`, `Sim.enter`/`Sim.back`), each sub-program's outcome a
    hypothesis.  The `cases` on a call's `CallRet` inside `stmt_sim` took
    more than 200000 heartbeats (a `whnf` timeout on the declaration);
    moved into `call_family` it is gone.  Then `compile_correct` (both
    succeed; both revert, a panic only with an `assert`; or a refused
    payment), `compile_exact`, `compile_box`, `compile_net`, `Sim.init`
    and `compile_storage`.
  - `Evm/CoreInterpreter.lean`: the four interpreter theorems of
    `Evm/Examples.lean` (`setAge_interpreter`, `overflow_interpreter`,
    `payOwner_interpreter`, `callTwice_interpreter`) over
    `Core.Prog.run (State.ofSem (State.fresh C 0)) (scopedOf P).2`, from
    `Evm/CoreExamples.lean`'s runs; fragment checks, bounds, `pays` and
    `asserts` by `decide +kernel`.  `overflow_interpreter` needs no
    `run_noPanic`: the program has no `assert`, so `compile_exact`
    excludes the panic.
  - `not_stuck`/`never_stuck`: none on the Core path.  `compile_correct`
    lists every outcome and none is `stuck`; the untyped `not_stuck`
    (`Evm/Correctness.lean`) and `never_stuck` (`Theorems.lean`) stay with
    the untyped compiler until M4 retires it.
  - Timing against the M0 baselines (same method: wall time of
    `lean_diagnostic_messages` after an edit at the top of the file, a
    fresh worker, so header load and about 1 s of round trip included;
    machine shared with other agents).  The gate: `stmt_sim` (the mutual
    block with `prog_sim`) passes at `maxHeartbeats 10000` and fails at
    5000, against 470000 for the untyped one (M0: 4.4 s by the profiler);
    its profiler items over 10 ms sum to 0.25 s (type checking 0.15 s,
    `simp` 0.05 s, pre-definitions 0.03 s).  Whole files:
    `Evm/CoreSim.lean` 7.1 s, `Evm/CoreExpr.lean` 5.9 s,
    `Evm/CoreStmt.lean` 4.8 s, `Evm/CoreCorrect.lean` 4.9 s (the four
    add 22.7 s after `Evm/Correctness.lean` (25.6 s), which they import
    and do not replace; each elaborates in its own worker, so in a build they run in
    a chain).  `Evm/CoreExamples.lean` 10.7 s against `Evm/Examples.lean`'s
    9.5 s (+13%, within the 20% gate), and `Evm/CoreInterpreter.lean`
    4.9 s.
- Left: timing the compiler on a quoter-built program (M2.3);
  `Machine.mem : Nat → Word` (with `cell = id`) once `Evm/Compile.lean`
  retires at M4; at M4, moving the machine-level lemmas the Core path uses
  out of `Evm/Correctness.lean` into a module of their own
  (`ValOut`/`LocOut`/`EnvSim`, the `*_run` code lemmas, `State.fresh`,
  `Evm.Sim.init`), then deleting `wtStmt`, the untyped
  `stmt_sim`/`compile_*`/`not_stuck`/`never_stuck` with the untyped
  compiler, and re-timing the chain.

## Cutover waves (W0–W6), plan of record 2026-10-08: moving the calculus onto Core (M4 retirement, M6a, M6c, M7)

The plan finishes each part in three steps: build the Core version beside the old one, switch the users file by file, then delete the old one. Every wave leaves `lake build Solidity SolkeyTestSuite SolidityCorpus` green.

**Decision 8, replaced:** the bridge ends at **W4**. By then the calculus, the strategy and the closer entry run on Core, and the old runs are deleted. Two IRs with no semantics stay unless the user decides otherwise:
- `Surface.Stmt` is today's `Stmt` with no run, no `Taclet` and no `wt`. It is the elaborator's output and the printers' target (`resolve`/`erase`, `Core.Delab`). M2 measured `resolve` at 0.045 ms a block, so porting about 4k elaborator lines and 2k printer lines buys nothing.
- `NFml` is today's `Fml` with `.modal` removed. It is the closer's input until the M6c waves retire it.

**One user decision is needed:** does demoting the old `Stmt` to `Surface.Stmt` count as "deleting the untyped Stmt"?

## W0 — land the four lanes (the lead, one agent)
- Merge calculus, sound2, calctools and frontend. `docs/intrinsic.md` is still `UU`; keep every lane section.
- Build the unconditional `Core.Stmt.Sound C` from `stepSound`, sound2's block arms and `WkRuns := Prog.run_wk`. Then `Core.Proves.valid` needs no hypothesis.
- **Low-module fix, before any lane branches:** make `resolve`'s output `Fresh`.
  - Today `elabBranch` emits a raw block, a `for` init and a modifier's `_` flat.
  - Emit them as `Core.Stmt.block` scope markers instead.
  - `holds_erase` on leaves needs this: two `for (uint i…)` loops must not shadow each other.
- Checks: full build, `check-orphans`, `check-doc-paths`. No pins change.
- Record the Core example timings as the W-baseline.

## W1 — off the M3 run; build the rule table beside the old one (4 lanes)
Each lane owns the files listed for it. Merge in the order the lanes are listed.

1. **`runlemmas`**
   - Owns: new `Semantics/Core/TypedRunWk.lean` and `TypedRunFrame.lean`; `Semantics/Core/Callback.lean`; `Examples/Tactics/CoreCallback.lean`.
   - Work:
     - `Prog.trun_wk`, `trun_frame`, `Loop.run_variant` over `TState`.
     - `TState.toSem ns : TState C Γ → Semantics.State` and its agreement lemmas.
     - Callbacks over `TState`; `havoc` over typed `Storage C`.
2. **`typing`**
   - Owns: `Typing/{State,Soundness,Reachability,Constructibility}.lean`, `SortCheck/Faithfulness.lean`, `Calculus/Problem.lean`.
   - Work:
     - `RunWT` mostly by construction.
     - `Reachable` by `trun`; the builder runs over `trun`.
     - Close the `ReachableU → Reachable` gap.
   - Gate: the four Typing modules ≤ 25.6 s (21.3 s +20%); Faithfulness ≤ 30.7 s.
3. **`evm`**
   - Owns: `Evm/Core*.lean`, `Corpus/Basic.lean` (`corpus_decide` on `trun`), `Tools/{Run,DiffTest,Counterexample}.lean`.
   - Work: `Look.ofEnv` over `TEnv`; `ReprV` without `∃ v`; `Machine.mem : Nat → Word`.
   - Gates:
     - `stmt_sim` within 10000 heartbeats.
     - `Evm/CoreExamples` ≤ 11.4 s (M0 9.5 s +20%).
     - `check-corpus.sh` unchanged.
4. **`rules`**
   - Owns: `RuleSyntax.lean`; `Calculus/Core/{Schema,Taclet}.lean`; new `Calculus/Core/{Rules,Completeness,RuleShapes,PrintedRules}.lean`; `scripts/core-rules.mjs`; `scripts/check-rule-text.sh`.
   - **How the 241 constructor lines keep their text:**
     - Fold Schema's insertions into `schemaAt`/`schemaStmt`/`declVar` behind `open scoped Solidity.Core.Schema`. The insertions are `Idx.there^d`, `up^d`, `Premise.unfold P (Ext.push^d .refl)`, `Premise.bind` for the three `…DeclInitDrop` rules, and `BlockKind.block` vs `.capture` on splits.
     - The script copies `Rules.lean`'s lines verbatim under a Core header. `check-rule-text.sh` diffs the two copies and must print nothing.
     - `Calculus/Core/Taclet.lean`'s hand-written constructors are deleted, along with the `Core.Schema` prototype.
   - New theorems and modules:
     - `Taclet.toStep : Taclet C k m s p → s.step k m = some p`, one `rfl` per constructor. Soundness then comes from `Stmt.Sound`, with no per-rule proofs.
     - Core `Completeness`: the dispatcher that names the fired rule, for `#step` and `sol_derive?`.
     - Core `RuleShapes`: `blockEmpty`, `functionFrameEmpty` and `functionBodyExpand` become claimed.
   - Restriction: `Step`/`Arms`/`Blocks` are frozen. Where a line cannot be produced, change the macro, or list the mismatch for W2.
   - Checks: a `#guard` that every Core rule prints exactly as the old one does (`Core.Delab`). `solkeycheck` stays at zero (no names change).

**Pins in W1:** none outside `Core*` example files.

### W1 lane `runlemmas` (2026-10-08)

Done, four modules over `TState`/`trun`, no M3 run in their statements:

- `Semantics/Core/TypedRunWk.lean`: `Stmt.trun_wk`/`Prog.trun_wk` (`TWkRel`).
  The background locals `d` are typed over the start heap and come out
  weakened along the heap the run grew (`TEnv.wk`, `offWk`); with the
  background fixed, `TWkRel.eq_lifted` gives the run as `liftedT`.  Also
  `Frames.trun` (the frames' typed run, for `holds` over `TState`) and the
  `TLoop` lemmas: `run_map`, `run_unfold`, `run_induct`, `run_variant` (the
  variant a `TRes Int`, the condition a `Bool`, so no cover).
- `Semantics/Core/TypedRunFrame.lean`: `Stmt.trun_frame`/`Prog.trun_frame`.
  A program within a mutability allocates nothing, so the frame keeps the
  heap typing (`TGFrame.H`) and compares heaps and locals by `HEq`
  (`TLocAgree`); `TState.anon`, `TState.havoc`, and
  `TState.eq_anonHavoc`/`Prog.trun_frame_anon`: a state in a loop body's
  frame is `(σ.anon xs b).havoc st nt` for some `b` (with `TGFrame.keeps`
  giving `st`, `nt` unchanged in a `view` frame).  This is the semantic half
  of `holds_anonHavoc`; the `holds` half is W2's.
- `Semantics/Core/TypedToSem.lean`: `TState.toSem ns` read straight off the
  typed parts (`LTy.TDenote.bind`), with `lookup_toSem` and the moves under
  `push`/`setLocal` (`setBy`)/`drop`/`withStorage`/`havoc`/`adopt`; the
  bridge `toSem_eq` (= `σ.erase.erase ns`) and `agree_toSem` go with
  `RunErase` at W4.
- `Semantics/Core/Callback.lean`, rewritten over `TState`: `COut C H Γ`
  carries `Out` (a call needs the heap extension to give its caller's
  locals back, `TRun.callLeave`); the invariant is a predicate on states of
  the empty context (`StateInv`), since `holds` on `TState` does not exist
  yet; `callEnter` and `tryHalt` are gone (typed entry and `keyT` are
  total).  `Prog.exec_run`, `Frames.exec_run`, `ExecP.eq_run`,
  `ExecF.eq_run`, `ExecP.forall_iff`, `ExecF.forall_iff` are proved.

Left for W2 (the `tree` lane, with `holds` on `TState` from `sound`;
its Work list carries it): everything this rewrite removed that reads a
formula — `holdsC`, `ValidC`, `TransferSem`, `holdsT`, `ValidT`,
`validT_noCallback`, `validT_withCallback`, `Modality.afterRunC_congr`,
`Modality.afterC_congr`, `after_frames_iff`, `holdsC_iff_holds`,
`holds_of_holdsC_modal`, `holds_of_holdsC_imp`, `valid_of_validC` — over
`TState`, with `StateInv := ⟨fun σ => holds σ I.fml⟩`.  Gone for good
(the typed run makes them moot): `Invariant`/`Invariant.at` (now
`StateInv`), `State.havoc`/`havoc_self`, `Val.evalB`, and the `Run.*`
lemmas (now `TRun.*`).  The M3 versions are removed with this rewrite (their only user was `Examples/Tactics/CoreCallback.lean`,
re-pinned to the typed relation).

For W2 `sound`: `TypedRunWk.lean` imports `Calculus/Core/RunWk.lean` for
`Thin.Over` and `Stmt.wk_over`/`Prog.wk_over` (syntax only), and
`TypedRunFrame.lean` imports `Calculus/Core/RunFrame.lean` for
`Prog.frame_some` and `frameMut` (syntax only).  Deleting the old
`RunWk`/`RunFrame` means moving those into these two files first.

Check: `TypedRunWk.lean` re-elaborates in about 7 s warm; `import Solidity`
elaborates with every module (no name clash).

### W1 `typing` note (2026-10-08)
- New modules: `Typing/StraightRun.lean` (the builder's straight-line typed
  run) and `Typing/TypedWT.lean` (`RunWT` by construction).
  `Reachability` now imports `Semantics.Core.TypedRunErase`, through
  `StraightRun`.
- **`Reachable` is the typed run of a program on the bridge.** It needs
  `Core.Prog.bridgeOk`: no `bool` mapping key, even in a read, and no storage
  copy at a type with a repeated member name.  It is a subset of
  `ReachableS`, the scoped run (`Reachable.reachableS`).  The six
  non-reachability witnesses are stated over `ReachableS`, the stronger
  claim: `map_default`, `struct_missing_field`, `map_dup_key`
  (`Reachability`), and `dirty_word`, `fixed_past_end`, `bool_key`
  (`Constructibility`).  `not_reachable_of_not_reachableS` gives the
  `Reachable` form.  `bool_key_not_reachable` is about the scoped run, which
  reads a key with `Value.asInt`.  The typed run writes `bool` keys
  (decision 10), which `bridgeOk` keeps out of `Reachable`.
- **The `ReachableU → Reachable` gap is closed only under premises.**
  W0's unconditional theorem is now `ReachableU.reachableS`.
  `ReachableU.reachable` (`Calculus/Problem.lean`) needs `nodupKeysB C.vars`,
  `C.vars.all okDeep` and `FitsStorage C st` (words, keys and slots in range).
  It goes through the builder (`ReachableS.reachable`).
- **`RunWT` by construction is conditional and not yet used.**
  `TState.erase_wt` needs `Ty.nodupDeep` of the state variables and of the
  heap typing (no struct with two members of one name: every struct but
  `BadDup`), and `nodupKeysB C.vars`.  `Soundness.lean` still proves
  `Stmt.run_wt` by following the scoped run, until the calculus reads the
  typed run.
- Docs outside the lane, for the lead at merge: `docs/testsuite-proofs.md`
  (the Diamond item) and `docs/solkey-feedback.md` (item 1) still say
  `Reachable` is by the scoped interpreter, and that `ReachableU.reachable`
  holds with no condition.  They should say: `Reachable` is by the typed run
  on the bridge.  The untyped run's storage is `ReachableS` unconditionally
  (`ReachableU.reachableS`), and `Reachable` when its words, keys and slots
  are in range (`ReachableU.reachable`).
- Gate, measured as in M3.3: CPU s of the module alone (`#clock`, reading
  `/proc/self/stat`, at both ends of a copy with `Elab.async false`, imports
  cached), with other lanes' agents running.  Both gates pass.

  | Module | M3.3 | W1 `typing` |
  |---|---|---|
  | `Typing/State` | 1.59 | 1.39 |
  | `Typing/Soundness` | 5.98 | 6.44 |
  | `Typing/Reachability` | 4.34 | 3.82 |
  | `Typing/Constructibility` | 9.39 | 10.66 |
  | the four (gate ≤ 25.6) | 21.30 | 22.31 |
  | `Typing/StraightRun` (new) | — | 2.69 |
  | `Typing/TypedWT` (new) | — | 0.83 |
  | the six | — | 25.83 |
  | `SortCheck/Faithfulness` (gate ≤ 30.7) | 25.57 | 25.31 |

### W1 evm lane (`w1-evm`, 2026-10-08)

- The EVM correctness proof runs over the typed run (`Core.Prog.trun`,
  `TState`), no longer M3's `Core.Prog.run`:
  - `Evm/CoreExpr.lean`: `Look.ofTEnv σ.env` instantiates `Look`
    (`Look.ofTEnv_cons`/`_set`); the global part a machine-level lemma reads
    is `TState.sem` (storage erased, ledger, funds, transaction), and the
    simulation is `Sim … σ.sem (Look.ofTEnv σ.env) m`.  The dichotomies are
    `ValOutT`/`LocOutT`, on typed results.
  - `Evm/CoreCorrect.lean`: `freshT C balance hb self hs` is the fresh typed
    state (`freshT_sem`: its `sem` is `Evm.State.fresh`), and `Sim.init`
    now takes `hb : balance < W`, since the typed state's funds are a `uint`.
  - `Evm/CoreInterpreter.lean`: the four interpreter theorems over
    `Core.Prog.trun (freshT C 0 W_pos 0 W_pos)`.
  - `Evm/CoreCompile.lean`: a struct copy needs `nodupS` (M5.1's "Out" list).
  - `Corpus/Basic.lean` (`corpus_decide`), `Tools/Run.lean` (`#run`) and
    `Tools/DiffTest.lean` (`#difftest`) run `Core.Prog.trun`.  `#run … from σ`
    reads only σ's storage, ledger, funds and transaction (`typedState?`); a
    start state with locals or memory is an error, no longer run.
- Gates:
  - `stmt_sim` within `maxHeartbeats 10000`, pinned in
    `Evm/CoreCorrect.lean`.
  - `Evm/CoreExamples.lean` 7.9 s (two runs, both 7.9 s) against the 11.4 s
    gate.  Method: a fresh worker, wall time from its start until its CPU
    stays idle (header load included, no MCP round trip); `Evm/Examples.lean`
    measured the same way takes 10.0 s.
  - Corpus: the lane changes only `Corpus/Basic.lean`; the generated modules
    and `tests/solkey/expected.tsv` are untouched, and the six `Corpus/Solc*`
    modules, which re-check every pinned `corpus_decide` verdict, check clean
    (per-file diagnostics), as do `Evm/CoreInterpreter.lean`,
    `Tools/{Run,DiffTest}.lean` and `Examples/Tools.lean`.
  - **`check-corpus.sh unchanged`: fails, by design.**  The typed
    `corpus_decide` proves every one of the 16 `evaluated` rows (a scratch
    module stating each `#eval`-pinned program as a `corpus_decide` theorem
    checks clean), so the probe will report 16 `evaluated → proved`:
    `SolcStructs.{structCopyViaMemoryLocal, structArrayElementCopy,
    structArrayElementCopyMemberwise}`, `SolcArrays.{popThenPushSlotIsZeroed,
    pushedSlotIsZeroed, deleteArrayElementOfStructs, matrixElementWriteRead}`,
    `SolcMemory.{memoryStructDefaultsToZero, memoryStructWriteRead,
    storageArrayElementCopiedIntoMemory, memoryStructToStorage,
    memoryToStorageCopyIsDeep, memoryAliasIsNotACopy}`,
    `SolcMappings.arrayElementsToMapping`, `SolcControlFlow.{swapViaTemporary,
    ifElseSelectsMemorySource}`.  The reason: the typed run has no
    well-founded definition in the kernel's way (`SVal.dflt`, a fold for the
    memory copy).  `evaluated` now means the typed route does not apply (no
    resolution, or off `Prog.bridgeOk`); `scripts/solkey-port.mjs`'s
    `EVALUATED_REASON`, its header, the scoreboard legend and the generated
    docstrings say so, which is drift in the generated text too.  At the W1
    merge the lead runs `scripts/check-corpus.sh --update` (a pin change:
    reason, the typed `corpus_decide`); the lane may not run `lake`.
    `Corpus/Basic.lean`'s memory-default example is now a `corpus_decide`
    theorem, no longer an `#eval` pin.
  - **G0 condition 1: `corpus_decide` is exempt.**  Through `decide +kernel`,
    `trunOk` evaluates `Core.Prog.resolve` (a `match` on the untyped syntax,
    which G0 had counted as elaboration-time only) and `Prog.bridgeOk` (a
    mutual `match` on `Stmt C Γ Γ'`/`Prog C Γ Γ'`, and on the index-typed
    paths) in the kernel.  Timing (scratch modules, `Elab.async false`,
    `profiler`, the 35 `proved` obligations of the six `Corpus/Solc*`):
    - whole tactic, summed: old `corpus_decide` (untyped run over the
      `dflt`-spelt store) 1.81 s, new 2.84 s (1.6×); kernel only 0.73 s old,
      1.72 s new; the slowest new obligation 0.20 s.
    - the new kernel cost by part, all 35 programs as one conjunction:
      `resolve` alone 0.78 s, `resolve` + `bridgeOk` 1.04 s,
      `resolve` + `trun` 1.14 s, `trunOk` 1.39 s.  So `bridgeOk` is about
      0.26 s (19%), `resolve` 56%, the typed run 26%.
    - `Corpus/Basic.lean`'s storage example: kernel 1.12 s old (TestSuite's
      store, spelt by `dflt`), 35 ms new; its memory example 27 ms new.
    - Kept as `match`: the whole corpus is under 3 s and no speed gate
      covers it; a `Stmt.rec`/`Prog.rec` twin of `bridgeOk` would save at
      most its 0.26 s, and `resolve` is the larger part.  If the corpus
      joins a gate, the fix is condition 1's for both (`rec` forms with the
      motive over the indices, the `match` versions as `implemented_by` and
      for the equation lemmas).
- Not done, moved:
  - `Machine.mem : Nat → Word` is deferred to W4 (`sem-del`): `Machine.lean`
    is outside this lane, and its untyped users (`Evm/Compile.lean`,
    `Evm/Correctness.lean`) go there; until then a level is the cell
    `cell l` (M5.1).
  - `ReprV` keeps its `∃ v` in `ValOutT`.
  - `Tools/Counterexample.lean` stays on the untyped `Prog.runFuel` (its
    `Fml.eval3` evaluates the old `Fml`'s modalities, `.stuck` included);
    its port is listed under W4 `sem-del`.
  - Stale since this lane, outside its files (for the lead or W4
    `sem-del`): `Examples/Tactics/Loops.lean` (line 13, "`#run` runs it";
    line 194, "`Loop.runImpl`, which the kernel never sees") and
    `docs/loops.md` (line 106) say `#run` iterates loops by `Loop.runImpl`
    over `Stmt.run` (and the sentence after ties `corpus_decide` to
    `Stmt.run`'s kernel reduction).  `#run` now resolves and runs
    `Core.Prog.trun`, whose
    loops iterate by `TLoop.runImpl'` (`Semantics/Core/TypedRun.lean`), as
    `Tools/Run.lean`'s docstring says.

### W1 lane: rules (`w1-rules`, 2026-10-08)

- **The reader** (`RuleSyntax.lean`, under `open scoped Solidity.Core.Schema`,
  `schemaTacletCore`): the same `dl{ … }` text read from `coreScope`.
  `headOfCore` makes a declared name a position (`Idx.there^j .here`) and
  weakens a `\find` schema variable past the fresh locals (`.there`, the
  family's `up`; a hole by `SHole.up` and kin, a whole right-hand side by
  `ARhs.up`/`MRhs.up`/`Src.up`/`MSrc.up`, a block by `Core.Prog.up`).  The
  premise: `Premise.unfold P (Ext.push^d .refl)`, `Premise.bind` when the
  `\find` declares, `Upd.decl` for a declared update target (and the
  invariant rules' `b`/`variant`), `BlockKind.block` for an `if`'s split, a
  check with no program, `Premise.branches` with `Branch.mk`, the invariant
  premise (`schemaInvCore`: `xs`/`hv` bound by the side condition
  `Prog.frame body = some (xs, hv)`).  A program spliced in is `Stmt.block`.
  `coreNames` then turns every name the reader wrote into its scoped twin
  (`Solidity.F.x` ↦ `Solidity.Core.F.x`; the term symbols under `Core.Tms`,
  since `Solidity.Core.MAddr` is the typed heap's; `Hole` ↦ `SHole`), and
  fails on a missing twin.  Old-mode output is unchanged (the full build
  re-checked every old pin).
- **The table** (`Calculus/Core/Rules.lean`): `Taclet` (158 lines) and
  `LeanTaclet` (8 lines) copied by `scripts/core-rules.mjs`, docstrings and
  lines verbatim; only binders change (`Val C .bool` ↦ `Val C Γ .bool`,
  `Prog.loopFrame` ↦ `Prog.frame`).  `scripts/check-rule-text.sh` compares
  docstrings and lines, binders aside, and prints nothing.  Stated by hand
  after the markers: `Taclet.blockEmpty` (scoped only: a block is a
  statement now) and `LeanTaclet.functionCallArgCapture` (today's line
  escapes to the untyped call); `Rule`.
- **`Taclet.toStep`, `LeanTaclet.toStep`, `Rule.toStep`,
  `Rule.premise_unique`** (`Calculus/Core/Taclet.lean`; axioms: `propext`,
  `Quot.sound`, pinned in `Examples/Tactics/CoreRules.lean`):
  one lemma per constructor, 153 (149 `Taclet`, 4 `LeanTaclet`) replayed
  from two `#replay_toStep` tables, 15 by hand (10 `Taclet`, 5
  `LeanTaclet`: an array's element type, a
  call's arguments, a hole that is a copy, a conditional written to a
  member, the loop rules).  The table is the plan `#derive_toStep?` found
  by `to_step_tac`'s search (holes taken apart, side conditions settled,
  `rfl` after case splits, each lemma its own heartbeat budget), so a
  re-check does not search (AGENTS.md, "Writing or fixing a tactic").  The
  search never backtracked: every plan is "n goals, each by `rfl`", and the
  replay costs what the search did, 19.2 s for `Taclet` (7 ms for
  `LeanTaclet`), in the case splits and the `rfl`s, not in failed
  attempts: `storageIndexWriteCaptureAllNonSimpleIndex` (1682 goals) and
  `memoryIndexRead_unfold_rightSndIndex` (116) 4.8 s each,
  `binopUnfoldLeft`/`Right` (667/609) 1.2 s each, the four
  `storage…Read_unfold_right{Fst,SndResult}` 0.5–0.8 s each, the rest
  under 0.3 s.  `Taclet.step_eq` stays
  as an alias (`Calculus/Core/Proves.lean` uses it).
- **Printing** (`Calculus/Core/RuleText.lean`, `#check_rule_text`, pinned):
  140 of 158 `Taclet` lines and 6 of 9 `LeanTaclet` lines print as today's
  (`Calculus/Core/DelabLean.lean` adds the printer for `Core.LeanTaclet`).
  The others need `Calculus/Core/Delab.lean`, which no W1 lane owns, **for
  W2**:
  - a hole's statement: `SHole.fill`/`MHole.fill`/`VHole.fill`/`NewLhs.fill`
    (with `SHole.up` and kin transparent) to today's `Hole.fill` and kin —
    the six `…_unfold_right…` reads through `lhs`, `ternaryToIf`,
    `ternaryCaptureCond`, `newArrayCapture`;
  - `Tms.Term.bumped` to today's `Term.bumped` — the six
    `…IncrementAssignment` rules;
  - `Premise.expandCall` to `⟨[ expand_function_body(ic); ]⟩` (with twins
    for `Args`/`CallRet` schema variables) — `functionBodyExpand`,
    `internalCallExpand`;
  - a `try` whose binders are schema variables (`rets`, `code.binders`) —
    `tryCallNoCallbackBox`, `tryCallDiamond`;
  - `progPieces` reduces a block before it looks for `up`, so `Prog.up body`
    inside a premise's program prints as an escape — `whileInvariantDiamond`;
  - `functionCallArgCapture` has no line to print.
- **Shapes** (`Calculus/Core/RuleShapes.lean`, `Calculus/Core/PrintedRules.lean`):
  today's rows by name; `blockEmpty` and `functionFrameEmpty` claimed
  (308 claimed, 15 excused); printed rules partitioned as today's.  The
  callback rows stay today's until the callback taclets are scoped (W2
  `tree`).
- **The dispatcher** (`Calculus/Core/Completeness.lean`, `ruleOf?`,
  `#rule_of m s`, pinned in `Examples/Tactics/CoreRules.lean`): the
  constructor whose line matches and whose side conditions evaluate, its
  premise checked against `Stmt.step`; a hole's statement matched by the
  hole and part read off the statement (`holeCandidates`).  It names a rule;
  a proof that every `Stmt.step` premise is some rule (today's
  `Stmt.complete`) is not stated.
- `#taclet` on a scoped taclet (`Tools/Inspect.lean`'s `soundLine`) prints
  "sound: Solidity.Core.Taclet.toStep (the premise is Stmt.step's;
  Core.Stmt.Sound)", the same for `Core.LeanTaclet`; pinned in
  `Examples/Tactics/CorePrint.lean` (on `storageFieldDelete_unfold_leftFst`:
  `storageFieldRead_unfold_rightFst` no longer prints as today's).
  `#derive_toStep?` goes on past a constructor whose search fails (a note,
  `addToStep (strict := false)`); `#replay_toStep` still fails loudly.
- Left: the Delab items above; `CallbackTaclet` on Core (W2 `tree`);
  `lake exe solkeycheck` was not run here (no rule names, sort annotations
  or `KeyTaclets.lean` changed).

### W1 integration (2026-10-08)

- **Merged** into `intrinsic`, in order: `w1-runlemmas`, `w1-typing`,
  `w1-evm`, `w1-rules`.  Text conflicts only in this file (each lane's
  section kept); `Solidity.lean` and `docs/module-map.md` merged clean, no
  duplicate import or row.  No fully-qualified declaration is declared twice
  across modules.
- **Second round**: three lanes committed their review passes after the
  first merge (`w1-typing` 7f8526b drops a dead lemma; `w1-evm` 4e63fb2
  corpus verdict wording and `solkey-port.mjs`; `w1-rules` 0258373 `toStep`
  counts, `#taclet`'s sound line in `Tools/Inspect.lean`, an axioms pin).
  Merged in the same order, no conflict; the duplicate check is still empty
  (but the known `Evm/Repr`/`Examples/Verify` `as` false positive).  The
  same four-target `lean_build` (294 jobs): green, about 8 s wall, all of
  it Lake-cache fetches but the modules those commits touched.
- **Full build: green on the first try**, no fix needed.  `lean_build` over
  `Solidity`, `solkeycheck`, `SolidityCorpus` and `SolkeyTestSuite` (294
  jobs; the last two in `defaultTargets` for the run only): 168 s wall,
  rebuilding from the Lake cache what the merge changed.  The slowest
  modules under the build's load: `Examples/Tactics/Calls` 102 s,
  `TestSuite/Derived7` 93 s, `Examples/Tactics/Decide` 70 s,
  `TestSuite/Derived8` 53 s, `Examples/Tactics/Loops` 52 s.
  No new `sorry`, `axiom`, or raised `maxHeartbeats` (the one new
  override, `stmt_sim`'s `10000`, is the evm gate).
- `scripts/check-orphans.mjs`: 280 reachable, none orphaned but the
  git-excluded `Solidity/Scratch/`.  `scripts/check-doc-paths.sh`: OK (the
  plan's three citations of the reader's `Corresp` files, which live in
  side-projects, are now module names, not paths).
- Lane gates as the lanes measured them (above): typing's four modules
  22.3 s ≤ 25.6, Faithfulness 25.3 s ≤ 30.7; evm's `stmt_sim` within 10000
  heartbeats, `Evm/CoreExamples` 7.9 s ≤ 11.4; rules' `Core/RuleText`
  print check and `scripts/check-rule-text.sh` empty.  The `SolidityCorpus`
  build re-checks every pinned corpus verdict and passes.
  `scripts/check-corpus.sh` was not run (it calls `lake`, which this session
  may not); the evm lane expects its probe to report `evaluated → proved`
  drift (the typed `corpus_decide` proves more), and re-pinning is a pin
  change, for the lead to decide.  `solkeycheck` was built, not run; no
  rule name, annotation or `KeyTaclets.lean` changed.
- Docs outside the lanes updated as the typing lane asked:
  `docs/testsuite-proofs.md` and `docs/solkey-feedback.md` now say
  `Reachable` is by the typed run on the bridge, `ReachableU.reachableS`
  unconditional and `ReachableU.reachable` under `FitsStorage`.
- The four lane worktrees are removed (the branches stay).

## W2 — soundness over the typed run; Core strategy tools (4 lanes)
1. **`sound`** (the critical path)
   - Owns: `Calculus/Core/{Logic,SoundKit,Sound*,RunWk,RunFrame,Cover,Proves,ProvesSound,HoldsErase,Step,Arms,Blocks}.lean`, and the modules it added: `Calculus/Core/{Closable,CloseErase,TLogic,TCloseErase,TProvesSound,TSoundKit}.lean`.
   - First commit, pushed on day one: `split`/`inv` lose `cov`, and the module `Calculus/Core/Cover` is deleted (`bool` locals are typed now). The other three lanes merge this commit at once.
   - Then:
     - `holds` over `TState`. Arms are re-proved through `StorageErase`/`HeapErase`'s `_erase` lemmas into `Update.lean`'s symbols.
     - `holds_of_erase` (one direction) for the hidden binder and `anon`.
     - `Proves.close`: a leaf closes if its erasure is valid.
     - `Taclet.sound`.
     - Delete the old `RunWk`/`RunFrame`.
2. **`symex`**
   - Owns: new `Calculus/Core/{Symex,Derive,Close,Termination}.lean`.
   - Work:
     - `normValid` with `Core.Fml.quote`.
     - `sol_symex`, `sol_derive`, `sol_derive?`.
     - `sol_prove`: kernel `Eq.refl` of `Core.symex`, then each leaf is erased and handed to today's closer (`close_of_erase`).
     - Uniqueness is free, because `step` is a function. Termination is either restated on Core or retired with a docs row.
   - **Early gate, in a `Core*` twin:** `sol_prove` over Derived9–11 ≤ 22.9 s (M0 19.1 s +20%).
     - If it fails, stop before W3.
     - The fix to try first is a kernel-evaluated Boolean equality on `Core.Fml`, or `Idx` as a number.
3. **`chains`**
   - Owns: new `Calculus/Core/{Chains,ChainKit,ChainGen,LastLine}.lean`, `Examples/Tactics/CoreChains.lean`.
   - Work:
     - Program links `~[r]~>` by Core rule names.
     - Rewrite links taken over from `ChainRewrites` on erasures (`Via.ofErase`). Only the direction from the erasure is needed.
     - `#chain` and `#derivation` on Core.
4. **`tree`**
   - Owns: new `Calculus/Core/{ProofTree,Sequents,Callback,Contracts}.lean`, `Tools/CoreInspect.lean`, `Calculus/Core/{Spec,Notation}.lean`, `Semantics/Core/Callback.lean`.
   - Work:
     - ProofTree, `#proof_tree`, `#wp`, `#step`.
     - `sol_spec` on `cspec!`.
     - Callback taclets and `ProvesC`.
     - The callback reading over `TState` (`Semantics/Core/Callback.lean`, removed by W1 `runlemmas`): `holdsC`/`ValidC`/`TransferSem`/`holdsT`/`ValidT` with `StateInv := ⟨fun σ => holds σ I.fml⟩`, `validT_*`, `after_frames_iff`, and `holdsC_iff_holds`, `holds_of_holdsC_modal`, `holds_of_holdsC_imp`, `valid_of_validC`, re-proved from `ExecP.forall_iff`, `ExecF.forall_iff` and `Prog.exec_run`. Then re-pin `Examples/Tactics/CoreCallback.lean` to them.
     - The **flip switch:** `open scoped Solidity.Core.Surface` makes `dl!`, `⊢`, `dl{}`, the chain notation and the `#` commands read Core. Tactics dispatch on the goal's head constant.

**Merge order:** sound → symex → chains → tree. Each later lane merges `intrinsic` and re-checks its own files.

### W2 lane `sound` (`w2-sound`, 2026-10-08)

**The cover is gone** (first commit): `Proves.split` and `Proves.inv` have
KeY's goals only, the module `Calculus/Core/Cover` (`Premise.cover`, `Fml.or`) is
deleted, and `Premise.Sound` takes no cover.  Over M3's untyped states a
`bool` local can still hold a number, so the diamond is read only from and
into states whose `bool` locals hold `bool`s (`State.BoolOK`,
`Calculus/Core/Logic.lean`): `holds` of a diamond update or modality is
`Modality.afterT`/`afterRunT`, `σ.BoolOK → …` with `BoolOK` asked of the
state it ends in.  The box is unchanged.  Where it is used:

* a split on a simple condition: the condition reads a `bool`
  (`Simple.eval_bool`), so one of `c`, `c'` holds; the stuck case is the
  box's alone (`Premise.Sound.splitStuck`);
* `whileInvariantDiamond`: the condition's update ends in a `BoolOK`
  state, so it pushed a `bool`, and the body's run ends in one, so every head
  is one (`Premise.Sound.whileInvDiamond`);
* the hidden binder (`Premise.sound_bind`) needs a witness that is `BoolOK`
  at its type: `false` for a `bool`, anything for an alias or a memory local.

Why not "the state is typed" (`RunWT`, every local of its type) as the
guard: a memory local's type can be uninhabited (no object of its type in
the heap), and then `memoryLocalDeclInitDrop`'s hidden binder ranges over no
typed value: under the diamond, with an initializer that reverts, its
premise holds vacuously and its conclusion fails.  **The same holds of the
typed state** (`LTy.TDenote (.mem R) = HRef H R`, empty when `H` has no
`R`): `holds` over `TState` needs a decision there (a binder over the heap
grown by a default object, or a diamond rule without the binder).

`holds_erase` is now for box updates and modalities only (`Fml.Plain`): the
erasure asks nothing of `bool` locals.  `Examples/Tactics/CorePrint.lean`
lost its `nofun` cover goal.  Two docstrings outside this lane still name
the deleted cover, for their owners: `Calculus/Core/Fml.lean`'s
`Premise.inv` ("under the diamond one of them, its cover: `Premise.cover`",
to drop) and `Examples/Tactics/CoreStep.lean`'s module docstring ("the
scoped calculus keeps it apart, `Premise.cover`": it has no cover goal, the
diamond reads `BoolOK` states), W3's `tactics` lane.

**`Proves.close`** (resumed after the usage limit): a leaf closes when its
erasure, the context in front and the outer locals named `ns`, is valid
(`Solidity.Valid`), under `Fml.Closable` (`Calculus/Core/Closable.lean`:
`Fml.Plain`, but hidden binders and `{anon(…)}` allowed in positive
positions, each name a hidden binder binds out of scope and left alone by
the updates above it), `Avoids bindNames ns`, and `Fml.Leaf` (no modality,
first-order where assumed: today's `close` asks `modalFree`).  The rule
asks the Bool twin `Fml.closableB` (`Closable` and `Leaf`, with
`Upd.freshB`, `Fml.foFreshB`) and `Avoids` as autoParams the kernel decides
(`rfl`, `decide`); `Fml.FO`, `Fml.Leaf`, `Fml.bindNames` and the twins are
written with `casesOn` (Gate G0, condition 1).  `Proves.lean` closes a
leaf behind a box update and a hidden binder this way.  **Box contexts
only**: over M3's states the erasure's diamond does not give `State.BoolOK`
of the state it ends in, so `close` does not fire behind a diamond update
(`⟨ x = 1; ⟩ x ≐ 1` has no derivation yet).
`holds_of_erase_valid` (`Calculus/Core/CloseErase.lean`) is the one-way
reading: the erasure holds in every untyped state that differs from one
agreeing with `σ` only at the hidden binders' names, which an update above
them leaves alone (`Upd.apply_keep`), so its validity covers every value
they take.  `Taclet.sound`, `LeanTaclet.sound`, `Rule.sound`:
`Stmt.sound` at `toStep`.

**`holds` over `TState`** (`Calculus/Core/TLogic.lean`, `tholds`, beside
M3's `holds` until the flip): terms read on the erasure (their symbols are
`Update.lean`'s, untyped until M6c), modalities run by the typed run
(`Prog.trunFrames`: the program, then the frames), binders over typed
values.  **An update** is applied to the erasure, and its rest is read in
*every typed state that erases to* the state it ends in.  No decoder of
untyped values back to typed ones is needed (a storage, a heap and its
typing, a path), and a rule's premise reaches its conclusion in the state
the typed run ends in, one of them.  The cost: `tholds` is not a function of
the erasure (two heap typings may erase alike: an empty array of any
element type), so only "premise gives conclusion" holds of a scope end's
update, which is all `Proves.tsound` uses (`tholds_exit`).
`Calculus/Core/TCloseErase.lean`: `tholds_of_erase_valid`, the induction of
`holds_of_erase_valid` read over the typed state, for `Fml.TClosable`
(`Closable` and `Leaf`, a diamond update allowed in a positive position:
the typed reading asks only of the typed states that erase to the state the
update ends in, so no `BoolOK` is needed), so `Proves.close` is sound there
too, and the flipped `close` covers diamond leaves (`tholds_of_holds`,
`tholds_iff_holds` for `Fml.FO`, for the atoms).
`Calculus/Core/TProvesSound.lean`: `Proves.tsound`/`Proves.tvalid` with the
structural part proved and the arms' part a hypothesis, `Stmt.TSound C`
(`Premise.TSound`, `Premise.Sound` over `TState`).  Not provable as stated
until decisions 2 and 3 below are taken: `Stmt.TSound` is false for a
contract with a `bool` mapping key, and under the diamond on a length past
`uint`'s range, and `Proves.tvalid` is vacuous there.  The decision taken
goes into `Stmt.TSound` (a `Prog.bridgeOk` premise, or a fixed key read in
`Update.lean`), not left a false hypothesis.

`Calculus/Core/TSoundKit.lean`: the premise shapes over `TState`
(`Premise.tsound_update` … `tsound_done`), each an equation between typed
runs read at the states they end in (`Stmt.trunSt`, `Prog.trunSt`,
`Frames.trunSt`).

**Left (the arms over `TState`, `Stmt.TSound C`)**, the bulk of the lane:
every arm of `Stmt.step` re-proved against `Stmt.trun`, through
`StorageErase`/`HeapErase`'s `_erase` lemmas into `Update.lean`'s symbols
(the shape lemmas of `Logic.lean`'s "Premise shapes" and the kit of
`SoundKit.lean` over `TState` first, then `SoundArms` … `SoundLoops` one
family at a time).  Then the old `RunWk`/`RunFrame` are deleted, after
`Thin.Over`/`Stmt.wk_over`/`Prog.wk_over` and `Prog.frame_some`/`frameMut`
move out of them (`TypedRunWk.lean`/`TypedRunFrame.lean` import them for
these, not this lane's files).  **Two decisions for the lead** before the
arms close:

1. *The hidden binder at a memory type* (above): `tholds` reads it as a
   universal over `HRef H R`, vacuous when the heap holds no `R`.  Under the
   diamond, `T memory mv = a[i];` with `a` empty and no `R` object in the
   heap reverts, while `memoryLocalDeclInitDrop`'s premise holds
   vacuously.  Options: (a) the diamond twin without the binder, a Lean-only
   rule (`T memory mv = mrhs;` read by `rebindMem`'s rules with a declaring
   update); (b) a memory local's typed value may be dangling
   (`LTy.TDenote (.mem R)` inhabited, a W1 typing change); (c) the binder
   asks for an inhabitant only under the diamond (`Fml.bind` taking the
   modality), printed as today.  Every other arm is unaffected.
2. *A length past `uint`'s range under the diamond*: the typed run
   diverges where it reads one (`lenT`), the untyped `len(…)` goes on, so
   `{v := len(storage, p)} ⟨ω⟩φ` holds where `⟨ v = p.length; ω ⟩φ` fails.
   Options: the diamond read from states whose arrays are within range (as
   M3's `BoolOK`), or `Update.lean`'s `len` diverging there too.
3. *A `bool` mapping key* (`docs/solc-alignment.md`, Decision 10): the
   typed run reads the slot `0`/`1`, `Update.lean`'s symbols are stuck on
   it (`Value.asInt`), so `{v := find(storage, at(m, b))} ⟨ω⟩φ` holds under
   the box (a stuck update says nothing) where `[ v = m[b]; ω ]φ` reads the
   slot: `Stmt.TSound` is false there, and `close` then proves
   `[ v = m[true]; ] false`.  Options: `Update.lean`'s key read hashing a
   `bool` as `0`/`1` (a low-module change, with M3's run), or the typed
   calculus restricted to `Prog.bridgeOk` programs (a premise of every
   arm, as `TypedRunErase.lean`'s bridge has).
   The first arm tried, `localValueAssign` (`sound_setLocal`), meets 2 and
   3 at once: `Val.evalT_erase` needs `bridgeOk`, and a typed `len` read
   diverges where the erased one does not.

**Also left, at the flip:**

- `Proves.close` behind a diamond update: switch its side condition to a
  Bool twin of `Fml.TClosable` once `Proves` is read over `TState` (M3's
  `Proves.sound` cannot have it, above).  Until then W2 `symex`'s
  `sol_prove` (each leaf through `close_of_erase`) does not reach a diamond
  obligation's leaves (the diamond statement of `TestSuite/Problems.lean`).
- Fold the `T*` modules back under the original names, in place:
  `TLogic`/`TSoundKit`/`TProvesSound`/`TCloseErase` into
  `Logic`/`SoundKit`/`ProvesSound`/`CloseErase` (`tholds` as `holds`,
  `Premise.TSound` as `Premise.Sound`, `Proves.tsound` as `Proves.sound`),
  and delete M3's `holds`, `State.BoolOK` and the `Modality.afterT`
  machinery.

### W2 lane `symex` (`w2-symex`, 2026-10-08)

**Built** (`Calculus/Core/{Symex,Close,Derive}.lean`, pins in
`Examples/Tactics/CoreDerive.lean`):

* `sol_step`/`sol_symex` on `Core.Valid φ`: `symex_valid` from
  `Stmt.sound` (W0's unconditional soundness), the result computed by the
  compiled strategy and quoted back (`Core.Symex.normValid`,
  `Core.Fml.quote`); an obligation with no code is read by its value
  (`evaluable`).
* `sol_close` on a scoped leaf: `Valid.of_erase` (the leaf's hidden binders
  where `Fml.posB` takes them, checked by the kernel), then today's
  `sol_close` on the erasure.  A diamond update is taken only where it
  cannot set a `bool` local to a non-`bool` (`Tm.boolB`), since the diamond
  reads `BoolOK` states (the `sound` lane's cover removal).
* `sol_prove`: one kernel evaluation of `Derive.proves φ = true`: the
  strategy, `posB` and today's `Derive.proves` on the erasure
  (`Valid.of_proves`); where the closer leaves goals, one `leafᵢ` per leaf
  of today's residue (`Valid.of_residue`), checked as one more kernel
  evaluation of the strategy, its leaf's `posB` and the residue together
  (`Derive.residueOf`).  No search, so it is its own replay.
* `sol_derive`/`sol_derive?` on `Core.Valid`/`Core.Proves`: one `apply`
  per rule, cited by its taclet (`Taclet.step_eq .rule`, the rule named by
  `ruleOf?`), `case thn`/`case els` on a split.  Today's `sol_derive` is a
  macro that never fails, and Lean expands macros before it tries
  elaborators, so the scoped one is a `macro_rules` (newest first) into
  `sol_derive_scoped`, which fails on an unscoped goal and lets today's
  macro run.  The other four are elaborators that throw
  `unsupportedSyntax` on an unscoped goal (`sol_close`'s macro fails on a
  scoped goal first).
* **Leaves of the walk:** `Core.Proves` has no `close` yet (the `sound`
  lane's `Proves.close`), so `sol_derive` closes `closeTrue` leaves and
  leaves the others as `Core.Proves` goals, printed `sorry` by
  `sol_derive?`.  When `Proves.close` lands, `Walk.movesAt` ends a leaf with
  `refine close ?_; sol_symex; sol_close`, as `ProofTree.closeTacs` does.

**Uniqueness** is `Core.Stmt.step` being a function, with the rules lane's
`Taclet.toStep` and `Rule.premise_unique` (`Calculus/Core/Taclet.lean`; `ruleOf?` in
`Calculus/Core/Completeness.lean`).
**Termination is retired**, not restated: `Calculus/Termination.lean`'s
weights are 1,300 lines over the untyped syntax, and the scoped strategy is
fuelled (`Core.symex n`), so a program it does not finish fails `sol_prove`
(the leaf keeps a modality, which `posB` rejects) rather than looping.
`Termination.lean` goes with the old calculus at W4.

**Early gate: passes.**  `sol_prove` over Derived9–11's 91 obligations in
the `Core*` twins (`TestSuite/CoreDerived9.lean` … `11`, over
`TestSuite/CoreProblems.lean`), elaborated serially in one scratch module
(`Elab.async false`, `IO.monoMsNow` stamps; imports loaded): **19.4 s**
against the limit 22.9 s.  Today's `sol_prove` on the same 91, measured the
same way right after: 19.0 s (2% apart).  M0's 19.1 s is the wall time of
the three modules, so the serial sum is the stricter reading.  No fix of
the list (a Boolean equality on `Core.Fml`, `Idx` as a number) was needed.

### W2 lane `chains` (`w2-chains`, 2026-10-08)

**The relations** (`Calculus/Core/ChainKit.lean`): `φ ~> ψ` is
`φ.step = some ψ` (`Fml.OneStep`), `φ ~*> ψ` a list of them (`Fml.Steps`,
a `Type`: a chain that is that one link is a `def`; inside a longer chain
`~*>` is `Nonempty (Fml.Steps …)`, so the chain is a `theorem`), and `φ ~[r]~> ψ`
(`Fml.StepBy`) the step with the statement it fires on
(`Fml.stepFocusR`, the recursor, whose line is `Fml.stepR`'s), labelled by
a `Rule` derivation of the constructor `r` on that statement
(`StepRule`).  Each is sound as `Fml.Leads φ ψ` (`ψ` holds ⇒ `φ` holds), and
a chain (`Fml.Via`) gives `Valid φ` from `Valid` of its last line.

**Past the program** a chain goes on from the erasure of its last scoped
line (`Fml.ViaE`: the scoped links, `(last).erase [] = L`, then
`Update.lean`'s `Fml.Via L rs`), so every rewrite of
`Calculus/ChainRewrites.lean` is a link unchanged; a postcondition
`φ : Core.Post C Γ` reads there as `↑(φ.erase ns)` (`Post.erase`, its names
checked to name no fresh variable).  `Fml.ViaE.valid` takes the bridge
(erasure valid ⇒ scoped line valid) as a premise: that direction is
`Valid.of_erase` (W2 `symex`'s `Calculus/Core/Close`, not on this branch), not this lane's;
once symex is merged, `bridge := fun h => Valid.of_erase hp h` closes it.

**`sol_chain`** (`Calculus/Core/Chains.lean`) runs the strategy as
compiled code (`Fml.chainLines`: postconditions in slots, a variable
modality run as both), checks each written line against the computed one by
its erasure (`matchWritten`: the computed line keeps the scope ends and the
hidden binder its print does not show), and proves each step by kernel
`rfl`, along the line's connectives where a postcondition stands in the way,
by `Modality.casesOn` where a rule reads a variable modality.  A program
running into a block's end is written `⟨[ s; } ω ]⟩ φ` (and `⟨ … } … ⟩`,
`[ … } … ]`, `Core.Delab`'s `core_item`), read without the `}`.

**The commands**: `#derivation`, `#chain`, `#chain_rest`
(`Calculus/Core/ChainGen.lean`) and `#last_line`
(`Calculus/Core/LastLine.lean`) dispatch on a scoped first line and reuse
`Calculus/ChainGen.lean`'s grouping and rewrite search and
`Calculus/LastLine.lean`'s check on the erasure.  `#chain` writes each line
in the first of `cdl![m]{}`, `cdl!{}`, `cdl![.box]{}`, `cdl![.diamond]{}`
that reads back as it; a generated scoped chain is one declaration (no
segments).  `Examples/Tactics/CoreChains.lean` pins them, with three
generated chains each pinned (`#guard_msgs`) and pasted back and checked, and a chain proving `Core.Valid`.

**Speed**: on a branch (`if … else …`, ten steps) and a struct copy, a
scoped `sol_chain` costs about what today's does (47 ms tactic + ~130 ms
kernel against 72 ms + ~150 ms).

Left:
* an update of `a == b` (or `!=`, `*`, …) prints as an escape
  (`‹Tm.app2 …›`): `RuleSyntax.lean`'s `ppUpdElem?`/`termOpSym?` write
  `+ - /` and the four comparisons only, today's printer too (not this
  lane's file); a generated chain through one cannot be pasted;
* the bridge for `Fml.ViaE.valid` (`Valid.of_erase`, W2 `symex`'s
  `Calculus/Core/Close`), and a `Valid` proof of a
  scoped formula through a chain past the program, waits for it;
* the chain notation reads `cdl!`; reading `dl!` is W2 `tree`'s flip
  switch, and the 14 worked-chain files move in W3 `chains`.

### W2 lane `tree` (`w2-tree`, 2026-10-08)

- **The proof tree** (`Calculus/Core/ProofTree.lean`): `Core.ProofTree.build`
  and `ofFormula` grow `Calculus/ProofTree.lean`'s `Tree` (rows, labels,
  JSON and display reused) on a scoped goal `H ⊢ φ`.  The rule at a
  statement is the one `ruleOf?` names, applied as
  `apply update (Taclet.toStep .r)` (`LeanTaclet.toStep` for Lean's rules,
  `rfl` for the non-emptiness of `branches`/`cases`); an operator family's
  rule prints as KeY's taclet at the operator (`keyName`, by today's
  constructor name).  `Proves.impRight`/`allRight`/`emptyModality` are the
  aliases a walk names.  **Silent moves**: a scope end (an update of pops,
  `updIntro`) and a hidden binder (`bindIntro`) are folded into the node
  before them, and at the root, since KeY has no step there.  Leaves close
  by `closeTrue` and then `Config.closers` (empty: a closer of scoped
  leaves, `Proves.close` from `sound` and the erased closer from `symex`,
  is to be plugged in once merged).
- **The commands** (`Tools/CoreInspect.lean`): `#proof_tree`, `#proof_node`,
  `#proof_tree_json` on a scoped formula, second elaborators of today's
  syntax; `#step` names the rule the scoped strategy fires (`ruleAtC?`, at
  the statement `Fml.stepAt` looks at), no longer through the erasure.
- **Callbacks** (`Calculus/Core/Callback.lean`): `Core.CallbackTaclet`, the
  three lines read under `Core.Schema`, each its no-callback twin
  (`toTaclet`) and so `Stmt.step`'s premise (`toStep`); a printer for it
  (the `try` line still escapes, as `tryCallNoCallbackBox`'s does, the W1
  Delab item).  `ProvesC I H φ` stated with solkey's goals: `plain`,
  `intro`, `allIntro`, `updIntro`, `bindIntro`, `update`, `unfold`, `bind`
  (statements that do not fork, `Rule`s), `split`, `empty`, `callback`,
  `send`, `tryCall`.  The invariant is a closed `Fml C []`, read in any
  scope past an update that drops every local (`Fml.closedAt`, invisible
  when printed), so no formula weakening is needed; a rule's fresh index is
  past it (`Hyps.freshC`).  Printer `dl{ ..H ⟹ᶜ[I] φ }`.
- **The flip switch** (`Calculus/Core/Surface.lean`):
  `open scoped Solidity.Core.Surface` makes `dl!{}`, `dl![m]{}`, `dl[C]{}`,
  `dl[C, m]{}` and their sequent lines `cdl…`, `spec!`/`problem!` `cspec…`/
  `cproblem…`, `⊨ φ` `valid% φ` (scoped validity for a scoped formula,
  today's otherwise; `Core.Valid` prints as `⊨`), and `⊢ φ` the scoped
  sequent with nothing assumed.  Each is a `scoped macro_rules`, tried
  before today's elaborator.  The commands read `dl!{}` scoped when the
  switch is on (`surfaceOn`, the macro `core_surface%`).  Chain notation is
  the `chains` lane's; it reads scoped once its elaborator takes a
  `Core.Fml` line, since its lines are `dl!{}`.

- **Checked sequent lines** (`Calculus/Core/Sequents.lean`): a scoped
  goal carries frames (`pop`, `seq`, hidden binders) that a flat program
  read back does not, so `show` cannot compare it by unfolding.
  `show_sequent!{ Γ ⟹ φ }` (and, under the switch, `show sequent!{ … }`)
  compares the goal's erasure, as it prints, with the line read as
  today's sequent, by unification: the line is written as the goal prints
  (today's spellings), without a block's `}`, a hidden binder no entry,
  a `∀ T x` entry read (`readSequent`).

- **`sol_spec` on `cspec!`** (`Calculus/Core/SolSpec.lean`): a second
  elaborator of `sol_spec_prep`, so `sol_spec` (`sol_symex; sol_spec_close`)
  runs the scoped strategy and then erases each leaf (`Valid.of_erase`, the
  kernel checking `Fml.posB`) into today's `sol_spec_prep`/`sol_spec_finish`.
  `Examples/Tactics/CoreSolSpec.lean` proves all seven of
  `Examples/Tactics/Specs.lean`'s obligations scoped, `_mint` under 700000
  heartbeats (today's needs 1000000).

- **Left for the integration**: `ProofTree.Config.closers` stays empty
  until `w2-sound`'s `Proves.close` (w2-sound's Calculus/Core/CloseErase.lean) is
  merged; then a leaf with a formula left closes by
  `apply Proves.close` and the erased closer.
- **Left: the callback reading over `TState`**, this lane's Work item not
  done: `holdsC`/`ValidC`/`TransferSem`/`holdsT`/`ValidT` and their
  theorems (`validT_*`, `after_frames_iff`, `holdsC_iff_holds`,
  `holds_of_holdsC_modal`, `holds_of_holdsC_imp`, `valid_of_validC`),
  `ProvesC.sound : ProvesC I Γ₀ H φ → ValidC I (H.wrap φ)` and
  `ProvesC.close`, then the re-pin of `Examples/Tactics/CoreCallback.lean`.
  Blocked on `holds` over `TState` from `sound` (that lane leaves the
  uninhabited-memory-type decision open).  Until then `ProvesC` is a
  stated judgement with no soundness theorem
  (`Calculus/Core/Callback.lean` says so), and the callback-taclet rows
  stay today's.  Carried into W3/W4: nothing may rely on a `ProvesC` rule
  before `ProvesC.sound` is proved.

Pins (`Examples/Tactics/CoreProofTree.lean`, `CoreSurface.lean`, `CoreSequents.lean`,
`CoreCallback.lean`) differ from today's `Examples/ProofTree.lean` where
the scoped calculus does, each for a reason W3's list should carry:
a parameter is bound by `∀` (`cdl!`), so a tree starts with `allRight`;
a rule that leaves no statement goes on into the rest or past the frames
(`Fml.modalK`, G0 condition 6), so **no `emptyModality` node** follows it
(a new pin reason for W3: today's trees have one after every last
statement); the branch's `}` prints in a split's goals; no `cov` goal
(merged `w2-sound`'s first commit: a split has KeY's two goals).

Found, not this lane's: `Core.Proves.valid` leaves its `R` open on a
`⊨` goal (`apply Proves.valid` needs `(R := .all)`); an update of a
comparison (`se1 := x == 1`) escapes in today's printer too (the `dl_term`
grammar has no `==`).

### W2 integration (2026-10-08)

- **Merged** into `intrinsic`, in order: `w2-sound` (its tip, past the
  cover removal: `Taclet.sound`, `Proves.close`, the typed reading),
  `w2-symex`, `w2-chains`, `w2-tree`.  One text conflict, in
  `docs/module-map.md` (the `Examples/Tactics/Core*` rows of `chains` and
  `tree`): kept as a union, one row per module, `CoreCallback`'s row with
  `tree`'s `ProvesC` clause.  `Solidity.lean` merged clean, no duplicate
  import or row.
- **One clash** of fully-qualified names: `Upd.freshB` in both
  `Calculus/Core/Closable.lean` (`sound`) and `Calculus/Core/Close.lean`
  (`symex`), which imports the first through `HoldsErase`.  `Close.lean`'s
  is renamed `Upd.freshK` (with `Upd.fresh_of_freshK`): it decides the
  same `Upd.Fresh` by `List.contains`, which the gate's kernel evaluation
  was measured with, and keeps its compiled twin `Upd.freshM`.  The
  duplicate check is otherwise empty (but the known `Evm/Repr`/
  `Examples/Verify` `as` false positive).
- **Full build: green after that rename, no other fix.**  `lean_build` over
  `Solidity`, `solkeycheck`, `SolidityCorpus` and `SolkeyTestSuite` (321
  jobs; the last two in `defaultTargets` for the run only): **95 s wall**,
  rebuilding from the Lake cache what W2 changed.  The slowest modules
  under the build's load: `TestSuite/Derived7` 84 s, `TestSuite/Derived8`
  46 s, `Examples/Tactics/CoreSolSpec` 40 s.  No new `sorry` or `axiom`;
  one new override, `CoreSolSpec`'s `erc_mint` at `700000`, below its
  twin's `1000000` in `Examples/Tactics/Specs.lean`.
- **Gates.**  `symex`'s early gate passes (19.4 s serial against 22.9 s,
  above), so W3 may start.  Under the parallel build the twins took
  `CoreDerived9` 14 s, `CoreDerived10` 15 s, `CoreDerived11` 5.6 s,
  against today's `Derived9` 14 s, `Derived10` 18 s, `Derived11` 4.2 s.
  `sound`'s gate (`Stmt.TSound C`) does not pass yet: it waits on the
  three decisions in its section.
- `scripts/check-orphans.mjs`: 307 reachable, none orphaned but the
  git-excluded `Solidity/Scratch/`.  `scripts/check-doc-paths.sh`: OK (the
  deleted-cover and spike citations `symex` reported were fixed by
  `sound`); `Close.lean` is now an ambiguous citation (two files), which
  the script allows.
- **Left over, across lanes**, now unblocked by the merge: `Proves.close`
  is on `intrinsic`, so `tree`'s `ProofTree.Config.closers` and `symex`'s
  `Walk.movesAt` can end a leaf with `refine close ?_; sol_symex;
  sol_close` (re-pin `CoreProofTree` and `CoreDerive`), and `chains`'
  `Fml.ViaE.valid` premise can come from it.  The `==`/`!=`/`*` update
  printer gap is `Calculus/RuleSyntax.lean`'s.  The read-only review pass
  was not run for `symex` and `chains`.
- The four lane worktrees are removed (the branches stay).

## W3 — the flip, file by file (4 lanes)
Each lane adds the `open scoped` line to the files it owns and re-pins them.

| Lane | Files |
|---|---|
| `testsuite` | `TestSuite/**`, `Solkey/**`, `Frontend/Problems.lean` |
| `tactics` | `Examples/Tactics/**`, `Examples/Benchmark/**` |
| `chains` | `Examples/Chains/**` (14 files, 188 theorems), `ChainNotation`, `ChainRewrites` |
| `tree` | `Examples/{ProofTree,Tools,Verify,Notation,ExampleNames}.lean` |

**TestSuite:**
- `solc_scoped_problems` declares `N.f.problem` at Core; the old problems become `N.f.problem.legacy`.
- A `#guard` checks that each Core problem erases to its legacy one.
- The text of Derived1–14 (`⊢ … := by sol_prove`) is unchanged.
- `Report.lean`'s count of 437 and `check-testsuite.sh` must not move.
- Keep at most 3 open files: the Derived workers take 3–4 GB each.

**Pins that may change, each with its reason:**
1. `cov` is gone: ProofTree branch rows and `case cov` in `sol_derive?` suggestions.
2. A split's goals print the branch's `}` (`core_item`).
3. Fewer steps, because branches share the rest of the program as a frame: `#derivation` lines, ProofTree serial numbers, `~*>` spans.
4. A loop's `{anon(…)}` list no longer names the body's own locals.
5. Return values that are read but not assigned print as `(uint a, uint b) = f(…)`.
6. Errors for reading a block's local after the block ends (`Branch.lean`).

The fresh names (`se1`, `sp1`) must not change. Any other pin change is a bug. Each lane lists every pin it changed, with its reason, in its doc section.

**Gates vs M0:**

| Module | M0 | Limit (+20%) |
|---|---|---|
| Derived9–11 | 19.1 s | 22.9 s |
| `TestSuite/Problems` | 1.2 s | 1.44 s |
| `Examples/ProofTree` | 10.1 s | 12.1 s |
| `Examples/Chains/Storage` | 7.5 s | 9.0 s |
| `Solkey/TestSuite` | 10.4 s | 12.5 s |
| `Examples/Benchmark/Syntax` | 1.2 s | 1.44 s |

Per Decision 9 the gate is the aggregate; each outlier is explained in the docs.

### W3 lane `tactics` (`w25-tactics`, 2026-10-08)

**Flipped** (`open scoped Solidity.Core.Surface` after each `local instance`,
imports `Calculus/Core/{Surface,Closers}.lean`, `Calculus/Core/Sequents.lean` where a
walk checks `show sequent!{…}`, `Tools/CoreInspect.lean` where a command is
pinned): `Examples/Benchmark/{Coin,Counter,ERC20,EtherWallet,Mapping,Purchase,SimpleStorage}`;
`Examples/Tactics/{ApplySteps,Branch,CallOperands,Calls,Checked,CrossDomain,Decide,LedgerDelete,Loops,Memory,Net,Operators,Payment,Revert,Specs,StorageDelete,StorageSteps,StorageSuite,Tour,TryCatch,Values}`.
Every file checks with no error or warning.  What the scoped calculus
cannot state or close yet sits in a closing block of the same file, read
without the switch (`## Read without the switch`, or a named section), each
with its reason.

**Not flipped**, each for a reason outside this lane:
* `Benchmark/Syntax`, `Tactics/{Theory,TermTaclets}`: no formula; the gate
  module (`Benchmark/Syntax`, 1.2 s) keeps its imports.
* `Tactics/LoopsImport`: states today's `Valid (Fml.modal …)` of solc-imported
  programs; moves with the testsuite lane's scoped problems.
* `Tactics/{Contracts,Constructors,Dangling}`: today's `FunContract`,
  `Problem.text`/`Problem.deploy_of_valid`, and the closer's budgets
  (`Derive.residue` on today's `wtStd → dl!{…}`) have no scoped twin.
* `Tactics/{UpdateRules,SelectOnSaveConsr}`: today's update rewrites
  (`Fml.updAt`, `merge`, `mergeStorage`) and the interpreter's own lemmas;
  the scoped sequent has the program rules and `close` only.
* `Tactics/Callback`: `ProvesC` has no soundness yet (W2 `tree`).
* `Tactics/Core*`: the twins state `cdl!` themselves; `CoreSurface` contrasts
  the two readings on purpose.

**Built** (no rule, name or soundness theorem changed):
* `sol_prove` on `⊢ φ` is the testsuite lane's
  `Calculus/Core/ProvesDerive.lean` (merged here; this lane's `ProveSeq`,
  a `match` on `Fml C Γ`/`Premise` run in the kernel, is dropped, G0
  condition 1).  Two changes to it: a leaf's erasure has its parameters'
  `∀` stripped (`Fml.stripAlls`, `Valid.of_stripAlls`, in
  `Calculus/Core/Derive.lean`; the identity on the testsuite's obligations,
  which have none), and the compiled walk runs before one kernel check, as
  today's `Derive.prove` (the kernel try at no leaves cost a second
  evaluation where leaves are left: `Purchase.ctor_spec` ran out of the
  declaration's heartbeats).
* `Calculus/Core/Closers.lean`: today's closers on a scoped leaf (`sol_decide`
  and its parts, `sol_reduce`, `sol_reads`, `sol_close_eval`,
  `sol_apply_upd`, `sol_merge`, `sol_fold_terms`) through the erasure
  (`Derive.eraseLeaf`, `onErased`); refutations by a run's outcome
  (`Modality.afterRunC_not_panic`, `afterRunC_diamond_halt`, `decide +kernel`).
* `Calculus/Core/WalkSyntax.lean`: today's walk lines on a scoped goal, scoped
  rule first, today's last (`apply update r`, `unfold r` as `unfold`/`bind`/
  `inline`, `split`, `splitBox`, `done`, `Proves.check`, `cases`,
  `branches`, `invBox`, the `…Lean` forms, `unfoldRule`, `empty`,
  `emptyModality`, `intro`, `allIntro`, `impRight`, `allRight`,
  `Proves.valid`, `refine close ?_`), the taclet elaborated last
  (`by exact`) so that side conditions read the goal; `core_silent`, the
  steps KeY does not show (a scope's end, a hidden binder, and before any
  rule the parameters' `∀`); `core_skip`, the no-op of `apply empty`
  where no modality is left and of `apply allIntro` where the parameters
  are already bound, refused anywhere else.  The walks' text is today's.
* `Calculus/Core/Derive.lean` (W2 leftover): `sol_derive?`'s leaves close
  by the tree lane's `Walk.closeLeaf` (merged; this lane's copy dropped);
  a rule whose line `apply` cannot match (a read into a hole) by
  `refine Core.Proves.c (by exact Core.Taclet.step_eq .r) ?_`, the taclet
  elaborated after the goal, its name kept; `sol_close` runs today's macro through a scoped
  `sol_close_unwrap` (`eraseLeaf`, the parameters' `∀` stripped), so
  `sol_close_mt` and `sol_spec_close` read scoped leaves too and a failing
  close is not run twice.  `Examples/Tactics/CoreDerive.lean` pins a
  postcondition that is not `true`.
* `Calculus/Core/Symex.lean`: a failing scoped tactic throws where errors
  are not recovered from (`fail_if_success`, `first`), keeps an abort's
  logged errors (today's `all_goals`), and `sol_step` keeps the goal's
  tag.
* `Calculus/Core/ProofTree.lean`: the tree lane's `closeTacs`/`Config.erased`
  kept, this lane's copy reverted.
* `Examples/Tactics/CoreStep.lean`: the stale `Premise.cover` docstring.

**Pins changed** (each with its reason; the listed reasons are W3's 1–6,
"the parameter's `∀`" is W2 `tree`'s: `cdl!` binds a read-before-bound
name by `∀`, so a tree starts with `allRight`):
- Benchmark/Counter `#check spec!{ dec }`: type `Fml Counter` -> `Core.Fml Counter []` (the flip itself: the term is scoped).
- Tactics/Specs `#check spec!{ pay }`, `spec!{ order }`: same type change; `order`'s line wraps.
- Tactics/CallOperands: no pin changed; the memory call's step (`~[internalCallExpand]~>`) moved to a closing block read without the switch (Left, 7).
- Tactics/CoreDerive: new pin, `sol_derive?` with leaves closed (`Proves.close` + `sol_symex; sol_close`), `allRight` as the tree lane names it.
- Tactics/Decide: no pin changed; the two refutations over an untyped storage (`deleteWithoutWrite`, `survivesMappingOnly`) and the three fragment pins (`Fml.inL`, `sol_decide` on a modality) moved to a closing block read without the switch (they are about today's untyped storage and the closer's input).
- Tactics/Payment: `transferBox`, `sendBox`: the parameter `to` is bound by `∀` (W2 tree reason; the walk takes it before its first rule); their checked lines carry `∀ uint to,` and end `⟹ true` where today's had `⟹ [ ] true` (no `emptyModality` after a last statement: reason 3); `sendDiamond` (⊢ under the diamond) moved to a closing block read without the switch: `Core.Proves.close` takes box contexts only.
- Tactics/StorageSteps, Memory, CrossDomain, Net, Tour, LedgerDelete: walks unchanged in text (today's walk lines read scoped, `Calculus/Core/WalkSyntax.lean`); refutations re-proved by the run's outcome.
- Tactics/Calls: the two call walks take solkey's `blockEmpty` on the callee's body (the scoped inlining keeps the body a block; one step more, a solkey taclet); the `TestSuite` shapes (`⊢ wt → ⟨…⟩`, diamond) moved to a closing block read without the switch.
- Tactics/Loops: `#proof_tree` of `countToNWalk`'s formula starts with `allRight` (parameter `n` bound by `∀`), has no `emptyModality` nodes (reason 3), serials shift by those; `#step` pins of `whileClose`/`whileNoVariantDiamond` print `dl{ ∀ uint i; false }` (the parameter's `∀`); `countToNWalk`'s docstring loses the `cov` goal (reason 1); `countTo1Walk` (diamond walk), `countToNDiamond`, `breakKeepsBound` (leaves `Fml.posB` refuses) and the diamond `#proof_tree` of `notEntered` moved to a closing block read without the switch.
- Tactics/Branch: `branchLocals`'s goals pin: two goals (no `cov`, reason 1), each branch's `}` (reason 2), the parameters' `∀` entries (taken before the first rule), `{ se1 := a == b }` (the chains lane's `==` printer, merged); `ifTrue`'s `sol_step` pin: no cover conjunct (reason 1), `}` (reason 2); `branchDiamond` and the stuck-condition refutation (valid when scoped: `a`, `b` are bound) moved to a closing block read without the switch.
- Tactics/Revert: `case cov` blocks of the box walks deleted (reason 1); refutations re-proved by the run's outcome, the `require` one at `a = 0`, `b = 1` (scoped, the parameters are bound, so "nothing binds `a`" became "the `require` reverts"); `requireDiamond`, `branchDiamond` (⊢ under the diamond) moved to a closing block read without the switch.
- Tactics/StorageDelete: no pin changed; the three `_theory` derivations (today's sequent rules on updates and the Theory's laws) and the refutation over a `bool`-holding root moved to a closing block read without the switch.
- Tactics/TryCatch: the `#check` of a `try` formula ascribed `Core.Fml Pinger []` (the flip's type); `getWalk` (today's `Fml.alls` goal shape) and the callback proofs (`ValidC`, no `ProvesC` soundness yet) moved to a closing block read without the switch.

**Left** (for the lead or a later lane):
1. *Diamond leaves.* `Core.Proves.close` takes box contexts only, so no
   `⊢` walk or `sol_prove` on `⊢` closes a leaf behind a diamond update;
   `Payment.sendDiamond`, `Branch/Revert.branchDiamond`,
   `Revert.requireDiamond`, `ApplySteps.guardedCopy`, `Loops.countTo1Walk`,
   the `Calls` `TestSuite` shapes and the diamond `#proof_tree`s stay
   today's.  Needs `TClosable` at the flip (W2 `sound`).
2. *Leaves `Fml.posB` refuses* under the `Valid` path:
   `Loops.countToNDiamond` (an anonymised loop flag), `Loops.breakKeepsBound`.
3. *Refutations over an untyped storage* (`Decide.deleteWithoutWrite`,
   `survivesMappingOnly`, `StorageDelete.deleteRootUnknown`) and the stuck
   `if` of `Branch` (valid when scoped) say what only today's storage and
   unbound locals allow: at the typed-state flip they are false as stated
   and should become positive theorems.
4. `apply empty` is a no-op where the scoped strategy already went past
   the frames (reason 3); the walks keep the line, and it is refused
   before a statement (`ApplySteps`).
5. `sol_prove?` on a scoped sequent, and `sol_derive?`'s suggestion in
   today's short walk text (`apply update .r`), are not written.
6. Not run: `lake build` of the targets (Bash `lake` is denied); every
   touched file, the `Core*` example twins, `TestSuite/CoreSeq`, and the
   merged lanes' `Examples/{ProofTree,Tools,Notation,Verify,ExampleNames}`
   checked one by one through the server.
7. *For the lead* (review, 2026-10-08): (a) `Person memory p =
   choosePersonMem();` steps by `functionBodyExpand` scoped, because
   `CallRet.isRets` (`Calculus/Core/Rules.lean`) counts a memory return;
   rule-map rows 54/55 give it `internalCallExpand`.  Either `isRets`
   follows today's or the rows name the memory return; the pin waits in
   `CallOperands`' closing block.  (b) Two pin reasons outside W3's 1–6
   to approve, or to remove at the source: the flip's own type change in
   `#check` pins (`Fml C` → `Core.Fml C []`: Counter, Specs, TryCatch), and
   `apply unfold .blockEmpty` on an inlined callee's body (Calls; the
   scoped inlining keeps the body a block, one step more).

**Review fixes** (2026-10-08): `w25-testsuite`, `w25-tree` and `w25-chains`
merged into this branch, their conflicts resolved toward the owning lane
(`ProvesDerive`, `closeLeaf`/`closeTacs`, the `==` printer); Coin and
Mapping keep today's `refine close ?_`; the chains lane's `int` product
pin of `Examples/Tools.lean` moved out of the tree lane's scoped section
(the two merged would print the scoped escape); stale headers and
docstrings moved with their proofs (ApplySteps, TryCatch, StorageDelete,
Revert, StorageSteps).

### W3 lane `testsuite` (`w25-testsuite`, 2026-10-08)

**The flip does not land: it waits on the diamond.**  Under
`open scoped Solidity.Core.Surface`, `⊢ φ` is `Core.Proves C .all [] .nil φ`,
and `Proves.close` takes no leaf behind a diamond update (`Fml.closableB`
asks `m = .box`; W2 `sound`, "Also left, at the flip").  330 of the 437
obligations are diamonds, and every `Derived` module holds some (box ones per
module: 7, 3, 21, 12, 0, 8, 29, 14, 1, 0, 0, 7, 0, 5; Derived9–11: 1 of 91),
so no `Derived` module can flip with its text unchanged.  What landed is
everything the flip needs but that:

* **`sol_prove` on `⊢`** (`Calculus/Core/ProvesDerive.lean`; **out of
  lane, for the lead**: this module, its `Solidity.lean` import and its
  `docs/module-map.md` row are outside `TestSuite/**`, `Solkey/**` and
  `Frontend/Problems.lean`, and its `@[tactic Solidity.tacticSol_prove]`
  elaborator reaches every `Core.Proves C R [] H φ` goal in the library,
  the `tactics` lane's `Examples/Tactics` among them.  The lead lands it as
  its own commit on `intrinsic`, or merges it ahead of `w25-testsuite`, so
  that `tactics` rebases onto it rather than meeting it at the merge): nobody had
  built it (W2 `symex`'s `sol_prove` proves `Core.Valid`, and `Valid` does
  not give `Proves`).  `Seq.run` walks the sequent as `Proves` has its rules
  (fresh index `Hyps.fresh`, so a split's branches number their fresh names
  apart, where `symex` numbers over the whole `and`), a leaf goes to
  `Proves.close` with today's residue of its erasure, and `Proves.of_residue`
  reads the walk back as the derivation, checked as one kernel evaluation;
  `leafᵢ` goals as before.  Lean's three axioms.  When `close` takes a
  diamond leaf (a Bool twin of `Fml.TClosable`), the side condition changes
  in one place (`Seq.leafRes`/`Seq.leafQuote`).
* **All 107 box obligations** are proved this way, with the `Derived`
  modules' text (scratch; ten pinned in `TestSuite/CoreSeq.lean`,
  `proved_seq`), serially 111 s against 144 s for today's `sol_prove` on
  the same 107 (one session, other lanes running).  One text difference:
  `testStorageNestedPushReturnAlias` leaves one goal of today's calculus,
  where `Derived7` has `case leaf1`/`case leaf2`; at the flip its
  `case leaf2` goes, because the walk splits the sequent before the closer
  does.  **A deviation, for the lead to approve**: it is none of the
  allowed kinds 1–6 (kind 3 is fewer steps where branches share a frame,
  not one fewer residual leaf), and it breaks W3's "`Derived1`–`14` text
  unchanged".  The alternative is to give the scoped walk today's leaf
  numbering for that obligation, so `Derived7` keeps both cases.
* **The flip switches** (`Frontend/Problems.lean`): `solc_problems N legacy`
  declares `N.f.problem.legacy`, `solc_scoped_problems N main` declares
  `N.f.problem`, `decl` skips compiling; `#solkey_problem`, `#solkey_scan`
  and `#solkey_derive?` read the legacy statement wherever it is
  (`legacyProblem`); `#solkey_obligations` counts a theorem of either `⊢`
  (`provesScoped`), so `Report.lean`'s 437 holds across the flip.
* **The erase guard** is in `solc_scoped_problems`: each scoped obligation's
  `Fml.erase []` is its legacy statement, compared as quoted expressions
  (`Fml` has no `DecidableEq`).  437 of 437, in 0.36 s.  A mismatch, or a
  missing legacy statement (with `main`, no `N.f.problem.legacy`), is an
  error; the info line is unchanged.
  `TestSuite/CoreProblems.lean` now uses it (`… decl`), its local command
  gone.

**Gates.**
* Derived9–11 flipped: not measurable (90 of 91 are diamonds).  The
  `Core.Valid` twins, serially (`Elab.async false`, `IO.monoMsNow`): 18.8 s
  ≤ 22.9 s.
* `TestSuite/Problems`: **fails** as the plan places it.  Today's body
  0.7 s; with `solc_problems … legacy` and `solc_scoped_problems … main
  decl` 4.6 s (limit 1.44 s).  The time is the kernel's check of the 437
  scoped declarations, 3.5 s (8 ms each; resolve 16 ms, quoting shared
  already); compiled (no `decl`), the command runs out of the default
  200000 heartbeats after 20 s.  Proposal: at the flip `Problems.lean`
  keeps `solc_problems Solkey.TestSuite legacy` alone (0.7 s), and
  `CoreProblems.lean` holds `solc_scoped_problems Solkey.TestSuite main
  decl`, which the `Derived` modules import.

**Pins changed:** none.  (A first version added the erase guard's count
to the info line, moving `Solkey/Constructors.lean`'s and
`TestSuite/CoreProblems.lean`'s pins, a change of none of the allowed
kinds; review put them back, the guard reporting by error alone.)
`Derived1`–`14`, `Report.lean` and `Problems.lean`'s pins are unchanged.

**Checks.**  `lake build Solidity solkeycheck SolkeyTestSuite
SolidityCorpus` green (323 jobs; the `Derived` modules built a few at a
time: all fourteen at once went past 30 GB beside the other lanes);
`check-orphans` (but `Scratch/`), `check-doc-paths`, and
`check-testsuite.sh` (against solkey `1b4341a303`: 435 derived) ok.  No new
`sorry`, `axiom` or `maxHeartbeats`.  The read-only review pass was not run.

**Left.**
1. *The diamond leaf* (lead / `sound`): `Proves.close` on a Bool twin of
   `Fml.TClosable`, over the typed reading; then `ProvesDerive`'s leaf check
   follows.  The push at the bound (Decisions 12–14, "Left for the lead",
   item 1) then bites the diamond obligations whose functions push.
2. *The flip itself*, once 1 lands: `Problems.lean` →
   `solc_problems Solkey.TestSuite legacy`; `CoreProblems.lean` →
   `solc_scoped_problems Solkey.TestSuite main decl`; each `Derived`
   module imports `CoreProblems`, `Calculus.Core.ProvesDerive` and
   `Calculus.Core.Surface` and opens the scope; `Derived7` drops one
   `case leaf2` (the deviation above, if the lead approves it); `CoreDerived9`–`11` and `CoreSeq` are deleted.
3. `#solkey_derive?` still searches today's calculus; its suggestions read
   the same text, but the leaves it names are today's.

### W3 lane `tree` (`w25-tree`, 2026-10-08)

- **Flipped** (`open scoped Solidity.Core.Surface`, in `section Scoped`
  blocks): `Examples/ProofTree.lean` (every box tree, `#proof_node`,
  `#proof_tree_json`, the `sol_derive?` walks and their replays),
  `Examples/Tools.lean` (`#wp`, `#step`), `Examples/Notation.lean` (the
  formulas, `#step`, the `twoKeys` walk), `Examples/ExampleNames.lean` (the
  formulas and fresh-name tables).
- **Kept today's**, each said in its file: the diamond trees and walks
  whose leaves sit behind a diamond update (`Proves.close` is box-only,
  `Fml.closableB`: the first tree, `sendNoCallbackDiamond`, `guardedCopy`,
  the two call trees, the unwound loop); `sol_prove?`, `sol_chain?`,
  `#chain`, `sol_rws?` (no scoped `sol_prove?`/`sol_chain?`/`sol_rws?`,
  and Core `sol_prove` takes `Core.Valid`, not `⊢`); `ExampleNames`'
  `sol_chain` error (the scoped chain's error does not print the line it
  does not reach); `Examples/Verify.lean` whole (`#verify` elaborates
  `spec[C]{f}` in the caller's scope; `#counterexample` is over
  `Prog.runFuel`, W4); `Notation`'s rule lines and `⊢` rules (W5 names).
- **W2 leftovers done.**  `Core.ProofTree.Config` closes a leaf by
  `closeTrue`, then `refine Core.Proves.close [] rfl List.nodup_nil ?_;
  sol_symex; sol_close` (`closeTacs`, `Config.erased`), then `closers`;
  `movesAt` whnfs a premise built by a function (`Premise.expandCall`), so
  `internalCallExpand`/`functionBodyExpand` are nodes (they were open
  goals).  `CoreProofTree` pins a leaf closed by its erasure.  The callback
  reading over `TState` is `Calculus/Core/CallbackHolds.lean`: `holdsC`
  (`StateInv := Fml.stateInv I = ⟨fun σ => tholds σ I⟩`), `Invariant`,
  `ValidC`, `TransferSem`, `holdsT`, `ValidT`, `validT_*`,
  `after_frames_iff`, `holdsC_iff_holds`, `holds_of_holdsC_modal`,
  `holds_of_holdsC_imp`, `valid_of_validC` (axioms: `propext`,
  `Classical.choice`, `Quot.sound`).
- **Outside the lane's files, needed by the flip**
  (`Calculus/Core/Derive.lean`, `symex`'s): `sol_derive?` closes a leaf as
  the tree does (`Walk.closeLeaf`, at the empty outer scope; `sol_derive`
  still leaves it), and a rule of labelled goals (`cases`, `branches`) is
  written `apply … <;> (try simp only […]) <;> (try and_intros)` with
  bullets, as today's walk is (it left `case fml`/`case upd` goals open).
  `CoreDerive`'s pins do not move.
- **Pins changed, with reasons** (numbers are the W3 list's):
  - `ProofTree`, every scoped tree: `allRight` first (a parameter is bound
    by `∀`, W2 `tree`); no `emptyModality` after a last statement
    (`Fml.modalK`, G0 condition 6, W2 `tree`); serials shift (3); the
    storage-write tree loses its `emptyModality`.
  - `ProofTree`, `#proof_node`: node 2 instead of 1 (the same node,
    `allRight` before it), its sequent prints `}` (2) and a `∀ uint x`
    entry, its tactics `apply Core.Proves.update (Core.Taclet.toStep …);
    apply Core.Proves.updIntro` (the scope end is silent, W2 `tree`).
  - `ProofTree`, `#proof_tree_json`: the same, 6 nodes for 7.
  - `ProofTree`, the walks: the scoped calculus's constructors
    (`Core.Proves.update (Core.Taclet.step_eq .r)`, `refine
    Core.Proves.valid (R := RuleSet.all) ?_`, `bindIntro` for a
    hidden binder, `updIntro` for a scope end), `split` for `splitBox`
    and no `cov` (1), a leaf `refine Core.Proves.close [] rfl
    List.nodup_nil ?_`; the replays rewritten to them.  A precondition,
    a quantifier and an empty modality keep solkey's names
    (`Core.Proves.impRight`/`allRight`/`emptyModality`, review fix:
    `Calculus/Core/Derive.lean`'s `Walk.movesAt` emits the aliases of
    `Calculus/Core/ProofTree.lean`, which it now imports); `allRight`
    first is W2 `tree`'s reason above.  `CoreDerive`'s walk re-pinned
    for the same alias.
  - `ProofTree`, new pins (review fix, the regression example for
    `movesAt`'s whnf of a premise built by a function): the box trees of
    an internal call and a tuple call over `Callees`, scoped, show
    `internalCallExpand`/`functionBodyExpand` as nodes, the body's
    `blockEmpty`, and a closed leaf (the diamond trees beside them stay
    today's).
  - `Tools`, `#wp` of a formula with parameters: `∀ uint i; ∀ uint n;` in
    front (W2 `tree`).
  - `Notation`: `#check dl!{…}` is `Core.Fml StandardExample []`, with its
    parameters bound; the `step = some …` `rfl` stays, its line read
    back as `dl![.box]{ … }` (the box's update; the default `dl!{ … }`
    reads an update at the diamond), with a `#step` pin of its printed
    form beside it (review fix: the pin alone checked only the printer);
    the `twoKeys` traces start `∀ uint b, ∀ uint a`
    and have no `[ ]` line.
- **Gate** (`Examples/ProofTree`, 12.1 s): 11 s in the default-target
  `lean_build` (286 jobs, under that build's load); by the M0 method, a
  fresh open, 14.6 s against 14.2 s for today's file timed the same way in
  the same minute (1.03×, four Lean agents on the machine).
- `lean_build` (default targets): green.  `check-orphans`: 308 reachable.
  `check-doc-paths`: OK.  No new `sorry`, `axiom` or `maxHeartbeats`.
  `CoreDerived11`, `CoreDerive`, `CoreCallback`, `CoreSurface`,
  `CoreProofTree` checked after the tool changes.
- **Left.**  (a) The diamond trees close only once `Proves.close` takes a
  leaf behind a diamond update (`Fml.TClosable`, over the typed state, at
  the flip of `Proves`' soundness to `Proves.tsound`): a lead decision, as
  `Proves.sound` over M3 would lose it.  (b) A scoped `sol_prove?`,
  `sol_chain?` and `sol_rws?`, and `sol_prove` on a `⊢` goal (`Core.Proves`
  from `Valid` needs a reflective `Proves` lemma).  (c) The scoped chain
  error should print the line it does not reach.  (d) `ProvesC.sound`
  against `ValidC`, waiting on `Stmt.TSound`; `Examples/Tactics/CoreCallback.lean`
  (the `tactics` lane's file) not re-pinned to `holdsC`.

### W3 lane `chains` (`w25-chains`, 2026-10-08)

**Flipped** (`open scoped Solidity.Core.Surface`, the Core imports): all of
`Examples/Chains/` but `EvaluationOrder`, 144 chain declarations; 33 declarations stay on
`Update.lean`'s calculus, in a trailing part of their file headed *Left on
`Update.lean`'s calculus* that says why (below).  `ChainNotation` and
`ChainRewrites` stay on today's calculus (below).

**What the flip needs besides the line:**
- *A postcondition at its context.*  `Core.Post C Γ` stands where it is, with
  no weakening, so a chain whose first line declares locals before `φ` (an
  update `{ ageVal := 42 }`, a parameter `v` bound `∀ uint v;`, a program's
  top-level `uint x`) takes `φ` at that context, as a binder of the
  declaration: `theorem chain (φ : Core.Post StandardExample [.val .uint]) :`.
  The section variable stays `Core.Post C []` for the others.  A hole
  (`Core.Post C _`) does not work: the coercion to `Core.Fml C Γ` does not
  unify the context.
- *No segments.*  Scoped chains have no `~~>`: the four chains composed of
  two segments (`Storage.BalanceWriteRead`, `StorageDelete.SubtreeDelete`,
  `MemoryDelete.FieldDeleteRef`, `StorageCoverage.ifElseUnfold`) are one
  chain each, every line kept; `run`/`reads`/`ifElseUnfold1`/`ifElseUnfold2`
  are gone.
- *Parameters past the program* (`Calculus/Core/ChainKit.lean`,
  `Chains.lean`): the erasure of a line whose parameters the reader binds
  outermost starts with `∀ uint v;`, which no rewrite goes under; `Fml.ViaE`
  now takes the erasure with its outer quantifiers dropped
  (`Solidity.Fml.dropAlls`, sound by `holds_of_dropAlls`: validity is closed
  under generalisation).
- *A fixed modality in a line over `m`* (`Chains.lean`): the diamond and box
  runs were compared with every `Modality` constant abstracted, so a hidden
  binder's `.box` (Decision 12) made a line over `m` stop ("depends on the
  modality").  `mergeModality` puts `m` back only where the two runs differ
  (`Memory.RootAlias`).
- `Fml.ViaE.valid_close`: the bridge of `Fml.ViaE.valid` is `Proves.close` at
  the last scoped line, its side conditions decided by the kernel
  (`ChainNotation`, §4, closes `[ alice.account.balance = 10; ] …` that way).
- The printer (`Calculus/RuleSyntax.lean`, `Calculus/Notation.lean`):
  `x := a == b`, `x := a != b` (a `uint` equality captured) and `a * b` have
  KeY's text and read back (`ChainNotation` §7 pins both readings).

**Pins and statements changed, each with its reason:**
- W3 reason 1 (`cov` gone): `CheckedArithmetic.OverflowReverts.{box,diamond}`,
  `StorageCoverage.{requireConditionCapture,requireSimple,ifElseUnfold,ifElseSplit}`:
  the third conjunct `(⟨ revert(); ⟩ false ∨ c ≐ true ∨ c ≐ false)` dropped
  from every line after the split.
- W3 reason 2 (a branch's `}`): `StorageCoverage.{ifElseUnfold,ifElseSplit}`.
- New, statements: the `φ` binders and the merged segments above;
  `StorageCoverage.{revertDiamond,revertBox}` proved `by sol_chain` (a
  scoped step over `φ` is not `rfl`).
- New, printer: `Examples/Tactics/Branch.lean` (the `tactics` lane's file),
  `branchLocals`' three goals print `{ se1 := a == b }` where they printed
  the `‹Term.binop BinOp.eqB …›` escape.
- `ChainNotation`: `headline_valid` and `ChainRewrites.headlineWrite` use a
  local copy of the headline (today's), the "It is that link" example
  (`AgeWrite.chain .diamond φ`) is gone; new pins: `==`/`!=`/`*`, a scoped
  chain through them, a scoped `valid_close`.
- No fresh name, `~*>` span or rule name of a flipped chain moved.

**Gate**, `Examples/Chains/Storage` (M0 7.5 s, limit 9.0 s): **passed,
8.7–8.8 s** after the review fixes, by the M0/M3.3 method (a copy under
`Solidity/Scratch/` with `Elab.async false`, `#clock` reading
`/proc/self/stat` and `/proc/uptime`, wall time from the worker's start to
the end, imports built, load average under 2): flipped 8.84, 8.69 s;
today's file (`e61996b^`) 7.48, 7.40 s in the same session, so the flip
still costs ×1.17, which `.claude/rules/derivations.md` rule 7 ("in the
time it did before or faster") does not allow: an explained cost, not an
outlier past the gate.  Where it went, per chain (CPU ticks between
`#clock`s, flipped against today's): every chain ×1.3–2 before the fixes,
the header (both calculi's imports) +0.1 s, `#last_line` 0.04–0.1 s per
chain on both.  The lane's first estimate (13.2–15.7 s against 10.5–12.3 s,
×1.27–1.31) was under load; on a quiet machine the flip measured 10.06,
10.12 s against 7.37, 7.40 s (×1.37) before the fixes below.
- The cost was the run's evaluation (`closedLines`/`closedErased`): four
  `evalExpr`s a run (lines and erasure, at the diamond and at the box), each
  a definition the kernel type-checked (12 ms each, the formula inside it),
  and every run done twice for a chain whose `φ` is a binder of the theorem
  (`(φ : Core.Post C [.alias …])`): the proof sees the binder as a new
  variable, so `runCache` missed in `sol_chain`.  Now one evaluation a
  modality (`Fml.chainRunQ`, lines and erasure together), not
  kernel-checked (`evalQuoted`, `debug.skipKernelTC`: the value is a quoted
  term that the kernel checks where it is used), and cached by the closed
  formula, postconditions in slots (`closedCache`), which is the same under
  the theorem's new variables.  `AccountCopy`: 0.40 s → 0.27 s (today's
  0.20 s).
- Left: the scoped statement's elaboration (102 ms against 71 ms on
  `AccountCopy`) and `sol_chain`'s meta-level `Kernel.isDefEq` before the
  kernel's own check (59 ms against 24 ms).

**Left on `Update.lean`'s calculus, with the reason** (the lead's call):
- *Captures in the postcondition's scope* (`EvaluationOrder`, and the tails of
  `Storage` (2), `StorageDelete` (1), `StorageArrays` (2), `Memory` (1),
  `MemoryArrays` (5), `MemoryDelete` (1), `StorageCoverage` (8),
  `MemoryCoverage` (5)): the elaborator writes a statement's captures
  (`uint idx; idx = ++i;`, a call's result, a receiver) in front of it at the
  top level, so the scoped program ends with them in scope, the postcondition
  stands at a context with fresh names, and its erasure is no `Post`
  (`Core.Post.erase`'s `maxIdx ns = 0`).  Fix: the elaborator puts a
  statement and its captures in a block of their own (as W0 did for raw
  blocks) — a low-module change whose pins are other lanes' too.
- *A rewrite under the open modality, then more program*
  (`StorageToMemory.{FieldCopy,TokenCopy}`): a scoped chain goes past a
  rewrite only with rewrites.  Fix: a scoped `sequentialToParallel` on
  `Core.Upd`, or chains re-pinned with the merge at the end.
- *A rule the finder does not name* (`MemoryArrays.ElementOfField.valueWrite`):
  the scoped strategy fires `memoryIndexWriteCaptureAllComplexRecv` on
  `b.items[i] = val;`, but `Core.ruleOf?` names nothing (`#derivation` prints
  `~[?]~>`), so the named link does not elaborate.
- `ChainNotation`, `ChainRewrites`: they test `Calculus/Chains.lean`'s notation
  and rewrites (`calc`, `~~>`, segments, rewrites before the program's end,
  `Fml.Steps.ofSymex`, `Fml.StepBy.unique`), which scoped chains do not have;
  `Examples/Tactics/CoreChains.lean` pins the scoped notation.  W4's
  `calc-del` deletes `Calculus/Chains.lean`: both files are rewritten or
  retired then.

**Found, not this lane's:**
- `Core/Notation.lean` says an update over a name nothing declares declares
  it (`{ x := 10 } x == 10`); it binds `∀ uint x;` outermost instead (the
  `.upd` case of `elabFmlC` does not put the update's new locals in the
  reader's scope, so the reading without the parameter fails).  Harmless for
  chains since `dropAlls`.
- When `Memory.CallWrite` flips, its two inlined calls name
  `functionBodyExpand` where today's chain names `internalCallExpand`
  (`Account memory pv = makeAccount();`): a re-pin with a reason the W3 list
  does not have.
- `~[r]~>`'s "the rule for … is …" error fails to print the scoped statement
  ("failed to pretty print expression").

**Review fixes** (2026-10-08):
- `#chain`/`sol_chain?` (`Core/ChainGen.lean`) and `#last_line`
  (`Core/LastLine.lean`) take the erasure with its outer `∀`s dropped
  (`dropAllsE`), as `elabCoreChain` does: a parameterised scoped line
  (`{ ageVal := 42 } ⟨[ … ]⟩ φ`) now gets its rewrites past the program,
  computed from the `L` `Fml.ViaE` checks.  Pinned: `#chain` of
  `AgeWrite`'s first line and the pasted chain
  (`Examples/Tactics/CoreChains.lean`).
- The printer (`ppTerm`) writes `+ - * /` only at `uint`, the type they read
  back at; an `int` (or unchecked `bool`) one escapes.  Pinned:
  `Examples/Tools.lean`'s `#wp` of `int f = e * 7;`.  No other pin moved
  (`ChainNotation`, `ProofTree`, `PrintedRules`, `Tactics/Values` checked).
- The gate above (`evalQuoted`, `closedCache`).
- Docs: `.claude/rules/derivations.md` rules 1 and 7 and the
  `chain-authoring` skill say a scoped chain is one declaration
  (`Core.Fml.Via`/`ViaE`), segments only on `Update.lean`'s calculus; the
  docstrings of `Fml.Via.valid`, `Fml.Steps.eq_of_length`/`eq_of_measure`,
  `StorageCoverage.requireSimple` and `CheckedArithmetic`'s module no longer
  cite what the flip changed.
- Checked after the `Core/Chains.lean` edit: all 14 `Examples/Chains/` files,
  `Examples/{ChainNotation,Tactics/CoreChains,Tactics/CoreSurface,Tactics/CoreSequents,Tactics/CoreSolSpec}`,
  `Tools/CoreInspect`, clean.

**Checks:** every touched file's diagnostics clean (the seven files checked
before `mergeModality` re-checked after it), `Examples/Tactics/CoreChains`
clean.  Not run: the full build (the printer edit rebuilds everything above
`RuleSyntax`; this session keeps Lake's parallel build off the shared
memory), `check-corpus.sh`, `solkeycheck` (no rule name or annotation
changed).

### W3b lane `chains` (`w3b-chains`, 2026-10-08): the chains flip finished

**Flipped**: every declaration of `Examples/Chains/` (the 33 left on
`Update.lean`'s calculus, `EvaluationOrder` included; no file keeps a *Left
on* part), `Examples/ChainNotation.lean` and `Examples/ChainRewrites.lean`.
Nothing of `Examples/` reads `Calculus/Chains.lean`'s chains any more; its
rewrites (`Calculus/ChainRewrites.lean`) still run on the erasure past the
program.

**What it took** (low first):
- *Captures out of φ's scope* (`Calculus/Core/Notation.lean`,
  `NCtx.dropFresh`).  Not the elaborator change the W3 lane proposed (a
  statement and its captures in a block): a Lean postcondition stands where
  the fresh locals of its context are dropped, by a `Frames.drop` after a
  program, an `Upd.drop` after an update (`{ se1 := 10 } φ`) or in front of
  it under a connective; both print as nothing and erase to nothing.  So
  `φ : Core.Post C Γ` is at the user locals only, `Post.erase` holds, and no
  program, derivation or other lane's pin moves (the elaborator is
  untouched).  It is `Update.lean`'s `Post.noFresh` made a context.
- *A rule the finder did not name* (`MemoryArrays.ElementOfField.valueWrite`,
  `memoryIndexWriteCaptureAllComplexRecv`): the constructor has two `LTy`
  implicits only a side condition's proof mentions (`MRhs.mapFree` under a
  pushed local), which no unification sets.  `Core.ruleOf?`
  (`Calculus/Core/Completeness.lean`) and the chains' `labelAs?` now give
  them any type (proof irrelevance) and check the derivation.
- *A scoped `sequentialToParallel`* (`Calculus/Core/Merge.lean`, new):
  `{U}{V}ψ` as one update, `V`'s right-hand sides read in `U`'s state
  (`Upd.held`, `Upd.graft`), a symbol that reads the global part only where
  `U` writes none (`Upd.envOnly`, `Op*.globFree`), through hidden binders
  when `U` declares nothing (`Upd.lift?`; a `bool` binder excluded, whose
  diamond reading asks a value the binder's type need not keep).  Sound by
  `Fml.mergeRun_leads` over M3's `holds`; the chain link is `Core.Link.merge`,
  proved by the kernel (`Modality.casesOn` under `m`), used while the
  program is open (past it, `Calculus/ChainRewrites.lean`'s merge on the
  erasure as before).
- *Composition* (`Calculus/Core/ChainKit.lean`): `~~>` is `Core.Fml.Leads`,
  and past the program `Core.Fml.LeadsE φ Z L` (`φ` leads to the last
  scoped line `Z`, whose erasure leads to `L`); `Leads.via`, `Leads.viaE`,
  `ViaE.leads`, `LeadsE.via`, `LeadsE.viaE` compose segments;
  `LeadsE.valid`/`valid_close` prove the first line.  `calc`: `Trans`
  instances and `SoundRel` as `Calculus/Chains.lean`'s, and in
  `Calculus/Core/Chains.lean` a step `_ R B` whose line is computed when its
  step is proved (`pendingLines`, checked against the text then).
  `Steps.length`, `Steps.eq_of_length`, `Steps.ofSymex`, `StepBy.unique`
  (the focus and the line).
- *Tactics*: `sol_chain` on a scoped `~~>` (steps, then merges; past the
  program it refuses, so that a re-check never searches: the rewrites are
  named, `sol_rws [..]`, and found by `sol_rws?`/`sol_chain?`, AGENTS.md
  "Writing or fixing a tactic" 1); `sol_chain?` on a scoped chain (proof, continuation) and on
  `~~>` (writes the chain); `sol_rws [..]`/`sol_rws?` on `~~>`
  (`Calculus/Core/ChainGen.lean`).  The scoped `sol_chain` error prints the
  line written it fails to reach, and a rule-mismatch error prints the
  scoped line (it printed "failed to pretty print expression").
- `Fml.ViaE.valid_close` lost its `Avoids` argument (always the empty
  context, now proved; its `decide` overflowed the stack on a long chain).
- Past-the-program rewrites run with the erased postconditions as local
  `Post`s (`withErasedPosts`), so their errors print `φ`.

**Pins and statements changed, each with its reason:**
- *Statement shape* (as the W3 lane's): the `φ : Core.Post C Γ` binders of
  every newly flipped chain; `MemoryDelete.IndexedDelete` (`run`, `reads`,
  `chain`) and `StorageToMemory.FieldCopy` (`source`, `copy`, `chain`) one
  chain each.
- *W3 reason 1* (`cov` gone): `StorageCoverage.requireConditionCapture_call`;
  `ChainNotation` §5, §9 (`requireTrace`, the overflow, `ifTrace`, …).
- *W3 reason 2* (a branch's `}`): `ChainNotation` §5, §8, §9.
- *W3 reason 3* (fewer steps): `ChainNotation` — no `⟨[ ]⟩` line before
  `emptyModality` (`#derivation`, §1, §7), `ageWrite` one step, `ofSymex`
  six.
- *Parameters bound by `∀`* (W2 tree, as the integration lists it):
  `ChainNotation` error and `#check` texts print `∀ uint v;`; the reading
  examples of `StorageCoverage`/`MemoryCoverage` (`dl!{ ⟨ values[++i] = val; ⟩ true } = …`)
  write the right side's parameters in the order the source reads them, a
  `where` clause in parentheses; `ChainRewrites`' refused merge prints
  `∀ uint se1;`.
- *The walk is `Core.Proves`'s* (as `Tactics/Calls`, `Tactics/CallOperands`):
  `Memory.CallWrite` names `functionBodyExpand` for `internalCallExpand` (a
  call with a target) and gains two `~[blockEmpty]~>` links (the callee's
  body block, printed as nothing).
- *New, a hidden binder between stack and alias* (decision 12):
  `StorageToMemory.FieldCopy`'s merge before the copy leaves
  `{ sp := alice.account }` apart (`memoryLocalDeclInitDrop`'s binder stands
  between, and a stack that declares locals is not moved under a binder);
  the last line is the same.
- *New, scoped messages*: the `sol_chain` errors of `ChainNotation` (the line
  written shown; "depends on the modality m, through a rule that reads it");
  `ChainRewrites`' `where Person memory carol` on the memory-read lines (a
  scoped line types `carol`), the two postconditions `φ`, `ψ` of the merge
  under a branch (they stand at two contexts), `:= rfl` → `by sol_chain`.
- *New pins*: `ChainNotation`'s `sol_chain?` and `sol_rws?` suggestions.
- *Review fixes* (second pass): `ChainNotation.unresolved` and
  `ChainRewrites.headlineWrite` are proved by the replay
  (`sol_rws [sequentialToParallel]`, `sol_rws [sequentialToParallel,
  simplifyUpdate]`), not by `sol_chain`, which searched past the program on
  every re-check; a new `ChainNotation` pin is `sol_chain`'s refusal there.
  `#last_line` (and `#chain_rest`) now read a `~~>` statement
  (`Core.Fml.Leads`, `Core.Fml.LeadsE`: `Core.Chain.chainEnd?`), so the two
  `#last_line` pins the flip had dropped are back as they were:
  `#last_line unresolved` (the unresolved read, its text unchanged) and
  `#last_line composed` (silent); `#last_line readSeg` is new, the same
  report at the end of a scoped chain.  The nested-branch `#derivation` of
  §9, deleted by the flip, is re-pinned with its new output (W3 reasons 1–3:
  no `cov` conjunct, a branch's `}`, no `⟨[ ]⟩` line before
  `emptyModality`).  §4's `calc` lost its no-op `~*>` link from a line to
  itself (it is one `~[storageFieldWriteSave]~>` step now), and a new
  scoped `calc` composes a `~[sequentialToParallel]~>` while the program is
  open and a `~>` to `~~>` (the `MergeBy` and `~>` arms of the calc step,
  `pendingLines` keyed by the merge's position, and the low-priority
  `Trans R S Fml.Leads`).
- No fresh name, rule name or `~*>` span of a chain flipped before moved.

**Gate** `Examples/Chains/Storage` (M0 7.5 s, limit 9.0 s): **failed,
9.7 s.**  The integration's method: the real file in a fresh worker, one
worker at a time, imports built, load under 1, wall time from the worker's
start to its last CPU (sampled from `/proc` every 20 ms), each run a fresh
worker:

| Run | Libraries | File text | Wall | CPU |
|---|---|---|---|---|
| `be64b9b` (a detached worktree of it) | `be64b9b` | `be64b9b` | 8.45, 8.54, 8.57 s | 8.96–9.06 s |
| mixed (a copy under `Solidity/Scratch/`) | `w3b-chains` | `be64b9b` | 9.43, 9.38 s | 9.84–9.90 s |
| `w3b-chains` (`cd85314`) | `w3b-chains` | `w3b-chains` | 9.73, 9.75, 9.71 s | 10.24–10.27 s |

So the branch costs +1.2 s (×1.14) over `be64b9b`: +0.9 s from the
libraries, +0.3 s from the file's two newly flipped chains.  The import
loading is the same on both (a file of the imports alone: 0.43, 0.44 s
CPU).  `profiler` on `be64b9b`'s text, its libraries against this
branch's, puts the +0.8 s in the statement elaboration of seven chains
(`BalanceWrite` +57 ms, `BalanceRead` +54, `TokenWrite` +126,
`AgeWriteRead` +39, `BalanceWriteRead` +238, `PushAfterPop` +245,
`AccountsWrite` +50 ms), with `sol_chain`'s tactic time and the kernel's
unchanged (`AgeWrite`, `AccountCopy` and the rest within a few ms); not
found yet which change of `Core/Notation.lean` or `Core/Chains.lean` it
is.  The first measurement of this section
(9.54–9.91 s CPU, both texts on this branch's libraries, the delta added
to the integration's 8.6 s) could not show this: both of its runs carried
the library cost.

**G0 exemption: the merge** (`Calculus/Core/Merge.lean`).  `Fml.mergeRun`
and what it calls (`Upd.held`, `Upd.graft`, `Upd.lift?`, `Tm.substH`,
`Fml.merge2`, `Fml.mergeAt`, `Subst.cons`) are written with `match` on
the indexed families, against condition 1, and the kernel evaluates them
(`Fml.MergeBy` by `rfl`, `kernelReflOrCases`; `ChainGen.mergePath`).
Kept, as measured: a merge runs once a link, not once a step, and only two
chains merge while the program is open.  Timed by the kernel's
`isDefEq` of each `mergeRun k n A = some B` hint of the proof terms (a
scratch module, this worktree): `FieldCopy.chain` 2.5 ms with `m` free
(the attempt that fails before `Modality.casesOn`), then 9.3 and 8.7 ms
(diamond, box); `TokenCopy.chain` 6.6, 12.2, 11.9 ms.  So about 20–30 ms a
merge link at elaboration and 18–24 ms again in the declaration's kernel
check, whose whole is 170 ms (`FieldCopy.chain`) and 66 ms
(`TokenCopy.chain`).  No chain of `Examples/Chains/Storage` merges while
the program is open.  A `casesOn`/`rec` rewrite with an
`@[implemented_by]` twin is the fix if a chain ever merges in a loop.

**Checks**: `lean_build` of `Solidity`, `solkeycheck`, `SolidityCorpus`,
`SolkeyTestSuite` (the last two in `defaultTargets` for the run only):
green, 338 jobs.  `check-orphans` (but the git-excluded `Scratch/`),
`check-doc-paths`, `check-rule-text` clean.  No new `sorry`, `axiom` or
`maxHeartbeats`; `#print axioms` of `FieldCopy.chain`, `TokenCopy.chain`,
`ChainNotation.composed`, `headline_valid`, `Fml.mergeRun_leads`: `propext`,
`Classical.choice`, `Quot.sound`.

**Left**:
- **The Storage gate** (above): 9.7 s against the 9.0 s limit, +0.9 s of it
  from this branch's library changes, in the statement elaboration of seven
  chains; the change responsible is not identified yet.
- `calc` over scoped lines takes program steps and open-program merges
  (tested: `ChainNotation` §4); a step past the program (`Update.lean`'s line) has no `Trans` with a scoped
  one, so such a trace is one chain term (`ChainRewrites` §2, §3 now are).
- The merge crosses a hidden binder only for a stack that declares nothing.
- `sol_chain?` writes its lines in `cdl![m]{ … }` (`Core/ChainGen.lean`'s
  wrappers), which the scoped files read as `dl![m]{ … }`.
- The merge's soundness is over M3's `holds`; CORE 2's fold redoes it over
  `tholds` with the rest of `ChainKit`.
- The read-only review pass was done by this agent alone (no subagents in
  this session); a second review's confirmed findings are applied (the
  pins and the gate above, `simp only` in `Merge.lean`'s `globFree`
  lemmas, now `cases h`).

### W2.5/W3 integration (2026-10-08)

- **Merged** into `intrinsic`, in order: `w25-tsoundA` (a fast-forward), `w25-tsoundB` (conflicts in `Solidity.lean`,
  `docs/module-map.md` and this file only, each a union of both sides: the
  `TSound{Capture,Store,Mem,Local,Control,Step}` and `TSound{Calls,Loops}`
  imports and rows, both lane sections), `w25-testsuite`, `w25-tactics`
  (which had already merged `w25-tsoundA`, `w25-testsuite`, `w25-tree`
  and `w25-chains`, with its own fixes across them: `sol_prove` on `⊢` by
  `ProvesDerive`, the `Branch.lean` `==` pin, the `Tools` int-product pin),
  so `w25-chains` and `w25-tree` were already in.  No duplicate import, module-map
  row or fully-qualified declaration (`dups.py`: only the known
  `Evm/Repr`/`Examples/Verify` `as` false positive).
- **Full build: green, no fix needed.**  `lean_build` over `Solidity`,
  `solkeycheck`, `SolidityCorpus` and `SolkeyTestSuite` (336 jobs; the last
  two in `defaultTargets` for the run only).  The first run (1724 s wall)
  overlapped other sessions under the 32 GiB cap: `TestSuite/Derived2` and
  `SortCheck/Faithfulness` were OOM-killed (exit 137, not a code error), and
  every module's time in that log is contention (Derived* about 1500 s).
  The second run rebuilt those two (Derived2 9.3 s, Faithfulness 25 s) and
  finished in 31 s.  No new `sorry`, `axiom` or `maxHeartbeats` override;
  five `erw`s in `TSoundCalls` (the lane's note).
- `scripts/check-orphans.mjs`: 322 reachable, none orphaned but the
  git-excluded `Solidity/Scratch/`.  `scripts/check-doc-paths.sh`: OK (50
  ambiguous citations, all resolving).  `scripts/check-rule-text.sh`: empty.
- **W3 gates**, re-timed fresh, one worker at a time with nothing else
  elaborating (wall from the worker's start to its last CPU, imports from
  the cache):

  | Module | M0 | Limit | Now |
  |---|---|---|---|
  | Derived9–11 (today's text, not flipped) | 19.1 s | 22.9 s | 19.7 s (7.0 + 9.9 + 2.8) |
  | CoreDerived9–11 (the scoped twins) | — | 22.9 s | 20.9 s (8.3 + 9.6 + 3.0) |
  | `TestSuite/Problems` (legacy only, not flipped) | 1.2 s | 1.44 s | 1.25 s |
  | `Examples/ProofTree` | 10.1 s | 12.1 s | 11.2 s |
  | `Examples/Chains/Storage` | 7.5 s | 9.0 s | 8.6 s |
  | `Solkey/TestSuite` | 10.4 s | 12.5 s | 10.8 s |
  | `Examples/Benchmark/Syntax` | 1.2 s | 1.44 s | 1.44 s (at the limit) |

  All within their limits as measured here.  Two are not the gate the plan
  means: Derived9–11 and Problems are still today's (the flip is blocked on
  diamond leaves, `testsuite` above), and the testsuite lane's own
  measurement of Problems with the scoped `main decl` is 4.6 s, over the
  limit, with its proposal (scoped statements in `CoreProblems`) left for
  the lead.  The chains lane measured `Chains/Storage` at 9.5–9.8 s before
  its cache commit (2086fa4); 8.6 s here.
- **Pins changed, union of the lanes** (each lane's section has the
  detail):
  - *W3 reason 1, `cov` gone:* `Chains/CheckedArithmetic`
    `OverflowReverts`, `Chains/StorageCoverage` (requireConditionCapture,
    requireSimple, ifElseUnfold, ifElseSplit), `Tactics/Revert` (`case cov`
    deleted), `Tactics/Branch`, `Tactics/Loops` docstring, `ProofTree`
    `sol_derive?` walks (`split` for `splitBox`).
  - *Reason 2, a branch's `}`:* `StorageCoverage` branch goals,
    `Tactics/Branch`, `ProofTree` `#proof_node` and JSON.
  - *Reason 3, fewer steps:* `ProofTree` serial numbers and JSON (6 nodes
    for 7), `Tactics/Loops` `#proof_tree`, `Tactics/Payment` (`⟹ true`, no
    `emptyModality` after a last statement).
  - *New, parameters bound by `∀` (W2 tree):* the `allRight` first node of
    the scoped trees, `#proof_node 2` for 1, `Tools` `#wp` prefixes,
    `Notation`'s `#check dl!{…}`, `Tactics/Payment`, `Loops` `#step`,
    `Branch`.
  - *New, scoped types printed:* `Benchmark/Counter` and `Tactics/Specs`
    `#check spec!{…}` (`Core.Fml C []`), `Tactics/TryCatch`, `Notation`.
  - *New, the walk is `Core.Proves`'s:* `ProofTree` and `Tactics/CoreDerive`
    `sol_derive?` text (Core constructors, `bindIntro`, `updIntro`,
    `Proves.close` leaves); `Tactics/Calls` gains a `blockEmpty` step;
    `Tactics/CallOperands` names `functionBodyExpand` for
    `internalCallExpand`.
  - *New, statement shape of scoped chains:* `φ : Core.Post C Γ` binders,
    segments merged into one chain (Storage.BalanceWriteRead,
    StorageDelete.SubtreeDelete, MemoryDelete.FieldDeleteRef,
    StorageCoverage ifElseUnfold), `rfl` → `by sol_chain`;
    `ChainNotation`/`ChainRewrites` use local today's copies.
  - *New, printer:* the `==`/`!=`/`*` update escape prints as source
    (`Tactics/Branch` `{ se1 := a == b }`, `ChainNotation` round trips).
  - *New, erase guard in the command:* `Solkey/Constructors` and
    `TestSuite/CoreProblems` info lines add "erasing to its legacy
    statement".
  - Moved unchanged into "Read without the switch" blocks: `Decide`,
    `StorageDelete`, and the diamond walks and trees.
  - Unchanged: Derived1–14 text, `Report.lean`'s 437, `Problems.lean`'s
    pins, the fresh names (`se1`, `sp1`).
- **Left, across lanes** (from the lanes' lists): `Stmt.TSound C` and an
  unconditional `Proves.tvalid` wait on the `Stmt.TArmOk` conditions (copy
  off the bridge, push at the bound under the diamond, empty memory type
  under the box binder); `Proves.close` is box-only, which blocks the
  Derived1–14 flip (330 of 437 obligations are diamonds) and the diamond
  walks and trees; no scoped `sol_prove?`/`sol_chain?`/`sol_rws?`; the
  statement-level captures in φ's scope keep about 25 chains on today's
  calculus; the read-only review pass was not run by any lane.
  `check-corpus.sh` and `solkeycheck` were not run (no rule name or
  annotation changed).
- The six lane worktrees are removed (the branches stay).

### W3b lane `testsuite` (`w3b-testsuite`, 2026-10-08)

**The flip still does not land.**  It needs diamond leaves to close, and at
`be64b9b` they do not: `Fml.closableB` asks `m = .box` of an update, and
`Proves.close`/`closeTrue` ask `H.boxOnly` (`Calculus/Core/Closable.lean`,
`Calculus/Core/Proves.lean`).  The switch to `Fml.tclosableB` is CORE 2's
item 5, which waits on decision 17 (CORE 2 section below).  Every `Derived`
module holds diamond obligations, so none can flip with its text unchanged;
in a scratch module with the flipped layout, `#solkey_derive?` on the
diamond `boolIsTrueOrFalse` reports the walk's error ("a leaf
`Proves.close` does not take").  What landed is the rest of the flip, ready
for it:

* **The erase guard was the cost, not the kernel.**  Of the 4.25 s the
  command elaborated in, 4.1 s was `evalConst` of each legacy statement:
  the interpreter evaluates the contract again for each of the 437 (9 ms
  each).  The guard now computes the legacy statement from the program it
  already holds (`Problem.fml m xs P`), and checks that the legacy
  declaration's value is that application, as an expression.  It checks the
  same thing as before.
* **One table.**  `solc_scoped_problems` declares the statements as one
  list, `N.problems.core` (`N.problems` with `main`), quoted and hash-consed
  together.  The kernel checks it once, in 0.40 s; checking 437
  declarations took 3.44 s, the contract's types, contexts and side
  conditions re-checked in each.  `N.f.problem[.core]` is the entry
  `List.getD N.problems i tt`.  `Core.Symex.evaluable` reads an entry of a
  codeless table back from its list literal (`listLitGet?`).  That is the
  lane's one edit outside its files (`Calculus/Core/Symex.lean`); it only
  adds a case.  The scoped command now elaborates in 0.38–0.43 s: resolve
  0.05 s, guard about 0.15 s, quoting 0.32 s (interpreted).
* **`solc_problems … legacy` does not compile.**  No tactic proves a
  legacy statement.  `#solkey_problem` and `#solkey_scan` read its value
  (`legacyStatement`), which is `Problem.fml N m xs N.f`, all of it
  compiled.  This saves the 0.34 s of LCNF/IR.
* **`#solkey_derive?` on the scoped calculus.**  Once `N.f.problem.legacy`
  exists, the goal is the scoped `⊢ N.f.problem` and the search is
  `scopedSearch`: `Core.Seq.prove`, then `Derive.searchLeaf` on each leaf of
  today's calculus.  The replay text is unchanged.  `Frontend/Problems.lean`
  now imports `Calculus.Core.ProvesDerive`.  In a scratch with the flipped
  layout it derives `additionStorageWrite`,
  `storageIndexArrayAddAssignOutOfBoundsReverts` (with its leaf lines) and
  `testStorageNestedPushReturnAlias`.  The last one prints a single leaf
  where `Suggestions.lean` pins `case leaf1`/`case leaf2`: this is the
  `Derived7` deviation already left for the lead (W3 lane `testsuite`), and
  it moves that pin at the flip.  `#solkey_obligations` counted the scoped
  theorem.

**Gates** (wall clock of one `lean_diagnostic_messages` call on a fresh
worker, the MCP round trip included, other sessions running):

| Module | Limit | Now |
|---|---|---|
| `TestSuite/Problems` as it is (not flipped) | 1.44 s | 1.24 s |
| flipped `Problems` (`solc_problems … legacy` and its pins) | 1.44 s | 0.85 s |
| flipped `Problems` with `solc_scoped_problems … main decl` in the same module | 1.44 s | 1.62 s |
| Derived9–11, today's text (not flipped) | 22.9 s | 20.1 s (7.2 + 10.0 + 2.9) |
| CoreDerived9–11, the scoped twins over the table | 22.9 s | 22.3 s (8.6 + 10.5 + 3.2) |

The scoped statements in `Problems` cost 1.62 s against 1.44 s, over by
12%, down from 4.6 s.  What remains is new work: quoting 437 programs, the
guard, and one kernel check.  Under Decision 9 the gate is the aggregate,
so this is recorded rather than worked around.  The flip as planned keeps
them in `CoreProblems` (`main decl`), which leaves `Problems` at 0.85 s.
Flipped Derived9–11 cannot be timed until diamond leaves close.

**Pins changed:** none.  `CoreProblems`' info line, `Suggestions`,
`Problems` and Derived1–14 are unchanged, and so are the fresh names.

**Checks.**  `lean_build` of the default targets is green (300 jobs, the
`Symex` edit rebuilding its importers).  The following were checked file by
file: `TestSuite/{Problems,CoreProblems,CoreSeq,Suggestions}`, Derived9–11,
CoreDerived9–11 and `Solkey/Constructors`.
Review fixes: `Solkey/ScopedFlip.lean` pins the three switches on every
build, over a one-function fixture (`tests/solc/ScopedFlip.sol`):
`solc_problems … legacy`, `solc_scoped_problems … main decl`,
`#solkey_problem`, the scoped `#solkey_derive?` (its replay is `sol_prove`)
and `#solkey_obligations` counting the scoped theorem.  `scopedSearch` is
`Derive.proveSearch` with the scoped walk as its `prove` parameter, so the
two loops are one.  `SolkeyTestSuite` was not built
whole: fourteen `Derived` workers at once exceed the memory cap.
`check-orphans` (apart from the git-excluded `Scratch/`) and
`check-doc-paths` pass.  No new `sorry`, `axiom` or `maxHeartbeats`.

**Left (the flip itself, once diamond leaves close):**
1. `Problems.lean` → `solc_problems Solkey.TestSuite legacy`;
   `CoreProblems.lean` → `solc_scoped_problems Solkey.TestSuite main decl`
   (its import of `Calculus.Core.Derive` can go: `Frontend/Problems.lean`
   brings `ProvesDerive`), plus `import Solidity.Calculus.Core.Surface`.
2. Each `Derived1`–`14` imports `CoreProblems` instead of `Problems` and
   adds `open scoped Solidity.Core.Surface` after `open Solidity Proves`.
   The theorem text stays the same, except `Derived7`'s `case leaf2` if the
   lead approves the deviation.  `Suggestions.lean` imports `CoreProblems`;
   its `testStorageNestedPushReturnAlias` pin then loses `case leaf1`/`case
   leaf2` (the same deviation).
3. Delete `CoreDerived9`–`11` and `CoreSeq` (their `Solidity.lean`/lakefile
   roots and module-map rows).  Check `Report.lean`'s 437 and
   `check-testsuite.sh`.  Time flipped Derived9–11 against 22.9 s.

## W4 — delete the old calculus and runs (3 lanes, plus a reader dry run)
Before the lanes branch, the lead makes `Surface` the default and removes the `open scoped` lines with sed.

1. **`sem-del`**
   - Delete:
     - The old `Stmt.run`/`Loop`.
     - `Semantics/Core.lean`'s M3 `State` and run.
     - `RunErase`, `TypedRunErase`, the fresh-name lemmas in `Agree`.
     - `Evm/{Compile,Correctness,Examples}.lean` and `never_stuck`.
     - The old `Mutability`/`NoPanic`/`Callback`.
   - First, port `Tools/Counterexample.lean` off `Prog.runFuel` (and its
     `.stuck`): `Fml.eval3` over the Core formulas, its loops by the typed
     run's fuel, `eval3_tt`/`eval3_ff` against `Core.Prog.trun`.  Its
     docstring's soundness is against the `Prog.run` deleted here.
   - Then `Machine.mem : Nat → Word` (`cell = id`), deferred from W1 `evm`.
   - `Halt` loses `stuck`. The term model's error for ill-sorted terms becomes `Res.undef`, because the closer's terms stay untyped.
2. **`calc-del`**
   - Delete every old calculus module that has a Core twin: `Logic`, `Symex`, `Quote`, `Derive`, `SoundKit`, `SoundUpdate`, `SoundUnfold`, `SoundLoop`, `RuleSoundness`, `Completeness`, `Uniqueness`, `Progress`, `SolkeyFragment`, `Sequents`, `ProofTree`, `Chains`, `ChainGen`, `LastLine`, `Notation`, `Spec`, `Contracts`, `Callback`, and the old body of `Rules.lean`.
3. **`modal`**
   - `Update.lean`'s `Fml` loses `.modal` and becomes `NFml`.
   - Delete the modal arms in `Close`, `UpdateRules`, `ChainRewrites` and `Decide`.
   - The untyped `Stmt` becomes `Surface.Stmt`.
4. **`reader-dry`** (side-projects `lean/solkey`, branch `intrinsic`, user approved)
   - On that branch only, point the `lakefile.toml` require at `../../../solidity-lean-intrinsic`.
   - Port the reader's `Corresp.LeanShape` module (19 `Stmt.` references) to read Core constructor types, erasing `.there`/`up` as `Core.Delab` does and mapping `unfold`/`bind`/`inline` to today's premise shapes.
   - Regenerate the reader's `Corresp.Proved` module with `GenProved`.
   - `expectedPins` may move only on the rows for the newly claimed `blockEmpty`, `functionFrameEmpty` and `functionBodyExpand`.

**Merge order:** sem-del → calc-del → modal.

**Carried from W2 `tree`:** the callback reading over `TState` (`holdsC`,
`ValidC`, their theorems), `ProvesC.sound` and `ProvesC.close`, unless a
W3 lane has landed them.  `Calculus/Callback.lean` is not deleted
(`calc-del`) before they are, so no `ProvesC` rule is left unverified.

**Checks:**
- All three libraries build; `check-orphans`, `check-doc-paths`, `check-corpus`, `check-testsuite`; `solkeycheck` at zero.
- No pins change.
- Re-time every M0 row: deleting modules must not slow anything.

## W5 — final rename (the lead alone)
- One scripted commit (`git mv` plus `rg`/`sed`, no hand edits):
  - `Solidity.Core.X` → `Solidity.X`.
  - `Calculus/Core/*` → `Calculus/*`; `TypedRun` → `Semantics`.
  - `trun` → `run`, `TState` → `State`, `Evm/Core*` → `Evm/*`.
- A full rebuild follows: about 24 minutes, plus the TestSuite.
- **Pins:** only those that print qualified constants (`#taclet` naming `Core.Taclet.*`, `#print axioms`) may change.
- **Reader:** the dry-run branch renames its identifiers and regenerates the reader's `Corresp.Proved`. The require goes back to `../../../solidity-lean` when `intrinsic` merges into `master`; the reader merges then.
- **Docs (M7):**
  - `module-map`, the `kernel-port` row.
  - `lean-key-rule-map` rows: the claimed rules, the capture pop, the hidden binder, `unset`.
  - `solc-alignment`, `loops.md`.
  - `solc-validation`'s "not stuck" claim, now true.
  - Trim `intrinsic.md` to its module-map entry.
- Then the review pass: a finder and a skeptic per area.

## W6+ — porting the closer (M6c), gated
- **The boundary moves top-down.** A ported module takes `Fml C Γ` and erases only before calling the modules below it.
- **Scope is smaller than 25k lines.** The symbol libraries never need porting, because Core terms share `Op0`–`Op3`: `ReadWrite`, `TermRules`, `TermTaclets`, `MemRead`, `MemNames`, `MemTheory`, `SlotLemmas`, `KeyNotation`, `DecideLang`, `Literals` and `Theory/**`. Only modules that handle locals, updates or formula structure port.
- **Waves:**
  - 6a: `Closer`, `DecideSyn`, `DecideComplete`, `Close`, with symbolic atoms keyed by `Idx`.
  - 6b: `Decide.lean` alone (10k lines in one file, so one agent).
  - 6c: `UpdateRules`, `StateParts`, `Rewrite`, `TheoryRewrite`, `ChainRewrites`, `ChainBranches`.
- **Gate per module:** the Derived* files and `Examples/Tactics/Decide` must stay within 1.2× of the erased-form timings taken at W5.
- **Fallback (Decision 7):** a module that fails the gate stays on `NFml` for good, documented as the decision procedure's IR. When nothing uses `NFml` any more, `NFml` and `Fml.erase` are deleted.

**Agent and memory limits:** at most 4 Lean agents in any wave, each with 3–4 open files. W0 and W5 rebuild low modules, so they run one agent.

Decision 11 (lead, 2026-10-08, open to the user's override before W4): the
untyped `Stmt` survives only as `Surface.Stmt`, the elaborator's output and
the printers' target, with no run, no taclet and no `wt`; every semantics is
on Core. W0 is done: `Core.Proves.valid` is unconditional, and the
elaborator's output is `Fresh` (`ReachableU → Reachable`).


Decisions 12–14 (lead, 2026-10-08), answering the `sound` lane's three
questions (W2 section):

12. *Hidden binder at a memory type*: option (c). `Fml.bind` takes the
    modality; under the diamond it asks for an inhabitant of the binder's
    typed domain, under the box it stays universal. Printed as today; memory
    locals stay non-dangling.
13. *Array length past `uint`'s range*: bounded by the type. A dynamic
    array's typed value carries `length < 2^256` (push at the bound
    reverts, as an out-of-gas stand-in, with a solc-alignment row), so the
    typed run never diverges on a length read and `len` on an erasure is in
    range.
14. *`bool` mapping key*: `Update.lean`'s key read (and M3's run) hash a
    `bool` as 0/1, as solc and the typed run do; `bridgeOk` drops its
    bool-key exclusion.

### Decisions 12–14, implemented (2026-10-08, on `intrinsic`)

Three commits, low modules first (14, 13, 12).  The four-target build
(`Solidity`, `solkeycheck`, `SolidityCorpus`, `SolkeyTestSuite`, the last two
in `defaultTargets` for the run only): green, 321 jobs, no pin moved.  No new
`sorry`, `axiom` or `maxHeartbeats`; `dups.py` (but the known `as`
false positive), `check-orphans` (but the git-excluded `Scratch/`),
`check-doc-paths` and `check-rule-text` clean.

**14, a `bool` mapping key** (`901684c`).  The hash is in the lowering, not
in `Update.lean`'s `at`.  The interpreters read an index at its key type
(`Value.keyAt k`: a `bool` as `0`/`1`, a number as itself, a value of the
other kind stuck), in `Semantics.lean`'s and M3's `Loc.resolve`; the typed
run already hashed it (`PrimTy.key`).  A rule's term writes the hash:
`m[b]` lowers to `at(m, b ? 1 : 0)` (`Term.keyAt`, `Tm.keyAt`, both
`Loc.lower`s), and the rule table names it `Simple.keyLower`/`Val.keyLower`
(`RuleSyntax.lean`'s `schemaKey`), which prints as the index, so no rule
text or pin moved.  So `at` still reads a number (`Value.asInt`), as the
solc frontend already wrote a `bool` key (`b ? 1 : 0`).
*Why not in `at` itself, as the decision's text has it*: the untyped
closer reads formulas over untyped states, where a `uint` local may hold a
`bool`.  With `at` hashing a `bool`, `a != b → [ m[a] = 1; m[b] = 2; ]
m[a] == 1` is no longer valid there (`a = true`, `b = 1` hit one slot), and
`sol_close` failed on every such leaf (`CloseTests`, `Notation.twoKeys`,
`Tour`, and the TestSuite's distinct-key proofs would follow).
`Prog.bridgeOk` keeps only the copy at a `BadDup` type (`Src`, `NewLhs`,
`assignFromMem`); the path and value `bridgeOk`s and their hypotheses are
gone from `TypedRunErase.lean`, `StraightRun.lean`, `Constructibility.lean`.
`PrimTy.keyAt_erase_key` replaces `asInt_erase_key`.  A storage keeps
entries at a `bool` key: `Ty.numericKey` is `Ty.isKey` (a reference key
alone has none), `SVal.fits` takes a `bool` key `0`/`1` (`PrimTy.keyFits`),
the builder writes it (`keyLit`), `Ty.keyFitsB` (`wt(storage)`) likewise,
and `bool_key_reachable` replaces `bool_key_not_reachable`.

**13, array lengths** (`9dcc754`).  `SVal.array {n} (elems : SVec E n)
(shadow : SList E) (hn : n < 2 ^ 256)`: the live elements are a vector of
their length, the bound a field (a mutual inductive cannot state it of an
`SList`, and a `Prop` family cannot join the block).  The functions stay
folds over the families (`Fold.array` takes `SVec`, `ArrView` is the
array's `Shape`); `overlay` takes the old elements as a list
(`SVec.overlayOn`), `beq` compares a vector with a list (`SVec.beqL`),
`pop` keeps `dropLast`.  A memory array is `{l // l.length < 2 ^ 256}`
(`MObj`), so `Storage.len` and `Heap.lenU` return a `uint` (`lenU`) and
`lenT` is gone: a length read never diverges.  `newArrT` takes the `uint`.
*A push at the bound diverges, not reverts* (`Storage.full`,
`TRun.push`, `ARhs.evalT`): a typed revert must be the untyped one's
(`TRes.Agrees`), and the untyped push has no bound; making it revert breaks
the untyped calculus's diamond obligations with a push (331 of the
TestSuite's 452 functions are diamonds), since a storage with `2^256 - 1`
elements is reachable.  `diverge` agrees with any untyped outcome, so the
bridge needs nothing; `docs/solc-alignment.md`, "Array lengths", says so.
The straight programs' bridge (`StraightRun.lean`) now asks that every push
of the scoped run land below the bound (`Prog.pushesShort`), and the
builder proves it of its own pushes (`pushes_short`, the run lemmas' fourth
conjunct), with `SVal.fits` strict for a dynamic array (`elems + shadow <
2^256`).  The compiler's `push_ok` takes the bound from `Lmax`.

**12, the hidden binder** (`daf67a5`).  `Fml.bind m x t φ`, and
`Hyps.bind H m x t`: `holds`/`tholds` read it as `m.forallB` (universal
under the box; under the diamond a value of the type first, then
universal).  `Premise.fml` passes the rule's modality; the binders the
notation and the specs put in front (`withBinds`, `Fml.closeN`) are box
binders, universal as before.  M3's types are all inhabited
(`LTy.denote_nonempty`, `holds_bind_intro`), so M3's soundness is
unchanged.  Over the typed state a memory type may be empty: `Hyps.boxOnly`
and `Fml.Leaf` (so `closableB`, `TClosable`) accept a diamond binder only
at an inhabited type (`LTy.inhabited`, `LTy.tdenote_nonempty`).
`Premise.tsound_bind_all` is the arm's shape: a statement that runs as `P`
from every value pushed is sound, the value from the premise under the
diamond, from the type under the box.  Printers drop `m` (`Delab`,
`Print`, `Quote` carry it), so no pin moved.

**Left for the lead.**
1. *A push at the bound under the typed diamond.*  `⟨ b.push(x); ⟩ true`
   is false over the typed state when `b` holds `2^256 - 1` elements, and
   `wt(storage)` allows that storage.  After the W3 flip a TestSuite
   diamond obligation whose function pushes is then false as stated, where
   solkey (unbounded arrays) proves it.
   Options: a diamond that reads out of gas as KeY does (no bound), a `wt`
   with a smaller length bound, or a precondition on the obligations.
2. *`Stmt.TSound` of the push rules at the bound.*  The rule's update
   (`Update.lean`'s unbounded `pushAt`) ends in a storage of `2^256`
   elements, which no typed state erases to, so `tholds` reads the update
   vacuously true while the typed run diverges.  Under the diamond the arm
   is false there unless the update term fails at the bound too (which
   brings back item 1 in the untyped world) or `tholds`' update reading
   asks for a typed state the update ends in.

### W2.5 lane `tsoundA` (`w25-tsoundA`, 2026-10-08)

Typed soundness, part A: every arm of `Calculus/Core/Arms.lean` and
`Step.lean` (all of `Stmt.step` but `Calculus/Core/Blocks.lean`'s calls,
`try` and loops) proved `Premise.TSound` against `Stmt.trun`, in new modules
beside M3's (`Calculus/Core/TSound{Arms,Capture,Store,Mem,Local,Control,Step}.lean`);
no M3 `Sound*` file is edited.  `Stmt.tstepSound_arms` dispatches them.
Build green (`lean_build`, 292 jobs, the new modules only rebuilt); no
`sorry`, `axiom` or `maxHeartbeats`; `check-orphans`, `check-doc-paths`
clean.

**The per-arm statement** (`Calculus/Core/TSoundKit.lean`, committed first
for `tsoundB`): an arm's theorem is M3's name with `tsound` for `sound`
(`localStep_tsound`, `tsound_setLocal`), takes the typed state `σ` first,
then the arm's arguments, the premise `q` and `hq : …Step k … = some q`, and
concludes `Premise.TSound m s q σ`; `Stmt.TStepSound` is `Stmt.StepSound`
over `TState`, in the states where the statement meets `Stmt.TArmOk`.  The kit adds, besides the shapes W2 left:

* `TRes.Sim` and the shapes up to the halt (`tsound_unfoldSim`,
  `tsound_capture{,SP,MV}K`, `tsound_capture{,SP,MV}Sim`, `TRes.Sim.err_bind`),
  and `Premise.tsound_of_halt` (a box over a statement that halts);
* **an update through the bridge** (`Premise.tsound_update_run`,
  `tsound_updateSim_run`, `tsound_cases_run`): an update rule's update is a
  term of `Update.lean`, read on the erasure, so M3's equation
  `U.apply σ = s.run σ` (or `Res.Sim`), stated over any untyped state,
  gives the typed arm by `Stmt.trun_erase`, where the statement is on the
  bridge and the typed run does not diverge under the diamond.  Every update
  arm is proved this way (`TSoundArms.lean`: M3's arm proofs as `*_run`
  lemmas, and `Val.evalT_nd` and its kin: an evaluator only reverts);
* the typed shift lemmas (`Val.evalT_up` and kin, `TState.push_lift`: a
  pushed state is the state lifted along `up`, so each is
  `TypedRunWk.lean`'s `*_wk`), `liftedT_up_drop`, `Ext.self_eq_refl`.

A capture compares typed runs exactly (no bridge): a statement read with a
local pushed runs lifted (`TRun.*_pushT`, `OpLoc.AgreeT`, `pushedT` in
`TSoundCapture.lean`, from `TypedRunWk.lean`'s `*_lift`), a hole's typed
continuation (`SHole.contT`, `MHole.contT`, `VHole.contT`), blocks of
captures by `Prog.trunSt_declLocal_cons` and kin.  A `bool` is a `bool`, so
the splits cover every state (`tholds_isBool`) and the short circuits run
as their unfolded `if` exactly; a captured `if` condition's weakened
branches run lifted by `Prog.trun_wk` (`Prog.trun_wk_up`).

**`Stmt.TSound C` is not provable as stated**: three arms are sound only
under a condition on the statement (`Stmt.TArmOk`, `TSoundKit.lean`, a
hypothesis of `Stmt.TStepSound`, which `Stmt.tstepSound_arms` concludes):

1. *A storage copy off the bridge* (`l = sp;`, `l = mp;` at a type with a
   repeated member name, `Ty.nodupS`): the rule's `save`/`copyMem` copy by
   name, the typed run by position.  `tsound_save`, `tsound_saveMem`,
   `assignStep_tsound`, `copyStep_tsound`, `assignFromMemStep_tsound` take
   `bridgeOk`.  A well-formedness condition on contracts would discharge it.
2. *A push at the bound under the diamond* (the lead's item 2 above):
   `tsound_pushSlot`, `tsound_extend`, `tsound_pushSome`,
   `tsound_rebindPush`, `pushStep_tsound`, `rebindStep_tsound` take
   `m = .diamond → (Stmt.trun σ s).NoDiv`.  Only the update arms use it; a
   capture compares typed runs and needs nothing.
3. **New: `memoryLocalDeclInitDrop` under the box.**  Decision 12 keeps the
   box binder universal; over a heap typing with no object of the local's
   type the premise `∀ mv. [mv = r; ω] φ` is vacuous, while
   `T memory mv = new T[](n);` (or a copy out of storage) allocates one and
   runs: `[T memory mv = new T[](1);] false` is false, its premise true in
   such a state.  `tsound_declMemInit` takes
   `m = .box → Nonempty ((LTy.mem R).TDenote C σ.H)`, at an allocating
   initializer only: an alias `T memory mv = mp;` needs none
   (`tsound_declMemAlias`), since the object `mp` names is one and a halt
   reading it is a revert, which closes the box.  A derivation cannot
   exploit it (the binder's erasure is universal over inhabited untyped
   values, so no leaf under it closes vacuously), but the per-state arm is
   false, so `Proves.tsound`'s shape (`Stmt.TSound`, per premise, in every
   state) cannot be met.  Options: the box binder at a memory type reads
   "every reference of the heap grown by the rest's allocations" (a typed
   reading change), or the binder asks an inhabitant under the box too
   (the diamond's reading: the arm is then sound, its premise false over
   such a heap, but a box derivation through the binder must show one), or
   `Proves.tsound` threads `Stmt.TArmOk` as an invariant of the states it
   reaches.  For the lead.

Since `Proves.tsound` applies the arms in arbitrary states, conditions 2 and
3 cannot be threaded through it as they stand; condition 1 can, as a
property of the program (`Prog.bridgeOk`), if `Stmt.TSound` takes it.

**Left (outside this lane):** the block arms (`tsoundB`); assembling
`Stmt.TSound C` once the lead decides the three conditions; the read-only
review pass (finder and skeptic) was not run: this session cannot spawn
subagents.

### W2.5 lane `tsoundB` (`w25-tsoundB`, 2026-10-08): typed soundness of the block arms

* **Syntax out of the M3 runs.**  `Thin.Over` (with `trans`, `append`),
  `CallRet.wk_over`, `Stmt.wk_over`, `Prog.wk_over`, `frameMut` and
  `Prog.frame_some` moved to the syntax-only `Calculus/Core/WkOver.lean`;
  `TypedRunWk.lean`/`TypedRunFrame.lean` import it instead of
  `RunWk`/`RunFrame`, so W4 can delete those two.  `RunWk` keeps only the M3
  reading `Thin.Over.env`.
* **`Calculus/Core/TSoundCalls.lean`**: `Stmt.tsound_call` (every
  `callStep` premise: the four `expand_function_body` shapes, the four
  `functionCallArgCapture` shapes) and `Stmt.tsound_tryCall`, as equations
  between typed runs read at their states (`Premise.tsound_unfold`/`inline`).
  The inlined body is the body run in its frame, lifted
  (`Stmt.trun_block_wk`, from `Prog.trun_wk`); the caller's locals come out
  weakened along the heap the body grew, which `TRun.call` gives back
  (`TEnv.drop_put_atop_wk`, `thin_put_keepAllAtop`, `thin_keep_put_atop`).
  A capture runs the call from the caller with the value on top
  (`TRun.callFrom_capture`).  `try`'s clauses bind typed values, so no
  `Fits` is needed (`tholds_binders_all`); decoding never panics.
* **`Calculus/Core/TSoundLoops.lean`**: `Stmt.tsound_loop`.  One turn
  (`Stmt.trunSt_loop_unfold`, via `TLoop.run_map`: the extension a loop
  head carries plays no part), `loopExit` by `tholds_isBoolD_lower` (a
  lowered condition read on the erasure is its typed value:
  `Val.evalT_erase` and `Val.evalT_nd`), the invariant rules by
  `TLoop.run_induct`/`run_variant` with `tholds_anonHavoc` (from
  `TState.eq_anonHavoc`).  No condition: a typed `bool` is `true` or
  `false`, and the diamond needs no `BoolOK`.  The block arm is here too:
  `Stmt.tsound_block`, by `Stmt.trunSt_block`.
* **`Fml.tclosableB`** (`Calculus/Core/Closable.lean`): the Bool twin of
  `Fml.TClosable`, with `Fml.tclosableB_sound`, ready for the switch of
  `Proves.close`; not used yet (`Proves.close` still asks `closableB`, and
  `Proves.tsound` goes through `Fml.closableB_tclosable`) until the
  assembly of `Stmt.TSound C`.
* Uses from M3 modules that the flip must keep or restate:
  `Args.capture_snoc` (`Calculus/Core/SoundCalls.lean`), `holds_isBoolD`
  (`Calculus/Core/SoundBlocks.lean`), `evalBinop_cmp_true`
  (`Calculus/Core/SoundLoops.lean`), `Val.eval_lower`
  (`Calculus/Core/SoundKit.lean`), `Val.evalT_erase` and
  `Val.evalT_noPanic` (`Semantics/Core/TypedRunErase.lean`, deleted at W4
  `sem-del`).


Decisions 15–17 (lead, 2026-10-08), answering the `Stmt.TArmOk` conditions
and "Left for the lead":

15. *Push at the bound*: resource exhaustion, read as KeY reads gas (not at
    all). The typed run's push at the bound ends in a new halt `exhausted`
    that both modalities accept, like solkey, which models no gas; the
    TestSuite's pushing diamond obligations stay provable. solc-alignment
    row: solc panics (0x41) on a storage array past 2^64 elements; Lean's
    bound is 2^256 and an exhausted run proves any modality. The `NoDiv`
    hypotheses of the push arms go.
16. *Copy off the bridge*: the elaborator rejects a struct with a repeated
    member name, as solc does ("Identifier already declared"); `BadDup`
    becomes a pinned elaboration error; `bridgeOk` and `Ty.nodupS`
    hypotheses go.
17. *`memoryLocalDeclInitDrop` under the box*: change the typed reading, not
    the rule text: the hidden binder at a memory type ranges over the
    references of the heap grown by the initializer's allocations (or any
    heap extension), so the premise is not vacuous where the conclusion
    allocates. Existing box derivations must keep closing. If that proves
    infeasible, `Proves.tsound` threads `Stmt.TArmOk` as an invariant of
    reachable states instead; record which.

### Decisions 15–17, implemented (2026-10-08, CORE 1, on `intrinsic`)

Build (`lean_build`, `Solidity`, `solkeycheck`, `SolidityCorpus`,
`SolkeyTestSuite`, the last two in `defaultTargets` for the run only): green,
337 jobs; one fix on the way (`Calculus/Problem.lean`, a `Reachable` tuple
that lost its bridge field).  No new `sorry`, `axiom` or `maxHeartbeats`;
`dups.py` (but the known `as` false positive), `check-orphans` (but the
git-excluded `Scratch/`), `check-doc-paths` and `check-rule-text` clean.
No pin moved but the new `BadDup` one; no rule name, branch label or fresh
name changed.

**15, a push at the bound is exhausted.**  `THalt.exhausted`
(`Semantics/Core/TypedRun.lean`): `TRun.push` and `ARhs.evalT`'s push halt
with it at `Storage.full`, not with `diverge`.  Both modalities accept it:
`Modality.onTHalt` (`Semantics/Core/TypedRunFrame.lean`: the box any halt,
the diamond only `exhausted`) is the halt clause of `Modality.afterRunTR`
(`tholds`), of `COut.after` (`Semantics/Core/Callback.lean`) and of
`CallbackHolds`' `thenF`; the panic stays excluded apart.  The untyped
readings (`holds`, `Modality.after`, `afterC`) are unchanged: an untyped run
has no bound and never sees it (`THalt.erase` maps it to `diverge`, and
`TRes.Agrees` matches it with anything).  Consequences:
- the push arms lose their `NoDiv` hypotheses: `TRun.push_nd` and
  `ARhs.evalT_nd` (`TSoundKit.lean`) prove a push never diverges;
- `TRes.Sim` also asks that the second halt is exhausted where the first
  is, so an evaluator's halt is a revert (`Val.evalT_revert`,
  `SPath.resolveT_revert`, `MPath.mvalT_revert`, from `TRes.Ends`: the
  evaluators neither diverge nor are exhausted, `Val.evalT_ends` and kin,
  moved to `Typing/StraightRun.lean`, replacing its straight-only copies);
  the capture shapes hand their `herr` a revert;
- `Premise.tsound_update`'s halt clause skips an exhausted run under the
  diamond; the diamond invariant loop runs by `TLoop.run_variant_or` (a body
  may end exhausted, `TSoundLoops.lean`);
- `Typing/StraightRun.lean`: `TRes.Ends` (no `diverge`, no `exhausted`)
  for straight programs, `Prog.trun_ends`; `Prog.run_halt_of_trun` asks
  both; `docs/solc-alignment.md`, "Array lengths", has the row (solc panics
  `0x41` past `2^64`; Lean's bound is `2^256`, and an exhausted run proves
  any modality).

**16, no struct repeats a member name.**  `BadDup` left `structDef` (and
`structRank`, `mapFreeStructs`) for `refusedStructs` (`AST.lean`): the
elaborator refuses a type that names one with solc's message
(`unknownStructMsg`, both `ty!` and `elabTy`), pinned in
`Syntax/Splice.lean` (`struct BadDup: identifier already declared: member
a`).  `structDef_nodup` (every struct of the table, `split <;> rfl`,
`Semantics/Core/StorageErase.lean`) replaces `nodupStructs`, `Ty.nodupS`
and `TyNodup` with its lemmas: `SVal.overlay_erase`, `SFields.overlay_erase`
and `SVec.overlayOn_erase` take no hypothesis (the struct case reads
`structDef_nodup`), and `Storage.writeStorage_erase` lost its `TyNodup`
argument.  Deleted with them: `Src`/`NewLhs`/`Stmt`/`Prog.bridgeOk`,
`Src.nodup`, the bridge hypotheses of `Stmt.trun_erase`, `Prog.trun_erase`,
`Prog.run_of_trun`, `Prog.run_halt_of_trun`, `Prog.trun_init_erase` and
every `TRun.*_erase`, `Prog.bridgeOk_of_straight` and kin, `Reachable`'s
bridge conjunct, `corpus_decide`'s `bridgeOk` test, `Ty.nodupDeep` and the
`nodupDeep` hypotheses of `Typing/TypedWT.lean` (`TState.erase_wt` takes
only the layout's keys distinct), the EVM's `nodupS` check in `assignIn`
and `copy_sim`'s hypothesis, and the arms' `bridgeOk`/`nodupS` hypotheses
(`tsound_save`, `tsound_saveMem`, `assignStep_tsound`, `copyStep_tsound`,
`assignFromMemStep_tsound`, `Premise.tsound_{update,updateSim,cases}_run`).
`Ty.defaultOkS` is unchanged (`defaultOkStructs` is now every struct).

**17, the hidden binder at a memory type: neither the reading change nor
the fallback can be met; recorded, not implemented.**
- *The reading change.*  Under the box, `memoryLocalDeclInitDrop`'s premise
  `∀ mv. [mv = r; ω] φ` at an allocating `r` says what the conclusion needs
  at one instance only: `mv` naming the object `r` is about to allocate.
  The premise's run then allocates it at that very id and overwrites `mv`
  with it, ending in the conclusion's state.  That is how M3's untyped
  binder (any id) is sound.  A typed state cannot hold that instance: a
  memory local is an `HRef` into the heap typing, and the object does not
  exist yet.  Any typed binder value instead needs a heap that already has
  an object of the type ("the heap grown", "any heap extension"); from it
  the premise's run allocates *another* object, at the next id, so its end
  state differs from the conclusion's by one object and every later id.
  Relating the two needs `tholds` to be invariant under adding unreachable
  objects and renaming ids, which the terms do not give (`defined` and
  heap reads observe ids).  A compositional reading that looks at what
  follows the binder breaks `Hyps.twrap_mono`.
- *The fallback* (thread `Stmt.TArmOk` as an invariant of reachable
  states): the condition fails at the start of most obligations, whose heap
  is empty (`T memory m = new T(..)` as a first statement), so it is not an
  invariant of reachable states either.
- *What is proved instead* (`Calculus/Core/TSound.lean`, new):
  `Stmt.tstepSound`, every rule (arms and blocks) sound wherever its
  statement meets `Stmt.TArmOk`, which is now only that arm's condition;
  `Stmt.tsound_diamond`, every rule sound under the diamond in every state;
  `Stmt.tsound_iff_residual`, `Stmt.TSound C` is exactly the arm in the
  states failing the condition (`Stmt.TResidual`).  And the residual is
  false at every contract: `Stmt.not_tresidual C`
  (`[uint[] memory m = new uint[](1);] false` from `TState.init C`, whose
  heap is empty: the premise holds, its binder having no value; the
  conclusion fails; the run's halt reduces by `rfl` at any `C`), hence
  `Stmt.not_tsound C`.  (`Proves.tvalid_of_residual`, `Proves.tvalid` from
  the residual, was deleted in review: its hypothesis is false, so it said
  nothing.)  So **`Proves.tvalid` with no
  hypothesis is not proved**: the per-rule route cannot give it while a
  memory local must name an existing object.
- *Options for the lead*: (a) a typed state whose locals may name objects
  not yet allocated (an env over a heap typing that extends the heap's,
  allocation checked against it), the binder ranging over that extension;
  (b) memory locals with an unset value, as storage aliases have (`.mem R`
  as `Option (HRef H R)`, a read of unset reverting), reversing decision
  12's "memory locals stay non-dangling"; (c) a garbage-and-renaming
  invariance of `tholds` (ids made unobservable to terms); (d) a typed
  soundness through M3's (`Proves.valid`, unconditional) and a bridge
  `holds σ.erase φ → tholds σ φ` on the formulas the strategy reaches.
  Each is a low change (the typed state or the terms), for W4 or before.
- *A partial result, not yet done*: `Proves.tvalid` for derivations that
  fire rules under the diamond only, from `Stmt.tsound_diamond` (no
  `TArmOk`).  `Proves` is a `Prop`, so "fires only diamond rules" cannot be
  a function of the derivation: it needs a second inductive (or `Proves`
  indexed by the modalities it may fire), or a formula predicate that every
  premise keeps, which a loop's invariant and postcondition (any formula,
  boxes included) do not give for free.

### CORE 2, the typed reading as the reading: blocked on decision 17 (2026-10-08)

CORE 2 was meant to fold the `T*` modules into their original names, so
that `tholds` becomes `holds`, `Proves.tvalid` becomes `Proves.valid`, and
M3's reading is deleted with its arm proofs, `RunWk.lean` and
`RunFrame.lean`.  `Proves.close` would then ask `Fml.tclosableB`, so that a
leaf behind a diamond update can close.  **It has not landed.**  The
reason is CORE 1's open decision 17, not missing work.  Nothing was
changed in Lean.  This section records why and what the lead has to
decide.

- *The fold makes soundness vacuous.*  `Proves.tsound` and
  `Proves.tvalid` (`Calculus/Core/TProvesSound.lean`) take `Stmt.TSound C`
  as a hypothesis, and `Stmt.not_tsound C` (`Calculus/Core/TSound.lean`)
  proves that hypothesis false at every contract.  Once the fold makes
  them `Proves.sound`/`Proves.valid`, no derivation proves a `Valid` goal.
  That breaks everything that uses M3's unconditional `Proves.valid` today:
  - `Solidity/Theorems.lean`'s `soundness'`
  - the `refine Core.Proves.valid` walks in `Examples/ProofTree.lean` and
    `Examples/Tactics/TryCatch.lean`
  - `Examples/ChainNotation.lean`
  - every `proved_core` in `TestSuite/CoreDerived9–11`
  - the replays of `sol_prove` and `sol_derive`
  - the pinned `#print axioms Proves.valid` in
    `Calculus/Core/ProvesSound.lean`

  Deleting M3's reading would remove the only soundness theorem that has no
  hypothesis.
- *The close switch has no sound justification without the fold.*
  - The Bool twin exists already: `Fml.tclosableB` and
    `Fml.tclosableB_sound` (`Calculus/Core/Closable.lean`, from `tsoundB`).
    Only the switch is missing.
  - The switch cannot be justified over M3's states.  There a diamond
    update asks `State.BoolOK` of the state it ends in, and an erasure's
    validity does not give it: an untyped storage read at a `bool` type may
    hold a non-`bool`.
  - Over the typed state, the switch is justified by
    `tholds_of_erase_valid` under `Fml.TClosable`
    (`Calculus/Core/TCloseErase.lean`).  But the typed `Proves.tsound` it
    would feed is the conditional one above.
  - So `Proves.close` keeps `closableB`.  No diamond leaf of
    `TestSuite/Problems` closes by `Proves.close` yet, and no Core example
    shows one.
- *`RunWk.lean`/`RunFrame.lean` stay.*  M3's `Sound*` arms import them.
  `Calculus/Core/WkOver.lean` already holds the syntax, so they can be
  deleted together with M3's reading.
- *The residual cannot be proved away inside the calculus.*  The only false
  arm is the box `memoryLocalDeclInitDrop` at an allocating initializer,
  over a heap with no object of the local's type.  The premise's run from
  any existing reference `v` allocates a second object.  Its end state
  then differs from the conclusion's by one unreachable object, and every
  later id shifts.  This holds for any reading that keeps `v` an existing
  reference: the grown heap, any heap extension, or a Kripke reading over
  extensions.  The two states can be related only by a
  garbage-and-renaming invariance of `tholds` (decision 17's option (c)).
  That invariance does not hold while a term can observe ids or a whole
  memory.  A derivation-level route through M3 (option (d)) keeps M3's
  reading as the proof vehicle, which CORE 2 deletes.  It also still
  cannot close a diamond leaf, for the `State.BoolOK` reason above.
- *The smallest typed change found*, offered to the lead and not
  implemented: option (b), with `LTy.TDenote (.mem R) := Option (HRef H R)`.
  - The binder then ranges over `none` too.  The premise's instance at
    `none` runs `mv = r` to exactly the conclusion's state, because nothing
    reads `mv` before that assignment.
  - Every diamond binder becomes inhabited, so the `LTy.inhabited` side
    conditions go away.
  - `none` must erase to something stable under heap growth
    (`TDenote.erase_wk`).  A read of `none` needs a halt that `TRes.Agrees`
    accepts against the untyped run.
  - It reverses decision 12's "memory locals stay non-dangling".  It is a
    low change (`Semantics/Core/{TypedState,TypedRun,TypedRunErase,TypedRunWk,HeapErase}.lean`,
    the memory arms in `TSound{Mem,Local}`, the `Evm/Core*` simulation,
    `Typing/` reachability) that runs before CORE 2.
- **Left, all of CORE 2**, in this order once decision 17 is settled:
  1. the change to the typed reading;
  2. `Stmt.TSound C` unconditional, and `Stmt.not_tsound` deleted;
  3. the fold and the renames;
  4. deleting M3's `holds`, `State.BoolOK`, `Modality.afterT`, its
     `Sound*` arms, `RunWk.lean` and `RunFrame.lean`;
  5. the `Proves.close` switch to `Fml.tclosableB`, and a Core example
     that closes a diamond obligation of `TestSuite/Problems`;
  6. the build with `SolidityCorpus` and `SolkeyTestSuite`, and the
     scripts.

### W3b lane `tactics` (`w3b-tactics`, 2026-10-08)

The W3 flip of `Examples/Tactics/**`, finished where the core allows it.
CORE 2 did not land (decision 17), so the diamond is unblocked on M3's
reading instead, by two contained closer changes that CORE 2 subsumes.

**Low changes** (no rule, name, branch label or fresh name changed; no new
`sorry`, `axiom` or `maxHeartbeats`):
- *`Proves.close` behind a diamond update* (`Calculus/Core/{Closable,CloseErase,Proves}.lean`):
  `Fml.Closable`/`closableB` take a diamond update that keeps the `bool`
  locals `bool`s (`Upd.boolB`, moved with `Tm.boolB`, `Rhs.boolB` from
  `Close.lean` to `Closable.lean`); `holds_of_erase_valid` reads it by
  `Upd.apply_boolOK` (moved to `CloseErase.lean`), the erasure's diamond
  giving the update's success.  This is the `State.BoolOK` obstacle of
  CORE 2's "close switch" answered on the terms, over M3's states; a
  diamond update that sets a `bool` local from storage is still refused
  (the typed reading, CORE 2, takes it).  `Proves.valid` is unconditional
  as before.
- *`Fml.posB` under `{anon(…)}`* (`Calculus/Core/Close.lean`): hidden
  binders under an anonymising update are taken (`holds_of_erase_pos`, the
  `anon` case through `mergeOn`), so a loop's frame with the body's
  binders under it closes (`Loops.countToNDiamond`, `breakKeepsBound`, the
  `LoopsImport` invariants).

**Tools**: `sol_derive?` under the scope writes today's short walk
(`Walk.surfaceOn`, `shortTac`: `apply Proves.valid`, `apply impRight`,
`apply allRight`, `apply emptyModality`, `apply update .r`, `unfold`,
`splitBox`/`split`, `Proves.check`/`checkLean`, `done`/`doneLean`,
`cases`, `branches`, `invBox`/`invLean`, `refine close ?_` at a leaf, the
silent steps unwritten), the walk running those very lines; without the
scope, the explicit `Core.Proves` text as before.  New scoped readings:
`apply invLean r`, `apply updIntro` (`WalkSyntax.lean`), `sol_prove?` on a
scoped goal and `sol_upd` on a scoped leaf (`Closers.lean`), `sol_erase`
and `Valid.of_erase_plain` (`Calculus/Core/Contracts.lean`, a plain
formula proved on its erasure), `Core.Problem.text` and
`Core.Problem.deploy_of_valid_nil` (`Calculus/Core/Deploy.lean`).

**Flipped**: the diamond walks (`Payment.sendDiamond`,
`Branch/Revert.branchDiamond`, `Revert.requireDiamond`,
`ApplySteps.guardedCopy`, `Loops.countTo1Walk` and its tree,
`Dangling`'s diamond, `Calls`' `TestSuite` shapes, `TryCatch.getWalk`);
`Loops.countToNDiamond`, `breakKeepsBound`; and the files that were not:
`Constructors`, `Dangling`, `Contracts` (statements scoped, today's
`useContract` reached by `sol_erase`), `UpdateRules` (its `⊨` part),
`LoopsImport` (`solc_problems … legacy`, `solc_scoped_problems … main`,
each function's obligation `⊨ Solc.Loops.f.problem`).

**Refutations over an untyped storage, now theorems** (no docs row
retired): `Decide.deleteWithoutWrite`, `Decide.survivesMappingOnly`,
`StorageDelete.deleteRootUnknown` are `⊨ defined(wt(storage)) → …` by
`sol_prove`, the positive statement the typed state makes valid; `Branch`'s
stuck-condition refutation is `⊨ ⟨ if (a == b) … ⟩ x != 0` (its parameters
bound).  Their counter-states (`boolBalance`, `fixedBalances`, `boolTotal`)
are deleted.

**Pins changed** (W3 reasons 1–6 by number):
- `Tactics/Revert`, `Branch`, `ApplySteps`: `case cov` deleted (1); goal
  comments rewritten to the scoped sequents (parameters' `∀`, a branch's
  `}`: 2).
- `Tactics/Payment.sendDiamond`: the outcome lines end `⟹ true` for
  `⟹ ⟨ ⟩ true` (3).
- `Tactics/Loops`: the diamond `#proof_tree` has no `emptyModality` node, 5
  nodes for 6 (3); `countTo1Walk`'s text loses `emptyModality` (3) and
  `case cov` (1), and gains `apply unfold .blockEmpty` on the unwound
  branch (the scoped branch keeps its block: the reason the W3 lane put to
  the lead, 7b).
- `Tactics/TryCatch.getWalk`: the walk is the scoped one (`apply branches`
  with today's `<;> simp only … <;> and_intros`, `apply allRight` on the
  success clause's binder), statement unchanged.
- `Tactics/Constructors`: `#check` of a formula and of `problem!`/`spec!`
  print `Core.Fml C []` (the flip's type, W3 lane 7b), and the deployment
  formula gains `∀ uint a;` (parameters bound by `∀`, W2 `tree`).
- `Tactics/UpdateRules.copyLocal_merge`: the trace gains `∀ uint y; ∀ uint
  x;` (W2 `tree`).
- `Tactics/LoopsImport`: new pin `7 obligations declared scoped`; the
  theorems are solkey's obligations `⊨ Solc.Loops.f.problem`, now assuming
  `wt(storage)` and binding the parameters by `∀`, where today's stated
  `Valid (Fml.modal m Solc.Loops.f .tt)` with no premise.
- `Tactics/CoreDerive`: new pins of the short walk (three, with replays).
- `Tactics/CoreProofTree`: the diamond tree's three leaves close (new, the
  diamond close above).
- Unchanged: every `sol_prove?` pin (`Dangling`, `Calls`), `Problem.text`,
  the refusal errors, the fresh names.

**Left**:
1. *`Tactics/Callback`*: `ProvesC.sound` against `ValidC` needs the plain
   rules' typed soundness, `Stmt.TSound C`, which `Stmt.not_tsound`
   refutes: blocked on decision 17 (CORE 2).
2. *Today's sequent rules on updates* (`merge`, `mergeStorage`,
   `eqDSplit`, `definedWritten`, the Theory rewrites `sol_rw`): no
   `Core.Proves` twin, so `SelectOnSaveConsr` (its subject is today's
   `consr` path besides), `StorageDelete`'s `_theory` derivations and
   `UpdateRules.deepFieldWriteMerged` stay today's.  A twin is a
   `Proves.lean` change (rules with soundness over `Core.Upd`).
3. *`CallOperands`' memory call*: the lead's `CallRet.isRets` decision (W3
   lane 7a).
4. *`Decide`'s fragment pins* (`Fml.inL`, `sol_decide` on a modality): the
   closer's input, today's until M6c.
5. *`Examples/ProofTree.lean`'s diamond trees and walks* (tree lane) and
   the `TestSuite` `Derived` diamonds (testsuite lane) can now flip where
   their diamond updates keep `bool`s; not touched here.
6. *A diamond update writing a `bool` local from storage* is still not
   closed (`Upd.boolB`); the typed reading (CORE 2) takes it.
7. `Contracts`' rule is today's (`FunContract` over today's run), reached
   through the erasure; a scoped `FunContract` is not built.

**Checks**: `lean_build` of `Solidity`, `solkeycheck`, `SolidityCorpus`,
`SolkeyTestSuite` (the last two in `defaultTargets` for the run only):
green, 339 jobs, after one fix (`sol_derive?`'s goal names past macro
scopes, `Examples/ProofTree.lean`).  `check-orphans` (but the git-excluded
`Scratch/`), `check-doc-paths`, `check-rule-text`: clean.  No new `sorry`
(the one added match is `sol_prove?`'s suggestion string), `axiom` or
`maxHeartbeats`; `#print axioms` of `Proves.valid`, `holds_of_erase_valid`,
`holds_of_erase_pos`, `Core.Problem.deploy_of_valid_nil`: Lean's three.
The scoped `TestSuite` shapes of `Calls` check in about 1.3× today's kernel
time (four of them, 3.3 s against 2.6 s); the gate modules were not
re-timed.

### W3b lane `tree` (`w3b-tree`, 2026-10-08)

Merged `w3b-chains` at c214204 (its scoped error printer, `indentLine`,
under the change below) and `w3b-tactics` at 1fb3e60, which had made the
same change to `Proves.close` (d30bb95) and the same scoped `sol_prove?`
(ac8d23f): their versions of `Calculus/Core/{Closable,Close,CloseErase,Proves}.lean`
and `Closers.lean`'s `sol_prove?` are kept, this lane's copies dropped
(its module, `ProvesSearch`, deleted).  No new `sorry`, `axiom` or `maxHeartbeats`.
Before that merge (3859a2a): `lean_build` (default targets) green, 301
jobs; `TestSuite/CoreSeq`, `CoreDerived11`, `Examples/Chains/StorageCoverage`,
`Tactics/CoreChains` checked one by one.

Then merged `w3b-tactics` through 1e71cb1: `Tactics/Dangling`'s diamond walk
flipped (its docstrings fixed), `Tactics/Contracts` flipped through
`sol_erase` (`Calculus/Core/Contracts.lean`), the module-map rows of
`Close`/`Closable`/`CloseErase` corrected.  `Core.Walk.walk`'s tag rule
stays this lane's (below); 0209193's last component past macro scopes and
`h` is not taken (erasing the macro scopes before the prefix test turns
the invariant walk's `checkLean .loopExit` case `thn` into `h` in
`ProofTree`'s pin).
On top of it, from the review: `Decide.deleteWithoutWriteUntyped`, the
refutation over today's untyped storage (`¬ ⊨`, no `wt(storage)`), restored
in `Tactics/Decide`'s closing block, which `Calculus/Decide.lean` and
`Benchmark/Mapping` now cite; two regression pins in
`Tactics/CoreProofTree` for `operatorOf?` (`lessEqualAssignment` before an
`if` and in its branch).  `lean_build` of the merged tree (default targets):
green, 302 jobs, every `sol_derive?` pin (`ProofTree`, `CoreProofTree`,
`Loops`, `CoreDerive`) among them.

- **A diamond leaf closes where its updates keep the `bool` locals
  `bool`s** (done by both lanes, `w3b-tactics`' kept; for the lead to confirm: a change to `Proves.close`'s side
  condition, not a new rule).  `Fml.Closable`'s update arm is `(m = .box ∨
  U.boolB = true) ∧ …` and `Fml.closableB`'s `(decide (m = .box) ||
  U.boolB) && …`; `holds_of_erase_valid` (`Calculus/Core/CloseErase.lean`)
  proves the diamond arm by `Upd.apply_boolOK`, exactly as the `Core.Valid`
  route's `Fml.posB` already did (`holds_of_erase_pos`); this lane's
  copy checked the same way.  So it is sound
  over M3's states with no hypothesis: `Proves.valid` and
  `#print axioms` are unchanged, and CORE 2's switch to `Fml.tclosableB`
  subsumes it (`Closable.tclosable` needed no change).  What it does not
  take: a diamond update that sets a `bool` local from a storage or memory
  read (`Tm.boolB` is false there), the case CORE 2 is about.
- **Scoped `sol_prove?`**: `w3b-tactics`' (`Calculus/Core/Closers.lean`),
  which `Examples/ProofTree.lean` now imports; with it come the walk
  macros (`WalkSyntax.lean`), so the scoped `sol_derive?` writes today's
  short walk there (`Walk.surfaceOn`).
- **Tool fixes.**  `Core.ProofTree.operatorOf?` takes a constructor of
  `BinOp`/`UnOp`/`IncDec`, not a function of the namespace: an `if`
  branch's statement carries `BinOp.ret` in a value's type, and its node
  printed `binopAssignment` for `lessEqualAssignment` (pinned since, in
  `Tactics/CoreProofTree`).
  `Core.Walk.walk` cites a step's goals by name only when every goal has
  one, else bullets in order, as today's walk takes `cases` apart (the
  diamond send's first goal is tagged `fml`, the others not); the name is
  the first component of the tag past the stepped goal's (`w3b-tactics`
  cc371e9 took the first component of the whole tag, right past a silent
  step's `thn.h` but `thn` for an invariant's `thn.els` inside a branch).  The scoped chain error
  (`Calculus/Core/Chains.lean`) is today's: the line not reached, printed
  as a line where it elaborates alone (lazily, `MessageData.ofLazyM`: done
  eagerly, a search that catches the error re-elaborated it at every try
  and `Chains/StorageCoverage` crashed), and its lines in today's layout
  (`showLinesErr`; `#derivation`'s `showLines` unchanged).
- **Flipped**: `Examples/ProofTree.lean`'s diamond trees and walks (the
  first tree, `sendNoCallbackDiamond`'s tree and walk, `guardedCopy`, the
  two call trees, the unwound loop), its `sol_prove?` section (box and
  diamond, `wtStd` now `Core.Fml.wt`), the `assert` `sol_prove?`;
  `Examples/ExampleNames.lean`'s chain error.
  `Examples/Tactics/CoreCallback.lean` pins the typed reading with
  callbacks (`ValidC ↔ TValid` with no payment, `validT_*`,
  `valid_of_validC`); `ProvesC`'s derivation stays pinned, not read as
  `ValidC` (decision 17).
- **Pins changed, with reasons** (W3's numbers; "W2 `tree`" is the
  parameters' `∀`):
  - `ProofTree`, the first tree: `allRight` first (W2 `tree`), no `cov`
    (1), no `emptyModality` after the last statement and serials shifted
    (3): 11 nodes, 2 branches for 12 and 3.
  - `ProofTree`, `sendNoCallbackDiamond`'s tree: no `emptyModality` (3), 6
    nodes for 8.
  - `ProofTree`, the two diamond call trees: the callee's body ends by
    `blockEmpty` (the reason the tactics lane left for the lead, W3
    `tactics` Left 7(b): the scoped inlining keeps the body a block), no
    `emptyModality` (3).
  - `ProofTree`, every `sol_derive?` suggestion: today's walk text again
    (`w3b-tactics`' short walk, which `Closers.lean` brings in), in place
    of the W3 tree lane's `Core.Proves` constructors: the diamond send's
    and `guardedCopy`'s are today's but for `cov` (1) and `emptyModality`
    (3); the unwound loop's also takes `blockEmpty` on the body (7(b));
    the box walks (the send, `ifElseSplit`, `transferFrameStorage`, the
    `assert`, the invariant) have no `allRight` line (the parameters' `∀`
    is not written), `splitBox`/`Proves.check`/`invBox` as today's, and a
    `true` leaf closed by `refine close ?_; sol_symex; sol_close` (today's,
    where the W3 tree lane's had `exact Core.Proves.closeTrue rfl`).
  - `Tactics/CoreProofTree`, the diamond send's tree: its three leaves
    close (they were `OPEN GOAL`): the change to `Proves.close` above
    (`w3b-tactics`' version of the pin).
  - Unchanged: every `sol_prove?` suggestion (the scoped one suggests
    today's replay), `ExampleNames`' error text, `#proof_node`,
    `#proof_tree_json`, the fresh names.
- **Gate** (`Examples/ProofTree`, 12.1 s): from its first command to its
  last (timestamps in a scratch copy, imports cached; not the M0 method,
  other agents running), 11.4 s before the `w3b-tactics` merge and 12.0 s
  after it (the short walks re-run each line through the scope's macros):
  at the limit.
- **Left.**
  1. `Examples/Verify.lean` whole.  `#verify` would elaborate `⊨
     spec[C]{f}` in the caller's scope (a one-line change), but its
     refutation certifies today's `¬ ⊨ spec[C]{f}`, not the scoped
     statement, and a typed-run `#counterexample` would refute `TValid`,
     while the scoped `⊨` is M3's `Core.Valid` until CORE 2.  Both wait on
     decision 17; the certificate over the scoped formula would then be a
     typed `eval3` (`Fml.eval3` over `TState` and `Prog.trun`).
  2. `ProofTree`'s `sol_chain?`, `#chain` and `sol_rws?` sections: no
     scoped twin on `w3b-chains` yet.
  3. `ProofTree`'s two interval examples (`∀ uint x; x <= 100 → …`): the
     scoped leaf's erasure has its leading `∀`s stripped
     (`Fml.stripAlls`, `Seq.leafRes`), the explicit one with the
     parameters', so today's closer loses `x`'s `uint` range: the diamond
     one leaves its leaf, the box one needs `sol_decide_cons`.  Keeping an
     explicit `∀` needs telling it from a parameter's, which `cdl!`'s
     output does not.
  4. The testsuite's diamond obligations where every diamond update keeps
     the `bool` locals `bool`s.  The tactics lane's diamond walks
     (`Payment`, `Branch`, `Revert`, `ApplySteps.guardedCopy`, `Loops`,
     `Calls`, `Dangling`) are flipped on this branch, through the two
     `w3b-tactics` merges; no `Examples/Tactics` closing block holds a
     diamond walk any more.
  5. The read-only review pass was not run.

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

### M4 lane (`intrinsic-values`)

**What exists** (2026-10-07), standalone: nothing on the interpreter's path
uses it yet.  Each typed operation returns an `Option`, `none` a revert, and
its agreement lemma reads `untyped (erase x) = toRes erase (typed x)`: the
untyped operation is never stuck on an erased input.

- **Values (M4a).** `Semantics/Core/Value.lean` (`PrimTy.Denote`,
  `PrimTy.erase`, `ofValue?`, `Core.toRes`), `Semantics/Core/Ops.lean`
  (`BinOp.evalT`, `UnOp.evalT`).  `UnOp.accepts .neg` is `int` only, as
  solc's (since 2026-10-07; it accepted `uint`, where the untyped
  `unopCheck` does not range-check, so `-x` left the type), and the
  elaborator and `Calculus/Spec.lean` reject `-x` at `uint`;
  `UnOp.evalT_erase` holds at every accepted type, and the closer's
  `Facts.unRets` lost its `-a` at non-`int` arm.
- **Storage (M4b).** `Semantics/Core/Storage.lean`,
  `Semantics/Core/StorageErase.lean`.  `SVal T` is mutual with `SFields`
  (over `structDef s`, exact members), `SList`, `SVec E n` and `SMap V`; a
  dynamic array keeps its slots past the end, a mapping its default, as the
  untyped ones; keys stay `Int`; `Storage C := SFields C.vars`.  `SVal.dflt`
  is structural (fuel `rankBound`, which reads no struct name, inside it
  structural on the type), so the kernel reduces it where it cannot reduce
  `defaultForTy`.  A struct copy (`SVal.overlay`) is positional, as solc
  copies; `SVal.overlay_erase` needs `TyNodup T`, which `Ty.nodupS` decides
  by `rfl` (all structs but `BadDup`).  `find`, `findLive` and `save` are
  `Path.rec` over `SVal.view` (its type `Shape T` computed from `T`), each
  with a `match` twin (`findM`, …) as `implemented_by` and an equality
  theorem (`SVal.find_eq_findM`); `SFields.get`/`set` likewise (`getM`,
  `setM`, `SFields.get_eq_getM`).  The eight stores of `Semantics.lean` are
  named constants (`Storage.testSuite`, …) with `_erase` lemmas.
- **Heap (M4c).** `Semantics/Core/Heap.lean`, `Semantics/Core/HeapErase.lean`.
  A heap typing `HTy := List RefTy` (identity = position, oldest first);
  `HRef H R` an identity typed at `R`; `MVal H T`, `MFields`, `MObj H R` (a
  mapping has none: `Empty`) and `Heap H` are computed from the typing, as
  `Env` is from Γ.  `Heap.alloc` returns a heap over `H ++ [R]`, weakening
  the old objects along `H <+: H'` (identities kept, so the erasure is the
  same); `SVal.copyStToM` returns a `Grown` heap (the extension, the heap,
  the value) and allocates members first, as the untyped copy;
  `MVal.copyMToSt` recurses on the type (rank fuel, then structural), with no
  cycle arm.  The agreement lemmas hold on `σ.heap = hp.erase` (and
  `σ.nextId = H.length` where they allocate): `getObj_erase`,
  `setObj_erase`, `alloc_erase`, `SVal.copyStToM_erase`, `allocDefault_erase`,
  `MVal.copyMem_erase` (the untyped cycle guard never fires: a reference's
  target has a smaller type by `(tyRank, sizeOf)`, `RemOk`),
  `memWriteField_erase`, `memWriteIndex_erase`, `memArrayLen_erase`,
  `readField_erase`, `readIndex_erase`.  The round-1 bridge copies through the
  untyped heap (`SVal.copyToMem`, `SVal.copyFromMem`) are deleted.

**Wiring, once M3's `Env`/`State`/typed run land.**

1. `Core.State C Γ` holds `storage : Storage C`, a heap typing `H` as a
   field and `heap : Heap H`; `LTy.Denote` takes `C` and `H`:
   `.val p ↦ p.Denote`, `.alias R ↦ Option (SRef C (.ref R))`,
   `.mem R ↦ HRef H R`.  `Env` stays computed from Γ (condition 4).  `H` is
   a field, not an index, so `Stmt.run`'s type does not change.
2. An allocating step (`declMem`, a memory copy, `new`, `delete` of a memory
   reference) gets a `Grown` heap and weakens the env along its extension
   (`Env.wk e`, which only rewrites `.mem` slots' proofs).
3. Locations: `Loc`/`SPath` resolve to an `SRef` (`SRef.field`,
   `SRef.index`), `MLoc`/`MPath` to an `HRef` read through `Heap.field`/
   `Heap.index`; `Val.eval` uses `BinOp.evalT`/`UnOp.evalT`.
4. `run_erase` erases the state to `{ storage := st.erase, heap := hp.erase,
   nextId := H.length, env := … }`; the lemmas above are its per-operation
   steps, so `Halt.stuck` leaves `Core`.
5. Done (2026-10-07, G0 condition 1 paid): every function the kernel
   evaluates on storage values is a fold (`Fold`, the recursor of the five
   families: `SVal.fold`, `match` twin `SVal.foldM` as `implemented_by`,
   `SVal.fold_eq_foldM`) or reads through a view whose type the index
   computes (`SVal.view`, `SFields.view`, `SVec.view`, `SList.uncons`,
   `SMap.uncons`): `erase`, the `toList`s (their own `match` twins, so
   compiled code does not walk the elements), `SVec.set`, `defaultOf`,
   `strip`, `overlay`/`overlayOn`, `SVal.copyStToM`, `beq`; `checkIndex`
   (`inBounds`, by `IndexTy.casesOn`/`ArrTy.casesOn`), `len`, `push`,
   `pushPlace`, `pop` read the array by `SVal.view`; `isPrim` reads the type.
   `Path.append` is `Path.rec`, `Path.index` and the heap's `MObj.elems`/
   `MObj.setElem` are `IndexTy.casesOn`/`ArrTy.casesOn`.  Every recursor
   form has its `match` twin as `implemented_by` and a theorem equating them
   (G0 condition 2: `SVal.fold_eq_foldM`, `SList.toList_eq_toListM`,
   `SVec.set_eq_setM`, `Path.append_eq_appendM`, …); `defaultOf`, `strip`
   and `overlay` have twins of their own (`SVal.defaultOfM`, …), since
   `SVal.foldM` is strict and would rebuild every mapping entry it discards.
   Each fold states its equations by `rfl`, is `@[irreducible]` and names
   them its equation lemmas (`attribute [eqns …]`, `Solidity/Eqns.lean`), so
   `simp only [SVal.erase]` rewrites a constructor application and nothing
   else, as it did by `match`; a proof that needs the definitional unfolding
   says `with_unfolding_all rfl` (and the elaborator's `decide`/`rfl` do not
   see through them: use `decide +kernel`).  `DecidableEq (SVal T)` and
   `(SFields fs)` are `SVal.beq`/`SFields.beq` with `beq_iff`; the kernel
   reduces them (`decide +kernel` of `Storage.testSuite = Storage.testSuite`
   in 16 ms), where the untyped `svalDecEq` does not reduce at all.  A `bool`
   key: decision 10; the untyped side stays stuck on one, so its agreement
   holds at numeric keys (`PrimTy.asInt_erase_key`).
   Wiring, after M3.1 (`Semantics/Core.lean`, untyped values) landed:
   `Semantics/Core/TypedState.lean` holds items 1 and 2 beside `Core.State`,
   which they replace at M4: `LTy.TDenote C H`, `TEnv C H Γ` (with `wk`
   along a heap extension and `erase` to `Env`), `TState C Γ` (heap typing
   `H` a field), `TState.erase : TState C Γ → State C Γ`, and the
   allocating steps over a `Grown` heap (`adopt`, `alloc`, `copyStToM`,
   `allocDefault`, `copyMToSt`), each with the lemma `run_erase` will use
   (`alloc_erase`, `copyStToM_erase`, …; `push_erase`, `setLocal_erase`,
   `drop_erase` for the locals).
6. Done (2026-10-07), items 3 and 4 beside `Semantics/Core.lean` (which
   the lead's M3 owns): the typed run `Semantics/Core/TypedRun.lean`
   (`SPath`/`Loc` to `SRef`, `SRef.atKey` at an index, `MLoc` to a heap
   address (`MAddr`: a struct member or an element of an `HRef`), `MPath`
   to the slot it holds (an `HRef` at a reference type), `Val.evalT` by `BinOp.evalT`/`UnOp.evalT`,
   `Stmt.trun`/`Prog.trun` on `TState`, halting only by `THalt`: `revert`,
   `panic`, `diverge`), with `TState.tx` typed (`TTx`: the environment's
   words are `uint`s, so `Simple.env` needs no range premise).  A length is
   compared as a `Nat` (`lenT`, `n < 2 ^ 256`): `PrimTy.uint.ofInt?` of a
   length the kernel does not know unfolds `Int`'s order against `2^256`
   (`Nat.sub` recursing `2^256` times) in any proof that whnf's it.
   The agreement is `Semantics/Core/TypedRunErase.lean`'s
   `Prog.trun_erase`: `TRes.Agrees (·.st.erase) (P.trun σ) (P.run σ.erase)`,
   the erased state, the same `revert` or `panic`, and a typed `diverge`
   against any untyped outcome (a length past `uint`, which the untyped run
   reads as an integer, diverges only in the typed run).  It holds on
   `Prog.bridgeOk` programs (decided by `decide +kernel`): no `bool` mapping
   key (decision 10; the untyped `asInt` is stuck on one) and no storage copy
   at a type with a repeated member name (`BadDup`: the typed copy overlays
   by position, the untyped by name).  Corollaries `Prog.run_of_trun`,
   `Prog.run_halt_of_trun` (the scoped run is never stuck where the typed
   one ends) and `Prog.trun_init_erase`.  One lemma per `TRun.*` step
   against its `Run.*` (`StepAgrees`); the loop by its unwinding
   (`SumAgrees`, `loop_run_erase`).  Left for M4: the typed run replaces
   `Core.State`/`Stmt.run` (and with it `Halt.stuck`), and the Typing and
   calculus layers move onto it.

**Timings** (2026-10-07, scratch modules `HeapBench`/`HeapBench3` under
`Solidity/Scratch/`, which are not committed: each row is one `decide
+kernel` of the statement it names).
Kernel time (`type checking` under `profiler`) of `decide +kernel`, with
`Elab.async false`; each run is a distinct statement, since `decide` shares
one auxiliary lemma per statement.  Repeats agree within 5%.  Untyped is
today's form: `unfoldStore` (`Corpus/Basic.lean`), `findStorage`/
`saveStorage`.

| What | untyped | typed | ratio |
|---|---|---|---|
| store `standardExample`, every value walked | 11.2 ms | 11.6 ms | 1.04 |
| store `testSuite` | 29.7 ms | 32.3 ms | 1.09 |
| store `solcStructs` | 21.9 ms | 22.4 ms | 1.02 |
| store `solcMemory` | 10.6 ms | 11.0 ms | 1.04 |
| store `solcMappings` | 16.4 ms | 17.2 ms | 1.05 |
| store `solcControlFlow` | 5.0 ms | 4.9 ms | 0.99 |
| stores `solcExpressions`, `solcArrays` | < 1 ms | < 1.3 ms | — |
| read `alice.account.balance` | 11.7 ms | 11.7 ms | 1.00 |
| save it, read it back | 14.2 ms | 13.2 ms | 0.93 |
| save a 3-element `persons`, read `persons[1].age` | 9.8 ms | 9.9 ms | 1.01 |
| read `folks[3].age` (a mapping's default) | 7.4 ms | 7.5 ms | 1.01 |
| save `folks[3].age`, read `folks[5].age`, `folks[3].age` | 9.5 ms | 9.4 ms | 0.99 |
| fresh `Person memory m; m.age = 3;` read back | does not reduce | 10.3 ms | — |
| `alice` storage → memory → storage | does not reduce | 15.4–15.6 ms (17–18 ms with `tyRank` fuel) | — |
| the corpus example (a whole untyped run) | 19 ms | needs the typed run | — |

- The store rows walk the value with `SFields.rec`; walked by `match`, the
  typed stores cost 1.15–1.55× the untyped ones (1.75–1.95× before
  `rankBound`, whose `tyRank` fuel matched a struct's name per default).
- `Path.rec` is lazy where `match` is not: a walk whose value nobody reads
  (`(st.find r).isSome`) costs 0.3 ms against 13.7 ms by `match` and
  10.3 ms untyped.  Rows that read the value are the fair ones.
- Untyped memory does not reduce in the kernel: `allocDefault` stops at the
  well-founded `defaultForTy`, `copyMem` at the well-founded `copyMToSt`
  (the corpus pins memory programs by `#eval` for this reason).
- The read rows compare the value read (three runs each).  With `find`,
  `save` and `SFields.get`/`set` by `match`, a read cost 1.37× and a save
  then read 1.48×; `find`/`save` by the recursor alone, 1.20× and 1.33×.
- The array and mapping rows run `find`/`save` by the recursor over the
  `match`-walked `SList.toList`/`SMap.toList` (median of three; the typed
  array row also checks its statement's `SRef.ofRoot "persons" rfl`
  once, 4.5 ms, outside the run).  The round trip is the typed copy back
  with `rankBound` fuel, as `SVal.dflt`.
- **Gate (within 20%)**: passes for store construction walked by the
  recursor (≤ 1.09×) and for reads and saves along struct, array and
  mapping paths (0.93–1.01×).  Open: the corpus examples (they need the
  typed run, M3 + wiring), and the operations still walked by `match`
  (`erase`, `overlay`, `defaultOf`, the heap copies: stores walked by
  `match` cost up to 1.55×; since paid, below).  The gate stays open until
  the corpus example runs through the typed forms.

**Timings after the folds** (2026-10-07, scratch `FoldBench`, same method:
`type checking` of each `decide +kernel` statement, `Elab.async false`;
two runs agree within 8%).

| What | typed | untyped | ratio |
|---|---|---|---|
| store `testSuite` built and walked (`Fold` size; bare recursor; `match`) | 33.5–36.7 ms; 34.8–37.5 ms; 50.8–54.4 ms | 33.8–34.8 ms | 0.99–1.05 (fold), 1.46–1.56 (`match`) |
| store `standardExample`, same | 12.6; 12.8; 18.4 ms | 12.7–13.1 ms | 0.99 |
| store `solcStructs`, same | 24.7; 25.0; 29.0 ms | 25.1 ms | 0.98 |
| `testSuite` erased by the fold, by `match` (`foldM`), then walked untyped | 42.9 / 59 ms | 33.8 ms | 0.73 fold/`match` |
| `standardExample`, same | 15.8 / 21.4 ms | 12.7 ms | 0.74 |
| `solcMappings`, same | 21.5 / 26.3 ms | 18.8 ms | 0.82 |
| the eight stores erased by the fold and walked untyped | | | 1.07–1.33 (by `match` before: 1.15–1.55) |
| save `alice.account.balance`, read it back | 13.1 ms | 14.3 ms | 0.92 |
| save a 3-element `persons`, read `persons[1].age` | 11.2 ms | 11.7 ms | 0.96 |
| read `folks[3].age` (a mapping's default) | 8.4 ms | 8.5 ms | 0.99 |
| save `folks[3].age`, read `folks[5].age`, `folks[3].age` | 10.3 ms | 11.1 ms | 0.93 |
| `persons.push()`, then the length | 7.2 ms | 8.2 ms | 0.87 |
| `alice = bob` (a struct copied over, `overlay`), read back | 12.9 ms | 15.6 ms | 0.83 |
| `delete alice`, read back | 13.3 ms | — | |
| fresh `Person memory m; m.age = 3;` read back | 10.8 ms | does not reduce | (10.3 ms before) |
| `alice` storage → memory → storage | 6.1 ms | does not reduce | (15.4 ms before) |
| `Storage.testSuite = Storage.testSuite` (`DecidableEq`) | 16.3 ms | does not reduce | |

- A fold costs what the bare recursor does (0.96–0.98×): the `Fold`
  structure's projections are free.  `match` costs 1.2–1.5× it.
- Every operation row is now at most the untyped one (0.83–0.99×), and the
  store rows within 5%.  The gate's open item is the corpus example through
  the typed run (M3 + wiring).

**Timings through the typed run** (2026-10-07, scratch `RunBench`, same
method: `type checking` of `decide +kernel` of `(run).isOk = true`, two
distinct statements per row, which agree within 5%).  Each block is a
corpus theorem's body (`Corpus/*.lean`), resolved and declared by
`Prog.defineCore`; "old" is today's `Solidity.Prog.run` on `unfoldStore`
(what `corpus_decide` checks), "scoped" `Core.Prog.run` on the same store,
"typed" `Core.Prog.trun` (`Semantics/Core/TypedRun.lean`) on `Storage.*`,
built in the kernel by the fold.  A ratio is of the ranges' midpoints, or
the whole range where that matters to the gate.

| Block (store) | typed | scoped | old | typed/scoped | typed/old |
|---|---|---|---|---|---|
| the corpus example, `p.account.balance = 100` through an alias (`testSuite`) | 14.5 ms | 16.0–16.3 ms | 16.5–16.9 ms | 0.90 | 0.87 |
| `sMap[1] = sBox` (`solcMappings`) | 12.7–13.0 ms | 14.2 ms | 14.4–14.5 ms | 0.90 | 0.89 |
| `withSubMap[5] = withSub`, three asserts (`solcMappings`) | 29.4–29.5 ms | 30.9–31.0 ms | 31.2–31.8 ms | 0.95 | 0.93 |
| `delete triple` and its neighbours (`solcStructs`) | 29.8 ms | 31.8 ms | 33.2–33.3 ms | 0.94 | 0.90 |
| `p = a++` (`solcExpressions`) | 4.3–4.6 ms | 4.1 ms | 6.4 ms | 1.05–1.12 | 0.70 |
| three pushes, an unrolled loop over them (`solcControlFlow`) | 33.6–34.1 ms | 32.7–33.0 ms | 34.4–34.9 ms | 1.03 | 0.97 |
| three pushes, writes, reads (`solcArrays`) | 23.6–23.7 ms | 23.8–24.0 ms | 24.3–24.6 ms | 0.99 | 0.97 |
| `require(age > 3)` (`standardExample`) | 3.0 ms | 3.0–3.2 ms | | 0.97 | |
| `Outer memory m = outerX;` and four reads (`solcMemory`) | 31.0–31.2 ms | does not reduce | does not reduce | | |

No block reads a `.length`, so the change of `lenT` to a `Nat` comparison
(after these timings) does not move them.

- **Gate (within 20%): passes.**  The typed run costs 0.89–1.12× the scoped
  untyped run and 0.70–0.97× today's interpreter on every corpus block the
  untyped runs decide; the 1.12× is the 4 ms `p = a++`, a few tenths of a
  millisecond.  Memory blocks reduce only through the typed run (the copy is
  a fold, no well-founded `copyMToSt`).

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

### M6a lane: soundness, part A (`intrinsic-calculus`, 2026-10-07)

- The statement (`Calculus/Core/SoundKit.lean`): `Premise.Sound m s p σ` (the
  premise in front of any rest, frames and postcondition gives
  `⟨ s; ω κ ⟩ φ`), `Stmt.StepSound k m s` (in every `State.Typed` state, the
  premise `s.step k m` gives is sound).  `State.Typed`: a `bool` local holds a
  `bool`, the one typing fact a split needs until M4a.
- Every arm of `Stmt.step` but the blocks is sound: `Stmt.stepSound`
  (`Calculus/Core/SoundStep.lean`), given the block arms (`Stmt.IsBlockArm`:
  calls, `try`, loops; lane `sound2`) and `WkRuns` (a block weakened under
  a captured `if` condition runs as before, the run of `Prog.wk up`, which
  lane `sound2` proves: `Prog.run_wk`).  `#print axioms`: `propext`,
  `Classical.choice`, `Quot.sound`.
  - Updates (`SoundArms.lean`, `SoundUpdates.lean`): the update ends as the
    statement does (`Premise.Sound.update`), or alike up to the halt
    (`updateSim`: `delete` of a memory reference reads the address and the
    fresh object in the other order); `send` by `Premise.Sound.cases`.
  - Captures (`SoundCapture.lean`): `captureSim`/`captureSPSim`/
    `captureMVSim`.  The statement read with the captured part on top runs
    as before (the push lemmas of `SoundArms.lean`); where the part halts
    the statement halts alike: with the same halt where it reads the part
    first, with another halt that is not a panic where it reads another part
    first (`Res.Sim.err_bind`, no expression panics).  Out of order are
    `sp[ie]`'s index with a simple receiver (read and `delete`), a storage
    write of a copy and a write from memory with the target captured first,
    a push's argument (read after the array), memory writes with the
    receiver or the index captured before a source.
  - The holes are read once: a statement with a hole filled is the read and
    then what the hole does (`SHole.cont`, `MHole.cont`, `VHole.cont`), so
    `readStep`, `VHole.step` and `ternaryStep` are sound for every hole.
  - Blocks of captures (`indexCaptureAll`, the memory `CaptureAll` rules)
    run one push at a time (`Prog.run_declLocal_cons` and kin,
    `pushed2_drop`, `pushed3_drop`).
- `holds_erase` (`Calculus/Core/HoldsErase.lean`): a scoped formula holds in
  `σ` iff its erasure holds, by `Update.lean`'s `holds`, in any untyped state
  agreeing with `σ` on the names `ns` (`Agree`), for `Fml.Plain` formulas:
  every binder fresh (an update's declarations, a `∀`, a modality's blocks:
  `Prog.Fresh [] ns` and `Frames.Fresh`), no hidden binder and no `anon`.
  A term reads as its erasure up to the locals a storage carries
  (`Tm.eval_erase`, `Srt.wl`: every symbol is natural in the locals, the
  `*_nat` lemmas of `RunErase.lean`), denotes the same (`Tm.denote_erase`);
  an update ends in agreeing states (`Upd.apply_erase`), a pop by
  `Agree.dropNames`, a frame dropped by `Agree.thin`; a modality is
  `run_erase`'s `Prog.erasesAt` and its frames (`Frames.run_erase`).
- `Prog.outNames` was defined twice (`Calculus/Core/Fml.lean`,
  `Semantics/RunErase.lean`), so the two could not be imported together: it
  is `Syntax/Core.lean`'s now, beside `Stmt.outNames` (as lane `sound2`
  moves it, the same hunk).
- Left:
  - `holds_erase` for a hidden binder and `anon`: their untyped readings
    range over more states (`anon` over any binding, the erased binder over
    whatever the name held), so only the direction from the erasure holds,
    and for a binder only where the block writes the local before reading
    it; not stated.
  - `Premise.sound` over all of `Stmt.step`: `Stmt.stepSound` with
    `sound2`'s block arms and `WkRuns` from its `Prog.run_wk`, once merged.
  - `Calculus/Core/Quote.lean` does not build on this branch (its `Premise`
    quoter misses `inline`, `inv`, `cases`, `branches`: the calctools
    lane's), so `Examples/Tactics/CoreStep.lean` and `CoreSymex.lean` were
    not re-checked here.

### M6a lane: the speed gate (kernel, `Eq.refl` of `symex n φ = ψ`)

Measured with a scratch module (`Solidity/Scratch/CoreBench`, not committed), median of 5
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
- Reducing it (round 3, the scratch `CoreBench`, median of 7;
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
**The prototype** (the module `Calculus/Core/Schema`, lane `intrinsic-calctools`; folded into `RuleSyntax.lean` in W1)
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
  covered at first: a call and a `try` (printed `‹…›`), and a sequent
  (`Core.Proves`); both landed in round 2 below.
- **`Hyps`/`Proves`** (`Calculus/Core/Proves.lean`): the telescope
  `Hyps C Γ₀ Γ` (`pre`, `upd`, `havoc`, `all`, `bind`, `anon`), `wrap`/
  `fresh`/`boxOnly` by `casesOn`, and `Proves` with `intro`, `allIntro`,
  `updIntro`, `bindIntro`, `update`, `unfold`, `bind`, `split` (two goals,
  and the cover under the diamond since the review),
  `check`, `done`, `empty`, `closeTrue`; a derivation of
  `[ if (b) { } else { } ] true` checks.  Soundness: round 2.
- **Round 2** (2026-10-07, after M3 and the calculus lane's `SoundKit`):
  - `Proves` gains `branches` (a goal per clause, at least one), `cases`
    (a goal per formula and per way the statement ends, at least one),
    `inv` (the invariant now, then the body and the rest under the
    frame's `{anon(…)}`) and `inline`.  No rule has zero goals: behind a
    diamond update that halts, a rule without goals would not be sound,
    and `closeTrue` asks the context to have no diamond update but scope
    ends (`Hyps.boxOnly`).
  - `Calculus/Core/ProvesSound.lean`: `Proves.sound` (`H.wrap φ` in every
    state) and `Proves.valid`, by induction on the derivation, given
    `Stmt.Sound C`: every premise `Stmt.step` gives is `Premise.Sound`
    (`Calculus/Core/SoundKit.lean`'s) in every state.  `Stmt.Sound.of_stepSound` builds it
    from the arms' `Stmt.StepSound`.  The hypothesis is what the arms owe;
    none is proved as `Stmt.StepSound` yet.  `ProvesSound.lean` has no
    `sorry` and no axiom beyond Lean's three.
  - **Review fix: the cover goal.**  As first stated, `Stmt.Sound` could
    not hold: a `bool` local may hold any value (a formula's binders range
    over every `Value`), `Run.ite` is then stuck, and under the diamond
    `split`'s two goals proved `⟨ if (b) { } else { } ⟩ true` of every
    state.  `split` and `inv` now have today's third goal under the
    diamond, one of the two conditions (`cov : m = .diamond → …`, after the
    frame's update for `inv`; `Calculus/Core/Cover`, deleted at W2:
    `Premise.cover`), and `Premise.Sound` takes the cover as a premise.
    `State.Typed` went: the cover is what it gave.
  - **Review fix: `sound_opAssign`.**  Its five storage and memory cases
    were `sorry` (commit 762d904); they are proved (`opStore_loc`,
    `opMem_loc`), so `Calculus/Core/SoundArms.lean` has no `sorry`.  It
    proves the update premises as `Premise.Sound` and no arm as
    `Stmt.StepSound`; the call, `try` and loop arms of
    `Calculus/Core/Blocks.lean` have no soundness proof.
  - Printing: a call and a `try` print as the statements they are
    elaborated from (a tuple call as `(a, b) = f(…)`, folded with the
    assignments after it; returns that none assigns but one reads as
    their declarations, `(uint a, uint b) = f(…)`, since the review: they
    stay in scope, `CallRet.outNames`), from the `Expr` as from the value; a frame or
    update end by `Thin` (`Frames.drop`, `Upd.drop`) prints as nothing; the
    four new premises have delaborators (a premise read alone names its
    context's locals `_`); a `Core.Proves` goal prints as today's sequent
    (`dl{ ∀ uint x, x = 1, { y := x } ⟹ [ x = y; ] true }`, `⟹ₖ` for
    solkey's rules alone, a schema context as `..H`).  Pinned in
    `Examples/Tactics/CorePrint.lean`.
  - The `Premise` quoter has the four new constructors (the same hunk as
    the frontend lane's, so the merge is clean).

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
- **The diamond's cover goal stays** (review fix): without it the rule is
  unsound in M3, whose values are untyped (a `bool` storage field holding
  `.int 5` makes both `b = TRUE →` and `b = FALSE →` vacuous while
  `Loop.step` is stuck), and a `Val.BoolValued` hypothesis would have
  excluded every condition that reads a local or storage.  So
  `whileInvariantDiamond` owes `b = TRUE ∨ b = FALSE` under its update
  (Lean only, today's `Premise.coverFml`), and `Stmt.stepSound_loop` has no
  hypothesis.  The box keeps KeY's two goals.  (This lane first put the
  cover inside `Premise.fml`, `Fml.invCases`; at the integration it is the
  calctools lane's `Premise.cover`, a goal apart, as for `split`.)
- `Prog.outNames` was declared both in `Semantics/RunErase.lean` (M3) and
  `Calculus/Core/Fml.lean`, which broke the root `Solidity.lean`; it is now
  one definition, in `Syntax/Core.lean` beside `Stmt.outNames`.

### M6b lane: formula frontends (`intrinsic-frontend`, 2026-10-07)

- **The reader** (`Calculus/Core/Notation.lean`, `NotationResolve.lean`):
  `cdl!{ φ }`/`cdl[C, m]{ φ }` read `dl!{}`'s text into `Core.Fml C []`.
  `elabFmlC` walks the formula with today's reader scope (`ECtx`) beside a
  named context: a quantifier, an update (`Upd.resolveN`: a target in scope
  at its type assigned, any other declared), a program's hints (`scopeHints`,
  hidden binders) and a `where` push on both; an atom is today's `elabFml`,
  resolved (`Fml.resolveN`).  A program's postcondition is read in the
  context the program leaves (`Prog.resolve`), so a branch's local is out of
  scope after it (`Examples/Tactics/CoreNotation.lean` pins the error).
  Parameters (every name read, a declared one included) are bound outermost
  (`Fml.closeN`): a `uint` by `∀`, an alias by a hidden binder, each only
  when the formula reads it before something binds it (tried without each,
  in order).  A declared name's parameter stays out of the reader's scope,
  so the program's declaration shadows it, as `dl!` reads it: `x = 1 → ⟨
  uint x = 2; ⟩ x = 2` binds `∀ uint x;`.  A Lean
  formula is elaborated at `Core.Fml C Γ` for the `Γ` of its place, so a
  `Core.Post C Γ` needs no weakening.  At the cutover `dl!` becomes `cdl!`.
- **`#wp`/`#step`** (`Tools/CoreInspect.lean`): a second elaborator of the
  commands that takes a closed `Core.Fml`, runs `Core.symex`/`Fml.step`
  compiled, and prints the quoted result by `Core.Delab`; the rule name is
  today's strategy's on the erasure.  `Core.Delab` now prints a closed call
  or `try` by running `Stmt.erase` (no more `‹…›` for a call in a formula);
  a taclet's call still prints `‹…›`.
- **Obligations** (`Calculus/Core/Spec.lean`): `Core.Problem.fml`/`ctorFml`
  take the program at the parameters' context (`paramsN`, the first
  parameter deepest) and bind it by `∀`; `Problem.ofLegacy` reads today's
  obligation's parts (`Problem.parts`) and resolves the program.
  `solc_scoped_problems N` (`Frontend/Problems.lean`) declares
  `N.f.problem.core : Core.Fml N []`, kernel-checked
  (`Solkey/Constructors.lean` pins EtherWallet's, and that it erases to
  `N.f.problem`).
- **Specifications**: `Core.specObligation` (`cspec!{f}`) is today's
  obligation read in its parameters' context: `old := storage` declares a
  local of `LTy.old`, `oldNet := net` one of `LTy.oldNet` (their own types,
  `UpdElem.ownTy?`), `result` is the program's; the parameters are bound by
  hidden binders, as today's free locals range over every value, so the
  erasure is today's obligation exactly (`#guard`ed in
  `Examples/Tactics/CoreSpec.lean`).
- **Callbacks** (`Semantics/Core/Callback.lean`; superseded by W1
  `runlemmas` (2026-10-08): `StateInv` over `TState`; `holdsC` and its
  theorems removed until W2 `tree`, which left them undone: see its
  "Left" bullet, carried into W3/W4): `Invariant.fml :
  Core.Fml C []`, read on a state's global part (`Invariant.at`), so no
  `I.vars = []` premise and no frame lemmas; `ExecS I : State C Γ →
  Stmt C Γ Γ' → COut C Γ' → Prop`, `ExecP`, and `ExecF` for a modality's
  frames.  No `iteStuck`/`loopStuck`: a condition is read by `Val.evalB`,
  whose word case is one more halt (it goes when values are typed, M4).  A
  branch, a block, a loop body and a callee's frame pop their locals on
  every outcome (`COut.map`); a block that pays runs statement by statement.
  Proved: `Prog.exec_run` (the deterministic run is a callback run unless
  `I` breaks), `Prog.eq_run` (with no payment it is the only one),
  `holdsC_iff_holds`, `holds_of_holdsC_modal`, `valid_of_validC`.
  `havoc` still ranges over untyped storages (`List (Name × SVal)`): typed
  `Storage C` is the values lane's.
- **Left**: the callback taclets and `ProvesC` on `Core`
  (`Calculus/Callback.lean`'s, at M6c or the cutover); `sol_spec` and `sol_symex` on a
  `cspec!` obligation (the closer is M6c's); `UpdElem.target?` of
  `Derive.lean` and the reader's `UpdElem.setsLocal?` are two names for two
  questions (the split's two kinds, every local an element sets).

### Integration of the lanes (2026-10-07)

The six lanes merged into `intrinsic` in order: `intrinsic-values`,
`intrinsic-evm`, `intrinsic-calculus`, `intrinsic-sound2`,
`intrinsic-calctools`, `intrinsic-frontend`.  Text conflicts only in
`docs/intrinsic.md` (Decisions 9 and 10 written twice: the longer kept),
`docs/module-map.md` (union; one row per module, the newer wording) and
`Calculus/Core/SoundArms.lean` (both sorry-free: `sound2`'s kept, which
also proves `++`/`--`; `calctools`' `opStore_loc`/`opMem_loc` had no other
user).  What did not compile together, and how it was resolved:

- **One cover design.**  `sound2` proved its arms against
  `Premise.Sound` over `State.Typed` states (a `bool` local holds a `bool`)
  with the loop cover inside `Premise.fml` (`Fml.invCases`); `calctools`
  dropped `State.Typed` for a cover goal apart (`Premise.cover`,
  `Calculus/Core/Cover`, deleted at W2), which `Premise.Sound` takes as a premise and
  `Proves.split`/`Proves.inv` prove under the diamond.  `calctools`' design
  is kept (a formula's binders and a capture of a `bool` storage word give
  a non-`bool` local, so `State.Typed` is not preserved by a derivation):
  `Fml.invCases` is gone, `whileInvDiamond` reads the cover from
  `Premise.cover`, and the splits on a simple condition (`iteStep`,
  `requireStep`) take a value that is no `bool` by
  `Premise.Sound.splitStuck` (`Calculus/Core/SoundLocal.lean`: the run is
  stuck, which the box allows and the diamond's cover excludes).  The
  short circuits need no typing: on a non-`bool` left operand both sides
  halt, and no expression panics (`Val.eval_noPanic`).
- **Names declared twice** (an import of both fails at the root):
  `Core.Prog.outNames` (one, in `Syntax/Core.lean`, already on
  `intrinsic-calculus`); `Core.MLoc.write_eq` (`Semantics/Core/TypedRunErase.lean`
  and `Calculus/Core/SoundArms.lean`: one, in `Semantics/Core.lean` beside
  `MLoc.addr`); `Core.Stmt.run_declMem` (`SoundCalls.lean` now imports
  `SoundCapture.lean`'s); `Core.Invariant` (M3's run invariant in
  `Typing/Soundness.lean`, renamed `RunInv`, against the callback
  invariant of `Semantics/Core/Callback.lean`, which kept today's name
  until W1 `runlemmas` (2026-10-08) made it `StateInv`: the name
  `Core.Invariant` is now free).
- **`negativeKey` deleted** (`Examples/Tactics/Decide.lean`): `values[-1]`
  no longer elaborates since `UnOp.accepts .neg` is `int` only (M4 lane), as
  solc rejects it; a `uint` key is never negative.
- `docs/intrinsic.md` cited files that do not exist (the side-projects
  `Corresp/Proved`, the scratch `CoreBench`): no longer as paths.

**Full build: green.**  `lean_build` over `Solidity`, `solkeycheck`,
`SolidityCorpus` and `SolkeyTestSuite` (283 jobs; the last two added to
`defaultTargets` for the run only), no `sorry`, no new `axiom`, no new
`maxHeartbeats`.  Wall time 173 s for the final build, which rebuilt every
module above `Semantics/Core.lean` (the `MLoc.write_eq` move) from the Lake
cache below it; the first build of the merged tree took 311 s (251 jobs, up
to the failures).  M0 has no whole-build time to compare with (it timed
single files in fresh workers); under the build's parallel load the per-file
times are not comparable with M0's either (`TestSuite/Derived9` 17 s
against 7.0 s, `Derived10` 23 s against 9.3 s, `Derived11` 4.6 s against
2.8 s, `Examples/ProofTree` 21 s against 10.1 s, `Solkey/TestSuite` 13 s
against 10.4 s).  `scripts/check-orphans.mjs`: 269 reachable, none
orphaned (without the git-excluded `Solidity/Scratch/`);
`scripts/check-doc-paths.sh`: OK.

Left after the integration: `Stmt.Sound C` itself (`Calculus/Core/ProvesSound.lean`'s
hypothesis) from `Stmt.stepSound` and the block arms (`stepSound_call`,
`stepSound_tryCall`, `stepSound_loop`) once `WkRuns` is discharged by
`Prog.run_wk` (done below); the M4/M5 deletions above; M6c; M7.

### Core soundness, unconditional (`intrinsic-calculus`, 2026-10-07)

- **`Proves.valid` has no hypothesis**: `Calculus/Core/SoundStep.lean`'s
  `Stmt.stepSound` now imports `SoundCalls` and `SoundLoops` and dispatches
  the call, `try` and loop arms to `stepSound_call`, `stepSound_tryCall`,
  `stepSound_loop` (`Stmt.IsBlockArm` is gone); `WkRuns` is
  `WkRuns.of_run_wk`, `Prog.run_wk` at `up` with the pushed value as the
  lift's background (`σ.lift up (w, σ.env)` is `σ.push w` by `rfl`).
  `ProvesSound.lean` proves `Stmt.sound : Stmt.Sound C` from it, and
  `Proves.sound`/`Proves.valid` take no `Stmt.Sound` argument.
  `#print axioms Proves.valid`: `propext`, `Classical.choice`, `Quot.sound`.
- **The cover is already threaded**: since the integration `Premise.Sound`
  takes `holds σ (p.cover m)`; `Premise.Sound.split`
  (`Calculus/Core/SoundLocal.lean`) packages `Logic.lean`'s
  `Premise.sound_split` with `splitStuck`: a split is sound given its two
  branch runs and that the statement is stuck where neither condition
  holds, the cover excluding that case under the diamond (`iteStep_sound`
  and `requireStep_sound` use it on a simple condition).  `inv`'s cover is
  `whileInvDiamond`'s premise (`SoundLoops.lean`).
- **No typing hypothesis was left**: `Val.BoolValued` and `State.Typed` do
  not occur in the calculus (the cover replaced both at the integration);
  every arm holds in every state of M3's untyped values.
- **`holds_erase`, one way for the two excluded binders**
  (`Calculus/Core/HoldsErase.lean`): `holds_erase_bind` (scoped to erased,
  in an untyped state binding `x` to a value of `t`; the converse fails,
  the erasure reading one value) and `holds_of_erase_anon` (erased to
  scoped, the untyped `{anon(…)}` ranging over every binding; the converse
  fails, `{anon(x)} defined(x)`).  Both are for a `Plain` body, at the top:
  a polarity-indexed `Plain` that admits them under negation is not done.
- `lean_build` of the default targets: green.

### Gate G0: passes, under conditions

The spike (the scratch module `Solidity/Scratch/IntrinsicSpike`, not committed) has seven
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
The SolKey reader (side-projects lean/solkey) depends on Taclet constructor names and arities and on `Stmt.*` arity in LeanShape. M6a breaks its 590-reference generated correspondence file (`Corresp/Proved` in the side-projects repository). Regenerating it requires the user's explicit go-ahead (memory: do not touch the side-projects reader unless asked).
Semantic change: scoped blocks and loops pop locals, and today they outlive the branch. This follows solc (≥0.5 C99 scoping) but changes `ifElseSplit`'s continuation (now through a pop frame), loop frames (`Prog.loopFrame`, `Fml.loopAnon`), modifier `_; _;` (commit 9ab7d94) and lowerReturns (Syntax.lean:3064-3110), where the continuation copied into branches may see branch locals. Each needs a solc-alignment.md row.
Dependent elimination: `Prog.cons`'s output stays a variable (no `Δ₂ ++ Δ₁`), but `Thin`/`Suffix` casts in `Env.thin`, `Frames.pop` and Stmt.step's dispatcher (Completeness.lean:531) can still produce 'motive is not type correct' in the about 387 match arms across 28 files. Dispatcher arms must use top-level patterns and `if h :`, as the old port learned.
Typed storage through `structDef` (a String match) may make the kernel whnf structDef in defeq checks. This risks whnf timeouts in Corpus `decide +kernel` and in concrete stores (Semantics.lean:977-985 already records one). uint as a subtype must not make the kernel unfold `Nat.land` (56642ee).
Callee frames: the typed `Stmt.call` body is closed over `rs ++ ps`, so expansion needs `Prog.wk` (O(|body|) once per call). Three return paths must be exported in the caller's output context: `CallRet.val`, `CallRet.rets` re-declared by elabTuple (:4129), and the memory return `mv` (elabMemCall :3583). Getting this wrong would break 449 imported functions at M2's lint.
Memory: Lean workers already use 3-4 GB on Decide.lean and Derived*. M6a touches both, inside the 32 GiB session cap, so at most two Lean agents can run, and only one during the M2/M4 low-module rebuilds.
Scope creep: M6c (about 25k closer lines) may not pay off. The plan allows it to stop at the `Fml.erase` reflection, which leaves the decision-procedure IR extrinsic. Users asking for 'everything intrinsic' should be told this before M6c starts.
