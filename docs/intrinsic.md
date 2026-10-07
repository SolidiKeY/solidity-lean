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

## Milestones

| # | Status | Work |
|---|---|---|
| M0 | done 2026-10-07: G0 passes under the conditions below | baselines + scratch spike, gate G0 |
| M1 | done | stuck causes that need no index; the elaborator runs the locals check (`wtCheck`) |
| M2 | done 2026-10-07: every import and `sol{}` site resolves, the scoped form kernel-checked; elaboration within 10% (below) | `Ctx`/`Idx`/`Thin`, typed `Core` syntax, `resolve`, quoter, lint |
| M3 | M3.1, M3.2 done 2026-10-07 (typed run, `run_erase`) | `Env Γ`, `State C Γ`, typed run; delete the locals checker |
| M4 | | typed values, storage, heap; delete `stuck`; retire old `Stmt` |
| M5 | M5.1, M5.2 on lane `intrinsic-evm` (see M5 lane) | EVM on typed syntax; delete `wtStmt`, `not_stuck` |
| M6a | | calculus: `Fml C Γ`, `Frames`, `Premise`, symex, chains, ProofTree |
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
  - Not done: that `resolve`'s output from the elaborator's names is
    `Fresh` (the separatedness conjunct follows from the others, also not
    proved); deriving `Stmt.wt`/`Prog.wt`/`Ctx.has`/`EnvWT` from `resolve`
    plus `run_erase`.  Applying `Prog.run_erase` to `callsCore` and a state
    times out in the elaborator at `whnf` (the partial application without the
    state checks); not yet diagnosed.

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
    several returns (`CallRet.rets`, no code) or of a memory return.
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
    `Evm/Examples.lean` (not the four interpreter theorems: they need the M5
    `compile_correct`), plus a scoped-branch run, a `pop` in a branch
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
`intrinsic`.  Status 2026-10-07, round 2: M3 (`Env Γ`, `State C Γ`, the
typed run) had not landed, so the simulation is stated against the
Env-from-Γ design and everything that does not need the run is proved.

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
  `inFrag`/`inFragP`, `Stmt.pushes`/`pays`/`shrinks`, `argsCode` and
  `retEnterCode`/`retLeaveCode` `match` on `Stmt C Γ Γ'`, `Prog C Γ Γ'`,
  `Args C Γ ps` and `CallRet Γ rs Γ'`, and `Evm/CoreExamples.lean` evaluates
  them in the kernel.  They are kept as `match`: the calculus never
  evaluates them (no symex or closer step reaches the compiler), the only
  kernel evaluations are the 44 example checks of one file, and every proof
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
- `not_stuck`/`never_stuck`: nothing to delete yet on the Core path, since
  there is no Core run to be stuck.  When M3/M4 land, `compile_correct` over
  `Core` has no `not_stuck` corollary (its `Halt` has no `stuck`); the
  untyped `not_stuck` (`Evm/Correctness.lean`) and `never_stuck`
  (`Theorems.lean`) stay with the untyped compiler until M4 retires it.
- Left (needs M3's `Core.Stmt.run`/expression evaluation over `State C Γ`):
  `simple_sim`/`spath_sim`/`loc_sim`/`val_sim`, `stmt_sim` (gate: at most
  470000 heartbeats, split per constructor family rather than raised),
  `prog_sim`, `compile_correct`/`compile_box`/`compile_net` over `Core`, and
  the four interpreter theorems of `Evm/Examples.lean` (`setAge_interpreter`,
  `overflow_interpreter`, `payOwner_interpreter`, `callTwice_interpreter`).  The lemmas above
  are what their cases call.  Also left: timing the compiler on a
  quoter-built program (M2.3); `Machine.mem : Nat → Word` (with
  `cell = id`) once `Evm/Compile.lean` retires at M4.

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
   elaboration-time code (`resolve`, quoters, `Stmt.wk`).
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
   `Thin` with `keep` is only for `Stmt.wk`.
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
