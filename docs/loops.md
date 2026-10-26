# Loops

`while`, `for`, `do … while`, `break`, `continue`: four decisions and their
status (`Examples/Tactics/Loops.lean`). An unannotated loop is unwound
within the proof search budget (`Taclet.whileUnwind`); an explicit
`/// @custom:key unwind k` clause limits it to that bound
(`LeanTaclet.loopExit`), or it is proved by its invariant
(`Taclet.whileInvariantBox`, `whileInvariantDiamond`). Background:
`docs/kernel-port.md` (its topics "Modalities", "Semantics", "One rule per
statement" and "Conditions" are the decisions this extends).

## What solkey has

solkey has loops since `ed7849d5b6` ("added loops", after the pinned
`1b4341a303`): one unwinding taclet and two invariant taclets in
`solidityProgramRules.key`, a source pass that reduces every loop to a
`while` first, and loop specifications. Its `docs/taclets-implementation.md`,
section "Loops", is the reference this plan follows; every name and shape
below is solkey's.

**`LoopLowering`** runs in `ExpandFunctionBody` right after `ReturnLowering`,
so it sees only bare `return;`. It leaves a `while` whose body has no
`break`, `continue` or `return`, recording the abrupt completion in fresh
`bool` flags:

| Source | Lowered |
|---|---|
| `break;` / `continue;` / `return;` in a loop body | `brk = true;` / `cnt = true;` / `ret = true;`, the rest of the block dropped |
| a statement that may set a flag, then `rest` | `s; if (!flag…) { rest }`, testing only the flags `s` may set |
| `while (c) body` with `break`/`return` | `{ bool brk = false; while (!brk && !ret && c) { bool cnt = false; body } }` |
| `for (init; c; upd) body` | `{ init; while (c) { body if (!brk && !ret) upd; } }`, so `continue` still runs `upd` |
| `do body while (c)` | `{ bool first = true; while (first \|\| c) { first = false; body } }` |
| a loop with a `return` | `ret` is shared by nested loops; the outermost is followed by `if (ret) return;` |

A flag is created only when used, so a loop without `break`/`continue`/
`return` keeps its condition; a guard tests the flags in the order `brk`,
`cnt`, `ret`. A missing `for` condition is `true`. A `break`, `continue` or
`return` inside a `try` inside a loop is rejected.

**`whileUnwind`** (rule set `loop_expand`):
`while (s#cond) s#body` ⇝ `if (s#cond) { s#body while (s#cond) s#body }`,
unbounded; solkey's strategy unwinds a loop that has no specification.

**`whileInvariantBox`** / **`whileInvariantDiamond`** (rule set `loop_inv`),
on `\modality{#box}{c# while (s#cond) s#body #c}` (resp. `#diamond`), two
goals:

- `"invariant initially valid"`: `inv`;
- `"invariant preserved and used"`:
  `#loopAnon(body, inv -> [bType b = cond;]((b = TRUE -> [body] inv) & (b = FALSE -> [c# #c] post)))`;
  under the diamond the hypothesis is `inv & dec = variant` (a fresh skolem
  `variant`) and the body's postcondition is
  `inv & <b = cond;>(b = TRUE -> 0 <= dec & dec < variant)`: **the variant
  decreases only when the condition holds again**, so the iteration a
  `break` or `return` ends need not decrease it.

`#loopAnon` (`LoopFrame`) gives a fresh constant to every local the body
assigns or declares (the lowering's flags included), to `storage` when it
writes a non-local, and to `net` when it calls anything but
`require`/`assert`/`revert`. **A body that allocates or writes memory gets
no invariant rule**: the heap is not anonymised. A loop without `invariant`
(or, under the diamond, without `decreases`) is unwound instead.

Specifications are `///` lines directly above the loop,
`/// @custom:key invariant <expr>` (several conjoined) and
`/// @custom:key decreases <term>` (at most one), in the function-spec
expression language; in Lean an invariant is a program expression, or a
quantified clause `\forall T x; a -> c` (`RawInv`, `LoopQ`), which the box
rule reads as `∀` (`invFml`, solkey's `\getInvariant`) and under which the
diamond rule closes to `false` (`whileNoVariantDiamond`, Lean only); `LoopLowering` moves them to the `while` it produces, so
the invariant of a `for` or `do … while` holds at the head of that `while`,
also on the iteration a `return` ends.  Under the box an iteration that
`break`s goes on to the rest of the program instead (solkey `473da8944c`'s
`\getLoopBreak`: `whileInvariantBox` assumes `inv ∧ ¬broke` and the body
ends in `(¬broke → inv) ∧ (broke → ⟨[ ]⟩)`); under the diamond the
invariant still holds where the `break` leaves, as upstream.

Lean's rules take solkey's names (`whileUnwind`, `whileInvariantBox`,
`whileInvariantDiamond`) as `Taclet` constructors (`RuleShapes.tacletOrigins`).
Lean keeps its explicit unwind bound, capture-free conditions,
boolean-expression invariants (with quantified clauses), conservative frame
restrictions and an unsigned variant; KeY's formula invariants and unbounded
integer variant are not claimed. What solkey lacks (`loopExit`, the bound's
end) stays a `LeanTaclet`.

## Decision 1: semantics, the least fixed point inside `Stmt.run`

The run is typed (`Semantics/Run.lean`, over `State C Γ`); the loop's body
is a scope whose locals are popped each iteration.

- `Stmt.loop (a : LoopAnn C Γ) (c : Val C Γ .bool) (body : Prog C Γ Γ₁)`
  (`Syntax/Scoped.lean`).
- `Stmt.run` stays total and structural. Its loop arm is
  `TLoop.run (fun τ => Prog.run τ body) c σ`: the recursive call is on the
  subterm `body` under a binder, which structural recursion allows.
- `TLoop.iterN n σ` runs at most `n` iterations and returns *running τ* or
  *done r*; *done* absorbs. `TLoop.run` returns the *r* of any `n` at which
  the iteration is done (all such `n` agree), and the halt `diverge` when
  none exists.
- `Modality.onTHalt`: a box accepts a divergent run, a diamond
  does not. This is the partial/total reading the "Modalities" topic gives
  the two modalities. The annotation `a` is invisible to `Stmt.run`.

Rejected:

| Option | Why not |
|---|---|
| Fuel everywhere (`Stmt.run n σ s`) | A `Nat` through every theorem that recurses on `Stmt.run`; box becomes `∀ n`, diamond `∃ n`, and monotonicity in `n` a lemma every proof needs. |
| A constant bound inside the loop only (fuel `2^257`) | Unwinding is not exact at the bound: a loop stopping at iteration `B + 1` is `diverge` while its unwinding is not, so `whileUnwind` is unsound for the diamond. |
| An inductive `Exec` beside `Stmt.run` | Two denotations. Every rule's `Premise.Sound` (`Calculus/ProvesSound.lean`) is over `Prog.run`, the corpus is decided by kernel evaluation of it (`corpus_decide`), and the callback relation anchors to it (`ExecS.det`). `Stmt.run` is the only semantics. |
| `partial_fixpoint` | `Res = Except Halt` is not a CCPO, and the kernel cannot unfold the result. |

**Cost: computability.** The existential makes `TLoop.run` classical, but
`@[implemented_by TLoop.runImpl']` (a `partial def` that iterates until done,
which the kernel never sees) keeps `Stmt.run` compiled: `#eval` and `#run`
run loops (and do not return from one that never ends). Kernel reduction of a
loop-free program is unaffected, so `corpus_decide` and `Evm/Examples.lean`
keep working. A concrete loop is decided with fuel: `Prog.runF`
(`Semantics/RunFuel.lean`, each loop entered at most `n` iterations) agrees
with the run wherever it does not say `diverge` (`Prog.runF_approx`), and
`TLoop.run_of_iterN : iterN n σ = .inr r → TLoop.run … σ = r` underlies it.

**Proofs that recurse on `Stmt.run`** take a loop's case from the lemmas of
`Semantics/RunWk.lean` and `Semantics/Run.lean`: `TLoop.run_map` (two loops whose iterations go in
step from related states run alike: `Prog.run_wk`, `Prog.run_frame`),
`TLoop.run_induct` (an invariant of the loop head), `TLoop.run_unfold` (the
unwinding) and `TLoop.run_variant` (a variant bounds the iterations). The
typing proofs read the typed run's states' erasure
(`Typing/TypedRunInv.lean`) and take a loop's case from `TLoop.run_induct`,
once for every invariant (`RunInv.tkeeps_loop`: the invariant at the loop
head, the body's locals popped each iteration). In more detail:

`Stmt.run_frame`/`Prog.run_frame` (`Semantics/RunFrame.lean`: a body runs
within its frame), the typed state (well-typed by construction,
`Semantics/State.lean`), `Prog.run_canon` and
`Prog.run_tight` (`Typing/Reachability.lean`, `Typing/Tight.lean`, both
`Stmt.keeps_all` of `Typing/HeredRun.lean`; `reachable_iff` stays true, since a loop
reaches nothing a finite sequence of body runs does not), and
`Stmt.exec_run`/`ExecS` (`Semantics/Callback.lean`: a loop whose body has no
transfer is `det`). `Stmt.forksIn pay (.loop …) := Prog.callsBack pay body`, not `true`: a forking statement with no `ExecS` constructor has no runs, so every
modality over it would hold vacuously. `stmt_sim` is out of the fragment
("The EVM").

**A loop that transfers, with callbacks**, has `ExecS` constructors
(`Semantics/Callback.lean`): the condition halts, the loop
exits, iterates (`loopIter`), stops in its body, or diverges
(`loopDiverge`). An inductive relation has no derivation of an infinite run,
so `loopDiverge` over-approximates: a loop whose body pays may always
diverge. A box accepts a divergence, and the callback reading is box-only
(solkey's), so nothing is lost; a diamond over such a loop is never valid.
Each constructor requires `Prog.callsBack J.pay body`, so a loop where nothing calls back has only
its deterministic run (`ExecS.det`), and
`Stmt.exec_run` and `Stmt.eq_run` keep their statements.

## Decision 2: `break`, `continue`, `for`, `do … while` are lowered

The elaborator lowers them and the kernel sees only `Stmt.loop`. `TRes` and
`THalt` gain nothing (beyond `diverge`), so no `cases` on an outcome gets a
new arm. This is the choice `return` already made (no abrupt completion in
`Stmt.run`; `lowerReturns` in `Syntax.lean`), and how KeY's loop scope works:
a boolean records the abrupt completion.

The pass is solkey's `LoopLowering`, shape for shape (the table in "What
solkey has"), as `lowerLoops` (`Syntax/Elab/Lower.lean`):

- **`break`/`continue`/`return`** in a loop body set fresh flags
  `brk`/`cnt`/`ret` (`freshCapture`), each made only when used; the rest of
  the block is dropped, and whatever follows a statement that may set a flag
  is wrapped in `if (!brk && !cnt && !ret) { … }`, testing only the flags it
  may set. The condition becomes `!brk && !ret && c`; `cnt` is declared
  `false` at the head of each iteration.
- **`for (init; c; upd) body`** is
  `{ init; while (c) { body if (!brk && !ret) upd; } }`, so `continue` still
  runs `upd`. The block scopes `init`, so a second `for (uint i …)` in the
  same function is legal.
- **`do body while (c)`** is `{ bool first = true; while (first || c) { first
  = false; body } }`. The body is not duplicated: that would double its
  declarations (`checkFresh`) and its weight.
- **`return` inside a loop.** In an inlined body, `return e;` in a loop is
  `r = e; ret = true;` (`lowerReturn`), `ret` is shared by nested loops, and
  the outermost loop is followed by `if (ret) return;`, which `lowerReturns`
  then lowers as any early `return`. So the loop lowering runs before
  `lowerReturns`, as solkey's runs after its `ReturnLowering` has made every
  `return` bare.
- A `break`, `continue` or `return` inside a `try` inside a loop is an
  elaboration error, as in solkey.

The cost: goals and invariants mention the flags; under the diamond an
invariant for a loop with `break` must say what holds when `brk` is set
(under the box the rule reads the flag, `loopBreak`).

## Decision 3: one rule per loop, chosen by an annotation

Unwinding and the invariant rule both apply to one loop. To keep "one rule
per statement" (`Stmt.rule_exists`, `Rule.iff_step` in
`Calculus/RuleExists.lean`; `Rule.premise_unique` in
`Calculus/Taclet.lean`), the choice is syntax. `LoopAnn C` is either
`.inv (I : Val C .bool) (dec : Option (Val C .uint))` (an invariant and an
optional variant), `.unwind (k : Nat)` or `.auto`. `Stmt.step`
(`Calculus/Step.lean`, its loop arm `loopStep` in
`Calculus/Blocks.lean`) dispatches:

| Annotation | Box | Diamond |
|---|---|---|
| `.auto` | `whileUnwind`: one iteration followed by the same automatic loop | same |
| `.unwind (k+1)` | `whileUnwind`: `unfold [if (c) { body while[k] (c) body }]` | same |
| `.unwind 0` | `loopExit`: `Premise.check (c = false) []`, the goals "loop exited" (`c = false ⟹ ⟨[ ω ]⟩ φ`) and "unwound to the end" (`c = false`), by `Proves.check` (walk: `apply checkLean r`) | same |
| `.inv I dec` | `whileInvariantBox`, below | `whileInvariantDiamond` with `dec = some v`; with `none`, `whileNoVariantDiamond`, the premise `done false` (sound, unprovable; solkey unwinds instead) |
| `.inv I dec`, a body with no frame | `whileClose`: `done false` | same |

In the source the annotation is solkey's specification (from solc's AST,
`scripts/solc-ast.mjs` reads the clauses from the source by the loop's `src`
offset, as solkey does, and the front end prints them above the loop:
`Examples/Tactics/LoopsImport.lean`),
`/// @custom:key invariant …` and `/// @custom:key decreases …` above the
loop, and, Lean only, `/// @custom:key unwind k` for the bound; a loop with
neither is `.auto`. `LoopUnwind` gives the one `whileUnwind` constructor
either automatic mode or a remaining explicit bound. The mode is proof
metadata; execution ignores all loop annotations.

`sol_prove` probes increasing walk budgets up to the existing 20,000-step
maximum and kernel-checks the first completed walk. A completed walk can
still leave goals; exhaustion is failure, never a proof. The probing stages
can attempt 52,640 nodes in total. `sol_prove?` retains the selected bound as
`sol_prove (steps := n)` so replay runs just that walk. An explicit step budget
must be between 1 and 20,000. It bounds both path depth and total walk nodes,
independently of the scoped closer's limits.

Use `sol_prove` for automatic unwinding: it refutes impossible branches while
walking (`Seq.refuteS`, `Calculus/LeafDerive.lean`). Once the context stacks
more than `sliceDepth` storage updates, a guard over locals is refuted on the
premises it reaches alone (`LFml.slice`): the storage writes of earlier
iterations, and their guards, would otherwise grow the closer's work with
each iteration and soon pass its bounds, so the loop would unwind until the
budget ran out. `sol_symex` expands both branches before closing leaves, so automatic
loops can exhaust its budget even when their guard is initially false. Give
that workflow an explicit unwind bound or invariant.

`.unwind 0` is not `assert(!c)`: a failed `assert` panics, so running out of
unwindings would be a failure of the program rather than of the bound.

**The annotation is a `Val`, not a `Fml`**: `Fml` contains `Prog`, so a
`Stmt` carrying one would make `Stmt`, `Term` and `Fml` one mutual
inductive. A boolean program expression is effect-free and lowered exactly
(`Val.lower_evalT`, `Calculus/LowerRun.lean`). Quantified clauses
`\forall T x; a -> c` are `LoopQ` (`Val`s under binders), which the box rule
reads as `∀` (`invFml`); under the diamond a quantified invariant closes to
`false` (`whileNoVariantDiamond`).

## Decision 4: the invariant rule and its soundness (built)

solkey's two goals, as `whileInvariantBox` writes them (`Calculus/Rules.lean`),
in the context's update `{U}`:

```
  "invariant initially valid":     Γ ⟹ {U} inv = TRUE
  "invariant preserved and used":  Γ ⟹ {U} {anon(body)} (inv = TRUE → { b := cond }
                                       ((b = TRUE → [ body ] inv = TRUE) ∧ (b = FALSE → [ ω ] φ) ∧ cover))
  ──────────────────────────────────────────────────────
  Γ ⟹ {U} [ /// @custom:key invariant inv while (cond) body; ω ] φ
```

`b` is KeY's `s#b` of `bType b = cond;`, a fresh local; `= TRUE` is KeY's
`=` (`Fml.eq`), and the update `{ b := cond }` is where the condition is
evaluated, so a condition that halts lands nowhere. The cover,
`b = TRUE ∨ b = FALSE`, is asked under the diamond only (`Premise.inv`'s `c'`);
under the box `cover` is `true`. `whileInvariantDiamond` binds the variant first,
`{ variant := dec ‖ b := cond }`, and the body's postcondition is
`inv = TRUE ∧ { b := cond } (b = TRUE → 0 <= dec ∧ dec < variant)`: **the
variant is checked only when the condition holds again**, as solkey checks
it. Lean reads `dec` where KeY compares it with a skolem (`dec = variant`),
so under the diamond `dec` must be defined wherever the invariant holds.

**The anonymising update `{anon(body)}`** is `Fml.anonHavoc`
(`Calculus/Fml.lean`), solkey's `#loopAnon`: `{anon(xs)}`, where `xs` is the body's
frame, `Prog.frame` (`Calculus/Blocks.lean`: the locals of the
loop's context the body writes, the lowering's flags included), and, for
the storage, what the body's modifies set says (see "Modifies sets"
below): nothing, the roots it may write
(`{storage := anon(storage, L, s')}` for every storage `s'`), or, where
it may write any root, pay or call out, `{havoc}` (storage and ledger
together). A body outside `nonpayable` (memory, a push or a pop, an alias,
an external call) has no frame, and its loop closes to `false`
(`whileClose`). The frame lemmas are `State.eq_anonHavoc` (the locals)
and `Prog.frame_keeps` (the storage, the ledger, the balance;
`Semantics/RunFrame.lean`); `holds_anonHavoc` (`Calculus/SoundLoops.lean`)
turns them into the premise at every loop head.

**Modifies sets**.  KeY frames a loop by its
`assignable` clause and anonymises only the locations it lists; Dafny has
`modifies`.  Here the set is computed, at the granularity of the roots:
`Stmt.storeAt` (`Calculus/Blocks.lean`) is `some L`, the state variables a
statement may write (a write's root, `Loc.root?`), or `none` where it may
write any root (a write through an alias, which may be bound to any root),
memory, an array's length, the ledger (a payment) or call out (a `try`, a
value call: the callee may call back).  Three pieces:

1. **The location set** is `Storage.anon L old new`
   (`Semantics/Storage/Anon.lean`), KeY's `anon(heap, locset, anonHeap)`:
   `old` with the roots `L` names taken from `new`, and the symbol
   `anon(s, r₁, …, rₙ, s')` (`Op2.anon`) that writes it in a formula.
   `Storage.Framed L σ τ` (`anon L σ τ = τ`) says that `τ` differs from
   `σ` only there; it is reflexive, transitive and monotone in `L`, and a
   `save` at a reference is framed by any set naming its root
   (`Storage.Framed.save`).  The laws are folds of `SFields.set` and `get`
   by name, so they hold for any member list, a repeated name included.
2. **The frame theorem** is `Stmt.run_keeps`/`Prog.run_keeps`
   (`Semantics/RunFrame.lean`): a run that ends normally ends in a storage
   framed by the statement's modifies set, the ledger and the balance as
   they were (`FrameKeeps`), whatever its mutability.  The lazy
   read-over-write rules are its one-step case: a write at `q` changes
   nothing outside `q`'s root.
3. **The narrower anonymisation**: `Prog.frame`'s second component is
   `Prog.storeAt body` for a `nonpayable` body (`some []` for a `view`
   one), and `Fml.anonHavoc` reads it.  Its soundness is
   `holds_anonHavoc` (and `holdsC_anonHavoc` with callbacks: a body with a
   modifies set calls nobody back, `Prog.callsBack_of_storeAt`, so its
   callback run is its run).  `sol_close` reads a root through the symbol
   (`Storage.find_anon`, KeY's `selectOfAnon`).

So an invariant no longer restates facts about storage the body never
touches (`untouchedRoot`, `Examples/Tactics/Loops.lean`).  What is not
here yet: a finer granularity than the root (a field, a mapping entry, an
array slot: KeY's `(o, f)` pairs; a write at `b[i]` anonymises all of
`b`); a modifies set through an alias (an alias bound before the loop to a
known root could name it); memory (a body that writes memory still has no
frame: `Prog.within` refuses it); and a callee summary with a modifies
clause, which would let a call that writes storage be one update instead
of inlined (`internalCallSummary` covers callees that compute values
only).  Separation logic is not needed for any of these: disjointness can
be stated in the location sets themselves (dynamic frames), which is the
first step if aliasing of memory references becomes the bottleneck.

The anonymising binder and update are produced under the box under both
modalities, as `{havoc}` is, so a diamond loop's context stays one
`closeTrue` reads (`Hyps.boxOnly`); every statement that calls back has
modifies set `none`.

**The flags are typed by the invariant.** An anonymised `brk`, `ret` or
`first` may hold anything, but the condition reads it; `lowerLoops`
conjoins `f || !f` (defined exactly when `f` is a `bool`) to an invariant for
each flag the condition tests, which KeY's `boolean` type gives.

**Soundness** (`Calculus/SoundLoops.lean`, `Stmt.sound_loop`). Box
(`Premise.sound_whileInvBox`): by `TLoop.run_induct`, every loop head is in the frame of the first and
satisfies the invariant; where the condition is `TRUE` the body's box keeps
it (and rules out a panic), where it is `FALSE` the rest's goal holds.
Diamond (`Premise.sound_whileInvDiamond`): `TLoop.run_variant` bounds the iterations
by the variant's value after the first, which is a `uint` below the one
before wherever the loop goes on; neither the condition (the cover) nor the
body (a diamond) can halt.

**In Lean.** `Premise.inv` (`Calculus/Fml.lean`), read by
`Premise.fml`, so `sol_symex` steps it as any premise; `Proves.inv`
(`Calculus/Proves.lean`, `apply invBox r`, `apply invLean r` under the
diamond) for a walk, its goals `init` ("invariant initially valid") and
`thn`, `els` past the context's anonymising update `Hyps.anonHavoc` ("body
preserves invariant", "use case"), which the proof tree labels as solkey
does.
`sol_close` reads `{anon(…)}` (`CloseS.holds_anon`, `CloseS.anon_cons`:
an anonymised local is set to `b x`, a binding nobody knows);
`sol_decide` and `sol_prove`'s closer do not (`anon` and `havoc` are
outside `Calculus/DecideLang.lean`'s language), so `sol_prove` leaves such a leaf to `sol_close`. Under the
diamond the closer is slow: a counting loop closes, a loop with a `break`
(whose flag is read through the cover) and a sum do not within the default
heartbeats; their box versions close (`Examples/Tactics/Loops.lean`).

**Typing and declarations.** In the scoped syntax (`Syntax/Scoped.lean`) a
loop is `Stmt C Γ Γ`: its condition and annotation are read in `Γ`, its body
is a `Prog C Γ Γb` whose locals the typed run pops every iteration
(`TRun.loop`), as for `ite`; the invariants of `Typing/` are kept at every
head (`RunInv.tkeeps_loop`, `Typing/TypedRunInv.lean`), and the state is
typed by construction (`Semantics/State.lean`). A local the body declares is
popped at the end of each iteration and declared again in the next, as solc
re-initialises it; it is not in the frame (`Prog.frame` lists locals of `Γ`
only), and the invariant, typed at `Γ`, cannot name it.

The loop condition is **not** captured before the loop, since it must be
re-evaluated: the invariant rule binds it to `b` at the head, the
unwinding's `if` captures it per copy.  So a condition, invariant or variant
that needs a statement before it is an elaboration error (`loopExpr`): an
`++`, as under `&&`, and also a call to a declared function, a cast, a
narrow operation that needs a capture, or a struct constructor, none of
them an effect, which solkey evaluates per iteration (`bType b = cond;`).
`while (i < len())` is refused; writing `uint n = len();` before the loop,
or `if (!(i < len())) break;` at the head of its body, is the workaround.

## The EVM

A loop is one structured instruction, `LOOP cond body` (`Instr.loop`,
`Evm/Machine.lean`), so `exec` stays structural and the skip-count lemmas
stand; its turns are `loopRun`'s, classical as `TLoop.run`'s, a fault where
no number of them ends it (`StmtOut.diverge`); the simulation is by
induction on the turns (`loop_sim`, `Evm/Correct.lean`). The fragment takes
a loop whose body pushes, pays and shrinks nothing and keeps the fragment's
flags (`docs/compiler-verification.md`). Lowering `LOOP` to
`JUMPDEST`/`JUMP` is an assembler's step. Absolute jumps were rejected: they
need a program counter and fuel, a "code at offset `o`" invariant in place of
`exec_append`, and a run-time bound on a loop's pushes, comparable to
rewriting the compiler proof. Loops would also unblock the compiler's gaps
"storage copies of a dynamic array" and "`push()` of a struct".

## Status

| Stage | Status |
|---|---|
| **L1** Syntax, lowering and semantics (`LoopAnn`, `Stmt.loop`, `lowerLoops`, `TLoop`) | built |
| **L2** Typing (the loop cases of `Typing/`, by `TLoop.run_induct`) | built |
| **L3** Unwinding (`whileUnwind`, `loopExit`) | built |
| **L4** Invariant rules (`whileInvariantBox`, `whileInvariantDiamond`, `Fml.anonHavoc`, `Calculus/SoundLoops.lean`) | built; the diamond is slow in the closer |
| **L5** Quantified invariants | partly: `\forall T x; a -> c` clauses (`LoopQ`) under the box; open: quantified invariants under the diamond, and the solkey examples that need them (Ballot's `winningProposal`, BlindAuction; also blocked on `bytes32`, events) |
| **L6** Callbacks | built under the box (`ProvesC.invBox`, `ProvesC.loopExit`, unwinding; `docs/options.md`); no diamond over a loop that calls back can be sound |
| **L7** EVM | built with a structured loop instruction (above) |

`tests/solc/Loops.sol` is the fixture (`Examples/Tactics/LoopsImport.lean`);
`scripts/solc-ast.mjs` reads the `///` clauses above a loop as solkey's
`KeyNatspec.of` does (a clause may span lines; only `invariant`,
`decreases` and Lean's `unwind`). Counterexample search runs loops with fuel
(`Prog.runF`, `Tools/Counterexample.lean`), so a counterexample through a
loop is certified.

## Automation notes

- **Later counter instances.** A quantified premise is instantiated at
  counters introduced after it (`Calculus/CloseAll.lean`, after the closer
  opens the leaf's binders; anonymised counters are typed value
  projections), bounded by declaration, expression, candidate, application,
  binder and heartbeat limits (`Examples/Tactics/AllLeftLater.lean`).
- **ABI memory scans** (`Examples/Tactics/ArrayScans.lean`): signed and
  unsigned element ranges from solc-imported ABI premises with a supplied
  invariant (`i <= xs.length`; variant `xs.length - i` under the diamond).
  The combined signed diamond uses `sol_symex; sol_close`; its `sol_prove`
  version exceeds the declaration budget.
- **Demanded memory observations.** `foldMem2` applies the memory
  read/length/identity taclets as the scoped reducer forms each
  observation, keeping a result only when it does not grow the tree; the
  full optional result's equality is proved in `DecideTyped.lean`, so a
  failed write cannot become an unguarded read.
- **Rigid local conditions.** `Seq.refuteLanded` reads a literal-local
  guard back through its local updates (`Fml.substU`), with a 512-node cap
  per substitution; the live sibling stays an obligation
  (`Hyps.rigid_lift`), since a refuted guard alone does not prove the
  prefix succeeds. Ground conditions past the bounds keep both branches.
- **The fresh index is carried** (`Seq.runK`, `Hyps.maxIdxH`,
  `Hyps.fresh_eq_freshK`): asking `Hyps.fresh` at every step made a walk
  `O(n²)` in the kernel (a 1024-step walk 658k → 465k heartbeats).
- **Budgets are checked between compiled stages** of `Seq.prove`: nothing
  checks heartbeats between `sol_prove`'s kernel lemma and the end of the
  declaration, so a stage past the budget is reported and no longer stage
  runs.
- **Reads past exposing updates** (`exposeBound` = 5,
  `Calculus/ReadBounds.lean`, `LTm.exposeDepth`): over an unknown history a
  read through an update exposing a slot past a live end (`Op2.exposes`)
  branches, growing the elimination about sevenfold per update; past the
  bound an early read stays lazy and a refutation is not asked
  (`LFml.refuteOk`).
- **Copy identities by their allocations.** A copy's root is formed over the
  memory without its writes (`LTm.stripW`, stopping at the newest `addM`;
  `copyRes`), where every word its writes land on folds to `true`
  (`guardQ`), since an identity depends on the heap typing alone
  (`SVal.copyStToM_H'`). Otherwise leaves double with each row of a
  binomial-style fill. `memFuel` is 256.
- **Walks in chunks.** `sol_prove (chunk := n)` (`Calculus/ProveChunked.lean`)
  checks a long walk `n` steps at a time, each chunk and leaf under its own
  heartbeat budget (the compiled walk proposing a chunk heeds none). On
  `binomialRowsNine` chunk 128 is the sweet spot (about 4 min, under 6 GiB;
  512 passes 14 GiB). The runner (`Frontend/Testing.lean`) chunks a walk of
  more than `oneCheckSteps` (1024) steps by `chunkSteps` (128).

## Open loop ports

solkey's four open loop ports are `tests/solc/OpenLoops.sol`
(`Examples/Tactics/OpenLoops.lean`; run one with
`node scripts/test-solidity.mjs --function f tests/solc/OpenLoops.sol`).

- `binomialFaithfulRowsSmall`: proved (demanded memory observations).
- `binomialRowsNine`: proved with chunk 128; through the runner it needs
  `--timeout-ms 1800000` (the default 300 s per contract is too short).
- `pushNoArgs2dLoop`: **not valid under `.solc` tails** — `array2d.push()`
  on a `uint[][]` recycles a shadow slot as it is (`pushSlot`), and
  `wt(storage)` clears only word arrays' shadow slots (`tightHB`), so a
  dangling `uint[]` can make `array2d[0].length == 43 + L`. Valid under
  `ValidTail .clean` (`docs/options.md` O6), which the runner states; in
  chunks its walk passes, but `sol_close` times out on each of its three
  asserts (45 stacked saves of one length slot, past `concreteDepth`, whose
  start is known only through premises formation-time folding does not
  read).
- `multiArrayFillByPushLoops`: open; `nests.push()` recycles a `Nest` whose
  `d` is a dangling array of unknown length, so the later loops' guards
  read unknown lengths. It needs a closer for exposed slots.
