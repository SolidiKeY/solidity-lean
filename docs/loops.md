# Loops

`while`, `for`, `do … while`, `break`, `continue`: four decisions and the
stages that implement them. L1 to L4 are built (the
syntax, the lowering, the semantics, the typing, unwinding and the
invariant rules; `Examples/Tactics/Loops.lean`): an unannotated loop is unwound
within the proof search budget (`Taclet.whileUnwind`). An explicit
`/// @custom:key unwind k` clause limits it to that bound
(`LeanTaclet.loopExit`), or it is proved by its invariant
(`Taclet.whileInvariantBox`, `whileInvariantDiamond`).
Background: `docs/kernel-port.md` (its topics "Modalities", "Semantics",
"One rule per statement" and "Conditions" are the decisions this plan
extends).

## Later counter instances

Quantified premises can now be instantiated at counters introduced after the
premise was stated. `Calculus/CloseAll.lean` applies the universal proof only
after the closer opens the leaf's binders; anonymised counters are typed
value projections. The search proves range/guard arguments and is bounded by
declaration, expression, candidate, application, binder and heartbeat limits.
`Examples/Tactics/AllLeftLater.lean` proves an actual invariant loop that reads
`balances[i]` from an earlier quantified premise. The loop still supplies its
invariant. General ABI memory-array scans remain open where their reads and
lengths do not yet normalize together; this does not resolve the four large
open loop ports below.

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

Loops block Ballot and BlindAuction (after `bytes32` and events),
`MultiAuction.closeAuction` is `skip`ped, and the solc ports unroll by hand.
Lean's rules take solkey's names (`whileUnwind`, `whileInvariantBox`,
`whileInvariantDiamond`). At the current pin they are `Taclet` constructors,
with their correspondence recorded by `RuleShapes.tacletOrigins`. Lean retains
its explicit unwind bound, capture-free conditions, boolean-expression
invariants, conservative frame restrictions and unsigned variant. KeY accepts
formula invariants and an unbounded integer variant; those broader shapes are
not claimed here. The origin table checks inventory coverage; soundness comes
from the existing kernel theorems, and upstream shape correspondence from the
recorded review. What solkey
lacks (`loopExit`, the bound's end) stays a `LeanTaclet`.

## Typed tuple measures

Loop annotations also accept `/// @custom:key decreases (outer, inner)` and
longer tuples of unsigned values. `LoopMetrics C Γ (n + 2)` retains every
component at its type and scope. Each component passes the existing capture-free
loop-expression check before the annotation is constructed. Empty, singleton
raw tuples, nested tuples, wrong types, unknown names and expressions requiring
statements are refused. Ordinary parenthesized scalar expressions keep their
existing meaning. Clause uniqueness and invariant/unwind restrictions still
apply.

For ordinary diamond loops with an admitted body frame, no break flag and no
quantified invariant clauses, `whileInvariantLexDiamond` snapshots every metric
at the loop head and after a successful body. Its verification condition requires
all components to be defined, the invariant to be preserved, and the new tuple
to be strictly smaller lexicographically. Every successful body turn must decrease,
including the final turn. Later components may increase when an earlier one
falls. Two- and three-component measures use separate typed ghost locals, with
no bounded-word packing. Unsupported diamond shapes remain pending.

The explicit Lean-only `loopLexErase` step retains the existing invariant safety
path for box proofs and other admitted readings. It preserves quantified clauses
and the break flag and does not check metric decrease. Callback erasure has its
own execution/capture theorem; callback diamonds have no lexicographic bridge.
The supported ordinary diamond path cannot bypass its metric checks by erasure.
Ordinary diamonds still accept exhaustion: this rule does not construct a strict
successful-termination certificate.

A source `do … while` also carries the lowering's synthetic first-iteration
flag. A user invariant such as `x <= 2` does not relate that flag to `x`, so
havoc admits `first = true, x = 0` and rejects a decrementing body. The actual
source initialization `x = 2` is safe; that abstract head is not a reachable
counterexample. This invariant limitation currently leaves the tuple do-while
countdown pending. The source tests also reject the actual zero-start underflow.
A future phase rule must check its initial relation and preservation. A checked
strengthening `first → condition` could cover initially true pure guards; general
do-first cases require separate entry-phase reasoning.

For strict successful termination, `Semantics/LexMetrics.lean` supplies
`LoopMetrics.SourceCertificate I G actualLoop`. Its indexed constructor retains
the check of the tuple actually stored on that loop. The semantic invariant `I`
and postcondition `G` are explicit proof parameters; they are not implicitly
identified with the annotation clauses. An initial proof of `I` is required to
project an actual `.ok` result. Every invariant head must define all components,
every live body must succeed and preserve `I`, and every body turn must decrease
lexicographically. Later components may increase when an earlier one decreases;
no bounded-word packing is used.

These sufficient conditions are conservative at break/return and exit heads.
Exhaustion, divergence and revert are not successful witnesses. The certificate
reads `Stmt.run`; callback total termination needs its own proof. A successful
run proposition alone cannot identify an annotation, since execution erases it;
source tools must retain the syntax-indexed certificate for claims that a declared
tuple was checked. `Examples/LexMetrics.lean` proves an actual annotated source
program succeeds and rejects bad metric certificates. Imported NatSpec coverage
is in `scripts/lex-metrics.test.mjs`. Declaration-ID renaming preserves shadowed
source locals and the innermost loop annotation binding; the additional scope
regressions are in `scripts/source-shadowing.test.mjs`. Automatic strict
certificates, broader metric sorts and total recursive termination remain open.

## Decision 1: semantics, the least fixed point inside `Stmt.run`

Since the intrinsic refactor the run is typed (`Semantics/Run.lean`, over
`State C Γ`; `docs/intrinsic.md`): the names below are its, and the loop's
body is a scope whose locals are popped each iteration.

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
transfer is `det`). Set `Stmt.forks (.loop …) := Prog.hasTransfer body`
(`Stmt.forksIn pay (.loop …) := Prog.callsBack pay body` since
`docs/options.md`'s O1), not
`true`: a forking statement with no `ExecS` constructor has no runs, so every
modality over it would hold vacuously. `stmt_sim` is out of the fragment
("The EVM").

**A loop that transfers, with callbacks**, has `ExecS` constructors
(`Semantics/Callback.lean`): the condition halts, the loop
exits, iterates (`loopIter`), stops in its body, or diverges
(`loopDiverge`). An inductive relation has no derivation of an infinite run,
so `loopDiverge` over-approximates: a loop whose body pays may always
diverge. A box accepts a divergence, and the callback reading is box-only
(solkey's), so nothing is lost; a diamond over such a loop is never valid.
Each constructor requires `Prog.callsBack J.pay body` (`Prog.hasTransfer`
before `docs/options.md`'s O1), so a loop where nothing calls back has only
its deterministic run (`ExecS.det`), and
`Stmt.exec_run` and `Stmt.eq_run` keep their statements.

## Decision 2: `break`, `continue`, `for`, `do … while` are lowered

The elaborator lowers them and the kernel sees only `Stmt.loop`. `Res` and
`Halt` gain nothing (beyond `diverge`), so no `cases` on an outcome gets a
new arm. This is the choice `return` already made (no abrupt completion in
`Stmt.run`; `lowerReturns` in `Syntax.lean`), and how KeY's loop scope works:
a boolean records the abrupt completion.

The pass is solkey's `LoopLowering`, shape for shape (the table in "What
solkey has"), as `lowerLoops` in `Syntax.lean`:

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
`Calculus/Taclet.lean`), the choice is syntax. `LoopAnn C Γ` has scalar
`.inv` and tuple `.invLex` invariant annotations (both retaining break flags and
quantified clauses), `.unwind (k : Nat)` and `.auto`. `Stmt.step`
(`Calculus/Step.lean`, its loop arm `loopStep` in
`Calculus/Blocks.lean`) dispatches:

| Annotation | Box | Diamond |
|---|---|---|
| `.auto` | `whileUnwind`: one iteration followed by the same automatic loop | same |
| `.unwind (k+1)` | `whileUnwind`: `unfold [if (c) { body while[k] (c) body }]` | same |
| `.unwind 0` | `loopExit`: `Premise.check (c = false) []`, the goals "loop exited" (`c = false ⟹ ⟨[ ω ]⟩ φ`) and "unwound to the end" (`c = false`), by `Proves.check` (walk: `apply checkLean r`) | same |
| `.inv I dec` | `whileInvariantBox`, below | `whileInvariantDiamond` with `dec = some v`; with `none`, `whileNoVariantDiamond`, the premise `done false` (sound, unprovable; solkey unwinds instead) |
| `.inv I dec`, a body with no frame | `whileClose`: `done false` | same |
| `.invLex I metrics false []`, with a frame | `loopLexErase`, then the invariant safety rule | `whileInvariantLexDiamond`: all components defined and strict decrease after every successful body turn |
| Other `.invLex` shapes | `loopLexErase`, then the existing invariant rule | erasure reaches the conservative pending path; callback diamonds have no lexicographic bridge |

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

**The annotation is a `Val`, not a `Fml`**: `Fml` (`Update.lean`) contains
`Prog`, so a `Stmt` carrying one would make `Stmt`, `Term` and `Fml` one
mutual inductive. A boolean program expression is effect-free, lowered
exactly (`Val.lower_evalT`, `Calculus/LowerRun.lean`), and how solkey's spec language compiles, but has
no quantifier: Ballot's `∀ q < p. proposals[q].voteCount ≤ winningVoteCount`
needs `Fml.all` (`docs/function-specs.md`) and a table of formulas outside
`Stmt` that the loop names by index.

**Termination** (`Calculus/Termination`, retired with it at W4 `calc-del`
of `docs/intrinsic.md`: the scoped strategy is fuelled). `.unwind k` weighs
`(k + 1) · (c.cost + c.pen + Prog.weight body + 3)`, so `whileUnwind` gets
smaller; `.inv I _` weighs `c.cost + c.pen + Prog.weight body + I.cost + 2`,
and its premise (`body` alone, `ω` alone) is lighter than `loop :: ω` under
`2 ^ weight · (measure φ + 1)`. `Fml.step_wellFounded` and `symex_normalizes`
survived the loops lane. Without the annotation, unwinding would copy the loop and no weight
could decrease.

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

**Modifies sets** (built 2026-10-25).  KeY frames a loop by its
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

*Review (2026-10-25).*  A read-only pass found no soundness gap (every
statement whose modifies set is `some L` checked against its run; every
statement that calls back has `none`).  Fixed after it: the anonymising
binder and update are produced under the box under both modalities, as
`{havoc}` is, so a diamond loop's context stays one `closeTrue` reads
(`Hyps.boxOnly`); `Locs.union` names each root once; `#latex_program`
prints the roots (`symDoc`'s `Op2.anon` arm); the `dl!` reader refuses a
root that is not a state variable; `docs/options.md` and `ProvesC.invBox`'s
docstring no longer describe the frame as a flag.  Left as it is: the
binder's printed name `anonStorage` is the same in nested loops (it is a
hidden binder; the update names it positionally).

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
does. (Before the intrinsic refactor: `Premise.invFml`, `Proves.invLean`,
`Hyp.loopAnon` and a third goal `cov`.)
`sol_close` reads `{anon(…)}` (`CloseS.holds_anon`, `CloseS.anon_cons`:
an anonymised local is set to `b x`, a binding nobody knows);
`sol_decide` and `sol_prove`'s closer do not (`Fml.inLS` is `false` on `anon`,
as on `havoc`), so `sol_prove` leaves such a leaf to `sol_close`. Under the
diamond the closer is slow: a counting loop closes, a loop with a `break`
(whose flag is read through the cover) and a sum do not within the default
heartbeats; their box versions close (`Examples/Tactics/Loops.lean`).

**Termination** (retired at W4 `calc-del`). `.inv I _` weighed `c.cost + c.pen + Prog.weight body +
I.cost + 2`, and the premise (`body` alone, `ω` alone, under modal-free
`{anon}`, `{U}` and conditions) measured less than `loop :: ω`
(`Premise.measure_lt`, `Fml.loopAnon_measure`).

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

The machine has only relative forward jumps, so `exec` (`Evm/Machine.lean`)
is structural; the one loop solc emits for the current fragment
(`checked_exp_helper`'s) is unrolled 255 times (`expLoop`, `Evm/Exp.lean`).
Backward jumps need absolute `JUMP`/`JUMPDEST` with a program counter and
fuel; a "code at offset `o` is `compile s`" invariant in place of
`exec_append` and the skip-count lemmas that every case of `stmt_sim` uses;
a third arm in `ValOutT` (`Evm/SimLemmas.lean`)/`StmtOut` (`Evm/Stmt.lean`) for "out of fuel
at every fuel"; and a new bound on a loop's pushes, since
`L + pushesP P ≤ 2^64` no longer holds (the interpreter's `push` would revert
at `2^64` as solc does, or the bound becomes a run-time invariant of `Sim`).
That is comparable to rewriting the compiler's correctness proof (about 2,300 lines).
**Decision** (until 2026-10-23): `inFrag` (`Evm/Compile.lean`) refused a
loop.  **Built** (2026-10-23, L7 without absolute jumps): a loop is one
structured instruction, `LOOP cond body` (`Instr.loop`), so `exec` stays
structural and the skip-count lemmas stand; its turns are `loopRun`'s,
classical as `TLoop.run`'s, a fault where no number of them ends it (the
fourth outcome, `StmtOut.diverge`); the simulation is by induction on the
turns (`loop_sim`, `Evm/Correct.lean`).  The fragment takes a loop whose body
pushes, pays and shrinks nothing and keeps the fragment's flags
(`docs/compiler-verification.md`); lowering `LOOP` to `JUMPDEST`/`JUMP` is
an assembler's step, as absolute targets already are. Loops also unblock its
gaps "storage copies of a dynamic array" and "`push()` of a struct", so the
EVM stage is worth doing once, for all.

## Plan

The stages' files are named as they were when each was built; the intrinsic
refactor (`docs/intrinsic.md`) moved the loop onto the scoped syntax and the
typed run (`TLoop`, `Semantics/Run.lean`), its rules onto `Calculus/Blocks.lean`
and their soundness onto `Calculus/SoundLoops.lean`.

| Stage | Scope (files) | Risk |
|---|---|---|
| **L1 Syntax and semantics** (built) | `Syntax.lean`: `LoopAnn`, `Stmt.loop`, `RawStmt.while/for/doWhile/brk/cont`, the lowering of Decision 2, printers, `Stmt.quote`, `renameStmts`. `Semantics.lean`: `Halt.diverge`, `Loop.iterN`, `Loop.run`, `implemented_by`. The untyped frame kit (deleted at W10): `Stmt.vars`, `run_frame`. `Semantics/Callback.lean`: `forks`, `hasTransfer`. The quoters in `Syntax/Quote.lean`, `Calculus/SurfaceNotation.lean`. | Done: `Stmt.run` stays structural (the loop arm calls the body's run under a binder), `#eval` runs `Loop.runImpl`. |
| **L2 Typing** (built) | The loop cases of `Typing/{Soundness,Reachability,Constructibility}.lean`, by induction on `iterN`. | Done. |
| **L3 Unwinding** (built) | `Calculus/Rules.lean` (`whileUnwind`, `loopExit`), `Completeness`, `Uniqueness`, `Termination` (weight), `Logic` (`Proves.checkLean`), `RuleSoundness`, `RuleSyntax` (the clause in a taclet, `if` without `else`, a program spliced into a block), `SolkeyFragment`. Examples: the hand-unrolled solc ports as real loops. | Low to medium: the weight arithmetic is new. |
| **L4 Invariant rule** (built) | `Calculus/Fml.lean` (`Fml.anon`), `Update.lean` (`State.anon`), `Calculus/Blocks.lean` (`Prog.frame`, the frame `Stmt.within`'s), `Calculus/Rules.lean` (`whileInvariantBox`, `whileInvariantDiamond`, `Premise.inv`), `SoundKit` (`Premise.invFml`), `SoundLoop`, `Logic`, `Termination`, `CloseScoped` (`CloseS.holds_anon`). `sol_decide` does not read `anon`. Examples: a counting loop (both modalities), a sum with a closed form, a loop with `break`. | Done; the diamond is slow in the closer. |
| **L5 Quantified invariants** | After `Fml.all` in an invariant: a table of invariants by index. Ballot's `winningProposal`. | High: depends on `Fml.all` and `grind` instantiation. |
| **L6 Callbacks** | `Calculus/Callback.lean` (the loop rules under `ProvesC`; the `ExecS` constructors are L1's). | Medium. |
| **L7 EVM** (built, 2026-10-23) | `Evm/{Machine,Compile,Sim,Stmt,Correct}.lean`: `Instr.loop`, `loopRun`, `StmtOut.diverge`, `loop_sim`; loops that push, pay or shrink stay out. | Done with a structured loop instruction rather than absolute jumps. |

L1 to L4 make loops provable. L5 is what Ballot and BlindAuction need once
their other blockers (`bytes32`, events, `keccak256`) are gone. L3 and L4
each add a `docs/solkey-feedback.md` entry: the rules solkey's plan asks
for, with their soundness side conditions (the frame, the cover, the
variant bound).

## L1–L4 review (2026-10-07)

A finder and a skeptic per area; what the skeptic confirmed, fixed:

- **A `return` inside a loop on import.** `solc_import` lowered a body's
  `return`s without its loops first, so a public function with one was
  refused.  It now runs `lowerLoops` before `lowerReturns`, as `contract!`
  and solkey's `ExpandFunctionBody` do (`Frontend/Import.lean`,
  `lowerBodyLoops`); a body with such a loop is renamed fresh first, so a
  `for`'s declaration spliced over the statements after the loop does not
  clash with a sibling `for (uint i …)`.  Pinned by `loopNestedReturn`
  (solkey's) and `returnBeforeSiblingLoop` in `tests/solc/Loops.sol`.
- **Unbounded runs in the counterexample search.** `Fml.eval3` ran programs
  through `Prog.run`, whose compiled `Loop.runImpl` heeds no heartbeats.  It
  now runs the typed run with fuel, `Prog.runF`
  (`Semantics/RunFuel.lean`, read by `Tools/Counterexample.lean`):
  each loop at most `loopFuel` iterations, `unknown` past them, proved to
  agree with `Prog.run` wherever it does not say `diverge`
  (`Prog.runF_approx`).  The kernel reduces it, so a counterexample
  through a loop is certified (`Examples/Verify.lean`).
- **Loop specifications as solkey reads them.** `scripts/solc-ast.mjs`
  joins the `///` lines above a loop and splits them at a line that starts
  with a tag, as `KeyNatspec.of`: a clause over two lines is kept whole
  (`invariantTwoLines`).  It reads them only where the loop starts its line,
  and refuses a directive other than `invariant`, `decreases` and Lean's
  `unwind`.  `--source` resolves in this repository first, needs `--out`,
  and `--wrapper` names the importing module (the ctor lane's flags, so the
  two merge); `Examples/Tactics/LoopsImport.lean` names the command.
- **The fixture.** `tests/solc/Loops.sol` says which clauses (`unwind`) and
  functions are Lean's own, and has solkey's
  `invariantVariantSkipsBreakIteration` with its `break`.  Five of its seven
  obligations are proved; `forContinueStillUpdates` (`sol_symex` passes
  `simp`'s step bound, `sol_prove` `Derive.budget`) and
  `invariantVariantSkipsBreakIteration` (the diamond's cover) are named in
  `LoopsImport.lean` as not proved.
- **A condition that needs a capture** (a call, a cast, a narrow operation,
  a constructor) is refused with a message that says so, and the
  restriction is written above (Typing and declarations) and in the rule
  map.
- **`invBox`**: under the box the invariant rule has solkey's two goals past
  `init` in the walk and the proof tree (`Calculus/Symex.lean`,
  `Calculus/ProofTree.lean`), its then third goal `cov` proved by
  `closeTrue`, as `splitBox` did (the scoped rule has no `cov`).
- **Pins.** `#taclet whileNoVariantDiamond`, `#step` pins of `whileClose`
  and `whileNoVariantDiamond` firing, the `sol_derive?` walks of an unwound
  loop and an invariant loop (`Examples/ProofTree.lean`), a loop inside a
  `try` clause lowered (solkey's `LoopLowering` leaves it,
  `docs/solkey-feedback.md` §10).
- **Wording.** Memory is refused for an invariant as in solkey; push, pop,
  alias and external call are Lean's own refusals (`Stmt.within`).
  `ed7849d5b6` is the commit that added loops, after the pinned
  `1b4341a303`.  The modifier contract of several `_;` is `ModifierRuns`
  in `Examples/Tactics/Loops.lean` only.  `docs/README.md`,
  `docs/solc-alignment.md`, `docs/module-map.md` and
  `scripts/solkey-port.mjs` describe loops as built.

**Cost.**  After the fixes, the whole `Solidity` target rebuilt, then
`Derived1`, `Derived12`, `Derived14` and `SolkeyTestSuite.lean` checked
clean one at a time: `Report.lean`'s pin still reads 435 derived.  Each
file copied to a scratch module with `set_option Elab.async false`, timed
by `IO.monoMsNow` at its first and last command, load average under 1 (the
other lanes idle); master `2979bb8` is the ctor lane's measurement under
the same method (`docs/testsuite-proofs.md`, "Constructors review"):

| File | master `2979bb8` | `loops` | change |
|---|---:|---:|---:|
| `Examples/Tactics/Calls.lean` | 130.3 s, 120.9 s | 120.8 s | −4% |
| `Calculus/Uniqueness` | 151.6 s, 151.6 s | 154.7 s | +2% |
| `TestSuite/Derived14.lean` | — | 75.3 s | — |

Both within 10%.  `Derived14` has no master time under this method (W7's
155 s predates its review), so it is recorded for the next lane.

## Open loops lane (2026-10-20): `SolcLoopsOpen.sol`

Running notes of the `open-loops` lane on solkey's four open loop ports
(`Solidity/Scratch/open/SolcLoopsOpen.sol`, run by
`node scripts/test-solidity.mjs --json --function f`; heartbeats are
`maxHeartbeats` units, `IO.getNumHeartbeats / 1000`).

**Baseline** (master `ee769637`, runner, default 200000 heartbeats):

| Function | Status | Wall | Peak RSS |
|---|---|---:|---:|
| `pushNoArgs2dLoop` | error, timeout at `whnf` | 68 s | 6.8 GB |
| `multiArrayFillByPushLoops` | killed by the runner's 900 s limit (no heartbeat check reached) | > 900 s | — |
| `binomialFaithfulRowsSmall` | error, timeout at `isDefEq` | 90 s | 1.5 GB |
| `binomialRowsNine` | error, timeout at `isDefEq` | 80 s | 1.5 GB |

**`pushNoArgs2dLoop` is not valid in the model.**  `array2d.push()` on a
`uint[][]` recycles the first shadow slot as it is (`pushSlot`,
`Semantics/Storage.lean`; solkey's `storagePushLengthSave`), and
`wt(storage)` clears only the shadow slots of word arrays (`tightHB`,
`Semantics/StorageWt.lean`): a reachable storage with `array2d.length == 0`
may hold a dangling `uint[]` of length `L > 0` past the end, and then
`array2d[0].length == 43 + L`.  Its walk leaves three leaves (the three
asserts); `assert(ll == 43)` is false there (true under clean tails,
`ValidTail .clean`, `docs/options.md` O6), so the best `⊢` can report is
`pending`.

**Where its heartbeats go** (`sol_prove`'s walk at 1024 steps, measured in
a scratch module):  compiled walk 65k (plus about 45k for the failed 128,
256 and 512 stages), kernel check 658k.  Of the kernel's: `Hyps.fresh`,
which wraps and scans the whole context at every step, about 200k (the
same walk with a constant fresh index: 458k); the three leaves 24–28k each
in isolation; the 94 refutations (47 splits, the first branch of each
tried in vain) the rest with the walk.  A refutation alone, checked in
isolation late in the loop, is about 108k (cached across the walk).
Slicing the context's premises before `toLS` (by the binders they read,
through the updates) left the kernel total unchanged (675k): the
refutations' cost is not in the premises' terms.

**`binomial*`**: under the diamond a refutation must also prove every
memory allocation's landing obligation of the history, and the memory
terms are trees that double with each `rows[i][j] = rows[i-1][j-1] +
rows[i-1][j]` (a write reading the memory twice): at 133 context entries
(`binomialFaithful(3, 1)`) the refutation is past `normalizationSize`
(24000 nodes) and fails, so the outer loop's guard is never refuted and the
walk unwinds until its budget runs out.  Slicing premises does not help:
the obligations are conjuncts the diamond asks, not premises.

**`multiArrayFillByPushLoops`**: `nests.push()` recycles a `Nest` whose
`d` is a dangling array of unknown length, so the second and third loops'
guards read unknown lengths; the history is unknown (`Op2.exposes`), and
the refutation of the second loop's guard at four to six stacked storage
updates (within `normalizationDepth` 12, `boundsOk` true) overflows the
interpreter's stack in the language server, and runs past 15 minutes in
the runner.

**The fresh index, carried** (`Seq.runK`, `Calculus/ProvesDerive.lean`).
Each step of the walk asked `Hyps.fresh`, which wraps the whole context
around the goal and scans it (`Fml.maxIdx`): a walk of `n` steps over a
context that grows with it costs the kernel `O(n²)`.  The walk now carries
the context's largest index (`Hyps.maxIdxH`, `max`ed with each entry it
adds) and asks `freshK k φ`, which is `Hyps.fresh` by `Hyps.maxIdx_wrap`
(`Hyps.fresh_eq_freshK`); `run` is `runK` from `H.maxIdxH`, so
`residueWithin` and its callers are unchanged.  Measured:

| | before | after |
|---|---:|---:|
| `pushNoArgs2dLoop`, kernel check of the 1024-step walk | 658k hb, 44.8 s | 465k hb, 29.9 s |
| `TestSuite/Derived17.lean` (whole file, alone) | 100.9 s | 97.1 s |
| its heaviest, `returnLeavesNestedLoops` (interpretation + type checking) | 14.8 s + 63.8 s | 13.6 s + 61.5 s |
| `Examples/Tactics/Loops.lean` | 24.8 s | 24.8 s |
| `Examples/Tactics/LoopsImport.lean` | 14.3 s | 13.8 s |

(Scratch copies under `set_option Elab.async false`, timed by
`IO.monoMsNow` at their first and last command; peak RSS 8.2 GB for
`Derived17`, 3.0 GB `Loops`, 1.7 GB `LoopsImport`, unchanged.)

**Heartbeats past the budget.**  `returnLeavesNestedLoops` passes with its
kernel check past the default 200000 heartbeats: nothing checks the budget
between `sol_prove`'s kernel lemma and the end of the declaration, so a
check there (proposal (c) of the slicing lane) fails it.  `Seq.prove`
therefore checks only between its compiled stages: a stage that ran past
the budget is reported by its bound, and no longer stage is run.

**Reads past exposing updates** (`exposeBound`,
`Calculus/ReadBounds.lean`).  Over an unknown history, a read through an
update that exposes a slot past a live end (`Op2.exposes`: an empty push of
a reference element, a pop, a shrink) branches on whether it is the exposed
slot, and the elimination's output grows about sevenfold with each:
`multiArrayFillByPushLoops`' refutations at four to seven stacked
`pushSlot`s eliminate to 980, 4937, 35938 and 476239 nodes
(`normalizationDepth` admits 12).  The same elimination runs where `toLS`
forms a read (`LTm.literalRead`, `Calculus/DecideScoped.lean`): its
`toLS` took 16 ms, 184 ms and 5.5 s at four, five and six, and did not
return at seven (the runner's 15-minute hang, the server's stack overflow).
Both now read through at most `exposeBound` (5) such updates where the
history is not known (`LTm.exposeDepth`): an early read past it stays lazy,
and a refutation past it is not asked (`LFml.refuteOk`,
`Calculus/LeafDerive.lean`), the split's two branches walked.
`multiArrayFillByPushLoops` now ends in 112 s with "timeout at `sol_prove's
compiled walk, after its 1024-step stage`": its second loop's guard reads
the dangling `d`'s unknown length, which only a refutation at seven exposing
updates could bound, so the walk unwinds until the budget is gone.  Even a
complete walk would leave about 30 leaves past `stackSize` (12 to 14
storage updates over an unknown history): `pending` at best without a
closer for exposed slots.

**Proposal (b)** (a `require(len == 0)` making push histories known) does
not apply: `pushNoArgs2dLoop`'s three leaves stack 45 storage updates,
past `concreteDepth` (40) too, and its push at `next(storage, array2d)`
is an exposing `pushSlot` of a `uint[]` element, which no length fact makes
known (the exposed slot is the dangling one above); the same holds of
`nests.push()`.

**After the lane** (`a97fba7f`), the runner on the four:

| Function | Before | After |
|---|---|---|
| `pushNoArgs2dLoop` | error, timeout at `whnf`, 68 s, 6.8 GB | error, timeout at `whnf`, 67 s, 6.6 GB (kernel check 465k hb instead of 658k; not valid under `.solc` tails, `pending` at best) |
| `multiArrayFillByPushLoops` | no answer in 900 s | error, timeout at "`sol_prove`'s compiled walk, after its 1024-step stage", 112 s, 1.6 GB |
| `binomialFaithfulRowsSmall` | error, timeout at `isDefEq`, 90 s | error, timeout "after its 8192-step stage", 64 s, 1.6 GB |
| `binomialRowsNine` | error, timeout at `isDefEq`, 80 s | error, timeout "after its 8192-step stage", 66 s, 1.6 GB |

With the early-read bound in, the regression files again: `Loops` 24.5 s,
`LoopsImport` 13.6 s, `Derived17` 103.1 s and 100.0 s (two runs; peak RSS
3.0, 1.7 and 8.4 GB), `Examples/Tactics/Decide.lean` clean, and
`scripts/test-solidity.test.mjs`' failures the same four assertions as an
earlier master run (its solc/open test, 51 rows, passes).

**What is left.**  None of the four closes within the default budget, and
none can by the cheap routes:

- `pushNoArgs2dLoop` is not valid under `⊢` (the dangling `uint[]` above);
  under `ValidTail .clean` it is, and its walk would still need the
  kernel's 465k heartbeats cut to well under 100k: the walk carrying the
  closer's state (proposal (a)), since what is left is the refutations'
  `wrap`/`toLS` over the whole context at each split, the leaves, and the
  steps, each linear in the context.
- `multiArrayFillByPushLoops` needs a closer for exposed slots: its loops'
  guards read a recycled `Nest`'s unknown lengths, whose reads branch
  sevenfold per exposing update.
- The binomials need the memory's terms shared (a DAG-aware or
  value-naming reduction): under the diamond each refutation proves every
  allocation's landing obligation, and those terms double with each write
  that reads the memory twice.

**Lane `open-closer` (2026-10-21), the runner on the four again** (after
the closer's nonlinear, byte and hash clauses; `node scripts/test-solidity.mjs
--json --no-build --function f`, wall time with the build cached):

| Function | Result | Wall |
|---|---|---:|
| `pushNoArgs2dLoop` | error, timeout at `whnf` (200000 heartbeats) | 55 s |
| `binomialFaithfulRowsSmall` | error, timeout "after its 8192-step stage" | 57 s |
| `binomialRowsNine` | error, timeout "after its 8192-step stage" | 58 s |
| `multiArrayFillByPushLoops` | error, timeout "after its 512-step stage" | 38 s |

None is within reach of a closer clause: the first is the walk's kernel
check (465k heartbeats of a 200k budget, above), the binomials the
unshared memory terms of their refutations, and `multiArrayFillByPushLoops`
the unknown lengths of recycled slots its guards read (its search now
stops after the 512-step stage, in 38 s, where `a97fba7f` stopped after the
1024-step one in 112 s; still a timeout).  What is left stays the list
above.

## ABI memory scans (assurance M7)

`Examples/Tactics/ArrayScans.lean` checks signed and unsigned array element
ranges from actual solc-imported ABI premises after the loop introduces its
counter. The supplied `i <= xs.length` invariant suffices for the box scans;
the diamond checks both signed bounds and supplies `xs.length - i` as its variant.
The closer preserves memory observations across local captures and counter
updates, instantiates the earlier premise, then reuses its typed read witness.
These are supplied-invariant proofs, not inferred invariants or a resolution
of the four open loops above. The combined signed diamond uses
`sol_symex; sol_close` to avoid the walk's repeated expansion of separate
leaves; its `sol_prove` version still exceeds the declaration budget.

## Demanded memory observations (assurance M13)

`foldMem2` applies the existing memory read/length/identity taclets as the
scoped reducer forms each observation. Input size is bounded, and the result
is retained only when it does not increase the tree's node count. Equality
of the full optional result is proved in `DecideTyped.lean`, so an invalid
address or a failed write cannot become an unguarded successful read.

This resolves the original `binomialFaithfulRowsSmall` timeout: the actual
runner proves it in about seven seconds, and `Examples/Tactics/OpenLoops.lean`
checks the same pinned-solc source with `sol_prove` under the ordinary
declaration budget. No invariant annotation was added to that source.

The other three remain open under the same 200000-heartbeat runner budget:
`binomialRowsNine` times out after its 1024-step stage (about 58 seconds),
`multiArrayFillByPushLoops` after its 512-step stage (about 37 seconds), and
`pushNoArgs2dLoop` at kernel reduction (about 59 seconds). The push-loop
measurement uses the runner's clean-tail premise; the earlier `.solc`
counterexample remains relevant outside that reading. This is one repaired
timeout, not general loop invariant inference.

### Rigid local conditions (M19)

`Seq.refuteLanded` reads a literal-local guard back through its local updates,
using `Fml.substU` from `applyOnRigidFormula`. It avoids expanding unrelated
memory histories just to decide a loop counter. The live sibling remains a
proof obligation: `Hyps.rigid_lift` transports the condition through the
original context, including failure and exhaustion of its diamond updates.
A refuted guard alone cannot prove that the prefix succeeds.

The projection checks a 512-node cap on its condition and update before
each substitution, and checks the final condition too. Thus repeated
`x := x + x` assignments refuse before an exponential tree can accumulate.
Ground conditions outside the projection or closer bounds keep both branches;
non-ground guards retain the existing contextual refutation. Ignoring unused
premises can lose pruning when those premises contradict each other. The
regressions pin that conservative choice, memory writes in an eight-iteration
diamond loop, and a failing prefix that remains invalid.

On the original nine-row source an isolated compiled walk reached two leaves
at 2048 steps in about five seconds, versus the previous timeout after the
1024-step stage. This is a walk measurement, not a theorem: the public proof
construction then exceeded the session's 16 GiB RAM limit, including when run
alone. The original obligation stayed open until the next section.

### Identities by their allocations, and the walk in chunks (2026-10-23)

`binomialRowsNine` is proved (`Examples/Tactics/OpenLoops.lean`) by two
changes, and so is it by the solc runner (below).

**The leaf.** The reduction named a copy's root `copy(M, S)`, `M` the whole
memory before it. A row's writes address the row's root, and the next row's
root carries the memory those writes built, so the leaf grew with each row
by a factor of its writes: about 12 000 nodes at three rows, 76 000 at four,
86 million at five. An identity depends on the heap typing alone
(`SVal.copyStToM_H'`, `SVal.copyStToM_id_eq`), which a write keeps, so a
copy's root is now formed over the memory without its writes (`LTm.stripW`,
which keeps the copies and stops at the newest `addM`; `copyRes`,
`Op2.memRes`'s `.copy` arm, applied at formation by `foldRead2`) where every
word its writes land on folds to `true` (`guardQ`); else the root is kept
as it was, so that the copy's laws still read it. A memory's own landing guard is read the same way
(`UpdElem.toLS`, `seqMemL_tt_eval`), and so are a copy's laws: the spine test
(`LTm.onSpineS`), the length (`lenAtN`, `LTm.base_eval`) and the reads of a
fresh copy (`LTm.unstripAddr`, `LTm.read_unstrip`). `memFuel` is 256. The
five- and six-row binomials then close inside the walk; every rewrite is an
equation of reads, as before (`copyRes_eval`, `LTm.stripW_eval`).

**The walk.** About two thousand steps over a context of some 360 updates:
one kernel check of the whole walk (`sol_prove`) passed 14 GiB.
`sol_prove (chunk := n)` (`Calculus/ProveChunked.lean`) checks it `n` steps
at a time (`Seq.cutK`, `runK` whose spent step budget leaves the sequent as
a leaf; `Proves.of_cutWithin`), each chunk's kernel check and each leaf's
`sol_leaf; sol_close` under a heartbeat budget of its own (the compiled walk
that proposes a chunk heeds none, as `sol_prove`'s does not). On the nine
rows:

| chunk | kernel | compile and evaluate | final leaf | total | memory |
|---:|---:|---:|---:|---:|---|
| 32 | 240 s | 91 s | 50 s | 390 s | below 6 GiB |
| 128 | 146 s | 19 s | 75 s | 242 s | below 6 GiB |
| 512 | 90 s for the first three chunks | | | | past 14 GiB, stopped |

The theorem uses 128. What is left is the kernel's evaluation of the walk
itself, linear in the context at each step.

**The runner** (`Frontend/Testing.lean`) checks a plain walk of more than
`oneCheckSteps` (1024) steps in chunks of `chunkSteps` (128): `Seq.prove`
refuses such a walk before its kernel check (`oneCheck`, `longWalkNote`),
and `Seq.proveChunked` walks it, each leaf searched as `sol_prove?` searches
it (`Derive.searchLeaf`, the chunked walk's `close`).  `node
scripts/test-solidity.mjs --function binomialRowsNine --timeout-ms 1800000
tests/solc/OpenLoops.sol` reports it proved in 4 min 34 s (one core); the
default 300 s per contract is too short for it.

`pushNoArgs2dLoop` under clean tails: in chunks its walk now passes (one
kernel check of it was 465k heartbeats), and leaves its three asserts, each
over 45 stacked saves of one length slot (`pointer.length := pointer.length +
1`). `sol_close` times out on each: the reads of that slot stay symbolic at
formation, since its starting length is known only through the premises
(`array2d.length == 0`, clean tails), which formation-time folding does not
read, and the stack is past `concreteDepth`. `multiArrayFillByPushLoops`
remains open for the reason above.

Review (read-only finder, then the findings checked against the code): no
unsoundness, the compiled twins agree (`LTm.stripW_eq_stripWM`). Fixed from
it: a copy's root wrapped in an unfolded guard hid it from the copy's laws
(now kept unwrapped unless every guard folds); a chunk that made no step was
walked again up to `chunkFuel` times (now left, with a note); a goal that is
neither `⊢ φ` nor `⊨ᶠ φ` was left silently (now an error); a stopped leaf's
note now carries the closer's own error; and the docs claimed more than the
code for `LTm.stripW` (it stops at an `addM`) and for the heartbeat budget
(the compiled walk heeds none). Not changed: `memFuel` 256 and the guard
read at every memory update cost more evaluation per update; the full build
(below) measures it.
