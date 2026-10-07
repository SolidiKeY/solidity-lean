# Loops

`while`, `for`, `do … while`, `break`, `continue`: four decisions and the
stages that implement them. L1 to L4 are built (the
syntax, the lowering, the semantics, the typing, unwinding and the
invariant rules; `Examples/Tactics/Loops.lean`): a loop is unwound to the
bound its `/// @custom:key unwind k` clause gives (`LeanTaclet.whileUnwind`)
and left there (`LeanTaclet.loopExit`), or proved by its invariant
(`LeanTaclet.whileInvariantBox`, `whileInvariantDiamond`).
Background: `docs/kernel-port.md` (its topics "Modalities", "Semantics",
"One rule per statement" and "Conditions" are the decisions this plan
extends).

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
expression language; `LoopLowering` moves them to the `while` it produces, so
the invariant of a `for` or `do … while` holds at the head of that `while`,
also on the iteration a `break` or `return` ends.

Loops block Ballot and BlindAuction (after `bytes32` and events),
`MultiAuction.closeAuction` is `skip`ped, and the solc ports unroll by hand.
Lean's rules take solkey's names (`whileUnwind`, `whileInvariantBox`,
`whileInvariantDiamond`). They are `LeanTaclet` constructors while the solkey
pin (`RuleShapes.tacletOrigins`, `KeyTaclets.lean`) is before `ed7849d5b6`,
and become `Taclet` constructors when it moves past; what solkey lacks
(`loopExit`, the bound's end) stays a `LeanTaclet`.

## Decision 1: semantics, the least fixed point inside `Stmt.run`

- Add `Stmt.loop (a : LoopAnn C) (c : Val C .bool) (body : Prog C)`.
- `Stmt.run` stays total and structural. Its loop arm is
  `Loop.run (fun τ => Prog.run τ body) c σ`: the recursive call is on the
  subterm `body` under a binder, which structural recursion allows.
- `Loop.iterN n σ` runs at most `n` iterations and returns *running τ* or
  *done r*; *done* absorbs. `Loop.run` returns the *r* of any `n` at which
  the iteration is done (all such `n` agree), and a new halt,
  `Halt.diverge`, when none exists.
- `Modality.onHalt` is unchanged: a box accepts a divergent run, a diamond
  does not. This is the partial/total reading the "Modalities" topic gives
  the two modalities. The annotation `a` is invisible to `Stmt.run`.

Rejected:

| Option | Why not |
|---|---|
| Fuel everywhere (`Stmt.run n σ s`) | A `Nat` through every theorem that recurses on `Stmt.run`; box becomes `∀ n`, diamond `∃ n`, and monotonicity in `n` a lemma every proof needs. |
| A constant bound inside the loop only (fuel `2^257`) | Unwinding is not exact at the bound: a loop stopping at iteration `B + 1` is `diverge` while its unwinding is not, so `whileUnwind` is unsound for the diamond. |
| An inductive `Exec` beside `Stmt.run` | Two denotations. Every taclet's `Premise.Correct`/`SameOk` (`Calculus/SoundKit.lean`) is over `Prog.run`, the corpus is decided by kernel evaluation of it (`corpus_decide`), and the callback relation anchors to it (`ExecS.det`). `Stmt.run` is the only semantics. |
| `partial_fixpoint` | `Res = Except Halt` is not a CCPO, and the kernel cannot unfold the result. |

**Cost: computability.** The existential makes `Loop.run` classical, but
`@[implemented_by Loop.runImpl]` (a `partial def` that iterates until done,
which the kernel never sees) keeps `Stmt.run` compiled: `#eval` and `#run`
run loops (and do not return from one that never ends). Kernel reduction of a
loop-free program is unaffected, so `corpus_decide` and `Evm/Examples.lean`
keep working. A concrete loop is decided by `Loop.run_of_iterN : iterN n σ =
.inr r → Loop.run … σ = r` (`Prog.run_loop_of_iterN` for a block), with `n`
found by `#eval` and the iteration computed by `rfl`.

**Proofs that recurse on `Stmt.run`** take a loop's case from two lemmas:
`Loop.run_rel` (two loops whose iterations go in step from related states
run alike: `Prog.run_frame`) and `Loop.run_induct` (an invariant of the loop
head: `Stmt.run_wt`, `run_canon`, `run_tight`, `run_noPanic`,
`frame_of_within`); `Loop.run_unfold` is the unwinding. In more detail:

`Stmt.run_frame`/`Prog.run_frame` (`Semantics/Agree.lean`: states agreeing off
`ns` iterate alike), `Stmt.run_wt` (`Typing/Soundness.lean`: `RunWT … Γ` at
the loop head is the invariant, the body typed as a branch),
`Stmt.run_canon` and `Stmt.run_tight` (`Typing/Reachability.lean`,
`Typing/Constructibility.lean`; `reachable_iff` stays true, since a loop
reaches nothing a finite sequence of body runs does not), and
`Stmt.exec_run`/`ExecS` (`Semantics/Callback.lean`: a loop whose body has no
transfer is `det`). Set `Stmt.forks (.loop …) := Prog.hasTransfer body`, not
`true`: a forking statement with no `ExecS` constructor has no runs, so every
modality over it would hold vacuously. `Stmt.run_call_expand` is unaffected;
`stmt_sim` is out of the fragment at first ("The EVM"); `Stmt.read?` is
`none`; `Stmt.weight` is Decision 3.

**A loop that transfers, with callbacks**, has `ExecS` constructors
(`Semantics/Callback.lean`): the condition halts or is stuck, the loop
exits, iterates (`loopIter`), stops in its body, or diverges
(`loopDiverge`). An inductive relation has no derivation of an infinite run,
so `loopDiverge` over-approximates: a loop whose body pays may always
diverge. A box accepts a divergence, and the callback reading is box-only
(solkey's), so nothing is lost; a diamond over such a loop is never valid.
Each constructor requires `Prog.hasTransfer body`, so a loop that pays
nothing has only its deterministic run (`ExecS.det`), and
`Stmt.exec_run`, `ExecS.eq_run` and `ExecS.frame` keep their statements.

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

The cost: goals and invariants mention the flags; an invariant for a loop
with `break` must say what holds when `brk` is set.

## Decision 3: one rule per loop, chosen by an annotation

Unwinding and the invariant rule both apply to one loop. To keep "one rule
per statement" (`Stmt.complete`, `Rule.eq_step`, `Rule.premise_unique` in
`Calculus/Uniqueness.lean`), the choice is syntax. `LoopAnn C` is either
`.inv (I : Val C .bool) (dec : Option (Val C .uint))` (an invariant and an
optional variant) or `.unwind (k : Nat)`. `Stmt.step`
(`Calculus/Completeness.lean`) dispatches:

| Annotation | Box | Diamond |
|---|---|---|
| `.unwind (k+1)` | `whileUnwind`: `unfold [if (c) { body while[k] (c) body }]` | same |
| `.unwind 0` | `loopExit`: `Premise.check (c = false) []`, the goals "loop exited" (`c = false ⟹ ⟨[ ω ]⟩ φ`) and "unwound to the end" (`c = false`), by `Proves.checkLean` | same |
| `.inv I dec` | `whileInvariantBox`, below | `whileInvariantDiamond` with `dec = some v`; with `none`, `whileNoVariantDiamond`, the premise `done false` (sound, unprovable; solkey unwinds instead) |
| `.inv I dec`, a body with no frame | `whileClose`: `done false` | same |

In the source the annotation is solkey's specification (from solc's AST,
`scripts/solc-ast.mjs` reads the clauses from the source by the loop's `src`
offset, as solkey does, and the front end prints them above the loop:
`Examples/Tactics/LoopsImport.lean`),
`/// @custom:key invariant …` and `/// @custom:key decreases …` above the
loop, and, Lean only, `/// @custom:key unwind k` for the bound; a loop with
neither is `.unwind 0`.

`.unwind 0` is not `assert(!c)`: a failed `assert` panics, so running out of
unwindings would be a failure of the program rather than of the bound.

**The annotation is a `Val`, not a `Fml`**: `Fml` (`Update.lean`) contains
`Prog`, so a `Stmt` carrying one would make `Stmt`, `Term` and `Fml` one
mutual inductive. A boolean program expression is effect-free, lowered
exactly (`Val.lower_eval`), and how solkey's spec language compiles, but has
no quantifier: Ballot's `∀ q < p. proposals[q].voteCount ≤ winningVoteCount`
needs `Fml.all` (`docs/function-specs.md`) and a table of formulas outside
`Stmt` that the loop names by index.

**Termination** (`Calculus/Termination.lean`). `.unwind k` weighs
`(k + 1) · (c.cost + c.pen + Prog.weight body + 3)`, so `whileUnwind` gets
smaller; `.inv I _` weighs `c.cost + c.pen + Prog.weight body + I.cost + 2`,
and its premise (`body` alone, `ω` alone) is lighter than `loop :: ω` under
`2 ^ weight · (measure φ + 1)`. `Fml.step_wellFounded` and `symex_normalizes`
survive. Without the annotation, unwinding would copy the loop and no weight
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

`b` is KeY's `s#b` of `bType b = cond;`, a fresh local; `= TRUE` is
`Fml.eqD` (defined and equal). The cover is a branch's (`Premise.coverFml`):
`b = TRUE ∨ b = FALSE` under the diamond, `true` under the box, since Lean's
locals are untyped. `whileInvariantDiamond` binds the variant first,
`{ variant := dec ‖ b := cond }`, and the body's postcondition is
`inv = TRUE ∧ { b := cond } (b = TRUE → 0 <= dec ∧ dec < variant)`: **the
variant is checked only when the condition holds again**, as solkey checks
it. Lean reads `dec` where KeY compares it with a skolem (`dec = variant`),
so under the diamond `dec` must be defined wherever the invariant holds.

**The anonymising update `{anon(body)}`** is `Fml.loopAnon`
(`Semantics/Mutability.lean`), solkey's `#loopAnon`: `Fml.anon xs`, where
`xs = Prog.writes body` (the locals the body assigns or declares, the
lowering's flags included), each bound to anything or to nothing
(`State.anon`), and `{havoc}` inside it when the body writes storage or pays
(`Prog.within .nonpayable`, storage and ledger together). A body outside
`nonpayable` (memory, a push or a pop, an alias, an external call) has no
frame, and its loop closes to `false` (`whileClose`). The frame lemma is
`Prog.loopFrame_run`, from `Prog.frame_of_within`; `Fml.loopAnon_holds`
turns it into the premise at every loop head.

**The flags are typed by the invariant.** An anonymised `brk`, `ret` or
`first` may hold anything, but the condition reads it; `lowerLoops`
conjoins `f || !f` (defined exactly when `f` is a `bool`) to an invariant for
each flag the condition tests, which KeY's `boolean` type gives.

**Soundness** (`Calculus/SoundLoop.lean`). Box (`Stmt.loop_inv_box`): by
`Loop.run_induct`, every loop head is in the frame of the first and
satisfies the invariant; where the condition is `TRUE` the body's box keeps
it (and rules out a panic), where it is `FALSE` the rest's goal holds.
Diamond (`Stmt.loop_inv_diamond`): `Loop.run_variant` bounds the iterations
by the variant's value after the first, which is a `uint` below the one
before wherever the loop goes on; neither the condition (the cover) nor the
body (a diamond) can halt.

**In Lean.** `Premise.inv`, read by `Premise.invFml` (`Calculus/SoundKit.lean`),
so `sol_symex` steps it as any premise; `Proves.invLean` for a walk, its
goals `init` ("invariant initially valid") and `thn`, `els`, `cov` past
`Hyp.loopAnon` ("invariant preserved and used"), which the proof tree labels
as solkey does. `Hyp.anon` is the context's anonymising update.
`sol_close` reads `{anon(…)}` (`Close.holds_anon`, `State.getEnv_anon_cons`:
a read of an anonymised local is `anonRead (b x)`, a binding nobody knows);
`sol_decide` and `sol_prove`'s closer do not (`Fml.inL` is `false` on `anon`,
as on `havoc`), so `sol_prove` leaves such a leaf to `sol_close`. Under the
diamond the closer is slow: a counting loop closes, a loop with a `break`
(whose flag is read through the cover) and a sum do not within the default
heartbeats; their box versions close (`Examples/Tactics/Loops.lean`).

**Termination.** `.inv I _` weighs `c.cost + c.pen + Prog.weight body +
I.cost + 2`, and the premise (`body` alone, `ω` alone, under modal-free
`{anon}`, `{U}` and conditions) measures less than `loop :: ω`
(`Premise.measure_lt`, `Fml.loopAnon_measure`).

**Typing and declarations.** `Stmt.wt` requires `c.wt Γ`, the annotation's
values well-typed at `Γ`, and `Prog.wt Γ body = some Γb` with `Ctx.le Γ Γb`,
and returns `Γ`, as for `ite`. A local declared in the body is declared
again each iteration (`declLocal` overwrites, as solc re-initialises); it is
in the frame, and the invariant, typed at `Γ`, cannot name it.

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
a third arm in `ValOut`/`StmtOut` (`Evm/Correctness.lean`) for "out of fuel
at every fuel"; and a new bound on a loop's pushes, since
`L + pushesP P ≤ 2^64` no longer holds (the interpreter's `push` would revert
at `2^64` as solc does, or the bound becomes a run-time invariant of `Sim`).
That is comparable to rewriting `Evm/Correctness.lean` (about 2,300 lines).
**Decision:** `wtStmt` (`Evm/Compile.lean`) refuses a loop, as it refuses
memory, and `docs/compiler-verification.md` lists it. Loops also unblock its
gaps "storage copies of a dynamic array" and "`push()` of a struct", so the
EVM stage is worth doing once, for all.

## Plan

| Stage | Scope (files) | Risk |
|---|---|---|
| **L1 Syntax and semantics** (built) | `Syntax.lean`: `LoopAnn`, `Stmt.loop`, `RawStmt.while/for/doWhile/brk/cont`, the lowering of Decision 2, printers, `Stmt.quote`, `renameStmts`. `Semantics.lean`: `Halt.diverge`, `Loop.iterN`, `Loop.run`, `implemented_by`. `Semantics/Agree.lean`: `Stmt.vars`, `run_frame`. `Semantics/Callback.lean`: `forks`, `hasTransfer`. The quoters in `Calculus/Quote.lean`, `Calculus/Notation.lean`. | Done: `Stmt.run` stays structural (the loop arm calls the body's run under a binder), `#eval` runs `Loop.runImpl`. |
| **L2 Typing** (built) | The loop cases of `Typing/{Soundness,Reachability,Constructibility}.lean`, by induction on `iterN`. | Done. |
| **L3 Unwinding** (built) | `Calculus/Rules.lean` (`whileUnwind`, `loopExit`), `Completeness`, `Uniqueness`, `Termination` (weight), `Logic` (`Proves.checkLean`), `RuleSoundness`, `RuleSyntax` (the clause in a taclet, `if` without `else`, a program spliced into a block), `SolkeyFragment`. Examples: the hand-unrolled solc ports as real loops. | Low to medium: the weight arithmetic is new. |
| **L4 Invariant rule** (built) | `Update.lean` (`Fml.anon`, `State.anon`), `Semantics/Mutability.lean` (`Prog.loopFrame`, `Fml.loopAnon`, `Prog.loopFrame_run`: the frame is `Stmt.within`'s, no new run lemma), `Calculus/Rules.lean` (`whileInvariantBox`, `whileInvariantDiamond`, `Premise.inv`), `SoundKit` (`Premise.invFml`), `SoundLoop`, `Logic` (`Hyp.anon`, `Proves.invLean`), `Termination`, `Close` (`holds_anon`). `sol_decide` does not read `anon`. Examples: a counting loop (both modalities), a sum with a closed form, a loop with `break`. | Done; the diamond is slow in the closer. |
| **L5 Quantified invariants** | After `Fml.all` in an invariant: a table of invariants by index. Ballot's `winningProposal`. | High: depends on `Fml.all` and `grind` instantiation. |
| **L6 Callbacks** | `Calculus/Callback.lean` (the loop rules under `ProvesC`; the `ExecS` constructors are L1's). | Medium. |
| **L7 EVM** | `Evm/{Machine,Compile,Correctness}.lean`, as above. | High: the largest stage. |

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
  now runs `Prog.runFuel` (`Tools/Counterexample.lean`): each loop at most
  `loopFuel` iterations, `unknown` past them, proved to agree with
  `Prog.run` where it returns (`Prog.runFuel_sound`).  The kernel reduces
  it, so a counterexample through a loop is certified
  (`Examples/Verify.lean`).
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
  `Calculus/ProofTree.lean`), `cov` proved by `closeTrue`, as `splitBox`.
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
| `Calculus/Uniqueness.lean` | 151.6 s, 151.6 s | 154.7 s | +2% |
| `TestSuite/Derived14.lean` | — | 75.3 s | — |

Both within 10%.  `Derived14` has no master time under this method (W7's
155 s predates its review), so it is recorded for the next lane.
