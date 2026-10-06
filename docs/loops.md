# Loops

`while`, `for`, `do … while`, `break`, `continue`. This is a design plan:
four decisions and an ordered implementation plan. L1 and L2 are built (the
syntax, the lowering, the semantics, the typing; `Examples/Tactics/Loops.lean`):
until L3, a loop closes to `false` (`LeanTaclet.whileClose`).
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
`whileInvariantDiamond`) as `Taclet` constructors once the solkey pin moves
past `ed7849d5b6`; what solkey lacks (the bound on unwinding, below) is a
`LeanTaclet`.

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
| `.unwind 0` | `loopExit`: premise `c = false ∧ ⟨[ ω ]⟩ φ` (a new `Premise` shape) | same |
| `.inv I dec` | `whileInvariantBox`, below | `whileInvariantDiamond` with `dec = some v`; with `none`, the premise is `done false` (sound, unprovable; solkey unwinds instead) |

In the source the annotation is solkey's specification,
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

## Decision 4: the invariant rule and its soundness

Write `Ic` for `I.lower == true`, `c⁺`/`c⁻` for `c.lower == true`/`false`.
solkey's two goals (`whileInvariantBox`), under the context's update `{U}`:

```
  "invariant initially valid":     Γ ⟹ {U} Ic
  "invariant preserved and used":  Γ ⟹ {U} {anon F} (Ic → cover ∧ (c⁺ → [ body ] Ic) ∧ (c⁻ → [ ω ] φ))
  ──────────────────────────────────────────────────────
  Γ ⟹ {U} [ while (c) body; ω ] φ
```

solkey evaluates the condition into a fresh `b` (`[bool b = c;]`); Lean
lowers it, and `cover` is `Premise.cover` (`Calculus/Logic.lean`) of `c⁺`,
`c⁻`: `c⁺ ∨ c⁻` under the diamond, `true` under the box.
`whileInvariantDiamond` adds the variant: the hypothesis is
`Ic ∧ dec = v` with `v` fresh, and the body's postcondition
`Ic ∧ (c⁺ → 0 ≤ dec < v)`. **The variant is checked only when the condition
holds again** after the body, as solkey checks it: an iteration after which
the condition is false is the last, and under the flag lowering the
iteration a `break` ends sets `brk` without decreasing anything. The rule
fires on the first statement of the modality, so `{U}` is the context's
update, as in `CallbackTaclet` (`Calculus/Callback.lean`).

**The anonymising update `{anon F}`** generalises `Fml.havoc`/`Hyp.havoc`,
which replace storage and ledger and keep locals, memory and funds. `F` is
solkey's `LoopFrame`, computed from the body's syntax (`Prog.frame body`):
the locals it assigns or declares (the flags included), storage if it writes
a non-local, the ledger (and storage) if it calls anything but
`require`/`assert`/`revert`. **A body that allocates or writes memory has no
invariant rule**, as in solkey: the heap is not anonymised, and such a loop
can only be unwound. `holds σ (.anon F φ)` quantifies over every state
agreeing with `σ` off `F`; `Fml.havoc` is `anon` at storage + ledger. A
syntactic frame needs one lemma, `Prog.run_frameOff` (a run changes nothing
outside `Prog.frame body`), proved beside `Prog.run_frame`.

**Soundness, box.** Fix `σ` with `Γ` true, `τ₀ = U σ`. By induction on the
iteration count `n` of `iterN`, every loop-head state `τₙ` satisfies `Ic` and
agrees with `τ₀` off `F`: for `n = 0` by the first goal; for `n + 1`, `τₙ` is
one of the states the second goal quantifies over, so a body run ending
normally ends in `Ic`, and by `Prog.run_frameOff` agrees with `τₙ`, hence
`τ₀`, off `F`. The loop then ends done at `τₙ` with `c⁻` (the second goal's use case
gives `[ ω ] φ`), in a halt of the body or of `c`, or in `diverge`; the box
accepts the last two.

**Soundness, diamond.** The variant is non-negative and strictly decreasing
on every iteration after which the loop goes on, so the iteration is done
within `v + 1` steps and `Loop.run` is not `diverge`. Neither
the body (the preserved goal is a diamond) nor the condition (the cover
conjunct) can halt.

**In Lean.** A new `Premise` constructor `inv` whose `Premise.fml` is the
conjunction above (`Fml.stepAt` reads premises through `Premise.fml`, so
`sol_symex` needs no change), one `Proves` constructor per new shape (`inv`,
`exit`), and two cases in `LeanTaclet.sound`. `Stmt.inSolkey m (.loop …) =
false` (`Calculus/SolkeyFragment.lean`), so `Proves.toSolkey` is untouched
and `Proves.solkey_lt_calculus` gains a witness.

**Typing and declarations.** `Stmt.wt` requires `c.wt Γ`, the annotation's
values well-typed at `Γ`, and `Prog.wt Γ body = some Γb` with `Ctx.le Γ Γb`,
and returns `Γ`, as for `ite`. A local declared in the body is declared
again each iteration (`declLocal` overwrites, as solc re-initialises); it is
in `F`, and the invariant, typed at `Γ`, cannot name it.

The loop condition is **not** captured before the loop, since it must be
re-evaluated: the invariant rule lowers it (`Val.lower`), the unwinding's
`if` captures it per copy, and an `++` in it is an elaboration error, as
under `&&`.

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
| **L1 Syntax and semantics** | `Syntax.lean`: `LoopAnn`, `Stmt.loop`, `RawStmt.while/for/doWhile/brk/cont`, the lowering of Decision 2, printers, `Stmt.quote`, `renameStmts`. `Semantics.lean`: `Halt.diverge`, `Loop.iterN`, `Loop.run`, `implemented_by`. `Semantics/Agree.lean`: `Stmt.vars`, `run_frame`. `Semantics/Callback.lean`: `forks`, `hasTransfer`. The quoters in `Calculus/Quote.lean`, `Calculus/Notation.lean`. | Medium: structural recursion through `Loop.run`, and `#eval` under `implemented_by`. Check both first in a scratch file. |
| **L2 Typing** | The loop cases of `Typing/{Soundness,Reachability,Constructibility}.lean`, by induction on `iterN`. | Low: the same proof three times. |
| **L3 Unwinding** | `Calculus/Rules.lean` (`whileUnwind`, `loopExit`, `Premise.exit`), `Completeness`, `Uniqueness`, `Termination` (weight), `Logic` (`Proves.exit`), `RuleSoundness`, `RuleSyntax` printers, `SolkeyFragment`. Examples: the hand-unrolled solc ports as real loops. | Low to medium: the weight arithmetic is new. |
| **L4 Invariant rule** | `Update.lean` (`Fml.anon`, `State.anon`, frame lemmas), `Semantics/Agree.lean` (`Prog.frame`, `Prog.run_frameOff`), `Calculus/Rules.lean` (`whileInvariantBox`, `whileInvariantDiamond`, `Premise.inv`), `Logic`, `RuleSoundness`, `Termination`. Check whether `sol_decide` handles `anon` (a local in `F` is a fresh free local, anonymised storage a fresh free storage). Examples: a counting loop, a sum with a closed form. | Medium to high: `Prog.run_frameOff` over every statement, and extending `Decide`'s reduction to a second base storage. |
| **L5 Quantified invariants** | After `Fml.all` in an invariant: a table of invariants by index. Ballot's `winningProposal`. | High: depends on `Fml.all` and `grind` instantiation. |
| **L6 Callbacks** | `Calculus/Callback.lean` (the loop rules under `ProvesC`; the `ExecS` constructors are L1's). | Medium. |
| **L7 EVM** | `Evm/{Machine,Compile,Correctness}.lean`, as above. | High: the largest stage. |

L1 to L4 make loops provable. L5 is what Ballot and BlindAuction need once
their other blockers (`bytes32`, events, `keccak256`) are gone. L3 and L4
each add a `docs/solkey-feedback.md` entry: the rules solkey's plan asks
for, with their soundness side conditions (the frame, the cover, the
variant bound).
