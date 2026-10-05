# Loops

`while`, `for`, `do … while`, `break`, `continue`. This is a design plan:
four decisions and an ordered implementation plan. Nothing here is built.
Background: `docs/kernel-port.md` (its topics "Modalities", "Semantics",
"One rule per statement" and "Conditions" are the decisions this plan
extends).

## What solkey has

solkey has no loop rule. Its parser builds `WhileStatement`,
`ForStatement`, `DoWhileStatement`, `BreakStatement` and `ContinueStatement`
(`program/parser/SolJSONParser.java`), but no taclet in
`keyext.solidity.core/.../proof/rules/*.key` matches them, so symbolic
execution gets stuck. The specification plumbing is unconnected:
`speclang/LoopSpecification.java` has no implementation,
`SpecificationRepository.addLoopSpec` is never called, the varconds
`\hasInvariant`/`\getInvariant`/`\getVariant` are used by no taclet, and
`KeyNatspec` has no loop directive. solkey's plan (`docs/taclet-ideas.md`,
Tier 3) is unrolling first, an invariant rule later, `for` desugared to
`while`, `break`/`continue` as abrupt-completion markers. Loops block
Ballot and BlindAuction (after `bytes32` and events), `MultiAuction.closeAuction`
is `skip`ped, and the solc ports unroll by hand. No printed rule covers loops
either, so every rule below is a `LeanTaclet` (`Calculus/Rules.lean`) and
belongs in `docs/solkey-feedback.md`.

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
| A constant bound inside the loop only (fuel `2^257`) | Unwinding is not exact at the bound: a loop stopping at iteration `B + 1` is `diverge` while its unwinding is not, so `loopUnwind` is unsound for the diamond. |
| An inductive `Exec` beside `Stmt.run` | Two denotations. Every taclet's `Premise.Correct`/`SameOk` (`Calculus/SoundKit.lean`) is over `Prog.run`, the corpus is decided by kernel evaluation of it (`corpus_decide`), and the callback relation anchors to it (`ExecS.det`). `Stmt.run` is the only semantics. |
| `partial_fixpoint` | `Res = Except Halt` is not a CCPO, and the kernel cannot unfold the result. |

**Cost: computability.** The existential makes `Loop.run` classical, so
`Stmt.run` becomes `noncomputable`. Kernel reduction of a loop-free program is
unaffected, so `corpus_decide` and `Evm/Examples.lean` keep working; `#eval`
breaks (the examples in `Semantics.lean`, the corpus's `evaluated` pins). The
fix is `@[implemented_by]` on `Loop.run`, pointing at a fuelled `partial def`
the kernel never sees (to confirm on v4.24). A concrete loop is decided by
`Loop.run_of_iterN : iterN n σ = done r → Loop.run … σ = r`, with `n` found
by `#eval`.

**Proofs that recurse on `Stmt.run`** each get the same new case, an
induction on `n` over `iterN` and a congruence through the choice of `n`:
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

**A loop that transfers, with callbacks**, needs `ExecS` constructors (exit,
iterate, halt) and an outcome for divergence, since an inductive relation has
no derivation for an infinite run and the callback diamond would accept one.
Divergence needs no coinduction: *some set of states contains σ and is closed
under "the condition is true and the body ends in the set"*. This is the last
stage.

## Decision 2: `break`, `continue`, `for`, `do … while` are lowered

The elaborator lowers them and the kernel sees only `Stmt.loop`. `Res` and
`Halt` gain nothing (beyond `diverge`), so no `cases` on an outcome gets a
new arm. This is the choice `return` already made (no abrupt completion in
`Stmt.run`; `lowerReturns` in `Syntax.lean`), and how KeY's loop scope works:
a boolean records the abrupt completion.

- **`break`/`continue`** set fresh flags `brk`/`cnt` (`freshCapture`). The
  condition becomes `!brk && c`; whatever follows a statement that may set a
  flag is wrapped in `if (!brk && !cnt) { … }`; a statement after an
  unconditional `break` in the same block is an elaboration error (dead
  code).
- **`for (init; c; upd) body`** is
  `{ init; while (c) { cnt = false; body'; if (!brk) { upd } } }`. `init` is
  scoped as `elabBranch` scopes a branch, so a second `for (uint i …)` in the
  same function is legal.
- **`do body while (c)`** is `bool first = true; while (first || c) { first
  = false; body }`. The body is not duplicated: that would double its
  declarations (`checkFresh`) and its weight.
- **`return` inside a loop.** `lowerReturns` moves the statements after a
  `return` into the branches that do not return, which cannot leave a loop.
  A `return` in a loop body sets the return variable and a flag `ret`, and
  the loop condition gets `!ret` like `brk`. (Today an early `return` in a
  loop is an elaboration error.)

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
| `.unwind (k+1)` | `loopUnwind`: `unfold [if (c) { body; loop(.unwind k) } else {}]` | same |
| `.unwind 0` | `loopExit`: premise `c = false ∧ ⟨[ ω ]⟩ φ` (a new `Premise` shape) | same |
| `.inv I dec` | `loopInvariant`, below | `loopInvariantTotal` with `dec = some v`; with `none`, the premise is `done false` (sound, unprovable) |

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
`(k + 1) · (c.cost + c.pen + Prog.weight body + 3)`, so `loopUnwind` gets
smaller; `.inv I _` weighs `c.cost + c.pen + Prog.weight body + I.cost + 2`,
and its premise (`body` alone, `ω` alone) is lighter than `loop :: ω` under
`2 ^ weight · (measure φ + 1)`. `Fml.step_wellFounded` and `symex_normalizes`
survive. Without the annotation, unwinding would copy the loop and no weight
could decrease.

## Decision 4: the invariant rule and its soundness

Write `Ic` for `I.lower == true`, `c⁺`/`c⁻` for `c.lower == true`/`false`.
KeY's three goals:

```
  Γ ⟹ {U} Ic                                                 (initially valid)
  Γ ⟹ {U} {anon F} (Ic ∧ c⁺ → [ body ] Ic)                    (preserved)
  Γ ⟹ {U} {anon F} (Ic → (cover ∧ (c⁻ → [ ω ] φ)))           (use case)
  ──────────────────────────────────────────────────────
  Γ ⟹ {U} [ loop(.inv I _) c body; ω ] φ
```

`cover` is `Premise.cover` (`Calculus/Logic.lean`) of `c⁺`, `c⁻`: `c⁺ ∨ c⁻`
under the diamond, `true` under the box. `loopInvariantTotal` snapshots the
variant into a fresh local `v₀`; its preserved goal is
`{v₀ := v} ⟨ body ⟩ (Ic ∧ 0 ≤ v < v₀)`. The rule fires on the first
statement of the modality, so `{U}` is the context's update, as in
`CallbackTaclet` (`Calculus/Callback.lean`).

**The anonymising update `{anon F}`** generalises `Fml.havoc`/`Hyp.havoc`,
which replace storage and ledger and keep locals, memory and funds. A body
also writes locals and memory, so `F` is a frame computed from its syntax
(`Prog.frame body`): the locals it assigns or declares, storage if it writes
storage, the heap and `nextId` if it touches memory, the ledger if it
transfers. `holds σ (.anon F φ)` quantifies over every state agreeing
with `σ` off `F`; `Fml.havoc` is `anon` at storage + ledger. A
syntactic frame needs one lemma, `Prog.run_frameOff` (a run changes nothing
outside `Prog.frame body`), proved beside `Prog.run_frame`.

**Soundness, box.** Fix `σ` with `Γ` true, `τ₀ = U σ`. By induction on the
iteration count `n` of `iterN`, every loop-head state `τₙ` satisfies `Ic` and
agrees with `τ₀` off `F`: for `n = 0` by the first goal; for `n + 1`, `τₙ` is
one of the states the second goal quantifies over, so a body run ending
normally ends in `Ic`, and by `Prog.run_frameOff` agrees with `τₙ`, hence
`τ₀`, off `F`. The loop then ends done at `τₙ` with `c⁻` (the third goal
gives `[ ω ] φ`), in a halt of the body or of `c`, or in `diverge`; the box
accepts the last two.

**Soundness, diamond.** The variant is a `uint`, strictly decreasing, so the
iteration is done within `2^256` steps and `Loop.run` is not `diverge`. Neither
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
| **L3 Unwinding** | `Calculus/Rules.lean` (`loopUnwind`, `loopExit`, `Premise.exit`), `Completeness`, `Uniqueness`, `Termination` (weight), `Logic` (`Proves.exit`), `RuleSoundness`, `RuleSyntax` printers, `SolkeyFragment`. Examples: the hand-unrolled solc ports as real loops. | Low to medium: the weight arithmetic is new. |
| **L4 Invariant rule** | `Update.lean` (`Fml.anon`, `State.anon`, frame lemmas), `Semantics/Agree.lean` (`Prog.frame`, `Prog.run_frameOff`), `Calculus/Rules.lean` (`loopInvariant`, `loopInvariantTotal`, `Premise.inv`), `Logic`, `RuleSoundness`, `Termination`. Check whether `sol_decide` handles `anon` (a local in `F` is a fresh free local, anonymised storage a fresh free storage). Examples: a counting loop, a sum with a closed form. | Medium to high: `Prog.run_frameOff` over every statement, and extending `Decide`'s reduction to a second base storage. |
| **L5 Quantified invariants** | After `Fml.all` in an invariant: a table of invariants by index. Ballot's `winningProposal`. | High: depends on `Fml.all` and `grind` instantiation. |
| **L6 Callbacks** | `Semantics/Callback.lean` (loop `ExecS` constructors, the divergence outcome), `Calculus/Callback.lean` (the loop rules under `ProvesC`). | Medium. |
| **L7 EVM** | `Evm/{Machine,Compile,Correctness}.lean`, as above. | High: the largest stage. |

L1 to L4 make loops provable. L5 is what Ballot and BlindAuction need once
their other blockers (`bytes32`, events, `keccak256`) are gone. L3 and L4
each add a `docs/solkey-feedback.md` entry: the rules solkey's plan asks
for, with their soundness side conditions (the frame, the cover, the
variant bound).
