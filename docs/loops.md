# Loops: design

`while`, `for`, `do … while`, `break`, `continue`. This document makes the
design decisions and gives the implementation plan. Nothing here is built yet.
Read `docs/kernel-port.md` first. The "Decisions" rows cited below are from
its table.

## What solkey has

solkey has no loop rule. Its parser builds `WhileStatement`, `ForStatement`,
`DoWhileStatement`, `BreakStatement` and `ContinueStatement` nodes
(solkey `program/parser/SolJSONParser.java`, `parser/SolidityToKeyConverter.java`).
No taclet in `keyext.solidity.core/.../proof/rules/*.key` matches them, so
symbolic execution gets stuck on a loop and the goal stays open. The loop
specification plumbing exists but nothing is connected to it:

- `speclang/LoopSpecification.java` is an interface with no implementation.
- `SpecificationRepository.addLoopSpec` is never called.
- The varconds `\hasInvariant`, `\getInvariant` and `\getVariant` are
  registered, but no taclet uses them.

`KeyNatspec` has no loop directive; its only directives are `box`, `skip`,
`invariant`, `requires`, `ensures` and `assignable`. solkey's own plan
(`docs/taclet-ideas.md`, Tier 3) is an unrolling rule first and an
invariant rule later, with `for` desugared to `while` and `break`/`continue`
handled "via abrupt-completion markers like KeY's Java loop scope".

Where the missing rule shows:

- In the benchmark README, loops are a blocker for **Ballot** and
  **BlindAuction**. Neither is the first blocker: those are `bytes32` and
  events.
- `MultiAuction.closeAuction` is `skip`ped.
- The solc ports unroll their loops by hand. `solc/README.md` says "the loop
  rule itself is untested".

No printed rule covers loops either. So every rule below is a `LeanTaclet`
(`Calculus/Rules.lean`) and should get an entry in `docs/solkey-feedback.md`.

## Decision 1: semantics — the least fixed point, inside `Stmt.run`

**Recommendation.**

- Add a statement `Stmt.loop (a : LoopAnn C) (c : Val C .bool) (body : Prog C)`.
- `Stmt.run` stays a total function that is structural on the syntax. Its
  loop arm is `Loop.run (fun τ => Prog.run τ body) c σ`: the recursive call
  is on the subterm `body`, under a binder, which structural recursion allows.
- `Loop.iterN n σ` runs at most `n` iterations. It returns *running τ* or
  *done r*, and *done* absorbs.
- `Loop.run` returns the *r* of any `n` at which the iteration is done.
  Because *done* absorbs, every such `n` gives the same *r*.
- When no such `n` exists, `Loop.run` returns a new halt, `Halt.diverge`.

`Modality.onHalt` is unchanged: a box accepts a divergent run and a diamond
does not. That is the partial/total reading the Decisions row "Modalities"
already gives the two modalities. The annotation `a` is invisible to
`Stmt.run`.

Options rejected:

| Option | Why not |
|---|---|
| Fuel everywhere (`Stmt.run n σ s`) | Threads a `Nat` through every theorem that recurses on `Stmt.run` (list below). The box becomes `∀ n`, the diamond `∃ n`, and monotonicity in `n` becomes a lemma every proof needs. |
| A constant bound (fuel `2^257` inside the loop only) | Computable and kernel-reducible, but unwinding is not exact at the bound: a loop that stops at iteration `B + 1` is `diverge` while its unwinding is not. That makes `loopUnwind` unsound for the diamond. |
| An inductive `Exec` beside `Stmt.run` | Two denotations. Every taclet's `Premise.Correct`/`SameOk` (`Calculus/SoundKit.lean`) is stated over `Prog.run`, the corpus is decided by kernel evaluation of it (`corpus_decide`, `Corpus/Basic.lean`), and the callback relation anchors to it (`ExecS.det`). The Decisions row "Semantics" names a `Prog.run_eq` bridge, but that bridge no longer exists: `Stmt.run` is the only semantics, and it should stay that way. |
| `partial_fixpoint` | `Res = Except Halt` is not a CCPO. The kernel cannot unfold the result either. |

**Cost: computability.**

- The existential makes `Loop.run` classical, so `Stmt.run` becomes
  `noncomputable` for the compiler.
- Kernel reduction of a *loop-free* program is unaffected: the loop arm is
  never reached, so `corpus_decide` and `Evm/Examples.lean` keep working.
- `#eval` does break: the examples in `Semantics.lean` and the corpus's
  `evaluated` pins use it.
- Fix: put `@[implemented_by]` on `Loop.run`, pointing at a fuelled
  `partial def`. The kernel never sees that implementation. This needs
  confirming on v4.24.
- A concrete loop is decided through the lemma
  `Loop.run_of_iterN : iterN n σ = done r → Loop.run … σ = r`, with the
  witness `n` found by `#eval`.

**Proofs that recurse on `Stmt.run`, and what the loop costs each one.**
Every proof gets the same new case: an induction on `n` over `iterN`,
followed by a congruence through the choice of `n`.

| Theorem | File | The loop case |
|---|---|---|
| `Stmt.run_frame`/`Prog.run_frame` | `Semantics/Agree.lean` | States that agree off `ns` iterate alike, so their `∃ n` sets and results coincide. |
| `Stmt.run_wt`/`Prog.run_wt` | `Typing/Soundness.lean` | `RunWT … Γ` at the loop head is the invariant. The body is typed as a branch is (`Ctx.le Γ Γb`). |
| `Stmt.run_canon` | `Typing/Reachability.lean` | Same shape. |
| `Stmt.run_tight` | `Typing/Constructibility.lean` | Same shape. `reachable_iff` stays true: a loop reaches nothing a finite sequence of body runs does not, and the builder needs no loop. |
| `Stmt.exec_run`/`Prog.exec_run`, `ExecS` | `Semantics/Callback.lean` | A loop whose body has no transfer is `det`. Set `Stmt.forks (.loop …) := Prog.hasTransfer body`, **not** `true`: a forking statement with no `ExecS` constructor would have no runs, so every modality over it would hold vacuously. |
| `Stmt.run_call_expand` | `Calculus/SoundUnfold.lean` | Unaffected. |
| `stmt_sim` | `Evm/Correctness.lean` | Out of the fragment at first (EVM section). |
| `Stmt.read?` | `SortCheck/Faithfulness.lean` | `none`: a loop is not a read. |
| `Stmt.weight`, `Stmt.step_smaller` | `Calculus/Termination.lean` | Decision 3. |

**A loop that transfers, with callbacks.** It needs `ExecS` constructors of
its own: exit, iterate, halt. It also needs an outcome for divergence. An
inductive relation has no derivation for an infinite run, so without that
outcome the callback diamond would accept one. Divergence can be defined
without coinductive types: *some set of states contains σ and is closed
under "the condition is true and the body ends in the set"*. This is the
last stage of the plan.

## Decision 2: `break`, `continue`, `for`, `do … while` are lowered

The elaborator lowers them, and the kernel sees only `Stmt.loop`. `Res` and
`Halt` are unchanged, so no `cases` on an outcome gets a new arm.
This is the choice the Decisions row "`return`" already made ("no abrupt
completion in `Stmt.run`"), and it is also how KeY's loop-scope rule works:
a boolean records that the body completed abruptly.

- **`break`/`continue`.** They set fresh flags `brk`/`cnt` (from
  `freshCapture`, `Syntax.lean`).
  - The condition becomes `!brk && c`.
  - Whatever follows a statement that may set a flag is wrapped in
    `if (!brk && !cnt) { … }`.
  - A statement after an unconditional `break` in the same block is an
    elaboration error, as dead code.
- **`for (init; c; upd) body`** becomes
  `{ init; while (c) { cnt = false; body'; if (!brk) { upd } } }`.
  - The `init` declaration is scoped as `elabBranch` scopes a branch.
  - A second `for (uint i …)` in the same function declares `i` again,
    which is legal: `Γ` forgot it.
- **`do body while (c)`** becomes
  `bool first = true; while (first || c) { first = false; body }`. The
  body is not duplicated: duplicating it would double its declarations
  (`checkFresh`) and its weight.
- **Early `return`** is wave 1 work in progress. A `return` inside a loop
  must also leave the loop. If wave 1 lowers `return` to a flag, the loop
  condition gets `!ret` the same way. If wave 1 introduces abrupt
  completion instead, `break`/`continue` should reuse it rather than add a
  second mechanism.

The cost: goals and invariants mention the flags. An invariant for a loop
with `break` must say what holds when `brk` is set.

## Decision 3: one rule per loop, chosen by an annotation it carries

Unwinding and the invariant rule both apply to one loop. The Decisions row
"One rule per statement" (`Stmt.complete`, `Rule.eq_step`,
`Rule.premise_unique` in `Calculus/Uniqueness.lean`) is kept by making the
choice **syntax**. `LoopAnn C` is one of:

- `.inv (I : Val C .bool) (dec : Option (Val C .uint))`: an invariant, and
  optionally a variant;
- `.unwind (k : Nat)`: unroll at most `k` more times.

`Stmt.step` (`Calculus/Completeness.lean`) dispatches on the annotation:

| Annotation | Box | Diamond |
|---|---|---|
| `.unwind (k+1)` | `loopUnwind`: `unfold [if (c) { body; loop(.unwind k) } else {}]` | same |
| `.unwind 0` | `loopExit`: the premise `c = false ∧ ⟨[ ω ]⟩ φ` (a new `Premise` shape; no existing shape yields `false` under the box) | same |
| `.inv I dec` | `loopInvariant`, below | `loopInvariantTotal` with `dec = some v`; with `none`, the premise is `done false` (sound, just not provable) |

About `.unwind 0`: `if (c) {…}` then `ifElseUnfold` captures a condition
that is not simple, as `if` does. Replacing the loop with `assert(!c)`
would be **unsound under the box**, because a box accepts the halt.

**Why the annotation is a `Val`, not a `Fml`.** `Fml` (`Update.lean`)
contains `Prog`, so a `Stmt` that carried an `Fml` would make `Stmt`,
`Term` and `Fml` one mutual inductive. A boolean program expression avoids
that:

- it is effect-free and lowered exactly (`Val.lower_eval`);
- it can read storage, locals, `.length`, `&&`, `||`, `?:`;
- that is also how solkey's spec language compiles (`SpecCompiler`);
- it has no quantifier, so Ballot's
  `∀ q < p. proposals[q].voteCount ≤ winningVoteCount` is out of reach.

Quantified invariants need `Fml.all` (`docs/function-specs.md`) and a
place outside `Stmt` for the formula, for example a per-contract table
that the loop names by index. That is a later stage.

**Termination** (`Calculus/Termination.lean`):

- `.unwind k` weighs `(k + 1) · (c.cost + c.pen + Prog.weight body + 3)`,
  so `loopUnwind` gets smaller.
- `.inv I _` weighs `c.cost + c.pen + Prog.weight body + I.cost + 2`.
  Its premise runs `body` alone and `ω` alone, which is lighter than
  `loop :: ω` under the measure `2 ^ weight · (measure φ + 1)`. `I.cost`
  pays for the invariant formulas the premise adds.
- `Fml.step_wellFounded` and `symex_normalizes` survive.
- Without the annotation, unwinding would copy the loop and no weight could
  decrease. That is the other reason for Decision 3.

## Decision 4: the invariant rule and its soundness

Write `Ic` for `I.lower == true`, `c⁺` for `c.lower == true` and `c⁻` for
`c.lower == false`. Following KeY's three goals:

```
  Γ ⟹ {U} Ic                                                 (initially valid)
  Γ ⟹ {U} {anon F} (Ic ∧ c⁺ → [ body ] Ic)                    (preserved)
  Γ ⟹ {U} {anon F} (Ic → (cover ∧ (c⁻ → [ ω ] φ)))           (use case)
  ──────────────────────────────────────────────────────
  Γ ⟹ {U} [ loop(.inv I _) c body; ω ] φ
```

- `cover` is `Premise.cover` (`Calculus/Logic.lean`) of `c⁺` and `c⁻`:
  `c⁺ ∨ c⁻` under the diamond, `true` under the box, as for `if`.
- The diamond version, `loopInvariantTotal`, snapshots the variant into a
  fresh local `v₀`. Its preserved goal becomes
  `{v₀ := v} ⟨ body ⟩ (Ic ∧ 0 ≤ v < v₀)`.
- The rule fires on the first statement of the modality, so `{U}` is the
  context's update, as in `CallbackTaclet` (`Calculus/Callback.lean`).

**The anonymising update `{anon F}`.**

- It generalises `Fml.havoc`/`Hyp.havoc` (`Update.lean`,
  `Calculus/Logic.lean`), which replaces storage, ledger and funds and keeps
  locals and memory.
- A loop body also writes locals and memory, so `F` is a **frame** computed
  from the body's syntax (`Prog.frame body`):
  - the locals it assigns or declares (aliases included);
  - storage, if it writes storage;
  - the heap and `nextId`, if it touches memory;
  - the ledger and funds, if it transfers.
- `holds σ (.anon F φ)` quantifies over every state that agrees with `σ`
  off `F`. `Fml.havoc` is `anon` at the frame storage + ledger + funds.
- A syntactic frame needs no proof obligation of the user, only one lemma:
  **`Prog.run_frameOff`**, which says a run changes nothing outside
  `Prog.frame body`. It is proved beside `Prog.run_frame`
  (`Semantics/Agree.lean`).

**Soundness, box.**

- Fix `σ` with `Γ` true, and let `τ₀ = U σ`.
- Claim, by induction on the iteration count `n` of `iterN`: every loop
  head state `τₙ` satisfies `Ic` and agrees with `τ₀` off `F`.
  - For `n = 0`, this is the first goal.
  - For `n + 1`, `τₙ` is one of the states the second goal quantifies over,
    by the induction hypothesis. So a body run that ends normally ends in
    `Ic`, and by `Prog.run_frameOff` it ends off `F` equal to `τₙ`, hence to
    `τ₀`.
- The loop's outcome is then one of:
  - done at `τₙ` with `c⁻`: the third goal gives `[ ω ] φ`;
  - a halt of the body or of `c`;
  - `diverge`.
- The box accepts the last two.

**Soundness, diamond.**

- The variant is a `uint`, so it is below `2^256` and strictly decreases.
  The iteration is therefore done within `2^256` steps, and `Loop.run` is
  not `diverge`.
- The body cannot halt: the preserved goal is a diamond.
- The condition cannot halt either: the cover conjunct.

**Structure in Lean.**

- A new `Premise` constructor, `inv`, whose `Premise.fml` is the
  conjunction above. `Fml.stepAt` (`Calculus/Symex.lean`) reads premises
  through `Premise.fml`, so `sol_symex` handles the new rule without
  changes.
- `Proves` (`Calculus/Logic.lean`) gets one constructor per new shape
  (`inv`, `exit`).
- `LeanTaclet.sound` gets the two cases above.
- `Stmt.inSolkey (.loop …) = false` (`Calculus/SolkeyFragment.lean`):
  `Proves.toSolkey` is untouched, and `Proves.solkey_lt_calculus` gains a
  witness.

**Typing and declarations.** `Stmt.wt` for a loop requires:

- `c.wt Γ` and the annotation's values to be well-typed at `Γ`;
- `Prog.wt Γ body = some Γb` with `Ctx.le Γ Γb`;

and returns `Γ`, exactly as for `ite`.

A local declared in the body is declared again on each iteration:

- `declLocal` overwrites it, which is solc's per-iteration
  re-initialisation.
- The Decisions row "Declarations" is an elaboration discipline
  (`checkFresh`), and the body is elaborated once, so nothing changes there.
- The body's declared locals are in `F`: the invariant is typed at `Γ` and
  cannot name them, and the preserved goal sees them anonymised.
- Scratch names `Stmt.step` picks inside the body are above every index in
  the formula, as elsewhere (the Decisions row "Continuations").

The loop condition is **not** captured before the loop, since the loop
must re-evaluate it:

- The invariant rule lowers it (`Val.lower`).
- The unwinding's `if` captures it on each copy (the Decisions row
  "Conditions").
- An `++` in a loop condition is an elaboration error, as it is under
  `&&`, because hoisting it would run it once.

## The EVM

The machine has only relative forward jumps: `exec` (`Evm/Machine.lean`)
is structural and carries the number of instructions left to skip. The one
loop solc emits for the current fragment, `checked_exp_helper`'s, is
unrolled 255 times (`expLoop`, `Evm/Exp.lean`).

Backward jumps cost:

1. **Absolute addressing.** Absolute `JUMP`/`JUMPDEST` with a program
   counter. `exec` then needs fuel (gas).
2. **A new proof layer.** `exec_append` and the skip-count lemmas, on which
   every case of `stmt_sim` composes, give way to a "code at offset `o` is
   `compile s`" invariant.
3. **A third outcome.** The dichotomies `ValOut`/`StmtOut`
   (`Evm/Correctness.lean`) grow a third arm: both diverge, meaning the
   machine is out of fuel at every fuel.
4. **The push bound.** The hypothesis `L + pushesP P ≤ 2^64` no longer
   bounds a loop's pushes. The interpreter's `push` would have to revert at
   `2^64` as solc does (a `docs/solc-alignment.md` row), or the bound would
   have to become a run-time invariant of `Sim`.

This is comparable to rewriting `Evm/Correctness.lean` (2,237 lines).
**Decision:** `wtStmt` (`Evm/Compile.lean`) refuses a loop, as it refuses
memory, and `docs/compiler-verification.md` lists it. Loops also unblock
the listed gaps "copies of dynamic arrays" and "clearing past an end", so
the EVM stage is worth doing once, for all three.

## Plan

| Stage | Scope (files) | Risk |
|---|---|---|
| **L1 Syntax and semantics** | `Syntax.lean`: `LoopAnn`, `Stmt.loop`, `RawStmt.while/for/doWhile/brk/cont`, the lowering of Decision 2, printers, `Stmt.quote`, `renameStmts`. `Semantics.lean`: `Halt.diverge`, `Loop.iterN`, `Loop.run`, `implemented_by`. `Semantics/Agree.lean`: `Stmt.vars`, `run_frame`. `Semantics/Callback.lean`: `forks`, `hasTransfer`. `Calculus/Quote.lean`, `Calculus/Notation.lean` quoters. | Medium: structural recursion through `Loop.run`, and `#eval` under `implemented_by`. Check both first, in a scratch file. |
| **L2 Typing** | `Typing/Soundness.lean`, `Typing/Reachability.lean`, `Typing/Constructibility.lean`: the loop cases, by induction on `iterN`. | Low. The same proof three times. |
| **L3 Unwinding** | `Calculus/Rules.lean` (`loopUnwind`, `loopExit`, `Premise.exit`), `Calculus/Completeness.lean`, `Calculus/Uniqueness.lean`, `Calculus/Termination.lean` (weight), `Calculus/Logic.lean` (`Proves.exit`), `Calculus/RuleSoundness.lean`, `Calculus/RuleSyntax.lean` printers, `Calculus/SolkeyFragment.lean`. Examples: the hand-unrolled solc ports as real loops. | Low to medium. The weight arithmetic is new. |
| **L4 Invariant rule** | `Update.lean` (`Fml.anon`, `State.anon`, frame lemmas), `Semantics/Agree.lean` (`Prog.frame`, `Prog.run_frameOff`), `Calculus/Rules.lean` (`loopInvariant`, `loopInvariantTotal`, `Premise.inv`), `Calculus/Logic.lean`, `Calculus/RuleSoundness.lean`, `Calculus/Termination.lean`. Check whether `sol_decide` handles `anon` (`Calculus/Decide.lean`: a local in `F` is a fresh free local; anonymised storage is a fresh free storage). Examples: a counting loop, a sum with a closed form. | Medium to high: `Prog.run_frameOff` over every statement, and the extension of `Decide`'s reduction to a second base storage. |
| **L5 Quantified invariants** | After `Fml.all` (`docs/function-specs.md`, stage S4): a table of invariants by index. Ballot's `winningProposal`. | High. Depends on `Fml.all` and `grind` instantiation. |
| **L6 Callbacks** | `Semantics/Callback.lean`: loop constructors of `ExecS`, the divergence outcome. `Calculus/Callback.lean`: the loop rules under `ProvesC`. | Medium. |
| **L7 EVM** | `Evm/Machine.lean`, `Evm/Compile.lean`, `Evm/Correctness.lean`, as described above. | High. The largest stage. |

L1 to L4 make loops provable. L5 is what Ballot and BlindAuction need
after their other blockers (`bytes32`, events, `keccak256`) are gone.
Each stage adds its `docs/kernel-port.md` Decisions rows, and L3/L4 add a
`docs/solkey-feedback.md` entry: the rules solkey's plan asks for, with
their soundness side conditions (the frame, the cover, the variant bound).
