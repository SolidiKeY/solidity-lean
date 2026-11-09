# Would interaction trees shrink the semantics?

Inspection with experiments (batch itree-20261109, lane `itree-inspection`),
base `d890f91eb`. Nothing here is for merging: the experiments live in
`Solidity/Scratch/ITree` at commit f0249758a (deleted from master since; not imported by any root, by design of
`register.sh`), and no core module changed.

**Verdict.** Interaction trees are a **net loss** (`partial_fixpoint` for loops: irrelevant). The saving
the coordinator expected is real, but it comes from **parametrizing `ExecS` by
a resumption predicate (B)**, which is a **modest saving**: about **−940
lines**, by arithmetic over measured line ranges (−1.04k with the
transaction-level twin), in 8 files, with mechanical churn in ≤29 client
files. On top of B, finite trees with handlers (A) **add** about +40 to +140
lines (an extrapolation from the fragment, so a net loss), and they require
rewriting the constructor-level reasoning of 31–49 client files. Coinductive
trees (C(ii)) are a net loss in this repository: no kernel evaluation, a
universe bump, and an `eutt` library to build. The recommended next step is B
alone.

Line counts: *raw* = `wc -l` (docstrings included); *code* = declaration lines
without docstrings or blank lines (the script is described under
[Method](#method)). A **measured** figure comes from code in this tree; an
**extrapolated** figure gives its source.

## 1. Inventory (measured)

| Area | Files | Raw | Code def / lemma | Client files |
|---|---|---:|---:|---:|
| Callback runs `ExecS/P/F` | `Semantics/Callback.lean` | 1611 | 476 / 880 | 60 (`Exec[SPF]`); 31–49 use its constructors by name (31: `Exec[SPF].ctor`; 49: loosest match) |
| Caller-model copy `ExecSM/PM/FM` | `Calculus/CallerModel{,Run,Valid}.lean` | 1587 | 402 / 810 | 5 |
| Callback weakening (thinning) | `CallbackWk`, `CallbackUnwk`, `CallbackFrame`, `CallbackCapture` | 1833 | 57 / 1506 | 2 + 3 importers |
| Deferred relations | `DeferredCallback`, `DeferredCorrespondence`, `NativeDeferred*` | 756 | 65 / 529 | 2 + 2 |
| Static invocation `Exec` | `Semantics/StaticInvocation.lean` | 185 | 49 / 83 | – |
| Deterministic run | `Run`, `RunWk`, `RunAccel` | 4116 | 1025 / 2125 | 441 (`Prog.run`/`Stmt.run`), 414 (`TRun.`) |
| Fuel twin | `Semantics/RunFuel.lean` | 472 | 120 / 259 | 15 importers |
| Fuel ↔ classical bridge (`*approx*` declarations, everywhere) | 26 files | – | 885 lines in 83 decls | – |
| Worlds and traces | `ContractWorld`, `PaymentWorld`, `Lifetime`, `Theory/Reachable/CallerModel`, `Source/Session` | 1710 | 407 / 737 | – |
| Context equivalence | `Semantics/CtxEquiv/*` (8 files) | 1908 | 255 / 669 | – |
| Lowering's "diverge ↔ fault" split | `Theorems.lean` l.269, `Goals.lean` l.25 | – | – | 44 (word-bounded) to 135 (substring) files mention both `diverge` and `fault` |

### Duplicated rule lists (measured by `diff` after renaming)

| Pair | Today | Difference |
|---|---|---|
| `ExecSM/PM/FM` vs `ExecS/P/F` (`CallerModel.lean` l.160–493 vs `Callback.lean` l.489–811) | 334 vs 325 raw | 21 differing diff lines: one premise `M.Allows J …` in `transferResume`, `sendResume`, `tryOk`, and docstrings |
| `Stmt.execM_run` vs `Stmt.exec_run` (`CallerModelRun.lean` l.255–670 vs `Callback.lean` l.893–1302) | 417 vs 410 raw | after full renaming, 10 differing diff lines: `(M.allows_refl J _)` at 4 sites in 3 resumptions |
| `ExecSM.toExecS` / `ExecS.ofExecSM` (×S/P/F) | 145 raw | constructor-by-constructor identity maps |
| `holdsR`/`COut.thenFM` vs `holdsC`/`COut.thenF` | 31 vs 31 raw | `ExecPM M` for `ExecP`; plus `holdsR_any_iff`, `thenFM_any_iff` (36 code) to bridge them |
| `ExecThen`, `ExecCall`, `DirectCall` vs `ExecP.cons/halt/violated` | 3 × ~10 | the same next/halt/violated "bind" shape, 4 more times (also `ExecF.seq*`) |
| `Lifetime.Step` vs `Reachable.StepE` | 15 + 15 | `StepE` is `Step` with the run as a parameter; the bridge back (`noCallback` is `Lifetime`, `Theory/Reachable/CallerModel.lean` l.155–246) is ~90 raw. Defining `Step` from `StepE` would also need `StepE` moved from Theory into Semantics, for the import direction |
| `StaticInvocation.Exec` | 33 | an independent event-trace model (read/credit/write/re-entry); no duplicate |

### Lemma classification (by family)

(a) disappears under a tree with handlers; (b) is re-proved in another form;
(c) is unaffected. Lines are raw.

| Family | (a) | (b) | (c) |
|---|---|---|---|
| `ExecSM` + `CallerModelRun` + `holdsR` | defs 334, `toExecS`/`ofExecSM` 144, `execM_run` 417, `holdsR*` 31 + 42 — **all of it also disappears under B** | `mono` 75 (one generic `Handle.mono`, 8 code) | Reentry/lattice 158, `CallerModelValid` polarity/weakening ~300 |
| `ExecS` + `exec_run` + `eq_run` (`Callback.lean`) | – | `ExecS` 325 → a tree semantics + handler; `exec_run` 410 → generic `Handle.runDet` (11 code) + per-constructor `runDet (tree s) = run s`; `eq_run` ~300 → generic + per-constructor "no callback event" | forks/callsBack 310, send_cases etc. |
| `CallbackWk`/`Unwk` | – | payment and `try` cases, 381 code (`transfer_wk` 22, `send_wk` 37, `tryCall_wk` 86, `catchData_wk` 29, unwk twins 13+44+90+36, helpers 24): the J/havoc bookkeeping becomes one generic lemma, the `TRun` commutations remain | ite/call/loop/block/det cases, ~800 |
| Deferred relations | – (the 3 bind-shaped relations and their join/split lemmas, ~100, can go with one generic relational bind, with or without trees) | – | the rest, ~650 |
| Run, RunWk, RunAccel, RunFuel, `*approx*` | – | – | all: the deterministic run stays the definition (see Experiment D) |
| Worlds, CtxEquiv, Session, Lowering | – | – | all; Session already has its own `Prefix Event Outcome` trace model |

Fuel ↔ classical: 83 declarations (885 code lines) relate fuelled runs to the
classical loop. None of them goes away under A, B or C(i), because the kernel
still cannot evaluate the classical loop (Experiment C(i)).

## 2. Experiment A: finite tree + handlers (measured on the fragment)

`ITree/Tree` (f0249758a) (168 raw): events `Ev` (a payment leaving
in a state, with the kind `transfer` or `send full`), answers (`Resume`, or
`Option Resume` for a send), the free monad `Tree`, `bind`/`map`/`runDet`, and
**one handler** `Handle A J viol` over an allowance `A` (`anyA` = `ExecS`,
`M.Allows J` = `ExecSM`), with `mono`, `bind_iff`, `map_iff` and `runDet` (the
generic `exec_run`). `ITree/Payments` (f0249758a) (339 raw): the
tree semantics of `transfer`/`send` and of straight-line programs, together
with the proofs below.

Re-proved end to end on the fragment (programs of payments and non-forking
statements); `#print axioms` shows only `propext, Classical.choice, Quot.sound`:

| Result | Tree proof | Original |
|---|---|---|
| `prog_iffM`: `ExecPM M J σ P o ↔ Handle (M.Allows J) J … (Prog.tree P σ) o` | 25 + `stmt_iffM` 9 + `transfer_iffM` 31 + `send_iffM` 53 (validation only; it would not exist if the tree were the definition) | – |
| `execPM_mono` (`ExecPM.mono`) | 5 + `Handle.mono` 8 | 59 code (`ExecSM/PM/FM.mono`) |
| `execPM_any_iff` (`ExecPM .any ↔ ExecP`) | 3 (the allowances are definitionally equal) | 118 code (`toExecS` + `ofExecSM`) |
| `prog_execM_run` (`Prog.execM_run`) | 5 + `Handle.runDet` 11 + `stmt_runDet` 17 + `prog_runDet` 15 | 399 code (`Stmt/Prog/Frames.execM_run`) and again 399 (`exec_run`) |

Side by side, the transfer/send fragment only (raw lines):

| | Today | B | A |
|---|---:|---:|---:|
| Constructors (`ExecS` 43, `ExecSM` 45) | 88 | 46 | tree semantics 28 |
| `mono`/`toExecS`/`ofExecSM` cases | 24 | 8 | 0 (generic) |
| `exec_run`/`execM_run` cases | 46 | 23 | ~15 (`stmt_runDet`'s payment cases) |
| `eq_run` cases | 3 | 3 | ~3 |
| **Fragment total** | **161** | **80** | **~46** |
| One-off infrastructure | – | ~10 (bridges) | ~95 code / 168 raw (`ITree/Tree`) |

Extrapolation to the whole of `ExecS` (from the fragment's ratios, A vs B).
Today the forking constructors are 287 code lines; at the fragment's ratio
(tree 28 against 43 constructor lines) the tree semantics would take ~190.
The remaining `exec_run` (410), `eq_run` (~300) and payment/`try` weakening
cases (381) take ~1.1k lines under B. In the fragment, `exec_run`/`eq_run`
cases go from 26 lines (B) to ~18 (A), about 30 % less; at that ratio
~330 lines become generic. A finite tree **cannot** express a loop whose body pays (unboundedly
many events). It needs a fuelled tree (`∃ n, Handle (treeF n σ) o`, which
matches `loopDiverge`'s over-approximation) and therefore a fuel ↔ classical
bridge for every loop (`runF_approx`-style, +50–100). Per-constructor
correspondence proofs (`runDet (Stmt.tree s σ) = s.run σ`) are needed because
the run must stay the definition (D). Net, A beyond B: **+40 to +140 lines (a net loss)**:
infrastructure ~170 + fuelled loops ~100 + correspondence ~200–300 (470–570)
against generic savings of ~430 (~97 from the constructors, 287 → 190, plus
~330). Churn: 31–49 client files reason by `ExecS` constructor names (`cases h with | transferResume …`); each would
become a `Handle` inversion.

## 3. Experiment B: `ExecS` by an allowance (measured)

`ITree/ParamExec` (f0249758a) (872 raw) is generated mechanically
from `CallerModel.lean` and `CallerModelRun.lean`: `ExecSA (A : Allow C) J`
replaces `M.Allows J` by `A`, and **one** `exec_run` (`execA_runS/P/F`) takes
`hA : ∀ σ, A σ σ.storage σ.net σ.selfBalance`. It checks with no edits beyond
names. Then `ExecS J := ExecSA anyA J` and `ExecSM M J := ExecSA (M.Allows J) J`.
`execSA_any` (`ExecSM .any ↔ ExecS`) is `Iff.rfl`. `ExecSA.toAny` is
`mono` with `trivial`. `prog_execM_run` and `prog_exec_run` are instances of
`execA_runP`.

| Disappears | Raw |
|---|---:|
| `ExecSM/PM/FM` (`CallerModel.lean` l.160–493) | 334 |
| `holdsR`, `COut.thenFM` (l.495–525; `holdsC` takes the allowance) | 31 |
| `toExecS`/`ofExecSM` ×3 (`CallerModelRun.lean` l.105–248) → `Iff.rfl` and 3 lines | 144 → ~10 |
| `execM_run` ×3 (`CallerModelRun.lean` l.252–668) | 417 |
| `holdsR_any_iff`, `thenFM_any_iff` (`CallerModelValid.lean` l.113–154) | 42 |
| Added: allowance parameter and 3 premises in `ExecS`, `hA` in `exec_run`, allowance in `holdsC`, `abbrev`s | +~20 |
| **Net (callback family), by arithmetic over these ranges** | **−~940** |
| Optional, same idea at the transaction level: `Lifetime.Step := StepE noCallback`, its bridge (`Theory/Reachable/CallerModel.lean` l.157–246) | −~100 |

Churn: the 89 uses of `transferResume`/`sendResume`/`tryOk` in 28 files gain
one `trivial` argument or one `_` pattern, and `Theory/CallerModel/Static.lean`
uses `toExecS`. ParamExec checks that the generic definitions and proofs
compile; the core refactor itself was not carried out. Keeping `ExecS`/`ExecSM` as
`abbrev`s leaves every other mention unchanged. Automation is unaffected (no
run changes). This is the baseline that any tree refactor has to beat, and A
does not beat it at all (§2), let alone by a margin worth 31–49 files of churn.

## 4. Experiment C: loops and coinduction

**C(i) `partial_fixpoint`** (`ITree/Loop` (f0249758a), 90 raw).
`runPF` (the loop in `Option`, `none` = never done) is accepted by Lean
v4.24's `partial_fixpoint`, which generates the unfolding equation and
`fixpoint_induct`. `Loop.run_eq : run body c σ = TLoop.run body c σ` is proved
in 49 code lines (`runPF_of_iterN`, `iterN_of_runPF` by fixpoint induction
with `admissible_pi_apply`/`Option.admissible_eq_some`). It works, but **like
`TLoop.run` it does not reduce by `decide` or `rfl`** (the fixpoint is
classical). `#eval` runs compiled code. The unfolding equation evaluates step
by step (`iterate n (rw [run_unfold]; simp …)`), and `simp` with it loops.
It would replace `TLoop.run`, `iterN_done_le/unique`, `run_of_iterN` and
`run_induct` (`Run.lean` l.586–663, 78 raw) with ~45 lines. `iterN` stays for
`RunFuel`, and **none of the 83 `*approx*` declarations (885 lines) goes
away**, because kernel evaluation still needs fuel. Net **−30 to 0**:
irrelevant.

**C(ii) homegrown coinductive tree** (`ITree/Coind` (f0249758a),
185 raw, 126 code). Without Mathlib's M-types, a tree is a pointed coalgebra
`CoTree E Ans R : Type 1` (states, `step : S → Node`, `root`), and equality
becomes bisimilarity. Proved: `bind_assoc` up to strong bisimilarity (44
lines; no axioms), `tau_eutt : Eutt t.tau t` (16 lines; `propext`), and
`Eutt.refl`, where `Eutt` is an inductive tau-stripping `EuttF` under a
coinductive (Knaster–Tarski, `∃ Rel`) bisimulation. Elaboration was fast (the
file checks in seconds); no kernel or elaboration problem appeared. Costs:
`Type 1` trees (a universe bump for every semantic function returning one); no
equational reasoning (every law up to a relation); and no evaluation, since
`decide` sees an existential state type. **Not attempted:** `Eutt`
transitivity and bind congruence up to `Eutt`, which every client proof
needs, as well as `iter` laws and the handler-to-relation interpretation with
divergence. At the measured 15–45 lines per basic law, that layer is ≥500
lines (an extrapolation from 20+ lemmas). It still needs the fuel bridge for
`decide`. Replacing the lowering theorem's "diverge ↔ fault" split by `eutt`
would also need a coinductive machine semantics (44–135 files mention both).
**Net loss.**

## 5. Experiment D: automation (measured)

`ITree/Auto` (f0249758a): today's run against the tree read
deterministically (`(Prog.tree P σ).runDet`), on `ScopedRuns.guardLowCore`,
`CallbackRuns.paysCore` and a 32-payment program. Kernel times are the
profiler's "type checking" for `decide +kernel`.

| Program | `Prog.run` kernel | tree kernel | ratio |
|---|---:|---:|---:|
| `guardLowCore` (no payment) | 7.9 ms | 8.2 ms | 1.0× |
| `paysCore`, funded | 4.4 ms | 8.1 ms | 1.8× |
| `paysCore`, unfunded (revert) | 3.6 ms | 7.8 ms | 2.2× |
| `pays32` (32 transfers), funded | 106 ms | 233 ms | 2.2× |
| `pays32` × 2000, `#eval` (interpreted, in the server) | 222 ms | 668 ms | 3.0× |

Everything still reduces by `decide +kernel`, because the finite tree is an
ordinary inductive. It is 2–3× slower, so the deterministic run must stay
the definition that the closer, `sol_prove`, chains and `RunAccel` evaluate.
Under A the tree would be an additional semantics beside the run (hence the
correspondence proofs in §2), not a replacement. C(ii) does not evaluate
at all.

## Summary by area

| Area | Today (raw) | A (trees) | B (allowance) | C | Churn | Automation |
|---|---:|---|---|---|---|---|
| Caller-model copy | 1587 | same as B | **−~940** (range arithmetic) | – | 5 files | none |
| `ExecS` + `exec_run` + `eq_run` + payment/`try` weakening | 1611 + 381 | +40 to +140 beyond B (extrapolated from the fragment; costs included) | 0 | fuelled loops +50–100 under A (included) | 31–49 files (A) / 29 files, 89 sites (B) | none (run stays primary) |
| Callback weakening, other cases | 1833 − 381 | 0 | 0 | – | 2–3 files | none |
| Deferred relations | 756 | 0 | 0 (−50 to −80 with a generic relational bind, independent of A/B) | – | 2–4 files | none |
| Run, RunWk, RunAccel, RunFuel, `*approx*` | 4588 + 885 code | 0 | 0 | C(i) −30..0; C(ii) net loss | 441 files if the run changed | tree 2–3× slower |
| Worlds / traces / CtxEquiv / Session | 3618 | 0 | −~100 (`Step`/`StepE`) | – | ≤3 files | none |
| Lowering split | – | 0 | 0 | C(ii) needs coinductive machine semantics | 44–135 files | – |
| **New infrastructure** | – | ~170 raw (Tree) + ~100 (fuel) + correspondence 200–300 | ~10 | C(ii) 185 measured, ≥500 more | – | – |

**Verdict.** Trees (A, C(ii)): **net loss**; `partial_fixpoint` (C(i)):
**irrelevant**. The allowance parameter (B): **modest saving**, about −940 lines out of the ~6k-line
callback, caller-model, weakening and deferred family (~16 %). This confirms the coordinator's range
(−500 to +1.5k) and locates the saving in B. The skeptic review corrected
the first draft's A estimate (−300..+200) to a net loss. **Next step:** apply B in the
core (`ExecS` by an allowance, `ExecSM`, `holdsR` and `execM_run` deleted,
the `Step`/`StepE` twin optional), and optionally add one generic relational
bind for `ExecThen`/`ExecCall`/`DirectCall`. Do not introduce trees.

## Method

- Line classes: a script splits each file at top-level declaration keywords
  and counts the lines from each keyword to the last non-blank line before
  the next declaration, docstring or command (so docstrings are excluded).
  Raw lines are `wc -l`.
- Duplicates: the copy is renamed (`sed`, e.g. `ExecSM M J` → `ExecS J`) and
  then compared with `diff -w`.
- Clients: `rg -l` over `Solidity/` and `Bridge/`, excluding `Solidity/Scratch/`.
- Gates: MCP diagnostics show no errors on each scratch module, and
  `#print axioms` on the re-proved results shows no `sorryAx`.
  `gate.sh checkpoint`: see the lane's CLOUD-RESULT.
