# Automation: expansions, sizes and the decision procedure

The milestones towards a closer that decides a fragment and a symbolic
execution of polynomial size.  M0–M5 and M8's A1/A3 are built; M6 is the
gate in force and the user's decisions; M7 is the decision theorem, its 32
features and what is still open; M7-next is the plan waiting for the
user's go.  Labels (M*n*, features *n*, plan steps *n*, decisions c … e3″)
are cited by Lean docstrings: keep them.

## M0 · The leaves of a type (`Theory/Typed/Leaves.lean`)

A type of finite shape (`Ty.Finite`, `Ty.finiteShape`: words, members,
fixed arrays up to `2^256`, mappings kept whole, no dynamic array outside a
mapping) is its words at its leaves (`Ty.leaves`, `Ty.leafCount`).  Leaves
are exactly the direct paths to a word (`Ty.mem_leaves`) and distinct
leaves diverge (`Ty.leaves_strip?_ne`).  A `uint[2^200]` has that many
leaves: every user bounds the count.

## M1 · The expansions, in the Theory and the interpreter (`Theory/Typed/Leaves.lean`)

A delete and a copy at a finite shape are a word written per leaf; a push
and a pop of a word are one slot and a save.  Theory: `Obs.delAt_expand`,
`Obs.copyTo_find_expand`, `Obs.push_prim`, `Obs.pop_prim` (under
`TVal.Shaped`, true of every typed value).  Interpreter, no premise:
`Storage.delete_expand`, `Storage.write_expand`,
`Storage.write_find_expand`, `Storage.push_prim`, `Storage.pop_prim`.

## M2 · The expansions as chain links past the program (`Calculus/ExpandLaws.lean`)

| link | from | to |
|---|---|---|
| `delAtExpand` | `delAt(s, p)` | `save(…save(s, p.l₁, 0)…, p.lₙ, 0)` |
| `copyExpand` | `save(s, p, find(s, q))` | `save(…save(s, p.l₁, select(s, q.l₁))…, p.lₙ, select(s, q.lₙ))` |
| `pushExpand` | `push(s, p, x)` | `save(pushSlot(s, p), p[p.length]@s, x)` |
| `popExpand` | `pop(s, p)` | `shrink(save(s, p[p.length - 1]@s, 0), p)` |

A delete and a copy fire at `Ty.expandable` types (finite shape, 1 to
`expandBound` = 64 words, counted by arithmetic so a huge array is refused
without listing it); a copy only from the storage it writes to; push and
pop only on arrays of words; no argument may push.  Exact in every typed
state, reverts and gas included (`Tm.eval_expand?`, `Tm.exhB_expandK?`,
`holds_upd_expand_iff`).  The links are Lean only and never tried by
`~=>`, `#chain` or `#last_line`: a worked chain keeps a `delete` whole, as
solkey does (`Examples/ChainExpand.lean`).

## M3 · Reads reduce write-free (`Calculus/ElimWriteFree.lean`, `Calculus/StepFragment.lean`, `Calculus/SymexFragment.lean`)

On the terms it reads (`LTm.Elimable`), the closer's read elimination
leaves no storage symbol (`LTm.elim_stoFree`).  The fragment
`Stmt.Frag`/`Prog.Frag` (storage writes of words or copies, expandable
`delete`, `push`/`pop` of words, aliases with an initializer, locals, `if`,
`require`, `assert`, `revert`, blocks, memory-free expressions) is kept by
every rule (`Stmt.step_saveLike`, `Stmt.step_elimOk`), so a `symex` leaf of
it eliminates storage-free (`symex_reduceS_stoFree`).  Left out: memory,
payments, calls, loops, `try`, compound assignment and `++`/`--` (saves too,
left out to keep the proof short), pushes of references.

Narrowed: an unset storage alias (binds `err`, which elimination keeps);
`wellFormed(s)` (kept as `wt(s)`, so a leaf with a `wt(storage)` premise is
not covered); save normal form is proved per update (`Upd.toLS_okNF`), not
on the pushed-in leaf; the walk (`Seq.residue`) is not covered, `symex` is.

## M4 · Completeness of the automatic decision (`Calculus/CondLift.lean`, `Calculus/LiftTotality.lean`, `Calculus/FlattenTotality.lean`, `Calculus/LeafTotality.lean`, `Calculus/AutoComplete.lean`)

`dependentReduction?` (`Calculus/DependentReduction.lean`; its stages in
[complete-verification.md](complete-verification.md)) decides a formula
once it returns a certificate.  The pipeline:

```
ProgramNormalization.ofFormula? 2048      exact program normalization
sourceReduction?                          updates pushed in (ExactAt, toLS)
LTm.elim / LFml.elim                      reads of writes eliminated
LFml.condSimp                             trivial conditionals folded
LFml.prenex                               consequent quantifiers in front  (M7)
LFml.liftCond condLiftFuel                conditionals lifted to cases
UniversalPrefix.ofFormula? 1024           the ∀ prefix
flattenedArithmetic? 2048                 reads to fresh atoms, alias constraints,
                                          checked linear arithmetic
```

**Lifting** (`Calculus/CondLift.lean`).  A read after a write at a
symbolic key eliminates to `kite x y t e`, a presence test to `ite`; the
compiler encodes affine values only, so conditionals are lifted at the
formula level rather than making the compiler return disjunctions.  The
split is three-way by the guard's outcome (equal, differ, halt), exact in
every context (`LTm.condSplit_eval`); `LTm.condSimp` first folds the
trivial ones.  The lift is complete once the fuel (`condLiftFuel` = 64)
exceeds `LFml.condMax` (`LFml.liftCond_src`).  `LFml.liftCondB` refuses
as soon as the lift passes `liftBudget` (1023 + 2048 nodes), so a leaf
with many conditionals is refused after bounded work, and refuses nothing
in `Fml.exactBounded` (`LFml.liftCondB_isSome`).

**The fragment** (`LTm.Src c w`, `LFml.Src c`): scalars (atoms, literals,
transaction fields, checked `+`/`-`, `*` by a literal, unary `-`/`~`, `seq`
guards, `err`, storage reads of a path, and before the cut, `w = true`, the
operators of features 5, 14 and 22), Booleans (comparisons, `!`, `&&`,
`||`, `==`/`!=`), paths (roots, fields, scalar mapping keys), and with
`c = true` `kite`/`ite`; formulas `tt`, equations, `¬`, `∧`, `→`.
`Fml.inExact` asks `leafOf? φ` to exist with a prefix under 1024 binding
every atom and a body in `LFml.Src true` within the lifting fuel;
`Fml.exactBounded` bounds the lifted (and cut) body to 511 nodes, from the
compilers' 1024-deep fuel.  The reads' bound is the leaf's own since
feature 15 (`readBudget`).

```lean
theorem auto_complete (φ : Fml C []) (h : φ.inExact = true) (hb : φ.exactBounded = true) :
    ∃ r, dependentReduction? φ = some r ∧ (Fml.Valid φ ↔ r.arithmetic.guarded.decide = true)
```

with `dependentReduction?_isSome` and `auto_countermodel`
(`DependentReduction.countermodelOfDecide` builds the state); axioms
Lean's three.  `Examples/AutoComplete.lean` applies them; on a `uint`-keyed
mapping the kernel's arithmetic over 256-bit codes overflows the language
server's stack, so that verdict is the compiled one and the refutation is
checked at its codes (`not_valid_of_codes`).

### What is narrowed, and what blocks the rest

The fragment is syntactic on the eliminated leaf, not the source:
`leafOf?` runs the stages above it.  A source characterization needs, per
stage:

* **Normalization**: its refusals are an unsupported statement
  (`ExactStatement.ofStatement?` takes local and storage assignment,
  deletion and primitive declarations; control flow and calls are unfolded)
  and the shared 2048-node budget, which counts continuations duplicated
  across branches.  Missing: a syntactic cost function mirroring
  `normalizeCore` with a proof that it bounds the consumption.
* **Update pushing** (`ExactAt.ofFormula?`): push-free updates, no memory
  local in scope, `Upd.toLS` defined, every atom read alike at both
  polarities (`Tm.agreeB`).  Missing: a characterization of `Tm.agreeB` and
  `Tm.toL` on the source fragment.
* **Elimination**: that `LTm.elim` maps those leaves into `LTm.Src true`
  below the fuel, an invariant the size of M3's `LTm.elim_stoFree`.

Kernel-evaluated recursion follows Gate G0 ([intrinsic.md](intrinsic.md));
the recognizers and size functions (`LTm.src?`, `LTm.nodes`, `LTm.conds`)
are `match`-based, a deviation from its condition 1 that is cheap on the
leaves the checks see.

## M5 · The size of what a rule emits (`Calculus/TermSize.lean`)

`Tm.size`, `Upd.length`, `Upd.tmSize`, `Fml.tmSize`, `Stmt.size` count
nodes, never a type. `Stmt.step_upds_le` bounds each generated update by
`s.updateLimit m`: two for non-lexicographic dispatches, including tuple
annotation erasure, and tuple arity plus one for the supported lexicographic
diamond dispatch (every old metric component and the condition capture).
`Stmt.step_upds_le_two` retains the two-element guarantee when the computed
limit is two. `Premise.Bounded` keeps two as its default update-length budget;
its optional explicit budget describes tuple snapshots without hiding their
elements. `LoopLex.snapshot_length` counts every component exactly.
The terms of the premise's updates and formulas (`Premise.upds`,
`Premise.fmls`) are still each at most `16 * s.size + 16`
(`Stmt.step_tmSize_le`), including all new-metric snapshots and all
lexicographic comparison connectives, with one lemma per arm.  The terms inside a program a
rule emits (a premise's continuation) are not bounded by it.

## M6 · The automation gate (2026-10-24)

The goal: every program the elaborator accepts (loops closed by their
invariants) and every specification decided without enumerating inputs,
symbolic execution polynomial in the text, the closer terminating with a
proof or a counterexample; CI fails on anything else.

**The user's decisions** (what may answer *unknown*):

* **(c)** a product of two non-literal KeY `int` terms (Matiyasevich: no
  terminating complete closer exists there); **(c′)** the same at 256-bit
  types (decidable bit by bit, but a kernel certificate for a 256-bit
  multiplier is out of reach without `Lean.ofReduceBool`).  Division,
  modulo, `**`, shifts and bitwise operators with two symbolic operands go
  with them (`x ** e` at a literal `e ≥ 2` is a product; `c / x` is
  division).
* **(d)** a quantified formula over array or mapping contents outside the
  array property fragment (Bradley, Manna and Sipma); negative-position
  `{havoc}`, `{anon}`, `allocAll`, `grow` and storage `bind` over formulas
  reading storage fall under it.
* **(e3′)** hashes are collision-free on each goal's own hash terms, a
  premise of that goal, not a global (false, vacuity-inducing) assumption;
  a verdict depending on `ecrecover` or a hash preimage may be unknown.
* **(e3″, 2026-10-26)** a negative-position value quantifier whose body
  compares two hashes the premise of its scope does not read: false only at
  a collision, so no certified refutation exists (`gapHashNegForall`,
  `Fml.negPairUnread`, no wider).

**Not impossible, but open**: a counterexample is a concrete typed state
certified by kernel evaluation, so a witness outside the symbolic shapes
below (a long array read element by element, a loop that does more than
count) is out of reach; literal-bounded loops are unrolled
(`docs/loops.md`, M8's A2).

**The gate**, `node scripts/check-automatic.mjs --strict` (CI, after the
TestSuite build): every TestSuite obligation derived by `sol_prove` (its
step budget and the leaf replay `sol_prove?` writes) or
`sol_auto_theorem`, or refuted by `sol_refute` (`TestSuite/Refuted.lean`:
false in the model, not merely underivable), none pending; counts equal to
`TestSuite/Report.lean`'s pin; and no TestSuite module past its build
budget (`--build-log`, 300 s by default).

Tools it relies on:

* `sol_refute` (`Tools/Counterexample.lean`): `¬ (⊢ φ)` or `¬ ⊨ᶠ φ` from a
  certified counterexample via `Proves.not_of_not_valid`.  Its search draws
  array shadows where `wt` admits them, which refutes the obligations that
  read an appended slot as its default (solkey's `SYMBOLIC_TAIL_OPENS`).
* `sol_auto_theorem n : φ` (`Calculus/Closers.lean`): the walk and each leaf
  with heartbeats of their own, the declaration added after.  A tactic
  cannot do this: whatever runs after it counts against the declaration.
* `sol_leaf_keep`: the leaf without the `allLeftHide` pre-pass, which loses
  the instance a goal's own `∀` opens later; the last of
  `Derive.leafTacs`.
* `sol_close_save_cases`: solkey's `selectOnSaveCons` at a symbolic index,
  the last alternative of `sol_close_quantified`.  The memory closer reads
  a copy of storage below its root (`readFromCopyToStorage`,
  `Theory/Typed/MemMirror.lean`).
* Leaf classification (`Derive.searchLeaf`, `Seq.goalFits`) also gets its own
  inherited heartbeat budget before the closing attempts. Earlier checked
  leaves can spend the enclosing command's budget; the next leaf must still
  be classified under the same fresh cap as its own attempts. If classification
  fails, the search skips reduction and tries the existing conservative closers.
  Proof construction, kernel checking and replay accounting are unchanged.

**Budgets: the rule.**  A heartbeat budget set as an option
(`withOptions … maxHeartbeats`) is never read by `checkMaxHeartbeats`,
which reads `Core.Context.maxHeartbeats`; set the context's limit.  Cap
each step at what the enclosing limit has left (`Budget.within`,
`Calculus/Budget.lean`; `sol_within`, `sol_skip_after`): a fresh count
alone lets a step started late overrun, and the declaration's next check
then throws a timeout nobody catches.

**Symbolic counterexamples (2026-10-25).**  `invariantClosedFormSum` is
refuted by `sol_refute` from a storage whose `values` has `2^255`
elements.  The witness is reachable in the model, where `wt` bounds a
length only by `2^256`; solc's `push` panics far below that, so the
refutation is a gap between the model and solkey's reading, not a bug in
solkey's obligation.  Three pieces, all kernel-checked:

* *Long arrays* (`Tools/LazyStorage.lean`): `SVec.rep v n`, unfolded only
  as far as a reader goes; `wt(storage)` is proved for it (`holds_wt_of`),
  not evaluated.
* *Counting loops in closed form* (`Semantics/RunAccel.lean`): a body that
  only adds literals to `uint` locals under `x < e`-style guards over a
  rigid `e` runs to its exit or first overflow in one step
  (`TRun.accel?_sound`); `Prog.runA` is `Prog.runF` with such loops
  accelerated (`Prog.runA_approx`).
* *The search*: when ordinary candidates fail, dynamic-array roots at
  `2^255` and `2^256 - 1` elements (`longCands`), certified by the kernel
  directly (`certifyLong`).  `invariantClosedFormSum`'s certificate checks
  in about 0.1 s.  Pins: `Examples/Tactics/SymbolicCounterexample.lean`.

**Why the walk was exponential.**  `ifElseSplit` copies the continuation
into both goals: `n` sequential `if`s give `2^n` leaves (about `6·2^n`
nodes; `n = 5` past 200 000 heartbeats); a call carries its callee's body,
so `fₖ(x) = fₖ₋₁(fₖ₋₁(x))` inlines `2^k` bodies, `7·2^(k+1) − 3` nodes;
literal-bounded loops unroll.  The remedies, each a change to the
calculus: joins, call summaries, loops by invariants only (M8's A2, open).

**The join** (`LeanTaclet.ifElseJoin`, `Calculus/Rules.lean`; arm
`iteStep`/`Upd.ifJoin?`, `Calculus/Arms.lean`; `sound_iteJoin`,
`Calculus/SoundControl.lean`).  An `if` on a simple condition whose branches
are each empty or one assignment of a value local (`Prog.joinArm?`, since
M8's A1) runs as one parallel update `{x := c ? e₁ : e₂}`, KeY's join.  The
branch reads its value lazily and never panics, diverges or calls, so the
update fails exactly where the chosen branch reverts (`ifJoin_agrees`).  The
rule is decided by the statement alone: `ifElseSplit` carries the converse
side condition.  The solkey fragment (`Stmt.inSolkey`) leaves out every
joined `if` and every conditional value (`Val.keyValue`).

**The joined leaf.**  The kernel closer lifts at most `liftConds`
conditionals (`LFml.decideLift`).  Past that, `sol_close` reads each joined
value as a fresh value and its defining fact (`sol_close_join`), and
`sol_close_join_steps` (`CloseJ`, `Calculus/CloseScoped/Steps.lean`) reads
the leaf one binder or update at a time, the rest held opaque (no
`kabstract`): every value is named once, intervals come from one-base
offsets (`hint`, `hintA`, `CloseJ.addInterval`), each `omega` runs in a
context cut to the facts it needs (`CloseJ.omegaIn`).  A single `simp`
over the whole leaf grew about cubically, because each update's rest is
entered under a fresh binder and `simp`'s cache misses it.  Thresholds:
the steps from `CloseJ.stepsMin` (2) joins within `CloseJ.budget`; the join
alternative within 160 k heartbeats and `joinMaxCases` (64) cases; a leaf
of more than `CloseJ.wholeMax` (5) joins is never evaluated whole, which
runs past the default heartbeats from six, so `sol_close` fails where the
steps do (a false leaf of six joins at 43 k).  Measured: the leaf by steps
grows about 5 k heartbeats a join (`n = 12`: 56 k), the walk `5n + 3`
nodes.  Open: a leaf that is not a chain of binders and updates over its
post is peeled only up to it; a joined value of two bases (`c ? y : z`)
gets no interval.

**Calls by summary** (`LeanTaclet.internalCallSummary`; `CallRet.summary?`,
`Calculus/CallSummary.lean`; `Premise.sound_callSummary`,
`Calculus/SoundSummary.lean`).  A call `y = f(args);` of one value to a
value local, arguments simple, whose callee calls and has a summary, is the
update `{ y := R(args) }`, `R` the body run symbolically once in its own
frame (`Prog.sym`).  `T v = e;`, `v = e;`, blocks and such calls have one;
anything else (`if`, `require`, loops, state writes, external calls,
reference locals) is inlined (`internalCallExpand`, side condition
`= none`).  A term that may revert is owed by the local holding it until a
strict read takes it over, so the update fails exactly where the call
reverts (`Prog.sym_sound`, `CallRet.summary_agrees`).  The gate
(`Tm.sumGate`) asks value locals only, nothing pushed, and size under
`16 * body.size + 16` (M5 still holds, `CallRet.summary?_bounded`).
Literal offsets and factors fold as the terms are built (`Tm.norm`,
`Op2.mk2`, KeY's `polySimp`), so the doubling family's summary is
`x + 2^k` and the tripling family's `x * 3^(2^k)`.  The tools compute the
summary by `Kernel.whnf`, which runs outside the heartbeats, so
`summary_cond` hands it at most `summaryNodes` (200 000) distinct
subterms.  The solkey fragment leaves out a call with a summary
(`CallRet.sumOK`).

**Call sites shared (2026-10-25).**  A summary is one term, so an unfolded
one (`f₀(x) = x * 3 + 1`: `2^(k+1)` operations) evaluated whole grows as
`3^(2^k)` under the checked wraps.  `sol_close` reads it one call site at a
time: `CloseJ.shareStep` rewrites `{ y := C[s] } φ` to
`{ shₖ := s } { y := C[shₖ] } φ` at the innermost strict redex
(`Tm.redex?`, `Calculus/LeafShare.lean`; `holds_upd_share`), then
`CloseJ.peel` reads it as a joined leaf, each checked product's failing
case closed by `omega` (`CloseJ.closeArith`).  From `CloseJ.shareMin` (4)
operations; past `CloseJ.shareWholeMax` (8) never evaluated whole.  Linear
in the call sites (32 sites: 79 k heartbeats); 64 sites run past
`CloseJ.budget`.

**The runaway.**  `simp`'s discharger tried `forall_const`
(`[Nonempty α] (α → b) ↔ b`) at every premise of nested range checks; the
failed `Nonempty` instance searches grew sevenfold a level (8.7 s at sixteen
products) in time the heartbeats do not count.  `Close.forall_const_type`
and `Close.exists_const_type` (`Calculus/CloseLemmas.lean`) take a type's
binder only and replace them in the closers' cleanup.  Whole evaluation
then costs 24 k, 107 k, 803 k heartbeats at 8, 16, 32 products: bounded,
not polynomial.  Lesson: a timeout that the heartbeats do not see is an
instance search or a `Kernel.whnf`; bisect on `simp`'s `maxSteps` and read
`set_option profiler true`.

**One body a function (2026-10-25).**  Every call of a callee holds the
same body term, so a program is a DAG the size of the source and the
kernel's caches evaluate a callee's summary once (distinct subterms grow by
87 a level of the doubling family, where they doubled).  No calculus
change: a callee whose locals end with the call (`FunDecl.endsWithCall`)
numbers its locals from its first call's (`CallMemo.enter`/`leave`,
`Syntax/Elab/Values.lean`), so its copies are one term; the elaborator
reads a repeated body back (`CallMemo.body?`, `implemented_by`), and
`reachableBy` visits each function once a round; the quoters memoise a
body per object (`QMemo`, `Prog.quoteBody`).  No earlier speed change is
undone.  `elabCallRetWith` is split because one more bind ran its own
definition past the default heartbeats.

## M7 · The theorem (`Calculus/Decision.lean`, `Calculus/Prenex.lean`)

### The statement

```lean
inductive LeafVerdict (C : Contract) | proved | refuted (σ : State C []) | unknown

def decideGoal (φ : Fml C []) : LeafVerdict C   -- total, computable

theorem decideGoal_sound    : decideGoal φ = .proved → Fml.ValidH φ
theorem decideGoal_refutes  : decideGoal φ = .refuted σ → ¬ Fml.holdsH σ φ

def DecisionTheorem (w : Waivers := {}) : Prop :=
  ∀ (C : Contract) (φ : Fml C []), φ.inTarget w = true → decideGoal φ ≠ .unknown
```

The statement is about one computable function ("some decider is
complete" is vacuous by `Classical.choice`).  It is the goal, not true
today: the pins in "What is not proved" are in `Fml.inTarget` and answered
*unknown*.

`Fml.inTarget w`, on a program-free leaf, is everything but the waived
shapes:

* (c, c′) products of two non-literal terms (`mulmod` of two symbolic
  factors included), and `/`, `%`, `**`, `<<`, `>>`, `&`, `|`, `^` with two
  symbolic operands (a symbolic divisor, exponent or shift counts as two);
  each class a field of `Waivers`, all four waived (2026-10-25).
* (d) polarity is tracked; a negative `∀` block reading at its variables
  must be the Bradley–Manna–Sipma shape (`Fml.apfBlock`): `guard → value`
  parts, guards `&&`/`||` of `<`, `<=`, `==` (never `!=`) on index terms,
  never a strict comparison of two bound variables (`strictSorted`), values
  reading bound variables only as indices, never nested (`a[a[i]]`), at
  most one bound index on a path (`gridApf`: Bradley, Manna and Sipma state
  their result for one dimension; decided 2026-10-25).  A Presburger
  quantifier (reads nothing at its variable) is in at any polarity, but
  past a negative one only Presburger ones are.
* (e3′) each goal read under its own collision-freeness premise
  (`Fml.HashFree`, `Fml.holdsH`: the premise taken at every scope, about
  finitely many evaluations; no axiom; `Fml.validH_iff` on a hash-free
  leaf).  A hash is in only where the premise settles it: an operand of
  `==`/`!=` against a hash of its kind, or a key of a root all of whose
  keys are hashes of that kind, the hash of a memory local in the starting
  memory (`Tm.hashOfLocal`).  Outside: `ecrecover`, a stored hash, a hash
  under a hidden memory binder or an anonymising update (they range over an
  unset reference, whose key reads `0`: `namesBound`).
* (e3″) `Fml.negPairUnread` (above).

Properties of the reading: the per-scope premise depends on where binders
stand, so `LFml.prenex` is exact for `holds` but not `Fml.holdsH`, and
`decideGoal` prenexes only hash-free leaves (and the swapped leaves of
feature 11, which have none); a hash of an identity naming no object
returns `0`; a program's hashes are not read by the premise (on a formula
with a program `decideGoal` answers by `Fml.Valid`, the stronger
reading).

### What is proved

`decideLeaf_sound`, `decideLeaf_refutes`, `decideLeaf_complete`
(`φ.Covered = true → decideLeaf φ ≠ .unknown`), `decideLeaf_proved_iff`;
`decideGoal_complete` (hash-free), `decideGoal_complete_hash`
(`Fml.hashCovered`).  Each pipeline has its exactness and totality
theorems, named in the feature that adds it; the `#print axioms` pins
(Lean's three, `sorry`-free) sit in `Calculus/Decision.lean` and in each
pipeline's module.

`Fml.Covered` is `Fml.CoveredA || Fml.memCovered || Fml.kintCovered ||
Fml.kencCovered`.  `Fml.CoveredA` (`decideLeafA`) is M4's
`Fml.inExact && Fml.exactBounded` extended by features 1, 2, 4, 5, 8, 14
and 15, or one of the pipelines' fragments: `Fml.quantCovered` (3, 6, 7,
16–20), `Fml.ledgerCovered` (9), `Fml.arrayCovered` (10),
`Fml.ledgerBlockCovered` (21), `Fml.arrayBlockCovered` (32).
`Fml.memCovered` is 13, 23, 24's; `Fml.kintCovered` 26's;
`Fml.kencCovered` 30 and 31's; `Fml.hashCovered` 11, 12, 27–29's.

### The features

Each extends the fragment with its completeness proved through every stage
(recognizer, lifting, flattening, compilers).  Pins: `Examples/Decision.lean`
(the former `gap*` leaves of every feature), `Examples/DecisionHashes.lean`
(11, 12, 27–29), `Examples/DecisionMemory.lean` (13, 23, 24),
`Examples/DecisionKInt.lean` (30, 31), `Examples/DecisionArrays.lean` (32):
a proved and a refuted leaf per shape, coverage kernel-checked
(`*_covered`) for at least one, `*_answers`/`*_iff` applying the theorems.

1. **Checked multiplication by a literal** on either side
   (`CheckedScalar.scale`: the code under the range guard); decided by
   `AFml.decide_iff`, not `omega`.
2. **Universal quantifiers in a consequent**: `pre → ∀ k. post` is
   `∀ k. pre → post` when `pre` reads no `k` (`LFml.prenex`).
3. **Presburger quantifiers** (plan step 4): a quantifier left past the
   prefix whose body reads no storage or transaction field (after
   feature 6).  `quantReduction?` (`Calculus/QuantReduction.lean`)
   abstracts each quantified subformula to a fresh Boolean atom
   (`LFml.abstractQ`), compiles it to `QFml` (`QArith.compile`), and
   decides one sentence by `QFml.decide_iff`/`QFml.verify`
   (`Calculus/PresburgerDecision.lean`: binary derivatives with
   projection; a bound `x < 2^256` is an atom whose derivatives halve it, no
   value enumerated).  Fragment `Fml.quantCovered`
   (`Calculus/QuantTotality.lean`), `quantReduction?_isSome`.
4. **Unary `-` (`int`) and `~` (`uint`)** as affine codes (plan step 1).
5. **Operators cut into fresh atoms** (`Calculus/QuotientCut.lean`, plan
   steps 1–2): `int(·)`/`uint(·)`, `/` and `%` by a nonzero literal, low
   masks, `>>`/`<<` by a literal, `+%`, `-%`.  `LFml.cutAll` replaces each
   node by an atom sequenced after its operands with its definition in the
   antecedent, one atom per distinct node; exact in a universal reading
   (`LFml.cutAll_valid_iff`, `LFml.holds_cutAll`); the compiler encodes each
   definition as a linear relation (`StorageEncoding.special?`).
6. **Reads hoisted out of quantifiers** (`Calculus/QuantHoist.lean`, step
   4): a read of a total path at no bound variable becomes an atom with its
   definition in front (`hoistPrep_valid_iff`).
7. **The array property fragment** (`Calculus/ArrayProperty.lean`, step 5):
   a negative `∀` block over a mapping at a root is replaced by its
   instances at the index set `U` (`0`, the ground keys, the guards' ground
   operands and their successors; `LFml.apfInst_sound`).  Exact
   (`ApfFml.apfInst_refute`): from a failing instance, the state whose
   rebuilt mappings hold at each key what its floor in `U` held.  Inner
   mappings (`allow[3][k]`) included.
8. **KeY `int`** (step 3): literals, `toInt`, `+`, `-`, products by
   literals, comparisons, compiled as the difference of two unbounded
   natural codes (`KIntValue`); nothing overflows, no guard.
9. **Reads of the starting ledger** (`net(a)`, `Calculus/LedgerReduction.lean`,
   `Calculus/LedgerCut.lean`): each read an entry atom with pairwise
   consistency premises (`LFml.ledgerCut_valid_iff`); a false assignment
   realized as a ledger pulled back to the addresses (`LFml.ledgerPull`).
10. **Storage arrays at symbolic indices** (step 6, arrays of primitives at
    roots, `Calculus/ArrayReduction.lean`, `Calculus/ArrayCut.lean`):
    updates pushed in exactly for the Theory's reads (`Tm.toLT_sound`,
    `Calculus/TheoryRead.lean`), slot tests a length check settles folded,
    fallbacks lifted, then every array read cut to index and value atoms
    under what actual arrays make of them (`LFml.aCut_valid_iff`); a
    refutation rebuilds the arrays (`arrRealize`) after shrinking its codes
    heuristically: a length near `2^256` the shrinking cannot lower exists
    but cannot be built.  Runs ahead of the ledger pipeline (which recurses
    too deeply on array leaves).
11. **Hashes under the premise** (step 7, `decideHash`,
    `Calculus/HashSwap.lean` … `Calculus/HashComplete.lean`): fresh byte
    strings read only by hashes of one kind are swapped for the words their
    hashes return (`Fml.swPrefix`; valid where the body's value binders are
    positive, `Fml.swPrefix_validH`); refutations are instances at one
    family string per class of equal strings (restricted growth strings:
    15 instances for four strings, 52 for five), whose hashes are distinct
    and nonzero by the kernel for four strings (`famOK`) and computed past
    that (`famCheck`); exact on `Fml.rl` (`Fml.swPrefix_exact`).
12. **Two kinds of hash** (`decideHash2`, `Calculus/HashKinds.lean`): the
    second kind's words as new `∀ uint` binders linked to the first kind's
    (`Fml.tk`, `linkE`); `Fml.tk_validH`, `Fml.tk_refutes`,
    `Fml.tk_complete`; `hashTries` tries the ordered pairs.
13. **Fresh memory arrays** (step 6, `decideMem`, `Calculus/MemSwap.lean`):
    reads of fresh arrays of primitives cut to a length word and one word
    per read under Ackermann's constraints (`Fml.mxTop`), a read past the
    length the halt `1 / 0`; exact at every state (`Fml.mxTop_holds`), so
    the refutation is the cut leaf's state.
14. **Literal operators through the others** (`Calculus/QuotientCut.lean`,
    `Calculus/BitArith.lean`): `x & c` bit by bit (`bandGo`, fuel `c` so the
    kernel never unfolds a fixed 256), `|`, `^` through `&`, `*%` by
    doubling, `**`/`**%` at `0` and `1`, `int` `/` and `%` by sign cases
    (`defDivI`), the literal on either side.
15. **Reads without a fixed bound**: the flattener's budget is
    `readBudget φ = max 2048 (words²)` in every pipeline.
16. **`bool` quantifiers expanded** (`Calculus/QuantExpand.lean`):
    `φ[true/b] ∧ φ[false/b]`, exact at every state.
17. **Positive quantifiers past the prefix** (`dropPrep`): a positive `∀`
    outside every negative one read at a fresh atom, one binder at a time
    (`LFml.dropOne_spec`); the refutation is the state itself.
18. **Every `uint` key along a root's mappings floored** (`FloorShape.of`,
    `FloorShape.rebuild_word`): a bound key need not be the last, may occur
    at two depths, may be followed by a member.  Price: a ground `uint` key
    along the mappings joins the index set, so it may mention no binder of
    the body.
19. **Guards whose ground operand may halt** (`k < x - 1`): allowed unless
    a `||`'s left operand may halt at the floors where it returned at the
    keys (`GuardP.floors`, `GuardP.defined`).
20. **Blocks over `int` keys, refutations by regions**
    (`Calculus/FloorRegion.lean`): one pass per key type (`OrdK`,
    `apfPrepK`), the type's least value as the floor's base; a rebuilt
    mapping listed region by region between breakpoints (`regionList`,
    `lookupBy_regionList`), its reads proved by region reasoning, never
    evaluated.  So leaves whose every refutation lists `2^255` keys are
    answered, the state a term no evaluation builds (`intTwoSides`).
21. **Blocks over the ledger** (`Calculus/LedgerBlock.lean`,
    `ledgerBlockReduction?`): `apfPrep` inside the ledger's pipeline, the
    ledger rebuilt region by region.  A region is left out only where the
    solver's word is the default, so a leaf with a small refutation may be
    answered by a huge one, which evaluating the verdict would try to build.
22. **`&`, `|`, `^` at `int`; `addmod`/`mulmod` at a literal modulus**:
    `int(uint(a) ⊙ word(v))` (`intBit`); `addmod` through remainders and a
    case-defined sum (`amodDef`); `mulmod` by doubling along the literal
    factor.  No new definition reaches the compilers.
23. **An index bound after its array** (`Calculus/MemHoist.lean`):
    `Fml.hoist` moves positive value binders out of consequents, conjuncts
    and past fresh objects' binders (`Fml.hoist_holds`); `decideMem` cuts
    `(φ.hoist 1024).mxTop`.
24. **Writes in a leaf's update** over fresh arrays (`Calculus/MemSwap.lean`):
    the read table rewritten past each write (`MxEnt.wr`), the update's
    landing a guard (`mxGuard`); still exact at every state.
25. **Ledger reads past ledger writes** (`Calculus/DecideScoped.lean`,
    `Calculus/DecideTyped.lean`): the symbolic state keeps the writes
    (`SymS.netW`) and a read past them is the starting entry moved by each
    (`NetW.read`, a `kite` the existing lift takes).  A snapshot
    `x := net` past a write stays outside.  Each write multiplies the lifted
    leaf: two payments to one address read once already pass 511 nodes.
26. **Binders of KeY's `int`, positive** (`Calculus/KIntBinder.lean`,
    `decideKInt`): `∀ int z. φ` in a positive position of a leaf reading no
    ledger is `{z := net(n)} φ`, the `n`-th binder at address `n`
    (`Fml.zT_valid`, `Fml.holds_zT`; fragment `Fml.zOK`).
27. **A second kind hashing one string**: no pair to link, so feature 12's
    condition holds vacuously (`Fml.tkBody`).
28. **Three kinds** (`Calculus/HashKinds3.lean`, `decideHash3`): the third
    kind's words a layer inside the second's (`Fml.tk3`; `Fml.tk3_validH`,
    `Fml.tk3_refutes`, `Fml.tk3_complete`).
29. **Second-kind strings the first does not hash** (`Fml.tkKeep`,
    `Calculus/HashMove.lean`): only kept pairs are linked; completeness
    moves a refutation to the fully linked reading first
    (`Fml.tk_complete_move`).
30. **Binders of KeY's `int` over two words, either polarity**
    (`Calculus/KIntEncode.lean`, `decideKEnc`): where every comparison reads
    the binder against a remainder bounded by `R` (`Tm.zl`), the body holds
    at `z` exactly where it holds at `z` clamped to `[-R-1, R+1]`, an
    interval inside `c·toInt(a) - toInt(b) - (R+1)` over two words, so
    `∀ int z. φ` is `∀ uint a b. φ[z := …]` (`Fml.holds_kencAt`).  *Why
    this route*: an unbounded atom position in `AEnv`/`LTm`/`LFml`/`QFml`
    touches some forty modules, the closer's among them; the ledger's
    addresses cannot give a negative binder its `∃`.  The clamp is one
    module and reuses the quantified and ledger pipelines.  A base-`2^256`
    encoding took over twenty minutes to evaluate; `c` is the least
    multiplier that covers the interval.
31. **Binders past an anchor**: a comparison against an unbounded term at
    another coefficient (`z == net(a)`, `y > z`) is tried past each key of
    the context (`Fml.holds_shift`, `Fml.kencAtA?`), needing only the key
    sums to cancel.
32. **Blocks over storage arrays** (`Calculus/ArrayBlock.lean`,
    `arrayBlockReduction?`): feature 10's pipeline with a preparation:
    array paths in `ApfTm`, dynamic arrays of primitives floored slot by
    slot (`FloorShape.arr`, `arr_rebuild_slot`, `ArrOK`), each length an
    atom in the index set (`lenPrep`), instances folded (`LFml.litFold`,
    `LFml.slotFold`; `gapArrayBlock` 1626 → 187 lifted nodes).

### Running time

Both decisions walk their derivative graphs depth first, the states seen
in an `HSet` (`Calculus/VisitedSet.lean`), stopping at the first state
false at zero.  `AFml.fastVerify` (`Calculus/LinearDecision.lean`) reads
one bit of one variable a step and normalizes first (`AFml.norm`); a closed
walk proves the formula by `AFml.valid_of_rounds`.  `QFml.fastVerify` sorts
`∃` lists by hash (`canon`) and memoizes zero tests (`atZeroC`, `exTest`).
The walks' fuel (`2^64`) is not proved to suffice; past it they fall back to
the proved breadth-first search (`AFml.search_iff`, `QFml.search`), so
`decide_iff` holds either way.

Costs that guide work:

* The `AFml` walk recurses once a bit read, about 256 × variables deep: a
  leaf of fourteen reads at distinct keys overflows the interpreter's stack
  (`gapManyReads`, fifty reads, is covered and answers by the theorem, its
  verdict not computed).  A walk with an explicit stack would lift this.
* Array verdicts are evaluated one after another (`set_option Elab.async
  false`); in parallel they overflow a command-line `lean`'s stack.
* Some interpreted verdicts take minutes (`gapIntAnd` 886 s, `mulmodLt`
  741 s: the arithmetic over conversion and remainder atoms), so they are
  pinned by coverage, not evaluated in the build; `Examples/DecisionKInt.lean`
  records its verdicts in a comment for the same reason.
* `Examples/Decision.lean` builds in about 460 s (`sortedLe`, a
  two-variable block, about two minutes of it), `Examples/DecisionArrays.lean`
  in about 1500 s, presumably its two kernel coverage checks
  (`gapArrayBlock_block`, `arrayBlockBad_block`), not yet profiled.  The
  gate's 300 s budget covers TestSuite modules only.

### What is not proved

* `DecisionTheorem` itself.
* `Fml.Covered ⊆ Fml.inTarget` on program-free leaves: `Fml.Covered` is read
  on the eliminated leaf, `Fml.inTarget` on the source, and M4's "what
  blocks the rest" stands.
* The node bound of `Fml.exactBounded` (511 lifted nodes, from the
  compilers' 1024-deep fuel); lifting it means computing those fuels from
  the term, as `readBudget` does for reads.
* A time bound.  The graphs stay exponential in the worst case (a bound
  `x < 2^256` costs 256 rounds of every variable; a quotient by `d` keeps
  about `d` constants a bit; a `QFml` state has `2^n` successors); ledger
  reads at one address are not merged (`netSwap`, four reads, is the
  slowest ledger pin); a block over `n` variables has `|U|ⁿ` instances
  (`sortedLe`: nine instances, nineteen reads, about two thousand nodes).
  A region refutation can be a term too large to build; no construction
  does better in general (a sorted mapping read at three far keys).
* **The pinned gaps**: in `Fml.inTarget` (by the kernel, `*_inTarget`) and
  answered *unknown*.  One leaf a shape:
  * `gapKIntTwoAnchors` (`Examples/DecisionKInt.lean`,
    `(∀ int z. ∀ int y. y > z → y > 0) → 0 == 1`): key sums that differ past
    every anchor, Presburger alternation over ℤ.  Needs an unbounded binder
    in `LFml`/`QFml` (`AEnv`, `LTm`, `QArith.compile`) or Cooper's test
    points (`Fml.kencAtA?` trying each anchor per comparison, the
    disjunction of the instances).  With one unbounded and one bounded
    threshold (`∀ int z. net(0) == z → z > 0`, not pinned) a one-point rule
    decides it: a `Fml.onePoint` pass before `Fml.kencB`, its lemma by
    `Fml.holds_sb`.
  * `gapQuantLedger` (`(∀ uint y. y > 0) → net(0) > 0`): a negative
    quantifier in a leaf that reads the ledger.  Next: the ledger cut ahead
    of `quantReduction?`'s abstraction, the entries as parameters of the
    abstracted subformulas (`Rep`, `QArith.compile` over two codes an
    entry).
  * `gapMemInnerNeg` (`Examples/DecisionMemory.lean`,
    `(∀ i. i < len(s) → s[i] == 0) → s[0] == 0`): a negative block over a
    fresh memory array.  Next: in `Calculus/MemSwap.lean`, before `Fml.mx`,
    instantiate it at the index set of the array's other reads, its length
    binder and the guards' operands with successors (the `Fml` analogue of
    `LFml.apfInst`); exactness needs a memory-array floor (feature 32's
    `arr_rebuild_slot` argument over `MxMap`).
    The additive reconstruction prerequisite now has an object-level interface
    (`Calculus/MemFloor.lean`); [its task handoff](feature-work/memory-negative-block.md)
    records the exact optional-read proof and remaining preparation obligations.
    The original gap and its `unknown` pin remain open.
  * `gapMemParam`: a hidden memory binder ranges over the given heap's
    objects, which may alias; a refutation needs a heap object holding the
    witness words, which `decideLeafA`'s state does not carry.
  * `gapMemStruct`: a fresh struct with reference members needs objects for
    them, so the cut is exact only at heaps that have them.
  * `gapWrittenMemory` (`Examples/Decision.lean`,
    `∀ s t. [ s[0] = 1; ] keccak256(s) == keccak256(t)`): a hash of written
    memory.  Next: `decideMem`'s cut inside `decideHash`, input equality as
    a negative `∀` over the written arrays (after `gapMemInnerNeg`).
* Unpinned shapes in the target: fixed arrays and arrays below a mapping
  key in a block (`FloorShape.of` keeps them; they need a `fixed` shape and
  their length in the index set, or a length atom); cut leaves past 511
  nodes (a two-variable block over arrays); a realized array with
  non-default words past its length rebuilds up to `2^256` slots; a `||`
  whose left operand holds a `&&` with a halting right operand (no `dl!`
  spelling; whether the instantiation is exact there is open); KeY-`int`
  remainders past about `2^511` (`zMul n ≤ 2^256`).
* Array reads outside feature 10: below a field or mapping key, of structs
  or arrays (`a[i][j]`), an index reading an array (`a[a[0]]`), whole-array
  reads (`delete a`, copies), more than `orBudget` fallbacks.  Memory:
  allocations and copies in a leaf's updates, struct members and nested
  arrays of a fresh object, an index reading memory or storage; programs
  with memory statements are refused by `ProgramNormalization` already.
* Outside the target by the decisions: `gapHashNegForall` (e3″), `notApf`
  and the waived classes, stored hashes, hashes of hidden binders' strings,
  nested blocks under a negative quantifier.

### The plan for the rest

Steps cited by the examples; one feature a round, each with its
completeness proof through the stages.

1. Unary `-` and the conversions: done (features 4, 5).
2. Literal division, modulo, shifts, masks, wrapping operators: done
   (features 5, 14, 22).
3. KeY `int`: done for linear terms, ledger reads and writes, binders of
   either polarity (features 8, 9, 25, 26, 30, 31).  Left:
   `gapKIntTwoAnchors`, `gapQuantLedger`.
4. Quantifiers in the arithmetic: done (features 3, 6).
5. The array property fragment: done for mappings at any depth, `bool`,
   `uint` and `int` keys, the ledger, dynamic storage arrays at roots
   (features 7, 16–21, 32).  Left: fixed arrays and arrays below keys,
   memory (`gapMemInnerNeg`), the halting `||` operand.
6. Memory and array indices: done for storage arrays of primitives at
   roots and fresh memory arrays of primitives (features 10, 13, 23, 24).
   Left: arrays below fields and keys, of structs and arrays; the memory
   gaps above.
7. Hashes under the premise: done for fresh strings of up to three kinds,
   any number of strings (features 11, 12, 27–29).  Left:
   `gapWrittenMemory`.
8. `Fml.Covered ⊆ Fml.inTarget` on program-free leaves: M4's list, then the
   511-node bound by fuel computed from the formula (reads done, feature 15).

Open small items from the reviews of feature 31: `Calculus/KIntEncode.lean`'s
docstring calls `[-R-1, R+1]` the encoding's range (it lies inside it) and
`c` a word, and its "Outside" paragraph should state the key-sum
condition; `Fml.kencB`'s docstring cites `Fml.kencAt?` (it uses
`Fml.kencAtA?`); `AKey`'s positions are `Nat`s where `Idx Γ .kint` /
`Idx Γ (.val .uint)` would make `State.zν` and `AKey.tm?` total;
`Idx.eq_of_toNat_eq` duplicates `Idx.toNat_inj`; bare `simp` on the
`s ≠ .kint` side goals; `φ.kencB` computed more than once in `decideKEnc`
and `Fml.kencCovered`; `Op2.zl` refuses `(1+1)*z`; `kencAtA?` retries
repeated literal addresses; no `kintNegWord_covered` pin.

## M8 · Polynomial size (2026-10-25)

M6's theorem measured where it is not yet true.
`Examples/Tactics/PolySize.lean` pins three families by `#proof_size`
(`#proof_tree`'s nodes, branches, open goals and the largest leaf in
`Fml.tmSize` term nodes):

* **F1**, sequential `if`s that both assign:
  `⟨ uint x = 0; if (a == 1) { x = x + 1; } else { x = 0; }; …; ⟩ x <= k`;
* **F2**, `k` literal-bounded loops in sequence, each closed by its
  invariant (`i <= 10 && s == 10 * (j - 1) + i`), then `s == 10 * k`;
* **F3**, one such loop whose body is `k` sequential `if`s.

Steps: **A1** joins every `if` whose branches only assign locals (done),
**A2** literal-bounded loops by their invariants only (open), **A3** the
recursion depth of kernel checks (done).

Counts and times (`maxHeartbeats 2000000` a command; scratch modules on a
4-core container), before → after A1:

| k | F1 nodes | F1 branches | F1 time | F2 time | F3 nodes | F3 time |
|---|---|---|---|---|---|---|
| 1 | 11 → 8 | 2 → 1 | 0.9 → 0.6 s | 2.1 s | 18 → 14 | 6.8 s |
| 2 | 26 → 13 | 4 → 1 | 2.1 → 1.3 s | 8.2 s | 35 → 19 | 42.6 s |
| 3 | 55 → 18 | 8 → 1 | 5.3 → 1.4 s | 20.2 s | past 2 M heartbeats | |
| 4 | 112 → 23 | 16 → 1 | 14.4 → 1.7 s | 42.7 s | past 2 M | |
| 5 | 225 → 28 | 32 → 1 | 35.7 → 2.3 s | 81.4 s | past 2 M | |
| 6 | 450 → 33 | 64 → 1 | 89.3 → 2.9 s | 145.5 s | past 2 M | |

F1 was `7 · 2^k + k − 4` nodes and is now `5k + 3`, its leaf `16k + 9`
term nodes.  F2's walk is linear (`7k + 3` nodes: an annotated loop is
closed by its invariant whatever its bound, `docs/loops.md`, decision 3)
but its time about cubic: the leaves past the `j`-th loop read `j`
anonymised frames.  F3's walk is linear since A1, but its preservation leaf
past `{anon}` is still past 2 M heartbeats from `k = 3`.

**A1 in force.**  The join gate (`Upd.ifJoin?`) takes every `if` whose
branches are each empty or one value-local assignment; a branch of two
statements, or one that writes state, calls, reverts or declares, splits.
Joining had been narrowed because two cases are cheaper for the closers
than a conditional term; the closer now gets them back at the leaf:
`sol_close_ite_split` (`CloseSplit`, `Calculus/LeafSplit.lean`, KeY's
`ifthenelse_split` on a joined value with a `bool` local condition; first on
one or two such updates, after the steps up to `CloseSplit.splitMax` (6),
each within `sol_within 160000`), and the walk's kernel closer lifts the
first conditional to the top (`LFml.liftTop`).  `⊢ₖ` (solkey's taclets
alone) no longer runs those `if`s nor conditional values.  May slow
checking: `sol_close` tries the split first on joined leaves, and the
kernel closer evaluates `liftTop` where `liftCond` did not close (the
TestSuite modules took 1023 s against 1045 s before).

**A3 in force.**  No `maxRecDepth` override for a certificate:
`certifyLong` builds its certificate with the arguments written, the peeled
state and formula read by `Kernel.whnf` (bounded by the stack, not by
`maxRecDepth` or heartbeats); `Evm/Examples.lean`'s `pow_run` decides each
conjunct separately.  The only `maxRecDepth` settings left are
`ProveChunked`'s and `Derive`'s per-step contexts and the generated
`Corpus/TestSuite.lean`'s.

### What is left

1. **A2 · Literal-bounded loops by their invariants only.**  An
   unannotated loop (`.auto`, `whileUnwind`) is unwound, its walk growing
   with the bound's value: report it (a warning naming the loop) rather
   than unroll silently, keep unrolling as an opt-in option in
   `docs/options.md` if the TestSuite needs it (list the obligations), then
   re-measure PolySize.
2. **The cost of a loop's leaves past `{anon}`** (F2 cubic, F3 past 2 M):
   measure one leaf in a scratch module before changing anything.
3. **Branches of more than one assignment** (`x = a; y = x + 1;`): a join
   needs the assignments composed without substituting terms into each
   other, so the update stays linear.
4. **A conditional term in `dl!`** (`Calculus/Notation.lean`): until then a
   chain cannot write a joined line.  Then restore the original programs
   of `Examples/Chains/StorageCoverage.lean`'s `ifElseUnfold`/`ifElseSplit`
   rows (their `else` now has a second assignment to keep the split), add
   an `ifElseJoin` row, and finish `Examples/ChainNotation.lean`'s
   `ifTrace` past the join.
5. **The kernel closer on a joined mapping key**
   (`boolKeyMappingSymbolicKey`, `TestSuite/Derived5.lean`, needs
   `sol_leaf; sol_close`): a case split on a Boolean atom with the atom
   substituted (`ifthenelse_split` with `applyEq`).
6. **Joined values the steps cannot bound**: two bases (`c ? y : z`), or
   more than `CloseSplit.splitMax` updates.
7. **The solkey fragment**: `⊢ₖ` cannot reach `ifElseSplit` on joinable
   `if`s under the one-rule-per-statement strategy.
8. **Small items**: `CloseJ.affine` misses `Int.negSucc` literals; the
   split's congruence lemmas (`Fml.SplitTo.valid`, `andL`, `andR`) carry no
   Solidity in their docstrings; `#proof_size` is declared by an example
   file (move it to `Tools/ProofTree.lean`, pin it in
   `Examples/ProofTree.lean`); `certifyLong` reads `Γ` off the formula's
   type, always `[]`.

## M7-close · The M7 lanes closed (done at step 1, 2026-10-26)

Features 30–31 (`kintneg`) and 32 (`apfarrays`) merged; steps 2–5 of the
original plan moved to M7-next.  Still pinned, in `Fml.inTarget` and
answered unknown (M7, "What is not proved"): `gapKIntTwoAnchors`,
`gapQuantLedger`, `gapMemInnerNeg`, `gapMemParam`, `gapMemStruct`,
`gapWrittenMemory`.

Group 07 direct file-backed profiling found its coverage proofs take about
one second each; the final verdict evaluation is the slow stage, rather than
the coverage theorem checks (see the aggregate milestone continuation).
The completed managed-cloud Group 07 run checked the unchanged exact verdict
pin in 2,262 s; this is not a controlled comparison with the historical timing.
The 300 s budget of the gate covers TestSuite modules only.
## M7-next · A checkpoint of the theorem (not started)

Waits for the user's go.  A fresh session starts here.

**Read first**: `AGENTS.md`; this document's M6 (the gate and the user's
decisions c, c′, d, e3′, e3″) and M7 (statement, features 1–32, "What is
not proved", the plan); `docs/module-map.md`.  The modules:
`Calculus/Decision.lean` (`decideLeaf`, `decideLeafA`, `decideGoal`,
`Fml.Covered`, `Fml.CoveredA`, `Fml.inTarget`, `DecisionTheorem`), then the
pipelines it names (`QuantReduction`, `ArrayProperty`, `ArrayBlock`,
`LedgerBlock`, `KIntBinder`, `KIntEncode`, `MemSwap`, `MemHoist`,
`HashKinds`, `HashKinds3`, `HashMove`), and the pins in
`Examples/Decision.lean`, `Examples/DecisionHashes.lean`,
`Examples/DecisionMemory.lean`, `Examples/DecisionKInt.lean`,
`Examples/DecisionArrays.lean`.

**Steps**:
1. **`DecisionTheorem'`.** For every leaf in `Fml.inTarget` not in
   `Fml.Residue`, `decideGoal` closes the goal or returns a
   counterexample.  It needs `Fml.inTarget ∧ ¬ Fml.Residue → Fml.Covered`,
   with no `sorry` and no new axioms (only propext, Classical.choice,
   Quot.sound).  `Fml.Residue` is a decidable predicate that names
   exactly the gaps still pinned (the six above, plus the unpinned shapes
   the proof finds it needs), each with a one-line reason.
2. **The goal is unchanged.** `DecisionTheorem` stays stated as it is;
   later milestones may only shrink `Fml.Residue`.
3. **Split `Examples/Decision.lean`** (and `Examples/DecisionArrays.lean`)
   into modules that each build in under 300 s; profile interpreted verdict
   evaluation first. Group 07 measured the `DecisionArrays` coverage pins at
   about one second each, with the final verdict `#eval` as its slow stage.
4. **Tag** the result `milestone-m7-next`, record it here, push to master,
   and stop for the user's next instruction.

**Rules** (the user's):
* At most two lanes (git worktrees) at a time; each agent keeps at most
  two files open in the Lean MCP.
* Builds: `LEAN_NUM_THREADS=3 ./run-lean.sh`, one lane building at a
  time, started only with at least 20 GiB available (`free -h`); kill the
  lane's own build if available drops under 8 GiB.  Lake has no job flag;
  without the variable a TestSuite build compiles about 20 modules at
  1.5–3 GB each.
* A lane is merged after its full build and the strict gate pass; never
  `git stash`; never kill processes by a pattern that matches the
  invoking shell.
* Another session works in the main checkout
  (`/home/guilherme/projects/solidity-lean`): do not commit or merge
  there.  It has deleted `../solidity-lean-integ` twice and pushes to
  master itself (it took `kintneg`'s early commits into master on
  2026-10-26).  Recreate the integration worktree from origin/master
  right before each merge
  (`git worktree add ../solidity-lean-integ -B integ origin/master`), test
  that the directory exists before running git there, and fetch before
  pushing.

## Guarded symmetric cancellation

One closer shape, outside M0–M8.

### Supported

`Facts.cancel` (`Calculus/Closer/Normal.lean`) cancels both `(a + b) - b` and
`(a + b) - a`, each after checking that the whole sum returns, and keeps the
typed result cast. `Facts.cancel_eval` proves both for checked unsigned and
signed integers. `Calculus/Closer/Bytes.lean` delegates subtraction to it.

KeY reaches the same by `polySimp_*` normalization (`polySimp_elimSub`,
`polySimp_addAssoc`, `polySimp_addComm0`, `intSimplificationRules.key`) over
unbounded integers. For checked machine integers the whole-sum premise is
necessary and cannot be weakened to success of the operands; the rule-map row
records the deviation.

### Tests

- `Examples/Tactics/FunctionTypes.lean`: universal `selectorOfValue` beside
  `addressOfValue` (after `cancelDiv` the selector lowering reads
  `(address * 2^32 + selector) - address * 2^32`), matcher regressions for
  both orders, unsigned overflow, signed underflow and failed operands, and two
  diamond counterexamples that fail before the subtraction.
- `tests/solc/GuardedCancellation.sol` and
  `scripts/guarded-cancellation.test.mjs`: both orders, signed and unsigned,
  overflowing and false cases. False cases may be `refuted` or `pending`,
  never `proved`. `externalValue == proved` is a hard gate; do not relax it to
  `pending`.
