# Automation: expansions, sizes and the road to a decision procedure

Milestones M0–M5 towards a closer that decides a fragment. M0–M5 are built. Each section says what is proved and where.

## M0 · The leaves of a type (`Theory/Typed/Leaves.lean`)

A type of *finite shape* (`Ty.Finite`, decided by `Ty.finiteShape`: words,
members, fixed arrays of finite shape up to `2^256`, mappings kept whole, no
dynamic array outside a mapping) is its words at its leaves: `Ty.leaves`,
the paths through members and in-range fixed indices that end at a word,
computed by fuel over `rankBound`; `Ty.leafCount` is their number.  The
leaves are exactly the direct paths to a word that stay inside the value
(`Ty.mem_leaves`, by `Path.direct`/`Path.out`), and two distinct leaves
diverge (`Ty.leaves_strip?_ne`, `Leaf.diverges`).  A fixed array's length is
part of its type, so a `uint[2^200]` has that many leaves: every user bounds
the count.

## M1 · The expansions, in the Theory and the interpreter (`Theory/Typed/Leaves.lean`)

* Theory, where a value is its observations, under `TVal.Shaped` (true of
  every typed value, `SVal.obs_shaped`, `Storage.obs_shaped`): a delete and
  a copy at a finite shape are a word written per leaf (`Obs.delAt_expand`,
  `Obs.copyTo_find_expand`); a push and a pop of a word (`Obs.push_prim`,
  `Obs.pop_prim`).
* Interpreter, with no premise on the storage, at a finite shape with a leaf
  (`T.leaves ≠ []`): `Storage.delete_expand`, `Storage.write_expand`,
  `Storage.write_find_expand` (the source read before the copy), and
  `Storage.push_prim` (one more slot, then the save at `len`),
  `Storage.pop_prim` (the save of the default at `len - 1`, then the length
  shrunk keeping it).

## M2 · The expansions as chain links past the program (`Calculus/ExpandLaws.lean`)

`Tm.expand?` rewrites a storage term at its head, one of four kinds
(`ExpandKind`, `Tm.expandK?`):

| link | from | to |
|---|---|---|
| `delAtExpand` | `delAt(s, p)` | `save(…save(s, p.l₁, 0)…, p.lₙ, 0)` |
| `copyExpand` | `save(s, p, find(s, q))` | `save(…save(s, p.l₁, select(s, q.l₁))…, p.lₙ, select(s, q.lₙ))` |
| `pushExpand` | `push(s, p, x)` | `save(pushSlot(s, p), p[p.length]@s, x)` |
| `popExpand` | `pop(s, p)` | `shrink(save(s, p[p.length - 1]@s, 0), p)` |

A delete and a copy fire at a type `Ty.expandable` accepts: finite shape,
between one and `expandBound` (64) words, counted by arithmetic
(`Ty.leafCountAt`, equal to the leaves' number by `Ty.length_leavesAt`), so
a huge fixed array is refused without listing it (`Ty.expandable_spec`).  A
copy fires only at a type that is no word, and only from the storage it
writes to (`s` both times, `Tm.beqR`).  A push and a pop fire only on an
array of words.  No argument may push (`Tm.pushFree`).

A leaf's path is `p` followed by its members (`.f`, unchecked as the
program's) and its fixed indices, written `p[i]@s` (`atIn`): checked in the
storage written to, where an in-range fixed index passes; the push's slot is
`p[p.length]@s` (`nextIn`, unchecked), the pop's `p[p.length - 1]@s`, whose
`- 1` reverts on an empty array exactly as the pop does.

**Proved.**

* `Tm.eval_expand?` (and per kind `Tm.eval_delAtLeaves`, `Tm.eval_copyLeaves`,
  `Tm.eval_pushWord`, `Tm.eval_popWord`): `t.expand? = some t' → t'.eval σ =
  t.eval σ` in every typed state, reverts included, from M1's interpreter
  lemmas and the symbols' evaluation equations.
* `Tm.exhB_expandK?`: the expansion is out of gas exactly where the term is
  (only the push can be: at a full array, `Tm.exhB_pushWord`).
* `holds_upd_expand_iff`: the rewrite of an update's right-hand sides
  (`Upd.rwBy (Tm.pickExpand k)`) is an equivalence under either modality
  (`Upd.rwBy_afterT`); `FmlRw.expandPast k i` is the rewrite of the update
  at position `i` of a scoped line.
* `Tm.spineSaves_expand?`: at most `expandBound` more `save`s on the storage
  spine (`Tm.spineSaves`); a delete exactly `T.leafCount` more
  (`Tm.spineSaves_delAtLeaves`).  A fixed index repeats `s` in its path.

**Chains.**  `~[delAtExpand]~>`, `~[copyExpand]~>`, `~[pushExpand]~>`,
`~[popExpand]~>` name the rewrite past the program (`rwExpandLinks`,
`Calculus/RewriteChains.lean`; the candidates in `Calculus/Chains.lean`).
They are Lean only and never tried by `~=>`, `#chain` or `#last_line`: a
worked chain's last line keeps a `delete` whole, as solkey does.
`Examples/ChainExpand.lean` shows each, and `sol_decide` closing the
expanded lines.

## M3 · Reads reduce write-free (`Calculus/ElimWriteFree.lean`, `Calculus/StepFragment.lean`, `Calculus/SymexFragment.lean`)

**The elimination is write-free** (`Calculus/ElimWriteFree.lean`).  On the
terms it has a reading for (`LTm.Elimable`: no memory sort, `mtSt`, `wt`,
`cleanTail`, `select`, `copyMem`; `orElse`/`kite`/`err` only at a word), the
closer's read reduction (`LTm.elim`, `Calculus/Decide.lean`) leaves no
storage symbol: the start is read only through the observation atoms
(`LTm.elim_stoFree`, `LFml.elim_stoFree`).  A storage in save normal form
(`LTm.SaveNF`: `storage` with `save`, `pushSlot`, `shrink` at elimable paths
and values) is elimable, so a read of it eliminates storage-free
(`LTm.SaveNF.find_stoFree`).

**A step on the fragment emits saves** (`Calculus/StepFragment.lean`).

* `Tm.SaveLike t`: `t` is `save`, `pushSlot` or `shrink` on `storage`, or
  what `Tm.expand?` turns into those — `delAt` at a `Ty.expandable` type, a
  `push` of a word (`sval x`), a `pop` of an array of words; `UpdElem.SaveLike`
  (a local, or `storage := t` with `t` save-like), `Upd.SaveLike` (every
  element).
* The fragment `Stmt.Frag`/`Prog.Frag`: storage writes of a word or of a
  storage copy (`Src.copy` at any type: a `save` already, expanded when
  `Ty.expandable`; `Src.fixedCopy`), `delete` at an expandable type, `push`
  of a word or of the default, `pop` of an array of words or of mappings,
  alias bindings, locals, `if`, `require`, `assert`, `revert`,
  `assume(false)`, blocks, every expression memory-free (`Val.MemFree`),
  every storage alias declared with an initializer.
  Left out: memory (a memory rule writes `memory`), payments and calls,
  loops (the invariant rule anonymises the frame), `try`, compound
  assignment and `++`/`--` (their updates are saves too, left out to keep the
  proof short), copies from memory, a push of a reference value (kept whole
  by `Tm.expand?`).
* `Premise.SaveLike P`: every update `P` writes is save-like and every
  program it runs next (an unfold, a bind, a split's branches) is in the
  fragment, so the property holds along the strategy's whole run.

**Proved.**

```lean
theorem Stmt.step_saveLike (s : Stmt C Γ Γ') (h : s.Frag = true) :
    (s.step k m).SaveLike
theorem Tm.SaveLike.saveNF_expand {t : Tm C Γ .st} (h : t.SaveLike) :
    ((t.expand?).getD t).SaveNF
theorem Stmt.step_saveNF (s : Stmt C Γ Γ') (h : s.Frag = true) :
    ∀ U ∈ (s.step k m).upds, ∀ t ∈ U.2.2.stores, ((t.expand?).getD t).SaveNF
```

one lemma per arm (`assignStep_saveLike`, `copyStep_saveLike`,
`localStep_saveLike`, `rebindStep_saveLike`, `deleteStep_saveLike`,
`pushStep_saveLike`, `popStep_saveLike`, `iteStep_saveLike`, …), under the
holes' (`SHole.readStep_saveLike`, `VHole.step_saveLike`); a captured
condition's branches are weakened by `Prog.wk up`, which keeps the fragment
(`Prog.frag_wk`).

**The bridge to `LTm`** (`Calculus/SymexFragment.lean`).  `Tm.ElimOk` is
`LTm.Elimable`'s symbols (`Op0.elimOk` … `Op3.elimOk`) on the scoped terms,
any local; `SymS.Ok ρ` says `ρ`'s bindings and storage are elimable,
`SymS.OkNF ρ` that its storage is in `LTm.SaveNF` (`SymS.init`, whose
storage is `storage`, is).  `Tm.toL` folds as it pushes in (`fold1`,
`fold2`, `foldAt`, `foldNext`, `literalRead`), and each fold keeps
elimability.

```lean
theorem Tm.ElimOk.toL (hρ : ρ.Ok) (ht : t.ElimOk) : t.toL ρ = some l → l.Elimable
theorem Tm.SaveNF.toL (hρ : ρ.OkNF) (ht : t.SaveNF) (he : t.ElimOk) :
    t.toL ρ = some l → l.SaveNF
theorem Stmt.step_elimOk (s : Stmt C Γ Γ') (h : s.Frag = true) : (s.step k m).ElimOk
theorem Stmt.step_toL_saveNF (s : Stmt C Γ Γ') (h : s.Frag = true) :
    ∀ U ∈ (s.step k m).upds, ∀ t ∈ U.2.2.stores, ∀ (ρ : SymS C U.1), ρ.OkNF →
      ∀ l, ((t.expand?).getD t).toL ρ = some l → l.SaveNF
```

`Premise.ElimOk` (every update a rule writes has a reading, every condition
is a fragment formula) is proved one lemma per arm, from
`Val.lower_elimOk` (a memory-free expression lowers to an `ElimOk` term) and
`Tm.expand?_elimOk` (the expansion keeps it); a capture is `True`, its
program being `Premise.SaveLike`'s.

**The lift over a run.**  `symex` never merges updates: its leaf is a nest
of `{U}` over the postcondition, and `Fml.toLS` composes them, each
update's storage substituted for the next one's `storage` (`Upd.toLS`).
That is the level where the lift is proved:

```lean
theorem Upd.ElimOk.toLS (hρ₀ : ρ₀.Ok) : U.ElimOk → U.toLS ρ₀ = some q → q.1.Ok ∧ q.2.Elimable
theorem Upd.toLS_okNF (hρ₀ : ρ₀.OkNF) : U.ElimOk → U.NF → U.toLS ρ₀ = some q → q.1.OkNF
theorem Fml.stepR_frag (k : Nat) (hφ : φ.Frag) : φ.stepR k = some ψ → ψ.Frag
theorem symex_frag (n : Nat) : φ.Frag → (symex n φ).Frag
theorem Fml.Frag.toLS (hφ : φ.Frag) : ρ.Ok → φ.toLS pos ρ = some ψ → ψ.Elimable
theorem symex_reduceS_stoFree (n : Nat) {φ : Fml C []} (h : φ.Frag)
    (hψ : (symex n φ).reduceS = some ψ) : ψ.StoFree
```

`Fml.Frag`: programs in the fragment (`Prog.Frag`, `Frames.Frag`), updates
save-like with a reading, equations with a reading, no `wellFormed`.
Preservation is by cases on the premise (`Premise.fml_frag`, from
`Stmt.step_saveLike` and `Stmt.step_elimOk`); `branches` and `inv` never
occur.  Elimability needs no expansion (`delAt`, `push`, `pop` have a
reading); save normal form is what the expansion adds:
`Tm.pickExpandAll` fires every kind at once, an equivalence on an update
(`holds_upd_expandAll_iff`) that maps a save-like update with a reading to
one in save normal form (`Upd.rwBy_expandAll_nf`), so each update of a
fragment leaf, expanded and pushed in onto a chain of saves, leaves one
(`Upd.SaveLike.toLS_expandAll_okNF`).

**Narrowed, and why.**

* *An unset storage alias* (`T storage x;`): `Rhs.toL` binds it to `err`
  at a path sort, which `LTm.Elimable` refuses (the elimination keeps an
  `err` path as written), and `uint y = x.f;` before a rebind pushes in to
  `find(storage, field(err))`.  `Stmt.Frag` now asks for an initializer.
* *`wellFormed(s)`*: pushed in as `wt(s)`, which the elimination keeps as
  written; `Fml.Frag` leaves it out, so a leaf with a `wt(storage)`
  premise is not covered.
* *Save normal form on the leaf itself*: proved per update and per
  composition (`Upd.toLS_okNF`), not as a predicate on the pushed-in
  `LFml` (the states `Fml.toLS` passes through are not recorded in it);
  an expansion of every update of a leaf in context
  (`Upd.rwBy Tm.pickExpandAll` under the binders) is not stated.
* *The walk* (`Seq.residue`) is not covered; `symex` is.

## M4 · Completeness of the automatic decision (`Calculus/CondLift.lean`, `Calculus/LiftTotality.lean`, `Calculus/FlattenTotality.lean`, `Calculus/LeafTotality.lean`, `Calculus/AutoComplete.lean`)

`dependentReduction?` (`Calculus/DependentReduction.lean`) decides a formula
exactly once it returns a certificate (`DependentReduction.valid_iff`,
`verify`).  M4 states when it returns one, and closes the gap that kept it
from returning one on writes at symbolic keys.

### The pipeline, as it now stands

```
ProgramNormalization.ofFormula? 2048      exact program normalization
sourceReduction?                          updates pushed in (ExactAt, toLS)
LTm.elim / LFml.elim                      reads of writes eliminated
LFml.condSimp                             trivial conditionals folded      (new)
LFml.prenex                               consequent quantifiers in front  (M7)
LFml.liftCond condLiftFuel                conditionals lifted to cases     (new)
UniversalPrefix.ofFormula? 1024           the ∀ prefix
flattenedArithmetic? 2048                 reads to fresh atoms, alias constraints,
                                          checked linear arithmetic
```

The two new stages are in `Calculus/CondLift.lean`; the certificate's
`sentence` is now over `source.leaf.elim.condSimp.liftCond condLiftFuel`
(`condLiftFuel = 64`), with `LFml.condSimp_holds` and
`LFml.liftCond_holds` in the transport.  On a leaf with no conditional
(`LFml.conds φ = 0`) both new stages are the identity
(`LFml.liftCond_condSimp_of_conds`, `Calculus/LiftTotality.lean`), so such a
leaf reaches the later stages as before; the compiler refuses a
conditional, so a leaf the pipeline accepted before had none in an
equation.  Before lifting, `LFml.liftCondB` lifts within `liftBudget`
nodes (1023 binders, the prefix's limit, and 2048, the flattener's node
budget) and the leaf is refused as soon as the lift would exceed it, so a
leaf with many conditionals is refused after bounded work rather than after
an exponential lift.  It refuses no leaf in `Fml.exactBounded`
(`LFml.liftCondB_isSome`), so `auto_complete` keeps its hypotheses.  The examples that
read the pipeline (`Examples/AutoComplete.lean`,
`Examples/DependentReduction.lean`, `Examples/CompleteVerification.lean`,
`Examples/Verify.lean`) are checked by the build.

### (a) Lifting the elimination's conditionals

A read after a write at a symbolic key eliminates to `kite x y t e` (`t`
where the keys `x`, `y` are equal, `e` where they differ) and the
location's presence to `ite c t e`.  `CheckedScalar` encodes affine values
with a definedness guard, so neither is encodable: a conditional value is
not affine.  Extending the compiler would mean returning a disjunction of
encodings, which is the case split done inside the compiler; lifting at
the formula level keeps the compiler as it is, and keeps the lifted leaf
in the language every later stage reads.

The split is three-way, by the guard's outcome (`CondGuard.case`): an
equation `A[K]` holds iff the operands return and agree and `A[t]` holds,
or they return and differ and `A[e]` holds, or one halts and `A[err]`
holds.  This is exact in every context, strict or not, because `LTm.eval`
is compositional (`LTm.condSplit_eval`).  Guards whose operands always
return (atoms, literals) get two cases (`CondGuard.split`).  Before
lifting, `LTm.condSimp` folds a `kite` on returning operands with equal
branches and an `ite` on a literal (`LTm.eval_condSimp`): the presence
test after a save is `true` either way, and lifting it would only
duplicate the formula (on the example below it cuts the arithmetic
formula from 325 to 111 nodes).

`LFml.liftCond_src` (`Calculus/LiftTotality.lean`) proves the lift
complete: on `LTm.Src true` (the fragment below, with `kite`/`ite` at
value positions) it yields `LTm.Src false`, once the fuel exceeds
`LFml.condMax`, where an equation `a = b` weighs `2^|a| + 2^|b|` (`|t|`
the conditionals of `t`, `LTm.conds`): a branch equation lowers one side,
a guard equation is over a conditional's operands, so each step lowers the
weight (`LTm.Src.split`, `LTm.Src.split_weight`).  Lifting adds no atom
(`LFml.liftCond_params`).

### (b) Fixed arrays at literal indices: not done here

Not in M4's pipeline: the path guards refuse `.atF` (`TSegs.guardFuel?`),
`ReadExpr` has no fixed-array index, and the realization layer that turns an
alias-consistent assignment into an actual storage
(`Calculus/ReadRealization.lean`, `Ref.Declared`) covers root, field and
mapping-key paths only.  M7 step 6 (feature 10 below) answers on leaves
that read arrays of primitives at roots, fixed and dynamic, at symbolic
indices (on `Fml.arrayCovered`, within its fuels and M4's bounds), by a
pipeline of its own
(`arrayReduction?`) that cuts them to atoms before these stages run, so
they stay as they are.

### (c) The fragment

On terms (`LTm.Src c k`, `Calculus/FlattenTotality.lean`), by kind:

* scalars (`num`): atoms, literals, transaction fields, `+`/`-` (checked),
  `*` with a literal factor on either side (checked, M7), unary `-` and `~`
  (M7), `seq` guards, `err`, and storage reads `obsW` of a path; with the
  flag `w = true` (before the cut, M7) also `int(·)`, `uint(·)`, `/`, `%`,
  `>>`, `<<` by a literal, `&` by a low mask, `+%`, `-%`, and (`litR`,
  `litL`, M7 feature 14) `&`, `|`, `^`, `*%` with a literal on either side,
  `**`, `**%` by `0` or `1`, `/` and `%` at `int` by any literal and at
  `uint` by `0`;
* Booleans (`bool`): a scalar at `bool`, `!`, `&&`, `||`, `==`/`!=` on
  Booleans or numbers, `<`/`>`/`<=`/`>=`, `seq` guards;
* paths (`path`): a root, fields, mapping keys whose keys are scalars;
* with `c = true`, also `kite x y t e` (scalar operands) and `ite c t e`
  (Boolean test) at value kinds.

On formulas (`LFml.Src c`): `tt`, Boolean equations of Booleans, numeric
equations of scalars, under `¬`, `∧`, `→`.  `LTm.src?`/`LFml.src?`
(`Calculus/AutoComplete.lean`) recognize it with its evidence, and are
complete (`LTm.src?_complete`, `LFml.src?_complete`).

`Fml.inExact φ` holds when `leafOf? φ` (the leaf after normalization,
update pushing, elimination and folding) exists and, as `LFml.inExact`
checks, has a universal prefix shorter than 1024 binding every atom of a
body in `LFml.Src true` whose lifting weight is below `condLiftFuel`.
`Fml.exactBounded φ` bounds the lifted body: at most 511 nodes.  The bound
comes from the compilers' 1024-deep fuel (a flattened term has at most
twice its source's nodes).  The reads had a bound too, 45 (`words² ≤ 2048`,
the alias-pair budget), until M7 (2026-10-25) computed the flattener's
budget from the leaf (`readBudget`, at least 2048 and the leaf's reads
squared).

### (d) Totality and completeness

```lean
theorem dependentReduction?_isSome (φ : Fml C []) (h : φ.inExact = true)
    (hb : φ.exactBounded = true) : (dependentReduction? φ).isSome = true

theorem auto_complete (φ : Fml C []) (h : φ.inExact = true) (hb : φ.exactBounded = true) :
    ∃ r, dependentReduction? φ = some r ∧ (Fml.Valid φ ↔ r.arithmetic.guarded.decide = true)

theorem auto_countermodel (φ : Fml C []) (h : φ.inExact = true) (hb : φ.exactBounded = true) :
    ∃ r, dependentReduction? φ = some r ∧
      (r.arithmetic.guarded.decide = false → ∃ σ : State C [], ¬ holds σ φ)
```

`DependentReduction.countermodelOfDecide` builds the countermodel itself.
Stage by stage:

| Stage | Statement |
|---|---|
| lift | `LFml.liftedExact_lift`: `ψ.inExact → (ψ.liftCond condLiftFuel).liftedExact` (via `LFml.liftCond_src`, `LFml.liftCond_stripAll`, `LFml.liftCond_params`) |
| prefix | `UniversalPrefix.ofFormula?_strip`; the covered check is the body's atoms in the prefix |
| flattening | `flattenFuel?_Src`, `flattenFormulaFuel?_Src`: a flattened term in the compilers' fragment, one laid-out occurrence per read (`Laid`, `OccOK`); `SPath.viewFuel?_PathF`, `TSegs.guardFuel?_FK`; `occurrenceLayout?_isSome`; read-free checks (`LFml.Arith.readFree`, `LFml.Src.readFormula`) |
| alias constraints | `ReadOccurrence.constraints_arith` (via `relSegsM_keys`, `SPath.alias_arith`) |
| arithmetic | `StorageEncoding.ofFormula?_good` with widths (`StorageEncoding.Good`), `leafArithmetic?_isSome` |
| leaf | `flattenedArithmetic?_isSome (φ : LFml C) (h : φ.Src false) (hn : φ.nodes ≤ 511) (hw : φ.words * φ.words ≤ 2048)` |

All are `sorry`-free, and `#print axioms` of each headline theorem shows
only `propext`, `Classical.choice`, `Quot.sound`.

`Examples/AutoComplete.lean` applies them to `∀ k j. [ m[k] = v; ] (k == j
→ m[j] == v)`, whose eliminated leaf has a `kite` and an `ite` (outside
`LFml.Src false`, inside `LFml.Src true`), and to its refutation without
`k == j`.  On a `bool`-keyed mapping both verdicts are kernel-checked
(`decide +kernel`) and the countermodel is printed; `sol_exact` proves the
valid one.  On the `uint`-keyed mapping the kernel's arithmetic decision
over 256-bit codes overflows the language server's stack, so the positive
verdict there is the compiled one and the refutation is checked at its
codes (`not_valid_of_codes`).

Coverage, observed by hand when M4 landed and not pinned: the formulas of
`Examples/ProgramReduction.lean`, `Examples/ParameterReduction.lean` and
`Examples/CheckedLinear.lean` were in `Fml.inExact` exactly when
`dependentReduction?` accepted them, but for the formulas with declaration
premises, which the tools remove first (`DeclarationReduction.dependent?`).
What is proved is one direction, `dependentReduction?_isSome`.

### What is narrowed, and what blocks the rest

The fragment is syntactic on the eliminated leaf, not on the source
formula: `leafOf?` runs the stages above it.  Characterizing them
syntactically needs, per stage:

* **Normalization** (`ProgramNormalization.ofFormula?`): its only refusals
  are an unsupported statement (`ExactStatement.ofStatement?` takes local
  and storage assignment, deletion and primitive declarations; `block`,
  `if`, `require`, `assert`, `revert` and calls are unfolded) and the
  shared 2048-node budget.  The budget counts nodes of generated formulas
  (`requireFormula`, `branchFormula`, the call unfoldings), with
  continuations duplicated across branches; a syntactic cost function
  mirroring `normalizeCore` and a proof that it bounds the consumption are
  missing.
* **Update pushing** (`ExactAt.ofFormula?`): needs every update push-free
  with no memory local in scope, `Upd.toLS` defined (`Tm.toL` refuses
  `netOf` and some operators), and every atom read the same at both
  polarities (`directional?`: `Fml.eqAt` agrees only where both sides are
  `Tm.agreeB`); a characterization of `Tm.agreeB` and `Tm.toL` on the
  source fragment is missing.
* **Elimination**: that `LTm.elim` maps the pushed-in leaves of that
  fragment into `LTm.Src true` (with weight below the fuel).  This is an
  invariant of the size of `LTm.elim_stoFree` (`Calculus/ElimWriteFree.lean`,
  M3), for the finer predicate.

Kernel-evaluated code follows Gate G0 where it is new term recursion
(`LTm.condSplit`, `LTm.condSimp`: recursor, `match` twin, link theorem).
The recognizer `LTm.src?` and the term sizes and weights the checks read
(`LTm.nodes`, `LTm.words`, `LTm.conds`, `LTm.total`) are `match`-based, as
are the recognizers they mirror (`ReadExpr.ofTerm?`, `flattenFuel?`): a
deviation from G0's condition 1, cheap on the leaves the checks see.
The budgeted lift (`LFml.liftCondB`) recurses on `LFml`, which has no
index, and counts nodes by `LFml.fits`/`LTm.fits` (recursors).

To prove totality the recognizers' helpers became public: `flattenFuel?`,
`flattenFormulaFuel?` (`Calculus/FlattenReads.lean`), `SPath.viewFuel?`,
`TSegs.guardFuel?`, the `CheckedValue`/`BooleanValue` fuels, `scalar?`,
`Result`, `StorageEncoding.equality?` (`Calculus/CheckedLinear.lean`) and
`ReadOccurrence.conjunction` (`Calculus/ActiveReadConstraints.lean`).

## M5 · The size of what a rule emits (`Calculus/TermSize.lean`)

`Tm.size`, `Upd.length`, `Upd.tmSize`, `Fml.tmSize`, `Stmt.size` count
nodes, never a type.  Every rule writes at most two elements an update
(`Stmt.step_upds_le`), and the terms of its premise's updates and formulas
(`Premise.upds`, `Premise.fmls`) are each at most `16 * s.size + 16`
(`Stmt.step_tmSize_le`), one lemma per arm.  The terms inside a program a
rule emits (a premise's continuation) are not bounded by it.

## M6 · The automation gate (2026-10-24)

The goal set on 2026-10-24: every program the elaborator accepts (loops
closed by their invariants) and every specification is decided without
enumerating inputs, symbolic execution polynomial in the text, the closer
terminating with a proof or a counterexample; CI fails on anything else.

**What blocks the theorem as stated** (reported, not worked around):

* KeY's `int` (`Srt.kint`) is unbounded and `BinOp.zArith` admits `*`;
  a formula's parameters are read universally.  Validity of
  `∀ x̄. p(x̄) ≠ 0` over the integers is undecidable (Matiyasevich), so no
  terminating closer is complete on that fragment, quantifiers or not.
  **Decided (2026-10-25, option c):** on a goal with a product of two
  non-literal KeY `int` terms the closer may answer *unknown*; it must be
  complete (a proof or a certified counterexample) on every other goal.
  **Extended (2026-10-25, option c′):** the same for a product of two
  non-literal terms of a 256-bit type (`uint`, `int`): bounded, so
  decidable, but only bit by bit, and a kernel-checked certificate for a
  256-bit multiplier is out of reach without `Lean.ofReduceBool` (an axiom).
* **Decided (2026-10-25, option d):** a quantified formula over array or
  mapping contents is decided completely inside the array property fragment
  (Bradley, Manna and Sipma: universal index quantifiers, linear index
  guards, array reads only at the quantified indices); outside it the
  closer may answer *unknown*.  Over 2^256-long storages the general case
  is decidable only by enumerating storages, which the theorem forbids.
* **Decided (2026-10-25):** division, modulo, `**`, shifts and bitwise
  operators with two symbolic operands may answer *unknown*, as products
  do; `x ** e` with a literal `e ≥ 2` is a product (c′); `c / x` and
  `c % x` with a symbolic divisor belong to the division class; `{havoc}`,
  `{anon}`, `allocAll`, `grow` and storage-typed `bind` in a negative
  position over formulas that read storage fall under (d).
* **Decided (2026-10-25, option e3′):** hashes are collision-free on each
  goal's own hash terms, a premise of that goal (its distinct hash inputs
  give distinct outputs), not a global assumption, which would be false
  (keccak maps unbounded byte strings to 256 bits) and make the theorem
  vacuous; the closer may answer *unknown* on a verdict that depends on an
  `ecrecover` value (an `opaque` function) or on a hash preimage.
* A counterexample is a concrete typed state, certified by kernel
  evaluation.  One that needs a storage array of `2^255` elements could not
  be built: `invariantClosedFormSum` is false in the model (`s + 2`
  overflows at `i = 2^255 − 1` when `values.length ≥ 2^255`, its invariant
  leaf shows it).  It is refuted now by symbolic counterexamples (below);
  a witness outside their shapes (a long array read element by element, a
  loop that does more than count) is still out of reach.
* Not impossible, but false today: `split` duplicates the continuation
  (`n` sequential `if`s give `2^n` leaves; since M8's A1 only for an `if`
  whose branches do more than assign one local), a call carries its callee's
  body (nested calls grow exponentially; a callee that computes values runs
  by its summary, below), and literal-bounded loops are
  unrolled (`docs/loops.md`).

**The gate**, `node scripts/check-automatic.mjs --strict` (CI, after the
TestSuite build): every TestSuite obligation is derived by `sol_prove`, its
step budget and the leaf replay `sol_prove?` writes, or `sol_auto_theorem`,
or refuted by `sol_refute` (in `TestSuite/Refuted.lean`, from `¬ ⊨ᶠ φ`:
false in the model, not merely underivable), and none is pending; its counts
must be the `Report.lean` pin's; and no TestSuite module the build compiled
took past its budget (`--build-log`, 300 s each by default; CI tees the
TestSuite build's log).  It failed on one pending obligation until the symbolic counterexamples (below).  Built this round:

* `sol_refute` (`Tools/Counterexample.lean`): `¬ (⊢ φ)` or `¬ ⊨ᶠ φ` from a
  certified counterexample, through `Proves.not_of_not_valid` (soundness
  read backwards).  `#solkey_obligations` counts `N.f.refuted`
  (`TestSuite/Refuted.lean`, ten).  The search now draws array shadows
  where `wt` admits them (`TGen.shadow`: elements of a reference type),
  which refutes the seven obligations that read an appended slot as its
  default (solkey's `SYMBOLIC_TAIL_OPENS`); a witness prints them
  (`fmtFoldShadow`, `[… | past the end: …]`).
* `sol_auto_theorem n : φ` (`Calculus/Closers.lean`): the walk and each leaf
  with heartbeats of their own, the declaration added after.  A tactic
  cannot do this: whatever runs after it is checked against the
  declaration's count since its start.  `bitAndSymbolic` and
  `invariantForBreakSkipsUpdate` and `invariantQuantifiedOverPrefix`
  (`TestSuite/Derived20.lean`).
* `sol_close`: the write facts and reads are skipped past 10 M heartbeats
  on a leaf past a `{havoc}` (`sol_close_saturate`, `sol_skip_after`; a
  budget is `Core.Context.maxHeartbeats`, not the option), so an
  invariant's exit leaf closes by the invariant and the guard
  (`invariantOverStorageWrites`, no hand proof left); a last fallback
  splits an `Option` read a premise and the goal both ask of
  (`sol_close_some_cases`).

* The closer's bounded steps are bounded now.  Every budget was set as an
  option (`withOptions … maxHeartbeats`), which `checkMaxHeartbeats` never
  reads (it reads `Core.Context.maxHeartbeats`); `sol_close_all`'s guards
  and instance search, `sol_close_captures` and `sol_close_nonlin` now set
  the context's limit.  `sol_close_quantified`'s nominal 20000 is gone: it is
  bounded by the declaration's heartbeats, which is all it ever was, and the
  ABI scans of `Examples/Tactics/ArrayScans.lean` need most of them.
  Each step's limit is also capped at what the enclosing limit has left
  (`Budget.within`, `Calculus/Budget.lean`; `sol_skip_after`,
  `sol_within`, `sol_close_join_steps`, the `sol_close_all`,
  `sol_close_captures`, `sol_close_save_cases` and `sol_close_nonlin`
  steps): a fresh count alone let a step started at 150 k of 200 k spend
  another 100 k, and the declaration's next check then threw a timeout
  nobody catches.
* `sol_leaf_keep` (`Seq.leafValid (keepAll := true)`): the leaf without the
  `allLeftHide` pre-pass, which instantiates a `∀` premise at the terms in
  its scope and hides it, losing the instance a goal's own `∀` opens later;
  the last of `Derive.leafTacs`.

* `sol_close_quantified`'s last alternative, `sol_close_save_cases`
  (`Calculus/CloseScoped.lean`): solkey's `selectOnSaveCons` at a symbolic
  index.  The Theory reads of the goal and of the `∀` premise's instances
  are unfolded alike, a written storage is read as the write
  (`Storage.obs_write`), a read the leaf knows as the Theory's
  (`Storage.obs_word_ref_some`), and the read is split on whether it goes
  through the write (`CloseS.copyTo_word_ite`): the word written, else the
  old storage's read, which an instance gives.  `sol_close_all` also
  instantiates at the goal's own numeric locals past its cap of eight.
  `invariantQuantifiedOverPrefix` closes so.

* The memory closer reads a copy of storage below its root (`copyObjN`,
  `copyPathRd?`, solkey's `readFromCopyToStorage` and
  `readFromCopyToStorageIdentity` `\then`; `Theory/Typed/MemMirror.lean`)
  and takes a read's guards out of its address (`LTm.hoistA`): the three
  `memoryIndexWrite*` obligations (`TestSuite/Derived21.lean`, `sol_prove`).

**Symbolic counterexamples (2026-10-25).**  `invariantClosedFormSum` is
refuted by `sol_refute` alone (`TestSuite/Refuted.lean`), from a storage
whose `values` has `2^255` elements; none pending.  The witness is reachable
in the model, where `wt` bounds a length only by `2^256`; to my knowledge
solc's storage `push` panics (0x41) far below that, at `2^64` elements, so
code solc compiles never builds it.  The refutation is a gap between the
model and solkey's reading, not a bug in solkey's obligation.  Three pieces, all
checked by the kernel, nothing trusted:

* *Long arrays* (`Tools/LazyStorage.lean`): `SVec.rep v n`, `n` copies of
  `v` as the function that makes them; the kernel unfolds it only as far
  as a reader goes, and `Storage.len` reads the vector's index.  The
  premise `wt(storage)` visits every element, so it is proved, not
  evaluated (`holds_wt_of`: the long root by `SVal.allB_arrayOf_rep`, whose
  element test is `SVec.allB_rep` by induction and whose node tests read
  only the length; every other root by evaluation).
* *Counting loops in closed form* (`Semantics/RunAccel.lean`): a body that
  only adds literals to `uint` locals (`x = x + d`, `x += d`, `x++`, `++x`,
  each local once: `Prog.bumps?`) under a condition `x < e`, `x <= e`,
  `e > x` or `e >= x` with `e` a term the body leaves alone (literals, the
  transaction, other locals, a root's value or length, operators over them:
  `Val.rigid?`).  `TRun.accel?` computes the iteration `K` where the
  condition fails (`guardBound`) and the last `T` every counter survives
  (`ovfBound`): the loop ends at `K` (each local at its value plus `K`
  steps, `State.bumpK`) if `K ≤ T`, and reverts at `T` otherwise.
  `TRun.accel?_sound` proves it is `TRun.loop`'s outcome, by
  `TLoop.run_of_steps` (a loop along a closed form `f k`); the recognizers
  carry their proofs (`Prog.BumpsAt`, `Guard.Spec`, `Val.Rigid`), so no
  `match` needs a splitter.  `Prog.runA` is `Prog.runF` with such loops
  accelerated (`TRun.loopA`, `Prog.runA_approx`), and the evaluator runs it
  (`Prog.runFramesF`): a loop bounded by an argument at `2^256 - 1` that
  only counts is now answered, not `unknown`.
* *The search* (`Tools/Counterexample.lean`, "Long arrays"): when the
  ordinary candidates fail, `sol_refute` and `#counterexample` propose each
  dynamic-array root whose element default is well-formed at `2^255` and
  `2^256 - 1` elements (`longCands`), the formula's parameters at their
  defaults, and ask the kernel for `¬ ⊨ᶠ φ` of a formula
  `wt(storage) → ψ` directly (`certifyLong`, at the default `maxRecDepth`
  since M8's A3; the kernel check is bounded
  by its own heartbeats, the elaboration that builds it only by the
  declaration's): no compiled evaluator can hold such a storage.  The
  certificate for `invariantClosedFormSum` checks in about 0.1 s; the
  tactic's 4 s are the ordinary search before it.

`Examples/Tactics/SymbolicCounterexample.lean` pins both closed forms
(an overflow, a loop that ends at `2^255`), `Prog.runF` giving up where
`Prog.runA` answers, and a true property of the same loop not refuted.
Soundness is the usual chain: `Prog.runA_approx` against the typed run,
`Fml.eval3_sound`, `Fml.not_valid_of_peel`, `Proves.not_of_not_valid`;
`#print axioms` of the refutation shows Lean's three.

**The exponential, measured** (`#proof_tree`, `StandardExample`, the
program `uint x = 0;` then `n` statements `if (vᵢ == 1) { x = x + 1; };`,
post `x <= n`):

| n | nodes | branches |
|---|---|---|
| 1 | 10 | 2 |
| 2 | 23 | 4 |
| 3 | 48 | 8 |
| 4 | 97 | 16 |
| 5 | timeout (200000 heartbeats) | |

`ifElseSplit` copies the continuation into both goals, so `n` conditionals
in sequence give `2^n` leaves and about `6·2^n` nodes.  What the polynomial
bound needs, each a change to the calculus (every derivation's walk and
`Examples/ProofTree.lean`'s pins move):

1. **A join after a conditional** (done, 2026-10-24, for accumulations;
   2026-10-25 for every `if` whose branches only assign a local, M8's A1;
   below): run both branches to the end of the `if` as updates, then go on
   once under the merged update `{x := c ? x₁ : x₂}` (KeY's join rules,
   `ifThenElse` in the update), with each branch's failures (revert, panic)
   kept as its own goal; a branch that halts the function needs no join.
   The rest of the program is then executed once, and the formula grows by
   one conditional per joined local.
2. **Calls by summary** (done, 2026-10-24, for callees that compute values;
   below): a callee's body inlined at every call makes nested calls
   exponential in the text; the summary is the callee run once as an
   update of its return variable, applied at each call.
3. **Loops by their invariants only**: a loop with literal bounds is
   unrolled today (`docs/loops.md`); under the theorem it needs an invariant.

**The join** (`LeanTaclet.ifElseJoin`, `Calculus/Rules.lean`; its arm
`iteStep` and `Upd.ifJoin?`, `Calculus/Arms.lean`; its soundness
`sound_iteJoin`, `Calculus/SoundControl.lean`).  An `if` on a simple
condition whose branches are each empty or one assignment of a value local
(`Prog.joinArm?`) runs as one parallel update, a local the `then` branch
sets to `e` set to `c ? e : v`, one the `else` branch sets to `c ? v : e`,
one both set to `c ? e₁ : e₂` (`Upd.ifJoin`).  Such a branch reads its
value lazily (`Tm.app3 .ite`, only the side `c` picks is evaluated), never
panics, never diverges and calls nobody, so the update fails exactly where
the branch `c` picks reverts (`ifJoin_agrees`), which is
`Premise.sound_update`'s condition.  Which rule an `if` gets is decided by
the statement alone: `ifElseSplit` carries the converse side condition
(`Upd.ifJoin? … = none`), `Stmt.ite.ruleExists` covers both.

The gate (`Upd.ifJoin?`) was, until M8's A1 (below): one branch empty,
the other empty or an accumulation, a local set from its own value
(`JoinArm.accumulates`: `x = x + 1;`); it is now every `if` whose branches
are each empty or one assignment of a value local, the closer splitting the
value back at the leaf.  Joining every joinable `if` was tried first and broke the
leaves of `if (c) { x = 2; } else { x = 1; }` (`CloseTests`'
`whichWriteWins`), of conditional values (`ternaryToIf`: `Bytes`,
`SignedCasts`, tuple returns) and of lowered `break`/`continue` flags
inside invariant loops (`Loops`' `breakKeepsBound`, `LoopsImport`'s
`invariantBreak`): their two cases are cheaper for the closers than the
conditional term, so they split as before.  A1 keeps the join and gives
the closer those two cases back at the leaf instead (`sol_close_ite_split`,
M8).  An accumulation's split copies
the rest of the program once per case of every `if` before it, which is
what the join removes.  The solkey fragment (`Stmt.inSolkey`) leaves out
every `if` of the joined shape (`Prog.joinShape`), and since A1 every
conditional value (`Val.keyValue`), whose `ternaryToIf` gives such an `if`.

**The leaf.**  The kernel closer lifts the conditionals into case splits
(`LFml.decideLift`, `Calculus/DecideComplete.lean`) when there are at most
`liftConds` of them (each lift splits three ways, and the update terms,
substituted, double with each join).  Past that, `sol_close` reads each
joined value as a fresh value and its defining fact (KeY's join with the
conditional in the antecedent, `sol_close_join`,
`Calculus/CloseScoped.lean`): `X = some a` as an implication per condition
and a checked value as its check and its integer, `omega` reading the facts;
a leaf whose conditionals the evaluation has already decided (a lowered
`break`'s `if (!brk) { i = i + 1; }`, `brk` known) reads the checked value
left (`if c then some v else none`) the same way, or goes on to
`sol_close`'s arithmetic (`sol_close_finish`) without being evaluated
again.  The TestSuite's `invariantVariantSkipsBreakIteration` replay
(`TestSuite/Derived15.lean`) has four leaves where it had six.
The same family, joined (`Examples/Tactics/Join.lean` pins `n = 1, 2, 5`
and proves `n = 1…12`), before `sol_close_join_steps`:

| n | nodes | branches | leaf closed by |
|---|---|---|---|
| 1 | 8 | 1 | `sol_prove` (kernel, lifted) |
| 2–5 | 5n + 3 | 1 | `sol_leaf; sol_close` |
| 6 | 33 | 1 | past 200000 heartbeats (≈ 11 s: evaluation 6 s, `omega` 2 s) |
| 7 | 38 | 1 | past 200000 heartbeats (≈ 22 s: evaluation 10 s, `omega` 8 s) |
| 8 | 43 | 1 | past 200000 heartbeats |

The walk is linear (`5n + 3` nodes, one leaf); the leaf was not.
`sol_close`'s evaluation is one `simp` over the whole leaf, and grew about
cubically (eval alone 10 k, 49 k, 152 k, 372 k heartbeats at `n = 2, 4, 6,
8`): each update's rest is entered under a fresh binder, so `simp`'s cache
misses the terms below it, and they are visited again for each rewrite
above (`CloseS.landedAll_const` tried 210, 1235, 3648, 8025 times).
`omega` then split each joined value's two cases (`2^n`).

**One update at a time** (`sol_close_join_steps`, `CloseJ` in
`Calculus/CloseScoped.lean`; 2026-10-24).  The leaf `σ ⊧ {U₁} … {Uₙ} φ` is
read one binder or update at a time, the rest held opaque: the goal
becomes `∀ ψ, rest = ψ → σ ⊧ {U₁} ψ` (built directly, no `kabstract`),
`close_rw_s` evaluates `U₁` alone, what it leaves in front is opened
(binders, premises, landed states; a value as a fresh `a` and its defining
fact `X = some a`: under the box whatever it returns, `CloseS.wp_box_optRes`,
under the diamond with a goal that it returns, `CloseS.exists_some_of`), and
`rest` comes back by its equation (`replaceTargetEq`).  Every value is
named once, and the leaf's terms stay the size of one update.  Then, for
each defining fact (KeY's join, the conditional in the antecedent):

* its cases read as `omega` reads them (`sol_close_join_fact`, on a copy);
  where every case's value is one base plus a literal offset, the interval
  `base + lo ≤ a ≤ base + hi` (`hint`), and with the base's own absolute
  interval, `L + lo ≤ a ≤ H + hi` (`hintA`) — each by `omega` in a local
  context cut down to the facts it needs (`CloseJ.omegaIn`), so a call
  costs the same at every step;
* a value that must return (`X.isSome`, the diamond) is split on its
  conditions by `CloseS.isSome_cond` and `CloseS.isSome_ite`, a halting
  case refuted by `omega` from its conditions and the absolute intervals of
  the values they read.

The post is evaluated the same way, then `omega` on the linear facts; only
if that fails, `sol_close_finish` (the defining facts' cases), within 20000
heartbeats of its own, so a false leaf fails at about the cost of a true
one (`x <= 5` after six joins: 42 k).  Nothing is trusted: each step is a
tactic whose proof the kernel checks, and the three new lemmas
(`CloseS.isSome_cond`, `CloseS.isSome_ite`, `CloseS.wp_box_optRes`) are
proved.  The same leaves under the box, and with offsets other than one
(`x = x + 2` on every other `if`, `n = 7`: 28 k), close the same way.  `sol_close` tries it first on a leaf of at least
`CloseJ.stepsMin` (two) joined updates (`CloseJ.countJoins`), within a
budget of its own (`CloseJ.budget`), restoring the leaf where it does not
close it.  Then the join alternative, on a leaf with at least one joined
update (an update whose value is conditional, not a specification's
ternary in the post: `sol_close_has_ite`), within 160 k heartbeats of its
own (`sol_within`) and at most `joinMaxCases` (64) cases split in all
(`splitBoolConds`; it bounded the depth before, `2^n` cases).  A leaf of
more than `CloseJ.wholeMax` (five) joined updates is never evaluated whole
(`sol_close_few_joins` guards the join alternative, `sol_close_quantified`
and the last alternative): those run past the heartbeats there rather than
fail, so `sol_close` fails where the steps do, a false leaf of six joins
at 43 k (`Examples/Tactics/Join.lean`, `fail_if_success`).

Measured (heartbeats in thousands, one declaration each, default
`maxHeartbeats`; walk `sol_prove`, leaf `sol_leaf; sol_close`):

| n | walk | leaf | path | leaf by `sol_close_join_steps` |
|---|---|---|---|---|
| 1 | 3.3 (0.26 s) | — | kernel | — |
| 2 | 2.4 (0.18 s) | 8.1 (0.33 s) | steps | 7.5 (0.29 s) |
| 3 | 3.1 (0.24 s) | 11.3 (0.42 s) | steps | 11.0 (0.42 s) |
| 4 | 4.0 (0.31 s) | 15.1 (0.60 s) | steps | 14.9 (0.55 s) |
| 5 | 5.1 (0.41 s) | 19.2 (0.71 s) | steps | 18.9 (0.70 s) |
| 6 | 6.4 (0.53 s) | 23.5 (0.85 s) | steps | 23.3 |
| 7 | 8.2 (0.65 s) | 27.9 (1.0 s) | steps | 27.9 |
| 8 | 10.8 (0.81 s) | 32.8 (1.2 s) | steps | 32.8 |
| 9 | 14.8 (1.1 s) | 38.0 (1.4 s) | steps | 38.0 |
| 10 | 29.9 (2.4 s) | 43.6 (1.6 s) | steps | 43.6 |
| 11 | 42.4 (3.5 s) | 49.5 (1.8 s) | steps | 49.5 |
| 12 | 43.6 (3.5 s) | 55.9 (2.0 s) | steps | 55.9 |

(`n = 14`: leaf 69.7.)  The leaf by steps grows by about 5 k a join, a
little more each time (the locals' stack every update reads grows with
the parameters): quadratic with a small coefficient.  The walk levels off
near 44 k from `n = 11` (`sol_prove`'s bounded attempts at the leaf).  The
leaf column for `n = 2…5` was the join alternative's until the review of
2026-10-24 (21.0, 45.9, 88.9 and 162.5 k: `n = 5` used 162 k of the 200 k,
past the alternative's budget of its own), with `CloseJ.stepsMin` six; it
is the steps' since (`stepsMin` two).

What stays open: a leaf whose formula is not a chain of binders and
updates over its post (a premise `pre → {U} φ`, a conjunction) is peeled
only up to it, the rest evaluated whole; a joined value whose cases are not
offsets of one base (`c ? y : z`) gets no interval, and its cases are split
by `sol_close_finish` as before.

**Calls by summary** (`LeanTaclet.internalCallSummary`, `Calculus/Rules.lean`;
the summary `CallRet.summary?`, `Calculus/CallSummary.lean`; its soundness
`Premise.sound_callSummary`, `Calculus/SoundSummary.lean`; 2026-10-24).  A
call statement carries its callee's body, so the family `f₀(x) = x + 1`,
`fₖ(x) = fₖ₋₁(fₖ₋₁(x))` inlines `2^k` bodies at `y = fₖ(a);`.  Measured
before (`#proof_tree`, `a < 1000 → ⟨ uint y = fₖ(a); ⟩ y >= a`, inlining):

| k | nodes | time | leaf |
|---|---|---|---|
| 1 | 25 | 1.6 s | closed |
| 2 | 53 | 9.4 s | open (the closer gave up on `{se1 := a} … {y := se2}`) |
| 3 | 109 | 2.5 s | open |
| 4 | 221 | 6.4 s | open |
| 5, 6 | `7·2^(k+1) − 3` (445, 893), not run | | |

The rule: a call `y = f(args);` of one value assigned to a value local,
its arguments simple, whose callee calls (`Prog.hasCall`; a body that does
not runs once per call either way) and has a summary, is the update
`{ y := R(args) }`.  The summary `R` is the callee's body run symbolically
once, in its own frame (`Prog.sym`, `Stmt.sym`, by the recursors): every
value local holds a term over the frame's locals; `T v = e;`, `v = e;`,
blocks and calls of the same kind are run (a call in the body read through
its own callee's summary at its arguments, `CallRet.sym`), anything else
(`if`, `require`, a loop, a write to the state, an external call, a
storage or memory local) has no summary and the call is inlined as before
(`internalCallExpand`, whose side condition is `CallRet.summary? … = none`,
so a call still has one rule, `Stmt.call.ruleExists`).  Literal offsets are
folded as the terms are built (`Tm.norm`, `Op2.mk2`: `(u + c₁) + c₂ ⇝
u + (c₁ + c₂)` at `uint`, KeY's `polySimp` adding literal summands), so
`fₖ`'s summary is `x + 2^k`, not `2^k` nested additions.

*Failure.*  A term that may revert (an overflow, a failed read) is owed by
the local that holds it (its pending flag, `SEnv`) until a term that reads
it wherever it is read (`Tm.strictReads`: not under `?:`, `&&`, `||`) takes
it over; a pending local is never overwritten or popped, and at the end of
the body only the return variable may owe.  So the update fails exactly
where the call reverts: `Prog.sym_sound` (from a frame that agrees with the
typed one, the run ends in one that agrees, or reverts where an owed term
does not return; what is owed after is owed before), `CallRet.sumOf_sound`,
`CallRet.summary_agrees`.  A body that drops a value it may revert on
(`uint t = x + 1;` never read) has no summary.  The gate (`Tm.sumGate`)
also asks that the summary read no local but a value local (`Tm.valOnly`:
value locals and the nullary symbols, literals and the state's roots
`storage`, `env` (`msg.sender`, …) and `memory`, so a callee reading
storage or the sender has one; no reference local), push nothing and be
smaller than `16 * body.size + 16`, so `Stmt.step_tmSize_le` still holds
(`CallRet.summary?_bounded`).  The tools compute the summary by the kernel
(`summary_cond`, `kernelNF`, `Calculus/Rules.lean`; `ruleOf?`): the
elaborator's reduction re-runs a nested callee's summary once per call
path.  `Kernel.whnf` runs outside the heartbeats, so `summary_cond` (and
`ruleOf?`) hands the kernel only a side condition of at most
`summaryNodes` (200 000) distinct subterms (`fewNodes`), its own and the
converse `= none` alike, and reads back at most as many terms, each once
(`kernelNF` memoised); past that the condition is left to `side_cond`'s
other alternatives, which are bounded.  The solkey fragment leaves out a call with a summary
(`CallRet.sumOK`), so `⊢ₖ` still fires solkey's taclets only.

After (`Examples/Tactics/CallSummary.lean` pins `k = 1, 6` and proves
`k = 1 … 6`; time of `#proof_tree` and of `sol_prove?`, one declaration
each):

| k | nodes | `#proof_tree` | `sol_prove?` | leaf |
|---|---|---|---|---|
| 1 | 5 | 0.33 s | 0.38 s | `{ y := a + 2 } y >= a`, closed |
| 2 | 5 | 0.36 s | 0.39 s | `a + 4` |
| 3 | 5 | 0.50 s | 0.43 s | `a + 8` |
| 4 | 5 | 0.77 s | 0.48 s | `a + 16` |
| 5 | 5 | 1.34 s | 0.59 s | `a + 32` |
| 6 | 5 | 2.43 s | 0.80 s | `a + 64` |

The walk is constant (one node a call) and the leaf one update of one
addition.  What still grows is the summary's computation: a call statement
carries its callee's inlined bodies (the elaborator inlines, `Stmt.call`),
a tree of `2^k` copies of `f₀`'s, which the kernel's evaluation of
`Prog.sym` walks; the times above grow by about `1.8` a level from it.
That is gone since "One body a function" (below): every call of a
callee holds the same body term, which the kernel's caches walk once.

**What a summary does not share** (review, 2026-10-24).  A summary is one
term over the callee's frame, and a call in the body substitutes its
callee's term at its arguments: only literal offsets are folded
(`Tm.norm`), so the summary stays small only where the callee's term
does.  In the family `f₀(x) = x * 3`, `fₖ(x) = fₖ₋₁(fₖ₋₁(x))`, `fₖ`'s
summary is `x * 3 * … * 3`, `2^k` checked multiplications, and
`Tm.sumGate` passes it (it is measured against the inlined body, itself
`2^k` bodies).  Measured (`a < 1000 → ⟨ uint y = fₖ(a); ⟩ y >= a`, a
scratch module, heartbeats in thousands, one declaration each; walk: the
four rules to the leaf, leaf: `sol_leaf; sol_close`):

| k | walk | leaf |
|---|---|---|
| 1 | 1.3 (0.08 s) | 10.4 (0.50 s) |
| 2 | 1.7 (0.11 s) | 19.8 (0.82 s) |
| 3 | 2.7 (0.18 s) | 79.4 (3.0 s) |
| 4 | 4.7 (0.34 s) | `sol_close_eval` alone not done after 6 min, at `maxHeartbeats 50000` |
| 5 | 8.7 (0.69 s) | not run |
| 6 | 17.0 (1.4 s) | not run |

The walk is five nodes for every `k`, and grows with the inlined bodies
the kernel's evaluation of the summary walks (about 2 a level).  The leaf
is `{ y := a * 3 * … * 3 }` with `2^k` multiplications, and its
evaluation reads each one's wrap (`uintOf`, `if 0 ≤ v ∧ v < 2^256 then v
else 0`) with its operand three times, so the evaluated leaf, as a tree, has
up to `3^(2^k)` nodes (`k = 3`: 228 000 characters printed); at `k = 4`
it runs in a part of the evaluation that does not check heartbeats.  So the
summaries are polynomial only for callees whose terms `Tm.norm` keeps the
size of one body (literal offsets); the doubling family above is one.
Sharing makes the leaf linear in the call sites whatever the callee:
each call's result a fresh value with its defining fact
(`{ t₁ := x * 3 } { t₂ := t₁ * 3 } …`, KeY's contract applied once per
call) rather than its callee's term substituted.  It is done at the leaf,
not in the rule (below, "Call sites shared"); the `k = 4` row's runaway was
an instance search, not the size of the term.

**Worktree consolidation (2026-10-24).** All three other worktrees' commits
were already ancestors of master. The `share` worktree's source matched the
integration at `3b03ac58`, except for a checked-result optimization and an
unfinished sharing prototype. The optimization is now in
`Calculus/CloseScoped/Leaf.lean` (`CloseS.wp_ite_uintOf`,
`CloseS.wp_ite_intOf`) and `Calculus/CloseScoped/Steps.lean`
(`CloseS.wpChecked`): under a successful range check, the continuation reads
`⟨n, proof⟩` directly instead of unfolding `uintOf n` or `intOf n` again.
Both the success and failure branches remain in the proved equivalence.
The scratch measurement above at `k = 3` took 2438 ms before and 1157 ms
after for `sol_leaf; sol_close`; `k = 4` still exceeded a 45-second limit.
This improves the existing term summary without implementing shared calls.

The read-only finder and skeptic agreed to port that optimization and keep
the unfinished `LeafShare` prototype out of the library: it has a one-step
soundness proof but no bounded sharing pass, tactic integration or tests.
Its source and three scratch benchmarks are preserved on the local branch
`codex/archive-share-20261024` (`3f0aca1e`). Regression examples in
`Examples/Tactics/CallSummary.lean` cover eight checked products, symbolic
signed arithmetic, signed and unsigned overflow, and constant positive and
negative inputs; the five-node tree and headline axiom sets are pinned.

The frozen TestSuite metadata check passes. Existing checkout checks remain
separate failures: strict automation has one pending obligation
(`invariantClosedFormSum`), the trust inventory has 13 drift findings, the
orphan check sees 33 scratch modules, and the documentation path check has
13 missing external/vendor references. This consolidation does not change
those inventories or obligation statuses.
All three other worktrees were removed after their archived source was
rechecked byte for byte; only the master worktree remains.

**Call sites shared (2026-10-25).**  The summary stays one term over the
frame (`CallRet.summary?`, the walk and its pins unchanged); `sol_close`
reads it one call site at a time.  `CloseJ.shareStep`
(`Calculus/CloseScoped/Steps.lean`) rewrites the leaf's
`{ y := C[s] ‖ pop } φ` to `{ shₖ := s } { y := C[shₖ] ‖ pop } φ`, `s` the
term's innermost strict redex (`Tm.redex?`, `Calculus/LeafShare.lean`: a
binary symbol on locals and literals, reached through operands that are
always read), until the term is one operation: `{ y := a * 3 * 3 * 3 }`
becomes `{ sh0 := a * 3 } { sh1 := sh0 * 3 } { y := sh1 * 3 ‖ pop }`, a
fresh local and its defining update per call site.  Soundness is
`holds_upd_share`: where `s` does not return neither does `C[s]`
(`Op2.eval_none_of_strictB`, the operator strict), so the two updates fail
alike, and where it returns `u`, `C[z]` at `z = u` reads what `C[s]` read
(`Tm.redex?_spec`); its axioms are `propext`, `Classical.choice`,
`Quot.sound`.  Each step is an `apply` of it, its redex equation and its
`pushFree` conditions by `rfl` (the redex computed by `Kernel.whnf`
through `Tm`'s constructors only, `CloseJ.tmNF`), which the kernel checks
again.

`CloseJ.peel` then reads the shared leaf as it reads a joined one, one
binder, premise (`Fml.imp`, new: the leaf's precondition, kept for every
later `omega`) or update at a time with the rest held opaque.  A checked
product evaluates to its two cases (`CloseS.wpChecked`:
`(0 ≤ v ∧ v < 2^256 → k ⟨v, _⟩) ∧ (¬ … → False)`); the failing case is a
side goal, closed by `omega` in a context cut to its premises, the leaf's
premises and the known intervals (`CloseJ.closeArith`, under the diamond:
the precondition `a < 1000` shows `a * 3^i` fits).  `sol_close` tries it
first on a leaf with a summary's update of at least `CloseJ.shareMin` (4)
operations, within `CloseJ.budget`; a leaf whose summary has more than
`CloseJ.shareWholeMax` (8) is never evaluated whole after it
(`sol_close_few_joins`), so a false leaf fails at about the cost of a true
one (`y >= a + 1` at `k = 4`: 47 k; an overflow past `10^62` at `k = 5`:
76 k).

**The runaway** (`k = 4`, past 45 s in `sol_close_eval`).  Bisected on
`simp`'s `maxSteps` under a watchdog: 5000 steps 12 k heartbeats, 0.5 s;
7000 steps 18 k, 2.6 s; 8000 steps 21 k, 14 s: the time grew while the
heartbeats did not.  `set_option profiler true` put it in
`typeclass inference of Nonempty` (0.18 s, 1.25 s, 8.7 s, each nesting
level about seven times the one before), and
`trace.Meta.Tactic.simp.discharge` named the lemma: `forall_const`
(`[Nonempty α] (α → b) ↔ b`) of `close_rw_s`, tried at every premise of
the nested range checks, `Nonempty (Nonempty (Landed …))` and
`Nonempty (v * 3 * … * 3 < 2^256)`, which no instance gives and whose
failed search the heartbeats do not count.  At a proposition the lemma
never applies (a premise is not an instance); `Close.forall_const_type`
and `Close.exists_const_type` (`Calculus/CloseLemmas.lean`) take a type's
binder only, and replace `forall_const` in `close_rw_s` and
`exists_const`/`forall_const` in `sol_close`'s, `sol_spec`'s and
`sol_close_quantified`'s cleanup.  The whole evaluation at `k = 4` is then
1.0 s and 27 k heartbeats (`triplingFourWhole` pins the whole path within
the default), and the whole `sol_close` 24 k, 107 k, 803 k at `k = 3, 4, 5`
(the `k = 3` leaf was 79 k before): bounded, but not polynomial, so the
shared steps are what the family takes.

Measured (`Examples/Tactics/CallSummary.lean`'s `triplingOne` …
`triplingFive`, `a < 1000 → ⟨ uint y = fₖ(a); ⟩ y >= a`, heartbeats in
thousands, one declaration each; walk: `sol_prove (steps := 128)`, leaf:
`sol_leaf; sol_close`):

| k | call sites | walk | leaf | path |
|---|---|---|---|---|
| 1 | 2 | 2 (0.18 s) | 5 (0.18 s) | whole |
| 2 | 4 | 2 (0.22 s) | 6 (0.28 s) | shared |
| 3 | 8 | 4 (0.31 s) | 12 (0.56 s) | shared |
| 4 | 16 | 7 (0.52 s) | 28 (1.3 s) | shared |
| 5 | 32 | 12 (0.88 s) | 79 (3.6 s) | shared |

(`k = 6`, 64 call sites: the walk 23 k; the steps run past their budget,
`CloseJ.budget`, and `sol_close` fails, at `sol_close_few_joins`, without
evaluating the leaf whole.)  The leaf is `2^k` updates of one product each,
linear in the call sites.
What the closer spends on it grows by about `n^1.5` in the `n` call sites
(per step, `peel` at `n = 32`: the share 0.4–0.7 k, the step's `simp`
0.8–1.3 k, the check's `omega` 0.1–1.5 k): each step's `simp` walks the
locals' stack, one deeper per call site, and each check reads the product
`a * 3 * … * 3` it is about.  Naming each checked value afresh (a variable
and its equation, rather than the product substituted) would make the
checks constant; the stack would still grow.  The walk grows with the
inlined bodies the kernel's evaluation of the summary walks (above).

**One body a function (2026-10-25).**  A call statement still carries its
callee's body (`Stmt.call`, the run, the rules and their soundness are
unchanged), but the body is now the same term at every call of the callee,
so the program is a DAG the size of the source, and the kernel, whose
caches are keyed by the term, evaluates a callee's summary once however
many call paths reach it.  Three changes, none in the calculus:

* *The names.*  A body differed between calls only by the fresh names of
  its locals (`se5` at one call, `se9` at the next), so its copies were
  distinct terms.  A callee all of whose locals end with the call (not
  recursive, not the constructor, no return variable left in the caller:
  `FunDecl.endsWithCall`, a call not in a tuple assignment) now numbers its
  locals from where its first call's were (`CallMemo.enter`,
  `Syntax/Elab/Values.lean`), and the caller's numbering goes on after the
  call where it was (`CallMemo.leave`).  Two such calls never have their
  locals live at once (the frame is popped after the call,
  `Premise.unfold`), so the names stay unique on every state; a printed
  inlining repeats them (`addOne`'s `se3`, `se4` twice in
  `Syntax/Splice.lean`'s pin).  The key (`calleeKey`) is what else the
  elaboration reads: the callee, a self-call's frame, the overflow mode,
  `msg.value`'s reading.
* *The elaborator* reads a repeated callee's body back instead of
  elaborating it again (`CallMemo.body?`, `inlinedBody`,
  `Syntax/Elab/Arms.lean`): logically `none` (elaborate again, which gives
  the same body), compiled the body its first call stored
  (`implemented_by`, the contract checked by address).  And
  `reachableBy` (`Syntax/Elab/Context.lean`) visits each function once a
  round: it explored `fₖ₋₁` twice, `fₖ₋₂` four times, at every call, the
  elaborator's last exponential.
* *The quoters* quote a call's body once per object and contexts
  (`QMemo`, `Prog.quoteBody` in `Syntax/Quote.lean`, `qStmtH` in
  `Calculus/Quote.lean`, logically quoting it again); `Prog.quote` and
  `Stmt.quote` are monadic (`QuoteM`) and `partial`, as `Calculus/Quote.lean`'s
  were, and `QM` carries the memo (`QM.go`).

Literal factors are folded as literal summands are (`Op2.mk2`,
`(u * c₁) * c₂ ⇝ u * (c₁ * c₂)` at `uint` where the product is a `uint`
and `c₂ ≠ 0`, KeY's `polySimp`; `Op2.mk2_mul_eval`,
`PrimTy.uint_ofInt?_mul_assoc`: `u * c₁` overflows only where the folded
product does), so the tripling family's summary is one product,
`x * 3^(2^k)`.  A summary whose operations do not fold
(`f₀(x) = x * 3 + 1`, `Examples/Tactics/CallSummary.lean`'s `Affine`) is
still `2^(k+1)` operations, read one call site at a time as above.

*Speed* (the review's question: none of this undoes an earlier speed
change; `git log` shows none on the elaborator's naming or the quoters).
The elaborator and the quoters do strictly less work on a repeated
callee and the same on any other; the extra monad layer (`StateT CallMemo`,
`StateM QMemo`) costs nothing measurable in the elaboration of the
examples.  `elabCallRetWith` is split (`elabCallRetCore`, `calleeBody`,
`inlinedBody`): one more bind in the old body ran it past the default
heartbeats while its own definition was elaborated.

Measured (`a < 1000 → ⟨ uint y = fₖ(a); ⟩ y >= a`, a scratch module, one
declaration each; *DAG*: distinct subterms of the `dl!` formula's term;
*walk*: `sol_prove (steps := 128)`; *leaf*: `sol_leaf; sol_close`;
*kernel*: the declaration's type checking):

| family | k | DAG before → after | walk before → after | leaf before → after | kernel before → after |
|---|---|---|---|---|---|
| `x * 3` | 1 | 422 → 408 | 0.18 → 0.16 s | 0.21 → 0.15 s | 0.16 → 0.14 s |
| | 2 | 623 → 495 | 0.24 → 0.17 s | 0.30 → 0.14 s | 0.21 → 0.15 s |
| | 3 | 1 024 → 582 | 0.32 → 0.19 s | 0.60 → 0.14 s | 0.30 → 0.17 s |
| | 4 | 1 825 → 669 | 0.52 → 0.19 s | 1.4 → 0.14 s | 0.49 → 0.18 s |
| | 5 | 3 426 → 756 | 0.94 → 0.21 s | 3.8 → 0.14 s | 0.88 → 0.19 s |
| | 6 | 6 627 → 843 | 1.7 → 0.22 s | fails (budget) → 0.14 s | 1.6 → 0.20 s |
| | 7 | 13 028 → 930 | 3.4 → 0.24 s | fails (budget) → 0.14 s | 3.1 → 0.21 s |
| `x + 1` | 1 | | 0.17 → 0.17 s | 0.14 → 0.14 s | 0.16 → 0.15 s |
| | 4 | | 0.31 → 0.21 s | 0.14 → 0.14 s | 0.28 → 0.19 s |
| | 7 | | 1.5 → 0.24 s | 0.14 → 0.14 s | 1.2 → 0.22 s |

The `sol[…]{ uint y = fₖ(a); }` program of the `x + 1` family: distinct
subterms 267, 554, 1 686, 6 202, 48 320 before and 255, 330, 404, 478, 589
after at `k = 1, 3, 5, 7, 10` (its tree, 2 471 … 1 568 175 nodes, is the
same); the elaboration of `fₖ` at `k = 8, 9, 10`, compiled code: 33, 59,
112 ms before, 6.6, 7.3, 7.8 ms after; quoting: 61, 119, 229 ms before,
8.9, 9.7, 10.6 ms after.  Every column grows linearly in `k` after,
the DAG by 87 subterms a level.  `Examples/Tactics/CallSummary.lean` proves
both families to `k = 7` by `sol_prove` and the leaf replay.

## M7 · The theorem (`Calculus/Decision.lean`, `Calculus/Prenex.lean`)

The closer's theorem, stated in Lean, with what is proved of it.

### The statement

```lean
inductive LeafVerdict (C : Contract) | proved | refuted (σ : State C []) | unknown

def decideGoal (φ : Fml C []) : LeafVerdict C   -- total, computable

theorem decideGoal_sound    : decideGoal φ = .proved → Fml.ValidH φ
theorem decideGoal_refutes  : decideGoal φ = .refuted σ → ¬ Fml.holdsH σ φ

def DecisionTheorem (w : Waivers := {}) : Prop :=
  ∀ (C : Contract) (φ : Fml C []), φ.inTarget w = true → decideGoal φ ≠ .unknown
```

`Fml.inTarget w` is the fragment the user named, on a program-free leaf.
It contains everything except what the user allowed to answer *unknown*:

* (c, c′) a product of two non-literal terms (KeY `int`, `uint`, `int`).
  `x ** e` at a literal `e ≥ 2` and `mulmod` of two symbolic factors count
  as products.
* `/`, `%`, `**`, `<<`, `>>`, `&`, `|`, `^` with two symbolic operands.
  A symbolic divisor (`c / x`, `c % x`, the modulus of `addmod`/`mulmod`),
  a symbolic exponent and a symbolic shift amount count as two.  Each class
  is a field of `Waivers`, and the user waived all four (2026-10-25).
* (d) a quantified formula over array or mapping contents outside the
  array property fragment.  Polarity is tracked: a positive-position `∀`
  is an `∃` of the negation, so it needs no check.  A negative-position
  `∀` block whose body reads at its variables must be the
  Bradley–Manna–Sipma shape (`Fml.apfBlock`): a quantifier-free body made of
  `guard → value` parts and their conjunctions; guards `&&`/`||` of
  comparisons (`<`, `<=`, `==`, never `!=`) of index terms, a bound
  variable or a term mentioning none, never a strict comparison of two
  bound variables (`i < j` is `i + 1 ≤ j`, arithmetic on them); values
  reading the bound variables only as indices, never in a nested index
  (`a[a[i]]`), at most one bound index along a path (`m[i][j]` with both
  bound is outside), and writing nothing at them.  A Presburger quantifier, one whose body reads
  nothing at its variable, is in the fragment at any polarity, but past a
  negative-position one only further Presburger quantifiers are.  Negative
  `havoc`/`anon`/`allocAll`/`grow` and storage binders over a body that
  reads contents fall under d.
* (e3′) hashes.  Each goal is read under its own collision-freeness
  premise.  `Fml.HashFree σ φ` says that the hash terms of `φ` outside its
  binders, evaluated at `σ` or past its updates, whose outputs agree read
  the same bytes (each word modulo 256, as `HashKind.apply` reads them).
  `ecrecover` is excluded: it is `0` on every invalid signature.
  `Fml.holdsH` is `holds` with the premise taken at every scope, each
  binder's body under its instance's premise.  So each premise is about
  finitely many evaluations and fails only at an actual collision among
  them.  `Fml.ValidH` is validity so read.  It is no axiom and no global
  assumption; on a leaf without a hash it is `Fml.Valid` (`Fml.validH_iff`).
  A hash term is in the fragment only where the premise settles it: as an
  operand of `==`/`!=` against a hash of its kind, or as a key of a mapping
  at a root all of whose keys are hashes of that kind, the hash of a memory
  local.  Elsewhere its verdict may turn
  on a preimage, which the user allowed to answer unknown. `ecrecover` (an
  `opaque` function) is outside everywhere.  So is a hash under a hidden
  memory binder or an anonymising update: they range over an unset
  reference, whose hash reads nothing, and a key of nothing reads the
  default key `0`, so the verdict turns on whether a string hashes to `0`
  (`namesBound`, step 7's review, below).

The statement is about one computable function. "Some decider is
complete" would be vacuous: `Classical.choice` gives a noncomputable one.
It is the goal of the rounds to come, not true today:
`Examples/Decision.lean` pins one counterexample per shape still answered
*unknown* (`gapArrayBlock` … `gapHashNegForall`, each in the fragment by the
kernel, `*_inTarget`), `Examples/DecisionMemory.lean` the memory ones
(`gapMemWrite` … `gapMemStruct`), listed under "What is not proved" below.  The
witnesses of earlier rounds are decided: `apf` (step 5), `rowApf` (a block
over an inner mapping, `allow[3][k]`), `namesTwoKinds` (two kinds of
hash of one string), `arrayRead`, `fixedRead` (storage-array reads,
feature 10) and `gapMemory` (a fresh memory array's element, feature 13),
the last five since 2026-10-25; `gapFiveStrings` (now `fiveStrings`) and
`gapHashUnderForall` (now `namesUnderForall`) since the hash round of
2026-10-25 (`Examples/DecisionHashes.lean`); `gapIntDiv`, `gapIntMod`,
`gapOr`, `gapXor`, `gapAnd`, `gapPow`, `gapMulW` (literal operators,
feature 14) and `gapManyReads` (fifty reads, feature 15) since 2026-10-25;
`gapBoolKeyed`, `gapPositiveForall`, `gapColumn`, `gapTwoPaths`,
`gapStructValue` and `gapPartialGuard` (features 16 to 19) since
2026-10-26; `gapIntKeyed` and `gapLedgerBlock` (features 20 and 21) since
2026-10-26, their astronomically large refutations returned as terms;
`gapLedgerWrite` (feature 22) since 2026-10-26.

`Fml.inTarget` is a conservative syntactic reading, a subset of the
fragment the user named, with one known exception (below, `gapHashNegForall`):
* an update or a program under a quantifier counts as reading at its
  variable;
* an index guard may not negate a comparison of bound variables;
* a hash stored by an update, a hash key of a nested mapping or of
  anything but a memory local, a hash under a hidden memory binder or an
  anonymising update, and a hash under any other operator are outside,
  even where the premise would settle them.

Three properties of the reading are worth knowing.
* The per-scope premise depends on where the binders stand:
  `pre → ∀ k. ψ` and `∀ k. pre → ψ` take different premises, so
  `LFml.prenex` is exact for `holds` but not for `Fml.holdsH`.
  `decideGoal` prenexes only leaves without a hash, where the two
  readings agree (`Fml.holdsH_iff`), and the swapped readings of leaves
  with hashes (feature 11), which have none; a leaf with hashes it takes
  has its quantifiers in front (`Fml.swPrefix`), where the premise is the
  body's.
* A hash of an identity that names no object reads `none` and returns
  `0`; an object hashing to `0` would count as colliding with it.
* A program's hashes are not read by the premise.  The fragment holds no
  program, and on a formula with one, `decideGoal` answers by `Fml.Valid`,
  the stronger reading.
* The premise of a binder's instance reads only the hashes under the
  binder.  At a negative-position value quantifier whose hash pairs the
  scope above does not read, the hypothesis is vacuous exactly where those
  hashes collide: `∀ s t. (∀ x. keccak256(s) != keccak256(t)) → !(∀ y.
  keccak256(s) == keccak256(t))` holds as `holds` reads it and fails under
  the premise exactly at two strings with different bytes and one hash
  (`gapHashNegForall`).  Its only refutations are collisions, which cannot
  be exhibited, so no decision answers it; `Fml.inTarget` admits it, and
  excluding it narrows the fragment, which needs the user's approval.

### What is proved

| Theorem | Statement |
|---|---|
| `decideLeaf_sound` | `decideLeaf φ = .proved → Fml.Valid φ` |
| `decideLeaf_refutes` | `decideLeaf φ = .refuted σ → ¬ holds σ φ` (the state certifies it) |
| `decideLeaf_complete` | `φ.Covered = true → decideLeaf φ ≠ .unknown` |
| `decideLeaf_proved_iff` | on `Fml.Covered`, `proved` exactly when valid |
| `decideGoal_sound`, `decideGoal_refutes` | the same under the hash premise |
| `decideGoal_complete` | `φ.Covered = true → φ.hasHash = false → decideGoal φ ≠ .unknown` |
| `decideGoal_complete_hash` | `φ.hashCovered = true → decideGoal φ ≠ .unknown` |
| `Fml.swPrefix_validH` | a valid swapped leaf, its body's value binders positive (`Fml.posAll`), is valid under the leaf's premise |
| `Fml.holdsS_of_sw` | on a swapped body, `holds` gives `Fml.holdsS` at a positive polarity and back at a negative one |
| `Fml.swInst_refutes` | a refutation of an instance at the family's strings refutes the leaf under its premise |
| `Fml.holdsS_fam` | in a heap of the family the premise is read nowhere: `Fml.holdsS ↔ holds` on a swapped body |
| `Fml.swPrefix_complete` | on the fragment (keyed roots `mapping(uint => uint)`, the swapped leaf in `Fml.rl`, `Fml.prefixOK`, at most `N` strings, `famOK k N`), a swapped leaf that is not valid has an instance at some classes that is not |
| `Fml.swPrefix_exact` | on that fragment, the body's value binders positive, `Fml.ValidH φ ↔ Fml.Valid φ'` |
| `famOK_keccak`, `famOK_sha256`, `famOK_ripemd160` | four one-word strings with distinct, nonzero hashes, by the kernel; past four, `famCheck` computes the family's hashes (`famN`, `famOKAll`, `famCovered`) |
| `Fml.holdsH_iff`, `Fml.validH_iff` | without a hash the premise is empty |
| `LFml.prenex_holds` | prenexing is exact |
| `CheckedScalar.scale_correct` | checked multiplication by a literal is encoded exactly |
| `QFml.decide_iff` | `F.decide = true ↔ F.Valid`: quantified linear arithmetic decided |
| `QuantReduction.valid_of_sentence`, `QuantReduction.verify` | a valid sentence makes the leaf valid; a false assignment gives a refuting state |
| `quantReduction?_isSome` | `φ.quantCovered = true → (quantReduction? φ).isSome` |
| `Prep.valid_iff` | a preparation's body is valid exactly where the body is |
| `hoistPrep_valid_iff` | hoisting reads out of quantifiers is exact |
| `apfPrep_valid_iff` | `Prep.valid_iff` for `apfPrep`, which every preparation has (`Prep.id` too): sound and exact wherever `apfPrep` instantiates, by the next row; the body kept outside the fragment |
| `LFml.apfInst_sound`, `ApfFml.apfInst_refute` | the instantiation implied by the blocks; a failing instance a failing block, in the rebuilt storage and ledger (Bradley–Manna–Sipma; every key of the pass's type along a root's mappings floored, feature 18, at `uint` and `int`, feature 20; the ledger at a `uint` pass, feature 21; guards whose ground operands may halt, feature 19) |
| `FloorShape.rebuild_word`, `ApfTm.eval_trel`, `GuardP.mono` | a rebuilt root reads at a path what the old one read at its keys' floors; a term of the fragment reads alike, a path of a root of the blocks at its floors (`SRef.floorRef`), a ledger address at its floor (`NetRel.eval`); a guard true at the keys is true at their floors, a halting ground operand allowed unless a `&&` skips it inside a `||`'s left operand (`GuardP.floors`, `GuardP.defined`) |
| `lookupBy_regionList`, `lastIn_breaks`, `netRebuild_floor` | a read in a region list finds its key's last breakpoint's region, nothing where that region is skipped; the floor is constant between breakpoints; a rebuilt ledger reads each address's floor's entry (features 20 and 21, `Calculus/FloorRegion.lean`) |
| `LedgerBlockReduction.verify`, `ledgerBlockReduction?_isSome` | blocks over the ledger: a proof of the prepared, cut body proves the leaf, a false assignment refutes it in the rebuilt ledger; `φ.ledgerBlockCovered = true → (ledgerBlockReduction? φ).isSome` (feature 21) |
| `expandPrep_valid_iff`, `LFml.holds_expandB`, `LFml.dropOne_spec` | `bool` quantifiers expanded and positive quantifiers dropped to fresh atoms: exact at every state (features 16 and 17) |
| `LFml.ledgerCut_valid_iff`, `LFml.ledgerCut_refutes` | the ledger cut is exact; a refutation of the cut leaf, its ledger pulled back, refutes the leaf |
| `ledgerReduction?_isSome` | `φ.ledgerCovered = true → (ledgerReduction? φ).isSome` |
| `Fml.tk_validH` | a valid reading with the second kind's words (`Fml.tk`) makes the leaf valid under its premise; the words read past updates where they land (`linkChoice`, `XRelQ`, `Fml.xk_holdsQ`) |
| `Fml.tk_refutes` | a refutation of an instance with the second kind's words fixed (a family of `N` strings checked for every kind, `famOKAll N`) refutes the leaf under its premise |
| `Fml.tk_complete` | on the fragment (`Fml.swPrefix_complete`'s conditions on the result for the first kind, at most `N` strings, `famOKAll N`, the second kind's words in `Fml.tkRL`), where the reading with the second kind's words is not valid, an instance at some classes, those words fixed, is not |
| `decideHash2_sound`, `decideHash2_refutes`, `decideHash2_complete` | the two-kind decision: sound under the premise, certified refutations, `φ.coveredK2 k₁ k₂ = true → decideHash2 k₁ k₂ φ ≠ .unknown` |
| `Tm.toLT_sound` | an array element read in the Theory pushed in exactly (`Calculus/TheoryRead.lean`) |
| `LFml.orLift_holds`, `LFml.gx_holds`, `LFml.hasFold_holds` | fallbacks lifted, guards extracted, slot tests a length check settles folded: exact |
| `LFml.aCut_valid_iff`, `LFml.aCut_refutes` | the array cut is exact; a refutation of the cut leaf refutes the leaf in the state its arrays are rebuilt in |
| `arrayReduction?_isSome` | `φ.arrayCovered = true → (arrayReduction? φ).isSome` |
| `Fml.mx_holds`, `Fml.mxTop_holds` | the fresh memory arrays' cut is exact at every state (`Calculus/MemSwap.lean`) |
| `decideMem_sound`, `decideMem_refutes`, `decideMem_complete` | the memory lane: a proof of the cut leaf proves the leaf, a state refuting it refutes the leaf, it answers on `Fml.memCovered` |

`#print axioms` of each of the six `decide*` theorems, of
`decideGoal_complete_hash`, of `decideHash2_sound`, `decideHash2_refutes`,
`decideHash2_complete` and of the hash reduction's four
(`Fml.swPrefix_validH`, `Fml.swInst_refutes`, `Fml.swPrefix_complete`,
`Fml.swPrefix_exact`) is pinned in
`Calculus/Decision.lean`, of the two kinds' three (`Fml.tk_validH`,
`Fml.tk_refutes`, `Fml.tk_complete`) in `Calculus/HashKinds.lean`, of `QFml.decide_iff` and `QFml.verify` in
`Calculus/PresburgerDecision.lean`, of the quantified reduction's in
`Calculus/QuantTotality.lean`, of the preparations' in
`Calculus/QuantHoist.lean`, `Calculus/QuantExpand.lean` and
`Calculus/ArrayProperty.lean`, of the ledger blocks' in
`Calculus/LedgerBlock.lean`, of
`Fml.mxTop_holds` in `Calculus/MemSwap.lean`: `propext`,
`Classical.choice`, `Quot.sound`.  Everything is `sorry`-free.

`Fml.Covered` is `Fml.CoveredA || Fml.memCovered`.  `Fml.CoveredA`, the
pipelines' fragment (`decideLeafA`), is `Fml.inExact && Fml.exactBounded`
(M4), extended by features 1, 2, 4, 5, 8, 14 and 15, each with its
completeness proved through every stage (recognizer, lifting, flattening,
compilers), or `Fml.quantCovered` (features 3, 6, 7 and 16 to 20, its own
pipeline),
or `Fml.ledgerCovered` (feature 9, its own pipeline), or
`Fml.arrayCovered` (feature 10, its own pipeline), or
`Fml.ledgerBlockCovered` (feature 21, its own pipeline); `Fml.memCovered` is
feature 13's, a leaf with fresh memory arrays whose cut is in
`Fml.CoveredA`:

1. **Checked multiplication by a literal**, on either side (`LTm.Src.mulL`,
   `mulR`; `LTm.Num.mulL`, `mulR`; `CheckedValue.mulLit`, `litMul`;
   `CheckedScalar.scale`, the code `c · (a - offset) + offset` under the
   range guard).  The decision over it is still `AFml.decide_iff`, the
   verified binary-derivative procedure, not `omega`.
2. **Universal quantifiers in a consequent**: `pre → ∀ k. post` (a
   postcondition's `\forall`) becomes `∀ k. pre → post` when `pre` reads
   no `k` (`LFml.prenex`), ahead of the prefix.
3. **Presburger quantifiers** (step 4): a quantifier left in the body past
   the prefix (in an antecedent, under a negation, alternating), whose
   body reads no storage and no transaction field once its reads at no
   bound variable are hoisted out (feature 6).  `decideLeaf` falls
   back to `quantReduction?` (`Calculus/QuantReduction.lean`) where
   `dependentReduction?` refuses:
   * the body lifted (within `liftBudget`), each quantified subformula
     `Qⱼ` outside binders replaced by a fresh Boolean atom `bⱼ`
     (`LFml.abstractQ`), the rest flattened and compiled as in M4;
   * each `Qⱼ` compiled to `QFml` (`QArith.compile`,
     `Calculus/QuantArithmetic.lean`): its equations by the shared checked
     compiler with no transaction field, read-free (`readFreeFormula?`),
     placed at their parameters' positions, a binder at its variable's
     position under the variable's range;
   * one sentence: the domain, `bⱼ ↔ Qⱼ` for each `j`, then the main
     arithmetic, decided by `QFml.decide_iff` and `QFml.verify`
     (`Calculus/PresburgerDecision.lean`).  The derivative of
     `∃ xᵢ. ⋁ S` reads both bits of `xᵢ` (the projection of the bit
     automaton): its states are lists over the body's universe, finite and
     never computed (it only bounds `reach`); the zero test of an `∃` is a
     reachability with the other bits `0`.  A bound is an atom
     `x < bound p` (`2^256` at a word) whose derivatives halve it: no
     value is enumerated.
   The abstracted body goes through M4's cut (`LFml.cutAll`, feature 5)
   like any leaf, so its main arithmetic may hold the cut operators.
   Validity of the sentence is validity of the leaf (`bⱼ` set to `Qⱼ`'s
   truth, the cut's fresh atoms by `Defs.Good.extend`); a false assignment
   is realized as in M4, the flattening's countermodel keeping each `bⱼ`
   equal to `Qⱼ` there, since `Qⱼ` reads no storage, and refuting the
   uncut body by `LFml.holds_cutAll`.  The cut keeps every atom of the
   body (`LFml.atomBound_le_cutAll`), so the flattening's read atoms, past
   the cut's bound, leave the `bⱼ` and the `Qⱼ`'s parameters alone.
   `Fml.quantCovered` (`Calculus/QuantTotality.lean`) is the
   fragment, on the eliminated leaf: a prefix binding the body's free
   parameters, the lift within budget, the abstracted body in
   `LFml.Src false` (the cut operators allowed), its cut within M4's
   bounds, each `Qⱼ` in `LFml.qfrag`
   (connectives, `∀`, equations of the checked compiler's `LTm.Num`/
   `LTm.BoolV` terms over value locals and literals, recognized with their
   evidence by `LTm.num?`, `LTm.bool?`).  It asks no quantifier to be
   left: a quantifier-free leaf M4 refuses may pass here.

4. **Unary `-` (`int`) and `~` (`uint`)**, affine codes like the literal
   product (`LTm.Src.neg`, `bnot`; `LTm.Num.neg`, `bnot`;
   `CheckedValue.neg` as `CheckedScalar.scale (-1)`, `CheckedValue.bnot` as
   `CheckedScalar.compl`, the code `2^256 - 1 - a`).
5. **Operators cut into fresh atoms** (`Calculus/QuotientCut.lean`, plan
   steps 1 and 2): the conversions `int(·)`/`uint(·)`; `/` and `%` by a
   nonzero literal and `&` by a low mask `2^k - 1` on either side (`uint`);
   `>>` by a literal (`uint` and `int`); `<<` by a literal (`uint`); the
   wrapping `+%`, `-%` (`uint`).  `LFml.cutAll`, the first stage of
   `flattenedArithmetic?`, replaces each such node `e` by a fresh atom `q`,
   sequenced after the operands it needs (`seq g q`), and puts `q`'s
   definition `g == g → e == q` in the antecedent; `%`, `&` and `<<` are
   written through the atom of a quotient (`a - q·c`, `(a - q·2^(256-k))·2^k`).
   A node written twice gets one atom (`quotAtom`, by term identity).  The
   cut is exact in a universal reading (`LFml.cutAll_valid_iff`), and a
   countermodel of the cut leaf refutes the leaf at the same point
   (`LFml.holds_cutAll`); the fresh atoms' values come from
   `Defs.Good.extend`.  The compiler encodes each definition exactly as a
   linear relation between codes (`StorageEncoding.special?`): a quotient
   `d·q ≤ x ≤ d·q + d - 1` with the bound `q ≤ M/d` stated, a wrapped sum
   `y = x₁ + x₂ ∨ y + 2^256 = x₁ + x₂`, a difference
   `y = x₁ - x₂ ∨ y = x₁ - x₂ + 2^256`, a conversion `y = x + 2^255 ∨ y + 2^255 = x`
   (`defDiv`, `defShr`, `defAddW`, `defSubW`, `defToInt`, `defToUint`).  On
   the source fragment the new term constructors are gated by a flag
   (`LTm.Src c w`, `w = true` before the cut) and the defining equations
   are `LFml.Src` constructors after it (`w = false`); `LTm.cut_src`,
   `LFml.cutAll_src` (`Calculus/CutTotality.lean`) map one to the other, so
   flattening and compilation keep their totality proofs
   (`readFlatten?_arith`, `flattenedArithmetic?_isSome`).
   `Fml.exactBounded` bounds the cut body (`body.cutAll`, the body itself
   where nothing is cut) as well as the lifted one.
6. **Reads hoisted out of quantifiers** (`Calculus/QuantHoist.lean`, step
   4's remainder): inside each quantifier of the body, a read `W(q)` of a
   total path (roots, fields, keys that are total terms) whose atoms
   the quantifiers on the way do not bind becomes a fresh atom `r`, and the
   body becomes `⋀ (W(q) == r) → body'` (`LFml.hoistOut`, `hoistPrep`).
   Exact (`hoistPrep_valid_iff`): the atoms set to the reads' values
   (`HDef.fill`) where the prepared body is valid, the same state and atoms
   where it fails (its definitions hold, so each atom is its read).  Where
   every read was hoistable the quantified subformulas are then read-free;
   the definitions are flattened with the rest of the body.  `evenGoal` (an `∃` in
   a consequent) is decided so; `evenRead`'s `∃` in a hypothesis is dropped
   to a fresh atom since feature 17.
7. **The array property fragment** (`Calculus/ArrayProperty.lean`, step
   5): a negative-position block `∀ k₁ … kₙ : uint. φ` outside binders,
   `φ` quantifier-free and reading a mapping `mapping(uint => p)` at a
   root at one of its variables, is replaced by its instances at the index
   set `U` (`LFml.apfInst`, `LFml.inst`): one per tuple of `U`, each
   guarded by its terms returning (`u == u → φ[ū/k̄]`).  `U` is `0`, the
   ground keys of those roots anywhere in the body, the guards' ground
   operands and their successors, each term once (`dedupKeys`).  Sound (`LFml.apfInst_sound`): the
   block implies each instance and stands where the body is antitone in
   it.  Exact (`ApfFml.apfInst_refute`, Bradley–Manna–Sipma): from a state
   and atoms where the instantiated body fails, the state whose rebuilt
   mappings hold at each key `i` what the key `⌊i⌋` held, `⌊i⌋` the
   largest value of `U` at most `i` (`MRoot.surgery`, `floorIn`), or `U`'s
   largest value where `i` lies past the second largest and the largest
   bounds no strict guard from above (`lastIn`: a guard true at `i` is
   true there).  The rebuilt mapping is listed region by region since
   feature 20 (`regionList`), a region holding the default left out; until
   then it listed one entry a key below the second largest value plus one:
   either way a solver's far key (`x > 2^200`) costs nothing.  Reads at `U`'s
   values keep their words, so every term outside the blocks reads as
   before (`ApfTm.eval_rel`); a guard true at the keys is true at their
   floors (`GuardP.mono`, `cmp_mono`: a variable against a ground
   operand, whose successor is in `U` for `t < k`; two variables by `≤`,
   `≥`, `==`); so each block holds by its instance at the floors
   (`LFml.block_refute`).  The fragment (`ApfFml.TopOk`, computed by
   `ApfFml.topB` with soundness `topB_sound`): every read of such a root a
   read along its own path (feature 18), at a block variable or at a
   ground key mentioning no binder of the body; guard atoms (`g == true`
   of `&&`/`||` of comparisons, or an equation of operands; their ground
   operands total until feature 19) only in negative positions of the
   block body; every other atom read alike.  With no quantifier left after instantiation,
   `QuantReduction.verify` decides the main arithmetic by `AFml.decide`
   (`valid_of_main`, `countermodelOfBody`), as `dependentReduction?` does.
   `bodyPrep` composes the two preparations (`Prep.trans`), and
   `Fml.quantCovered` reads the prepared body.
   Inner mappings (2026-10-25): `allow[3][k]`, `owed[a][k]`, a bound
   index as the last key under outer keys of any type, the floor
   construction under every outer key.  Since feature 18 (below) the
   outer `uint` keys are floored too, in the index set when ground, and
   the shapes of 2026-10-25 (`MShape`, `ApfTm.rread`) are gone.

8. **KeY `int`** (plan step 3, `Srt.kint`): a literal, a `uint` widened
   (`toInt`), `+`, `-`, a product by a literal on either side, and the
   comparisons (`LTm.Src.zlit` … `zcmp`; `LTm.ZNum`, `LTm.BoolV.zcmp`).
   An unbounded value has no range: `KIntValue` compiles it to an affine
   form over the typed codes, the difference of two of them where it
   comes from words, and a comparison to an `AFml` relation between the
   forms' positive and negative parts (`BooleanValue.zcmp`).  Nothing
   overflows, so no guard is added.  The flattener and the read queries
   take the new nodes (`flattenKInt?`, `ReadExpr.zbin`, `ReadExpr.zcmp`)
   under a variable symbol, so that the existing cases do not split on
   the sort.
9. **Reads of the starting ledger** (plan step 3, `net(a)`, an address a
   scalar of the fragment).  `decideLeaf` falls back to
   `ledgerReduction?` (`Calculus/LedgerReduction.lean`) where the
   others refuse (the array pipeline runs before it).  The lifted body's reads are cut (`LFml.ledgerCut`,
   `Calculus/LedgerCut.lean`): the `j`-th read `net(aⱼ)` becomes
   `seq aⱼ (net(j))`, and `aᵢ == aⱼ → net(i) == net(j)` for each pair is
   put in the antecedent.  The cut is exact in a universal reading
   (`LFml.ledgerCut_valid_iff`; it needs each address to read no ledger,
   `LFml.netOK`, and fewer than `2^256` reads).  The cut body goes through
   M4's cut and flattening, and the compiler takes each entry `net(j)` as
   the difference of two unbounded natural codes past the typed inputs
   (`Inputs.AgreeZ`, `LeafArithmeticZ`).  A false assignment realizes the
   entries as a ledger at the constants (`ledgerOfCodes`), and the
   refuting state's ledger is that one pulled back to the addresses'
   values (`LFml.ledgerPull`), which the reads' queries compute
   (`ReadExpr.query`), so the verdict stays computable.
   `Fml.ledgerCovered` is `Fml.inExact` with ledger reads
   (`LFml.srcL? .pre`) and the bounds of `Fml.exactBounded` on the ledger
   cut; `LFml.ledgerCut_src` (`Calculus/LedgerTotality.lean`) maps the
   fragment with reads at addresses to the one with reads at constants.
   A read under the symbolic execution's own ledger writes (`pay`,
   `store(net, …)`) was outside until feature 22.

10. **Storage arrays at symbolic indices** (plan step 6, arrays of
   primitives at roots, dynamic and fixed).  `decideLeaf` falls back to
   `arrayReduction?` (`Calculus/ArrayReduction.lean`) where
   `dependentReduction?` and `quantReduction?` refuse, ahead of the
   ledger's pipeline (on an array leaf that one recurses deeply enough to
   overflow the stack of a command-line `lean`).  Stage by stage:
   * *update pushing*: an equation over a formula's `a[i]` (the Theory
     reads every slot, the default past them; the interpreter halts past
     the live length) was read one way at each polarity.  `Tm.toLT`
     pushes it in exactly, as `orElse(find(S, a[i]), 0)` over the storage
     `S` the updates left (`Tm.toLT_sound`); `ExactAt.ofFormula?` takes
     an equation so where `directional?` refuses (`ExactAt.eqT?`).
   * *the eliminated leaf*: a slot test `has(a[i])` that a length check
     `i < a.length` of the same index guards is replaced by `true`
     (`LFml.hasFold`, `Calculus/ArrayFold.lean`), then the fallbacks are
     lifted out of equations (`LFml.orLift`, `Calculus/OrLift.lean`).
   * *the cut* (`Calculus/ArrayCut.lean`): the path guards, the read
     queries and the realization layer are not extended.  Instead every
     read of an array root (`obsW(a[i])`, `obsH(a[i])`, `obsL(a)`) becomes
     atoms before them: the index (the index itself where it is an atom)
     and the value, `seq i v`; the antecedent says what actual arrays make
     of them (`ARead.cons`: reads at equal indices one word, lengths of a
     root one, a slot there below the length and below a slot there, the
     default past a slot not there, exactly the slots below `n` in a fixed
     array of length `n`).  Exact in a universal reading
     (`LFml.aCut_valid_iff`): the actual observations satisfy the
     antecedent (`cons_fill`, `describes_fill`), and atoms that satisfy it
     rebuild a storage (`arrRealize`: each array root the array whose live
     length is the length atom and whose slots hold what the reads give
     them, up to the last slot the atoms need) in which the leaf reads
     what the cut leaf reads (`describes_realize`, `frames_realize`).  An
     index that reads an array root, and any other read of one, refuse
     the cut.
   * *the rest*: guards extracted (`LFml.gx`: an equation of guarded terms
     as its guards' conjunction and the values' equation), conditionals
     lifted, flattened and decided as in M4.  A false assignment is shrunk
     code by code while the arithmetic stays false at it
     (`ArrayReduction.shrinkCodes`, checked again by `AFml.check`), then
     realized as in M4 and its arrays rebuilt from the atoms, built
     eagerly.  The shrinking is a heuristic: the arithmetic is free to pick
     a length near `2^256`, and where the shrinking cannot bring it down
     (or a fixed array is long) the refuting state exists but cannot be
     built in practice.
   `Fml.arrayCovered` is the fragment, on the eliminated leaf: the array
   stages succeed, their leaf in `LFml.Src true` within the lifting fuel,
   budget and M4's bounds; `arrayReduction?_isSome` proves the pipeline
   never refuses it, through `LFml.liftCond_src` and
   `flattenedArithmetic?_isSome`.

11. **Hashes under the premise** (plan step 7, `decideHash`,
    `Calculus/HashSwap.lean` … `Calculus/HashComplete.lean`).  A leaf whose
    memory locals are fresh byte strings (`∀ fresh s.`, `Fml.allocAll` at
    `uint[]`, any bytes) read only by hashes of one kind (not `ecrecover`):
    * **the swap** (`Fml.swPrefix`): each string read as the word its hash
      returns, its binder a `∀ uint`, each hash node the local
      (`Tm.sw`), on a body of equations, `wt`, the connectives,
      one-element updates (a storage write, a value local declared or
      set, no push) and value binders.  A state of the leaf and one of the swapped leaf with
      one storage, ledger and transaction, any heaps, each string's word
      its hash, read every term alike (`SwRel`, `Tm.sw_eval`,
      `Tm.sw_denote`, `Fml.sw_holds`), so a valid swapped leaf is valid
      whatever the hash (`Fml.swPrefix_validH`), where the body's value
      binders are positive (`Fml.posAll`): the premise is read at each
      binder's instance, which only weakens a positive binder
      (`Fml.holdsS_of_sw`): `decideLeaf` decides it;
    * **the refutation** (`Fml.swInst`): the swapped leaf with each word
      fixed (`∀ v. v == c → …`) to the hash of a family's one-word string,
      one per class of equal strings (`rgs`, the restricted growth
      strings: one instance for one string, two for two, 15 for four, 52
      for five).
      The first instance `decideLeaf` refutes gives a state; the leaf's
      strings allocated there with the family's bytes hash to exactly the
      fixed words, and a heap of the family's strings meets every premise,
      their hashes being distinct and nonzero (`famOK`: by the kernel for
      four strings of each kind, `famBound`; for a leaf of `n > 4` strings
      the family of `n` computed, `famCheck`, `famN`), so it refutes the
      leaf under its premise (`Fml.swInst_refutes`, `Fml.holdsS_fam`);
    * **exactness** (`Fml.swPrefix_exact`, `Fml.swPrefix_complete`): the
      swapped leaf reads its words only as they compare, against each
      other and as keys of the roots they key (`Fml.rl`: the storage read
      at a path, written by a one-element update, no `wt`, keyed roots
      `mapping(uint => uint)`), so a state refuting it is relabeled into
      one refuting the instance at its classes (`classesOf`): each fixed
      word sent to its class's free word, each keyed root's entry at a
      fixed key moved from the free one (`RelRL`, `relabel_state`,
      `Fml.rl_holds`).  So `Fml.ValidH φ ↔ Fml.Valid φ'` on the fragment.
    `Fml.hashCovered` is the fragment: a hash, and for some way of
    deciding it (`hashTries`) its coverage: for one kind, the swapped leaf
    and every instance in `Fml.Covered`, the family of `n` strings checked
    where `n > 4` (`famCovered`: the kernel's theorem up to four, the
    computed check past it), the swapped leaf in `Fml.rl` over the roots
    its words key (`Fml.vRoots`), each `mapping(uint => uint)`
    (`kTypedB`), the prefix's string levels the words' (`Fml.prefixOK`),
    the body's value binders positive (`Fml.posAll`) (`Fml.coveredK`); for
    two, `Fml.coveredK2`, below.

12. **Two kinds of hash** (2026-10-25, `decideHash2`,
    `Calculus/HashKinds.lean`): a string hashed by two kinds stands for one
    word per kind.  For an ordered pair `k₁`, `k₂` (`hashTries` tries the
    six), `k₂` hashes at least one string (else the one-kind decision of
    `k₁` is the same), anywhere: past an update the premise reads a hash
    where the update lands (`Fml.HashIn`); and `k₁` hashes each of those
    strings where the premise always reads it, outside every update's
    continuation (`Fml.topLevels`).  The body's one-element updates are a
    storage write, a value local declared or set (`Upd.xk1?`):
    * **the second kind's words** (`Fml.tk`): past the prefix, one new
      `∀ uint` per string `k₂` hashes (`Fml.allN`), each `k₂` node of the
      string read as its word, the rest of the body read past the new
      binders (`Tm.xk`, `Fml.xk`, a thinning and the strings' words,
      `XMap`; `Fml.xk_holds`), and the premise per kind assumed as the link
      of the two kinds' words: for each pair of those strings,
      `k₁(sᵢ) == k₁(sⱼ)` exactly where `eᵢ == eⱼ` (`linkE`).  The result has
      hashes of `k₁` only, which the one-kind swap reads;
    * **valid** (`Fml.tk_validH`): each word set to its string's hash
      where the premise reads that hash, and to a word that keeps the link
      elsewhere (`linkChoice`: the class's word, or a fresh one); the link
      holds by the premise (equal outputs of one kind, equal inputs, equal
      outputs of the other, `Grown.hashId_of_input`), the body reads each
      word only where the premise reads its hash (`XRelQ`,
      `Fml.xk_holdsQ`), and the result's premise is the body's
      (`Fml.xk_hashIn`);
    * **refuted** (`Fml.tk_refutes`): the instance at classes (`Fml.swInst`)
      of the result with the words fixed to a family string's two hashes
      (`fixE`, `famPairE`: `k₁(s) = famHash k₁ j ∧ e = famHash k₂ j` for
      some `j < N`, `N = famN n`); refuted, it refutes the leaf with the
      family's strings, where every kind's hashes are distinct
      (`Fml.hashFree_memNodes`, `famOKAll N`);
    * **complete** (`Fml.tk_complete`): the one-kind completeness
      (`Fml.swPrefix_complete`) relabels the first kind's words; at the new
      binders the link makes the free words of the second kind follow the
      classes, so they are relabeled to the family's second hashes, their
      roots' entries moved (`RelRL` over the new binders' levels,
      `relabel_stateΓ`, `RelRL.envOfSw`, `Fml.tkBody_fix_complete`).
    `Fml.coveredK2` is the fragment: `Fml.coveredK`'s conditions on the
    result for `k₁`, every instance with the words fixed covered, and the
    swapped body over the new binders in `Fml.rl` of their levels and the
    roots they key, each `mapping(uint => uint)` (`Fml.tkRL`).  The fixed
    reading `Fml.tk … true` is computed once per leaf, not per class
    assignment (`refuteAt2`, `Fml.coveredK2`).

13. **Fresh memory arrays** (2026-10-25, plan step 6, `decideMem`,
    `Calculus/MemSwap.lean`).  `decideLeaf` is `decideLeafA` (the
    pipelines above), then, where that answers `unknown` and the leaf binds
    fresh memory objects (`Fml.allocAll`: a `catch` clause's data, a memory
    parameter), `decideMem`: the leaf with its reads of fresh arrays of
    primitives (`T[]`, `T[n]` with `n < 2^256`, any contents) cut into
    atoms (`Fml.mxTop`), decided by `decideLeafA`.
    * **the cut** (`Fml.mx`, `Tm.mx`): each binder `∀ fresh x : T[]`
      becomes `∀ uint n` (the length; a word nothing reads for `T[n]`),
      then one `∀ w` per read `x[e]` the leaf makes (`Fml.mxIdx`, repeats
      dropped), under what actual arrays make of them (`mxCons`, Ackermann's
      reduction: `eᵢ == eⱼ → wᵢ == wⱼ`); `len(x)` becomes `n`, the read
      `e < n ? w : ⊥` (`n` the literal length of a `T[n]`, `⊥` the halt
      `1 / 0`: a read past the length reverts).  The binder's atoms stand
      right after it, so it may stand anywhere among `∀`s and connectives,
      at either polarity; an index must name no local bound after the array
      and read as it denotes (`Tm.ixOk`: value locals, literals, the
      transaction's fields, operators).
    * **exact at every state** (`Fml.mx_holds`, `Fml.mxTop_holds`):
      `MxRel` relates a state of the leaf to one of the cut leaf: global
      parts alike but for the heap, value locals alike, each read the cut
      has abstracted (`MxOrig`: a length, an element at an index) read by
      the term that stands for it (`MxMap.tbl`); terms read and denote alike
      over it (`Tm.mx_eval`, `Tm.mx_denote`), an allocation keeping every
      older read (`MxOrig.eval_alloc`).  At a binder, a fresh object's reads
      give words that meet the premise (`mxFill`), and words that meet it
      give an object of length `n` holding at each index the word of the
      first read there (`mxRealize`), so `∀ fresh x. φ` holds exactly where
      `∀ n w. cons → φ'` does (`MxRel.alloc`).  A proof of the cut leaf
      proves the leaf; a state refuting it refutes the leaf, as it is (the
      binders range over every object).
    `Fml.memCovered` is the fragment: the leaf binds a fresh object, its cut
    is defined and in `Fml.CoveredA` (`decideMem_complete`).

14. **Operators with a literal operand, through the others** (2026-10-25,
    `Calculus/QuotientCut.lean`, `Calculus/BitArith.lean`).  `cut2` writes
    each through the operators already cut, so no new definition reaches
    the compilers but one (`defDivI`):
    * `x & c` at `uint` for any literal `c` (`bandGo`): bit by bit from the
      lowest, the atom `q` of `x / 2` (`defDiv`), the low bit `x - 2q`, the
      rest `2 · (q & ⌊c/2⌋)`, down to `c`'s top bit (the fuel is `c`
      itself, so the kernel never unfolds a fixed 256 on a symbolic
      literal); `BitArith.and_split`.  Low masks keep `maskCut`;
    * `x | c` as `(x - (x & c)) + c`, `x ^ c` as `(x - (x & c)) + (c - (x & c))`
      (`borLit`, `bxorLit`; `BitArith.and_or_eq`, `xor_and_eq`), checked
      sums that never overflow;
    * `x *% c` by doubling (`mulWGo`): `x *% c` from `x *% ⌊c/2⌋`, a wrapped
      sum with itself (`defAddW`) and, for an odd `c`, with `x`
      (`BitArith.mulMod_double`, `mulMod_succ`); about `2·log₂ c` atoms;
    * `x ** 0`, `x **% 0` as `1` after `x`; `x ** 1`, `x **% 1` as `x` (`powLit`);
    * `x / c`, `x % c` at `int`: `c = 0` fails (`x` then `err`, as at
      `uint` now), `c = -1` is `-x` and `0` after `x`, any other `c` the atom
      of the truncated quotient, defined by its sign cases
      (`StorageEncoding.defDivI`, `tdivRel`: `x - c·q` between `0` and
      `|c| - 1` on `x`'s side of zero, `BitArith.tdiv_iff`), and `x % c` as
      `x - q·c`;
    * the literal on either side of `&`, `|`, `^`, `*%` (`LTm.SrcL.litR`,
      `litL`, gated by `litCutR`/`litCutL`; recognized by `LTm.litSrc?`).
    `CutTm.Good` of each (`bandGo_spec`, `mulWGo_spec`, `bandLit_spec`,
    `borLit_spec`, `bxorLit_spec`, `mulWLit_spec`, `powLit_spec`,
    `int_rem_eval`), their source fragment (`bandGo_src` … `cut2_comm_src`,
    `LTm.cut_src`), lifting, the ledger fragment, flattening and the
    compiler (`LFml.Arith.defDivI`) carry the completeness through.
15. **Reads without a fixed bound** (2026-10-25): the flattener's budget is
    the leaf's own (`readBudget φ = max 2048 (words²)`, in
    `dependentReduction?`, `quantReduction?`, `ledgerReduction?` and
    `arrayReduction?`); `readFlatten?_arith` and `readFlatten?_arithZ`
    take any budget past 2048 that covers the reads' pairs, so
    `Fml.exactBounded`, `LFml.ledgerBounded`, `LFml.quantCovered` and
    `Fml.arrayCovered` bound the nodes only.
16. **`bool` quantifiers expanded** (2026-10-26, `Calculus/QuantExpand.lean`,
    the first preparation of `bodyPrep`): `∀ bool b. φ` is
    `φ[true/b] ∧ φ[false/b]` at any polarity (`LFml.expandB`, `LTm.substB`,
    `LFml.substB` stopping at a binder of `b`; `LFml.holds_expandB`, exact
    at every state, so `boolPrep`'s refutation is the state itself).  A
    block over a `bool`-keyed mapping becomes its two instances,
    quantifier-free (`gapBoolKeyed`).
17. **Positive quantifiers past the prefix** (2026-10-26, `dropPrep`): a
    `∀` in a positive position outside every negative-position `∀` is the
    prefix's, read at a fresh atom: `B ∧ ∀ k. C` is `∀ k. B ∧ C`,
    `(¬ ∀ k. C) → D` is `∀ k. ¬ C → D`, past `∧`, `→` and `¬` (the prenex
    laws `LFml.prenex` applies only to a consequent).  One binder at a time,
    the outermost first, renamed to the position past every atom
    (`LFml.ren`, `LFml.holds_ren`); `LFml.dropOne_spec` says the formula
    holds exactly where the result holds for every value of the new atom
    (at a positive polarity; for some value at a negative one), so the
    refutation is the state itself, at the same atoms.  A `∀` under a
    negative one stays (its variable may depend on the outer one).  So
    goes a `∀` inside a conjunction (`gapPositiveForall`), and a
    Presburger `∃` in a hypothesis, which is such a positive `∀`
    (`evenHyp`, `evenRead`: no quantifier left, decided by `AFml` and no
    longer by `QFml`; `evenGoal` keeps a hoisted read).
18. **Every `uint` key along a root's mappings floored** (2026-10-26,
    `Calculus/ArrayProperty.lean`): the rebuilt root is `FloorShape.of` its
    type (`floor` at a `mapping(uint => V)`, `outer` at a mapping keyed by
    another type, `keep` past the mappings: a struct, an array, a word),
    and `FloorShape.rebuild` holds at each floored key what its floor held,
    the whole value under it copied.  A read at a root of the blocks is a
    path of its own (`ApfTm.rroot`, `rkey` at a key, floored where its
    type is the pass's since feature 20, `rfield` past the mappings,
    `rword` the word there), and
    reads at its keys' floors (`FloorShape.rebuild_word`, `SRef.floorRef`,
    `FloorShape.floorPath_append`; `ApfTm.eval_trel` carries the shape the path
    reaches, `ApfTm.pre`).  So a bound key need not be the last
    (`gapColumn`, `allow[i][3]`), a root may be read at a bound key at two
    depths (`gapTwoPaths`, `allow[3][k]` and `allow[k][3]`, one floor for
    both), and a member may follow the bound key (`gapStructValue`,
    `accs[k].v`).  The price: a `uint` key along the mappings is in the
    index set when it is ground (`ApfTm.gkeys`), so it may mention no
    binder of the body (an outer key could before), and a refutation lists
    entries at every floored level (`rowFar`: seven rows of twelve entries
    and an empty default row since feature 20, where it listed one row and
    the default before feature 18).  Two bound indices on one path
    stay outside (`gridApf`, the target's decision).
19. **Guards whose ground operand may halt** (2026-10-26): `k < x - 1`
    (`gapPartialGuard`).  An operand need not be total (`IdxP.gnd`); a
    guard true at the keys returned there, so its operands did, and a
    ground one reads the same at the floors (`IdxP.values`), so the guard
    is true at the floors (`GuardP.mono`), except where a `||` evaluates
    its left operand false at the keys and halting at the floors:
    `(P && Q) || R` with `P` false at the keys, so the halting `Q` skipped,
    and true at the floors.  So the left operand of every `||` must
    return at the floors where it returned at the keys (`GuardP`'s `ds`,
    `guardDs`: a comparison does, a `&&` whose left operand does and whose
    right one returns wherever its atoms do, `tot`, `guardTot`;
    `GuardP.floors`, `GuardP.defined`).  `(k < x - 1 || k == 7)` is taken
    (no `dl!` spelling for a comparison under `||`, so not pinned).  The index set takes a guard's
    comparison operands, no longer the operands' own subterms (`guardGd`:
    `k < x - 1` puts `x - 1` and its successor in, not `x` and `1`).
20. **Blocks over `int` keys, refutations by regions** (2026-10-26,
    `Calculus/FloorRegion.lean`, `Calculus/ArrayProperty.lean`): the
    instantiation is one pass per key type (`OrdK`: `uint` and `int`, each
    value an integer in `[lo, hi)`; `apfPrepK`), the `uint` pass then the
    `int` one (`apfPrep`), each instantiating the blocks whose variables
    are all of its type (`LFml.chainQF K`, `LFml.inst`, `LTm.subst1` at
    `K`) and flooring the keys of its type along the roots they read
    (`FloorShape K`: `floor` at a `mapping(K => V)`, `outer` at any other
    key, `rkey` one path step, floored where its key type is the pass's).
    The floor has the type's least value as its base (`floorIn lo`,
    `lastIn` over `ApfSet`'s `[lo, hi)`), which the index set takes
    (`IdxKey.base`, `-2^255` at `int`), with the largest value at an `int`
    pass (`IdxKey.top`), so the keys past the goal's read a free word.
    A rebuilt mapping no longer lists one entry a key: the floor is
    constant between consecutive breakpoints (`ApfSet.breaks`: `lo`,
    `lo + 1`, the index set's values and their successors;
    `lastIn_breaks`), so it is listed region by region (`regionList`: for
    each breakpoint `b` the keys `[b, next b)` as one symbolic run,
    `regionKeys`), a region whose value is the default (`SVal.beq`, the
    largest key's floor's value) left out.  A read finds its key's last
    breakpoint's region and nothing else (`lookupBy_regionList`), so the
    refutation's reads are proved by region reasoning, the run's length
    symbolic, never evaluated (`FloorShape.rebuild_word`, `FloorsOn`).  So
    every `int`-keyed leaf of the shape is decided, also those whose every
    refutation lists `2^255` keys (`intTwoSides`): the theorem asks
    `≠ unknown`, and the refuting state is a term no evaluation builds;
    one whose regions away from the goal's keys hold the default is built
    at once (`intKeyedBad`: one entry).
21. **Blocks over the ledger** (2026-10-26, `Calculus/LedgerBlock.lean`):
    a `uint` block may read the starting ledger at its variables
    (`ApfTm.net`, KeY `int` terms `zlit`, `toInt`, `zbin`, `zcmp`;
    `ARoots.net`), and the pass then rebuilds the ledger as it rebuilds a
    mapping (`netRebuild`, region by region, a region of `0`s, the
    ledger's default, left out; `NetFloor`, `netRebuild_floor`,
    `NetRel.eval`), the index set taking the largest address (`IdxKey.top`).
    No pipeline took both: `ledgerBlockReduction?` is `ledgerReduction?`
    with `apfPrep` between the prefix and the ledger cut
    (`LedgerBlockReduction.valid_of_body`, `countermodelOfBody`, `verify`),
    after the other four in `decideLeafA`; `Fml.ledgerBlockCovered`
    (`LFml.ledgerBlockCovered`, `ledgerBlockReduction?_isSome`) asks the
    prepared body to be in the ledger fragment with no conditional
    (`LFml.srcL? .pre false`) within M4's bounds.  A leaf whose every
    refutation lists `2^256 - 6` addresses (`ledgerFar`) is decided so,
    its refuting ledger a term; `ledgerBlockBad`'s is built at once.  The
    pipeline also takes mapping blocks beside ground ledger reads.
    Whether a refutation is small depends on the arithmetic's free words:
    a region is left out only where the solver's word at its floor is the
    default (`0` for the ledger, the largest key's word for a mapping), so
    a leaf with a small refutation may be answered by a large one, which
    evaluating the verdict would then try to build (`regionKeys` is a
    list); the pinned refutations are small.

22. **Ledger reads past ledger writes** (2026-10-26,
    `Calculus/DecideScoped.lean`, `Calculus/DecideTyped.lean`): the
    symbolic state keeps the ledger writes its updates made (`SymS.netW`,
    the latest first; `NetW.op` for `net := store(net, r, net(r) ± a)`,
    `NetW.pay` for `pay(r, a)`, `NetW.mt` for `net := store(mtSt, r, a)`),
    each with its operands read where its update is applied.  A read
    `net(x)` past them is the starting ledger's entry moved by each write at
    the address it names (`NetW.read`): `net(x) ± toInt(x == r ? a : 0)`,
    `net(x) - toInt(x == r ? (r == this ? 0 : a) : 0)` for a payment,
    `toInt(x == r ? a : 0)` past `mtSt`.  The conditional is a `kite` at a
    word, the shape the elimination gives a read past a storage write, so
    the source fragment, `LTm.condSplit` and the lift take it unchanged
    (`LTm.SrcL.kite` under `zint`), and the lifted leaf goes through the
    ledger pipeline of feature 9.  A payment also moves the balance as
    `State.pay` does, from the balance its update is applied at
    (`payBal`: `b` where `r` is the contract, `b - a` where `a ≤ b`, `0`
    otherwise).  The builder's agreement reads the ledger past the writes
    (`AgreesV.netRd`, at each literal address; `NetW.read_eval` moves a read
    at a term to its value), and freshness likewise (`SymS.Fresh.net`);
    `NetW.read_op`, `NetW.read_pay`, `NetW.read_mt` and `payBal_eval` are
    the four landing lemmas.  A snapshot `x := net` past a write stays
    outside (`SymS.netOk`, now `netW = []`), and so does the step
    fragment's (`SymS.Ok` asks `netW = []`: `UpdElem.ElimOk` writes no
    ledger).  `gapLedgerWrite` is refuted (the payee `0`, its entry `0`),
    `ledgerWriteOk` and `payBalanceOk` proved, `payBalanceBad` refuted, the
    first three's coverage kernel-checked.  Each write multiplies the
    lifted leaf by the conditional's cases: two payments to one address
    read once already pass `Fml.exactBounded`'s 511 nodes.

All five were refused before (`dependentReduction?` returned `none`: the
compiler read only `+`/`-`, and `LFml.src?` refuses `.all`); so were six
and seven (`quantReduction?` compiled no storage read in a quantifier),
and eight and nine (no atom of `Srt.kint`, no ledger read), and ten
(`sourceReduction?` refused a formula's `a[i]` after an update, and no
stage read an array path); eleven was answered `unknown` (`decideGoal`
read no hash), and twelve too (the swap reads one kind), and thirteen
(`ExactAt` has no case for `allocAll`, `LTm.Elimable` refuses the memory
sorts); fourteen was refused by the cut, which wrote no `|`, `^`, `*%`,
other masks or `int` quotients, and fifteen by the fixed 45 reads;
sixteen to nineteen were outside `apfPrep`'s shapes (a `bool` block, a
bound key not the last, at two depths or before a member, a halting guard
operand) or reached no stage (`quantReduction?` abstracts a positive `∀`
reading storage at its variable to a quantified subformula outside
`LFml.qfrag`); twenty and twenty-one were outside them too (an `int`
block variable; a ledger read at one, and no pipeline taking both).
`Examples/Decision.lean` pins them: `2 * x`, `x * 3`, a doubled storage
read, a doubling that overflows under the diamond (refuted), nested
consequent quantifiers, a postcondition `∀ j` past a write (proved), and
its false variant (refuted); and for feature 3, an `∃` in a hypothesis
(`evenHyp`, proved; `evenHypBad`, refuted), a `∀` in one (`leastHyp`), an
alternation `∀∃` (`above`, proved; `below`, refuted) and an `∃` hypothesis
beside a storage write (`evenWrite`, proved; `oddWrite`, refuted).  The
coverage of `double`, `nested` and `evenHyp` is kernel-checked
(`decide +kernel`); the other rows and the verdicts are the compiled ones
(`#eval` pins), since the kernel's arithmetic decision over 256-bit codes
is too deep for the language server.
For features 6 and 7: `evenRead` (proved) and `evenReadBad` (refuted),
`evenGoal` (proved) and `evenGoalBad` (refuted), `evenGoal_covered`;
`apf`, `apfTwo` (proved), `apfBad`, `apfOut`, `apfTwoBad` (refuted), the
coverage of `evenRead`, `apf` and `apfBad` kernel-checked.
For the fourth and fifth it pins a proved
and a refuted verdict per operator (`-`, `~`, `int`, `uint`, `/`, `%`,
`>>` on `uint` and `int`, `<<` at 0 and past 256, `& 7`, `7 &`, `+%`,
`-%`), and kernel-checks one covered leaf per operator (`neg_covered` …
`subW_covered`).
For feature 8 it pins `toInt(x) + 1 > toInt(x)`, a difference that may
be negative, a sum past `2^256`, products by literals, a transaction field
and a storage read past a write, proved and refuted (`kintOk` …
`kintRead`), `kint_covered` and `kintScale_covered` kernel-checked.  For
feature 9: `net(a) = 7 → net(a) + 1 = 8`, reads at equal addresses
(`netSame`), a ledger entry against a storage read and past a write,
proved; `net(a) >= 0` and `net(a) = 7 → net(b) = 7`, refuted;
`net_covered`, `netSame_covered`, `netSwap_covered` kernel-checked.
For feature 10: an in-range read with its element read again in the
postcondition (`inRange`, proved; `inRangeBad`, refuted), a read past the
length under the diamond (`pastEnd`, refuted) and below it
(`inRangeReturns`, proved), a write then a read at equal indices
(`writeSame`), at different ones keeping the old word (`writeKeep`) and the
written word read back (`writeRead`), proved; at any indices
(`writeOther`), refuted; a fixed array written below its length
(`rowWrite`, proved) and past it (`rowPast`, refuted), read past it (the
default, `rowPastRead`, proved); the slots past the live length, which
the Theory reads as they are (`shadowRead`, refuted); an element stored
in a mapping (`owedRead`, proved); and the two leaves once pinned as
counterexamples (`arrayRead`, an element at a checked index, `fixedRead`,
a fixed array's at a literal one), proved, in `Fml.inTarget` and
`Fml.Covered` by the kernel.  `pastEnd_covered`, `writeSame_covered` and
`inRange_covered` are kernel-checked; `pastEnd_answers`,
`writeSame_answers` and `inRange_iff` apply the theorems.  The array verdicts are
evaluated one after another (`set_option Elab.async false`): evaluated
in parallel they overflow a command-line `lean`'s stack.
For feature 11, `Examples/DecisionHashes.lean` pins, over `Names` of
`Examples/Tactics/Hashing.lean` §3
(`mapping(string => uint) ids`, keyed by `keccak256`): `namesSet`, the leaf
`∀ s t. keccak256(s) != keccak256(t) → ids[s] == 0 → {ids[t] := 1}
ids[s] == 0` (`[ ids[t] = 1; ]` past the program; `s ≠ t` as their hashes,
the only way a leaf with no memory read states that two strings read
different bytes), proved; without `s ≠ t` (`namesSetBad`) refuted by two
strings with the same bytes; `keccak256(s) == keccak256(t) → ids[s] ==
ids[t]` (`namesEq`) proved and `keccak256(s) == keccak256(t)`
(`namesEqBad`) refuted by two strings with different bytes; `namesSet_covered`
and `namesEqBad_covered` kernel-checked (about 4 s each),
`namesSet_answers` by `decideGoal_complete_hash`.  `namesBound` (the
strings as hidden binders) is outside the fragment and `unknown`.  For
feature 12: `namesTwoKinds` (`sha256(s) == sha256(t) → keccak256(s) ==
keccak256(t)`, valid only under the premise) proved, `namesTwoKindsBad`
refuted (one string twice), `namesTwoKinds_covered` kernel-checked (about
16 s) and `namesTwoKinds_answers`; over `Names2`
(`mapping(string => uint) ids; mapping(uint => uint) shas`), `twoKeys`
(`sha256(s) ≠ sha256(t)`, a write at `ids[keccak256(t)]` leaves
`ids[keccak256(s)]` and `shas[sha256(s)]`) proved, `twoKeysBad` refuted,
`twoKeys_covered` kernel-checked (about 28 s).
The hash round of 2026-10-25 adds: `namesLanded` (`sha256(s) ==
sha256(t) → [ ids[0] = 1; ] keccak256(s) == keccak256(t)`, the second
kind's hashes past an update) proved, `namesLandedBad` refuted,
`namesLanded_covered` kernel-checked and `namesLanded_answers`;
`namesSetLocal` (a value local set, `{ x := 1 }`, in a two-kind leaf)
proved, `namesSetLocalBad` refuted; `fiveStrings` (two of five strings
alike, refuted by five classes: the family of five computed) refuted and
`fiveChain` (a chain of five equal hashes) proved, `fiveChain_covered`
kernel-checked (the family of five and 52 instances, about 35 s);
`namesUnderForall` (`keccak256(s) == keccak256(t) → ∀ x. x == 0 →
keccak256(s) == keccak256(t)`) proved, `namesUnderForallBad` refuted,
`namesUnderForall_covered` kernel-checked (`Examples/DecisionHashes.lean`).
For the inner mappings of feature 7: `rowApf` (`allow[3][k]`) and `rowVar`
(a parameter row) proved, `rowBad` (another row) and `rowOut` (a key past
the guard) refuted; `rowApf_covered`, `rowBad_covered` kernel-checked,
`rowApf_answers`, `rowApf_iff`; `rowFar` (`x > 2^200 → allow[3][x] == 0`
against the block) refuted by a state whose rows list twelve entries
(`allowRows`), `rowFar_covered` kernel-checked.
For feature 13, `Examples/DecisionMemory.lean` pins: `gapMemory`
(`len(s) > 0 → s[0] == 0`, once a counterexample) refuted; a read at a parameter index read twice
(`memSame`) and Ackermann's premise (`memAck`, `i == j → s[i] == 5 →
s[j] == 5`) proved, without `i == j` (`memAckBad`) refuted; two fresh
arrays apart (`memApart`) and their lengths (`memLenEq`) refuted; a read
below the length (`memInRange`) proved, past it (`memPast`, at length `0`)
refuted, and two reads that halt alike equal in the Theory (`memHalts`)
proved; a `uint[3]` read below its length (`memFixed`) proved, past it
(`memFixedPast`) refuted; a `bool[]` (`memBools`) proved.
`gapMemory_covered`, `memAck_covered` and `memAck_inTarget` are
kernel-checked, `gapMemory_answers` and `memAck_iff` apply the theorems.
For feature 14: the former counterexamples `gapIntDiv` (`x ≥ 0 → (x / 3) · 3 ≤ x`
at `int`), `gapIntMod`, `gapOr` (`x | 1 ≥ x`), `gapXor`, `gapAnd` (`x & 6 ≤ 6`),
`gapPow` (`x ** 1 == x`) and `gapMulW` (`x *% 3 ≥ 0`) proved; `intDivBad`,
`intModBad`, `orBad`, `xorBad`, `andBad` (`6 & x < 6`, the literal on the
left), `powBad` (`x ** 0 == x`) and `mulWBad` (`3 *% x ≥ x`) refuted; the
coverage of each of the seven, `andBad` and `mulWBad` kernel-checked
(`gapIntDiv_covered` …, under a second each), `gapOr_answers`,
`gapMulW_iff`.  For feature 15: `gapManyReads` (fifty reads) covered by the
kernel and answering (`gapManyReads_answers`, by `decideGoal_complete`);
its verdict is not computed (below, "Running time").  For features 16 to
19: the former counterexamples `gapBoolKeyed`, `gapPositiveForall`,
`gapColumn`, `gapTwoPaths`, `gapStructValue` and `gapPartialGuard`
proved; `boolKeyedBad` (`b == true → flags[b] == 0` against
`flags[false]`), `positiveForallBad`, `columnBad` (another column),
`twoPathsBad` (another row), `structValueBad` (the other member) and
`partialGuardBad` (`x - 1` halting or below `2`) refuted; the coverage of
the six and of `columnBad` kernel-checked (`gapColumn_covered` …),
`gapColumn_answers`, `gapPartialGuard_iff`.  For features 20 and 21: the
former counterexamples `gapIntKeyed` and `gapLedgerBlock` proved;
`intKeyedBad` (`(∀ int k; k > 0 → ibal[k] == 0) → ibal[0] == 0`, its
refuting `ibal` one entry) and `ledgerBlockBad` (an address past the
guard's bound) refuted; the four's coverage kernel-checked,
`gapIntKeyed_answers`, `gapLedgerBlock_iff`; `intTwoSides` and `ledgerFar`
(the leaves of the two shapes every refutation of which is astronomically
large) in the fragment and covered by the kernel and answering
(`intTwoSides_answers`, `ledgerFar_answers`), `intTwoSides`'s instance
refuted by its arithmetic (computed), the refuting states not computed.

### Running time (the walks)

Both decisions walk their derivative graphs depth first (`walk`,
`Calculus/VisitedSet.lean`), the states seen kept in an `HSet`: a search
tree on a hash, its buckets compared exactly, so membership is a walk down
the tree and a comparison, not a pass over every state found.  A walk
stops at the first state false at zero; its reconstruction is the
counterassignment, and the rest of the graph is not built.

* `AFml` (`AFml.fastVerify`, `Calculus/LinearDecision.lean`): a step reads
  one variable's bit (`AFml.pstep`: `xⱼ = b + 2·yⱼ`), two successors where
  `AFml.deriv` had `2^n`.  The atoms it touches are worked out by sign and
  halved where every coefficient became even, so a round of every
  variable halves each form back.  The formula is put in normal form first
  (`AFml.norm`: `true`/`false` absorbed by the connectives, an atom its
  sign settles worked out, an atom divided by its coefficients' divisor),
  and a hypothesis a bit falsifies (`q ≤ 15` once a fifth bit of `q` is
  `1`) closes its branch at once.  A closed walk proves the formula by
  `AFml.valid_of_rounds`: induction on the sum of the variables, a round
  halving all of them (`AFml.round`).
* `QFml` (`QFml.fastVerify`, `Calculus/PresburgerDecision.lean`): the same
  walk over `QFml.deriv`, whose `∃` lists are sorted by hash before
  repeats are dropped (`canon`): two orders of one list are one state.  The
  zero test of an `∃` is a walk of its own (`exTest`) that stops at the
  first state true at zero; the states of its closed walks are remembered
  as reaching none (`NGood`) and cut from later tests, and each `∃`'s
  answer is memoized (`atZeroC`, `ZGood`).  The caches thread through the
  walk (`walkC`), which is the plain walk on them (`walkC_eq`).

The walks' fuel (`2^64` steps) is not proved to suffice: the normalized
states' universe is not computed.  Where it runs out, `AFml.decide` and
`AFml.verify` fall back to the breadth-first search whose bound is proved
(`AFml.search_iff`), `QFml.decide` and `QFml.verify` to `QFml.search`;
`decide_iff` holds either way.  A refutation's witness is now the walk's:
six pinned countermodel values moved (`Examples/AutoComplete.lean`,
`QueryArithmetic.lean`, `AliasConstraints.lean`, `ProgramReduction.lean`,
`ReadFlattening.lean`), no verdict.

`verdict` of the pins of `Examples/Decision.lean`, in the language
server's interpreter (as a build runs the `#eval` pins), before
(`3f5f3f4b`) and after (2026-10-25), in seconds:

| Leaf | Before | After | | Leaf | Before | After |
|---|---|---|---|---|---|---|
| `shrOk` (`>> 4`) | 299 | 1.9 | | `netOther` | 111 | 0.002 |
| `maskBad` (`& 7`) | 78 | 0.08 | | `netDistinct` | 40 | 1.0 |
| `modBad` (`% 8`) | 77 | 0.08 | | `netSame` | 13 | 0.5 |
| `modOk` (`% 8`) | 45 | 1.0 | | `apfTwo` | 12 | 0.4 |
| `maskOk` (`& 7`) | 44 | 1.0 | | `apfTwoBad` | 6.5 | 0.01 |
| `divBad` (`/ 3`) | 17 | 0.001 | | `above` (`∀∃`) | 27 | 0.8 |
| `divOk` (`/ 3`) | 11 | 0.4 | | `leastHyp` | 21 | 0.5 |
| `doubleBalance` | 25 | 0.5 | | `evenReadBad` | 6.5 | 3.2 |
| `nested` | 7.3 | 0.03 | | the 59 pinned, in all | 877 | 16 |
| `shlOk` (`<< 4`) | > 900 | 1.2 | | `netSwap` (four ledger reads) | not finished | 21 |
| `sortedLe` (two-variable block) | crashed the server | 146 | | | | |

`shlOk`, `netSwap` and `sortedLe` are pinned now (`proved`).  The walk's
states: `shrOk` 27,784, `netSwap` 187,347, `sortedLe` 121,586 (a formula
of about two thousand nodes, about a millisecond a state).  The
`Examples/Decision.lean` build went from about fifteen minutes to 192 s,
146 of them `sortedLe`.

The literal operators of feature 14 cost little: each of their fourteen
pins answers in under a second (`x & 6` is two atoms of halving, `x *% 3`
two wrapped sums); the file now builds in about 275 s.  Reads are another
matter: the `AFml` walk recurses once a bit read, so its depth is about
256 times the variables, and a leaf of fourteen reads at distinct keys
(fifteen variables, about 3,800 levels) overflows the interpreter's stack
where ten do not.  `gapManyReads` (fifty reads) is covered and answers by
the theorem, but its verdict is not computed; a walk with an explicit
stack would lift this.

### What is not proved

* `DecisionTheorem` itself; it is false today (above).
* `Fml.Covered ⊆ Fml.inTarget` on program-free leaves.  It holds of
  neither direction in general: `Fml.Covered` also takes formulas with
  programs, which `Fml.inTarget` excludes.  `Fml.Covered` is read on the
  eliminated leaf, `Fml.inTarget` on the source, and M4's "what blocks the
  rest" stands: normalization's budget, update pushing's
  `Tm.agreeB`/`Tm.toL`, elimination's invariant.
* The node bound of `Fml.exactBounded` (511 lifted nodes), which comes from
  the compilers' fuel (1024 deep, `CheckedValue.ofTermIn?`, and the
  `depth ≤ 1023` fields of `LFml.Arith`); the reads' bound is gone
  (feature 15).  No pinned leaf of the target exceeds it; lifting it means
  computing those fuels from the term as the reads' budget now is.
* A time bound for either decision.  `decideLeaf_complete` says it
  answers, not when.  The walks' fuel is not proved to suffice (above,
  "Running time"); the graphs stay exponential in the worst case: an
  `AFml` state is a formula and the variable read next, a bound `x < 2^256`
  costs 256 rounds of every variable, and a relation whose coefficients
  are large keeps many constants apart (a quotient by `d`, about `d`
  constants a bit read).  A `QFml` state still has `2^n` successors (`n`
  the free variables): `QFml.deriv` reads every free variable's bit at
  once.  `quantReduction?` also re-runs the front `dependentReduction?`
  refused.
* Ledger reads: each read is two codes and each pair of reads a
  consistency premise; reads at the same address are not merged.
  `netSwap` (four reads, ten variables) takes the longest of the pins.
* Array property instantiation has no size bound either: a block over `n`
  variables has `|U|ⁿ` instances, each read an occurrence of its own in
  the flattening (`sortedLe`, `∀ i j. i <= j → a[i] <= a[j]` against
  `a[2] <= a[5]`: nine instances, nineteen reads, a formula of about two
  thousand nodes, decided in about two minutes).  A refutation's rebuilt
  mapping is listed region by region (feature 20), at every floored level
  of a root, each region not holding the default a run of keys: a region
  between two far values of `U` whose word is not the default, or the
  two outer regions of an `int`-keyed mapping holding different words,
  give a refutation that exists, as a term, but cannot be built in
  practice.  No construction does better in general: a mapping lists its
  entries one key at a time with one default, and a sorted mapping
  (`∀ i j. i <= j → m[i] <= m[j]`) read at three far keys `a < b < c`
  with increasing words has, in every refuting state, the keys between
  `a` and `b` listed or those past `c`.
* `DecisionTheorem` fails on the leaves below, each in `Fml.inTarget`
  (by the kernel, `*_inTarget`) and answered *unknown*
  (`Examples/Decision.lean`, the pinned verdicts).  The search
  (2026-10-25) went through each construct `Fml.inTarget` admits and
  `decideGoal`'s stages refuse; one leaf stands for each shape:
  * **quantifiers over contents outside `apfPrep`'s shapes** (features 7,
    18 and 19; the bound key not the last, two depths, a member past the
    key, `bool` keys, halting guard operands and positive quantifiers are
    decided since 2026-10-26, features 16 to 19, and `int` keys and the
    ledger since features 20 and 21, their refutations of `2^255` keys or
    `2^256 - 6` addresses returned as terms no evaluation builds):
    * a block over a storage array (`gapArrayBlock`).  The quantified
      pipeline reads no array (the Theory's `has`/`orElse` reads are
      outside `LFml.Src false`), the arrays' (`arrayReduction?`) has no
      preparation stage.  It needs the block instantiated before the array
      cut, the index set taking each array's live length and slot count
      (a read below the slots reads the slot, past them the default), and
      each array rebuilt with slot `i` holding what slot `⌊i⌋` held, its
      length and slots kept, on top of `arrRealize`.  An array has no
      default inside its slots, so a refutation lists every slot up to its
      length, as feature 10's do;
    * a `||` whose left operand contains a `&&` with a halting right
      operand (`(k < 3 && k < x - 1) || k == 7 → …`; no `dl!` spelling,
      so no pin): `apfPrep` refuses it (feature 19), since the floor proof
      needs the left operand to return at the floors where it returned at
      the keys, and that `&&` need not (`false && ⊥` at the keys,
      `true && ⊥` at the floors).  Whether the instantiation is exact there
      is open;
  * **memory outside feature 13** (`Examples/DecisionMemory.lean`): a
    write in a leaf's update (`gapMemWrite`, `{memory := write(memory,
    s[0], 5)}`: the cut takes no update; it needs the reads past the write
    as `e == e' ? v : w` and the fresh objects apart in `MxRel`); an index
    bound after its array (`gapMemInner`, `∀ fresh s. … ∀ i. … s[i]`: the
    reads' atoms stand at the binder, and the object cannot be chosen
    before `i`); a hidden memory binder (`gapMemParam`: it ranges over the
    objects already in the heap, which may alias, and over none); a fresh
    struct's member (`gapMemStruct`: the cut takes arrays of primitives;
    a struct with reference members needs objects for them);
  * **the ledger and KeY `int` without quantifiers** (the plain
    storage-array reads once pinned here, `arrayRead` and `fixedRead`, are
    decided by feature 10, the fresh memory array's, `gapMemory`, by
    feature 13, and fifty reads, `gapManyReads`, by feature 15): a
    binder of KeY's `int` (`gapKIntBinder`, `∀ int z. z + 1 > z`): an atom
    position holds a `bool`, `uint` or `int` (`AEnv`), `LTm.var` and the
    binder `LFml.all k p` are sorted by `PrimTy`, so the leaf has no
    position of sort `Srt.kint` to bind.  It needs one (a field of `AEnv`
    and a `kint` variable of `LTm`, or an `allZ` binder of `LFml`, with
    every recursion over them extended, some forty modules), the prefix
    taking it as a parameter compiled as two unbounded natural codes (as
    the ledger entries are, `Inputs.AgreeZ`), and, past the prefix, an
    unbounded binder of `QFml` (no range atom; Presburger over ℤ as two
    naturals) (the ledger read past a payment once pinned here,
    `gapLedgerWrite`, is decided by feature 22);
  * **operators with a literal operand still outside**: `&`, `|`, `^` at
    `int` (`gapIntAnd`; two's complement, `toInt(toUint(x) & c')` would
    carry it) and `addmod` with a literal modulus (`gapAddmod`; its sum may
    pass `2^256`), both in the target since the waivers name two symbolic
    operands only;
  * **hashes outside `Fml.hashCovered`** (features 11 and 12):
    * three kinds of hash of one string (`gapThreeKinds`).  `Fml.tk` reads
      one second kind's words.  Applied twice it is sound (`Fml.tk_validH`
      composes) and its refutations chain, but completeness does not
      compose: `Fml.tkBody_fix_complete` relabels the second kind's words
      in a body with nothing between the prefix and the link, and past
      the first layer the third kind's words sit under the second's
      binders, link and fixing hypotheses.  It needs that relabeling
      restated under a prefix of earlier extra words, or `Fml.tk` over a
      list of kinds (a link and a relabeling per kind; their keyed roots
      are disjoint by the key-kind check);
    * two kinds where some string hashed by the second kind has no hash of
      the first at the top (`gapMixedKinds`, `ids[keccak256(s)] == 1 →
      shas[sha256(t)] == 1`: in either order the second kind's string has
      no word of the first kind to link with).  Giving such a string's
      extra word no link (or a link through a class word `linkChoice`
      picks) stays sound; completeness then needs the swap's classes,
      read off the first kind's words (`classesOf`), to follow that extra
      word, whose string's first-kind word is read nowhere: the countermodel
      must first be moved (that word set to its extra word's class) inside
      `Fml.swPrefix_complete`'s relabeling, which is not proved;
    * a hash of written memory (`gapWrittenMemory`, `∀ s t. [ s[0] = 1; ]
      keccak256(s) == keccak256(t)`): the verdict turns on the strings'
      bytes past the write; feature 13 reads fresh arrays' elements, but
      takes no memory write in an update and no hash (`decideMem` is
      `decideLeaf`'s, not `decideHash`'s);
    * a hash under a negative-position value quantifier whose hash pairs
      the scope above does not read (`gapHashNegForall`, the statement's
      exception above): false only at collisions, which no refutation can
      exhibit; deciding it is impossible, excluding it narrows
      `Fml.inTarget` (the user's call).
  Not counterexamples, since `Fml.inTarget` excludes them: a hash stored
  in a local, a hash of a hidden binder's string or under an anonymising
  update, a hash key of anything but a memory local, a product of two
  symbolic terms and the waived operator classes, nested blocks under a
  negative quantifier, a strict comparison of two bound variables, two
  bound indices on one path.
* Array reads outside feature 10: arrays below a field or a mapping
  key, of structs or of arrays (`a[i][j]`), an index that reads an array
  (`a[a[0]]`), a read of the whole array (`delete a`, a copy), a leaf with
  more than `orBudget` fallbacks (Theory reads after writes); blocks over
  arrays (`gapArrayBlock`: the array property fragment over arrays needs
  the lengths in the index set).
* A time bound with arrays: each read is up to two variables of the
  arithmetic, whose search grows with their number; a counterassignment
  the shrinking leaves with a length near `2^256` is out of reach to
  realize in practice.

### The plan for the rest

One feature a round, each with its completeness proof through the stages,
in this order:

1. **Unary `-` and the conversions** (`toInt`, `toUint` at a literal
   range), like the literal product (`CheckedScalar` codes).  Done
   (2026-10-25): `-` and `~` as codes, the conversions as cut atoms (above).
2. **Literal division, modulo, shifts, masks, wrapping `+%`/`-%`/`*%`**: a
   fresh atom per quotient with its defining constraints in the antecedent
   (`q·c ≤ x < q·c + c`), exact in a universal reading. The compiler then
   returns constraints beside the code.  Done for `/`, `%`, `>>`, `<<`,
   low masks, `+%`, `-%` (above), the constraints a stage of their own
   ahead of the compiler (`LFml.cutAll`), the compiler encoding each
   definition.  Done too (2026-10-25, feature 14): `*%`, `|`, `^`, any
   mask, `**` at `0` and `1`, `int` `/` and `%`, written through the others.
   Not done: `&`, `|`, `^` at `int`, `addmod` with a literal modulus.
3. **KeY `int`**: an atom sort in `LTm` and `AEnv`, encoded as the
   difference of two natural codes in `AFml`.  Done (2026-10-25) for the
   linear operations, `toInt` and the comparisons (feature 8), and for
   reads of the starting ledger as atoms (feature 9).  Left: a binder of
   KeY's `int`, which needs an unbounded binder in `LFml` and its
   prefix.  Ledger reads past ledger writes are done (feature 22).
4. **Quantifiers in the arithmetic** (done, 2026-10-25): `QFml`, decided
   by projection in the binary-derivative automaton (`QFml.decide_iff`),
   and negative-position Presburger quantifiers and alternation over value
   locals (feature 3); a quantifier body reading storage at no bound
   variable, the read hoisted to a fresh atom with its defining equation
   (feature 6, done 2026-10-25).
5. **The array property fragment** (done for mappings at roots,
   2026-10-25, feature 7): a negative `∀` block instantiated at the index
   set (the goal's index terms and the guards' bounds, Bradley–Manna–
   Sipma), the instance decided by the quantifier-free pipeline; the
   instantiation proved exact on the fragment (`apfPrep_valid_iff`).
   Inner mappings at their last key done (2026-10-25: the floor
   construction over the inner mapping of every outer key).  Done
   (2026-10-26, features 16 to 19): every `uint` key along a root's
   mappings floored, the value under it copied (a bound key not the last,
   two depths, members past it), `bool` blocks expanded, guards with
   halting ground operands (except under a `&&` in a `||`'s left
   operand), positive
   quantifiers past the prefix dropped to fresh atoms.  Done (2026-10-26,
   features 20 and 21): `int`-keyed mappings, refutations listed region by
   region (those of `2^255` keys terms no evaluation builds), and the
   ledger, `apfPrep` inside the ledger's pipeline (`ledgerBlockReduction?`).
   Left: arrays (`gapArrayBlock`: lengths and slot counts in
   the index set, `apfPrep` inside `arrayReduction?`), memory, a `||`
   whose left operand may halt.
6. **Memory, array indices**: array indices done (2026-10-25, feature 10)
   for arrays of primitives at roots: update pushing made exact for the
   Theory's reads (`Tm.toLT`), and instead of in-range evidence through
   the path guards, read queries and `Calculus/ReadRealization.lean`, the
   array reads cut to atoms before those stages, with the arrays rebuilt
   from the atoms (`Calculus/ArrayCut.lean`).  Left: arrays below fields
   and keys, of structs and arrays, blocks over arrays.  Memory done
   (2026-10-25, feature 13) for fresh arrays of primitives read at indices
   named before them, the reads cut to atoms at the binder (Ackermann),
   exact at every state; refused at elimination still (`LTm.Elimable`), the
   cut runs on the source formula, ahead of the pipelines, so no stage
   realizes a heap: the refuting state is the cut leaf's.  Left: memory
   writes and allocations in a leaf's updates (`{memory := write(…)}`,
   `addM`, copies from storage: the cut takes no update), struct members
   and nested arrays of a fresh object, an index bound after its array
   (`allocAll s. ∀ i. … s[i]`), hidden memory binders, an index that reads
   memory or storage (in the fragment: `gapMemWrite`, `gapMemInner`,
   `gapMemParam`, `gapMemStruct`).  Programs with memory statements are
   refused earlier still: `ProgramNormalization` takes value statements
   only (`ExactStatement.ofStatement?`).
7. **Hashes under the premise**: a hash–hash equation as its inputs'
   equality (length and elementwise words, a bounded `∀` as in step 5), a hash key
   as its input's word list.  Done (2026-10-25) for fresh strings read only
   by hashes of one kind (feature 11): no stage reads memory, so the
   inputs are free, and their equality is the hashes' (the swap); the
   bounded `∀` over words is needed only once memory reads are, at step 6.
   Two kinds per string done (2026-10-25, feature 12), the second kind's
   hashes past updates and value locals set in the body since; any
   number of strings (the family computed past four) and positive value
   quantifiers in the body done (2026-10-25).  Left, in the fragment:
   three kinds (`gapThreeKinds`), two kinds where a string of the second
   has no hash of the first at the top (`gapMixedKinds`), hashes of
   written memory (`gapWrittenMemory`: in the fragment, not outside it as
   this step said before; it waits for memory writes and hashes of memory
   read, step 6), and a negative quantifier over unread hash pairs
   (`gapHashNegForall`: not decidable, the user's call).  Outside it:
   stored hashes, strings not fresh.
8. **`Fml.Covered ⊆ Fml.inTarget` on program-free leaves**: characterize
   normalization and update pushing syntactically (M4's list), then lift
   the size bounds by fuel computed from the formula.  Done for the reads
   (feature 15, `readBudget`); the 511-node bound (the compilers' fuel) is
   left.

**Review (2026-10-25).** A read-only review found nine issues, fixed here.
* Guards: `!=` written another way, and arithmetic on the bound variables,
  passed.  Guards are now comparisons of index terms.
* Hash keys of two kinds at one root passed.  Keys now record their kind.
* The premise compared words where the hash reads bytes.
* `ecrecover` was inside the premise.
* The premise ranged over every value of every binder, so a leaf with a
  binder over byte strings held vacuously by pigeonhole.  It is now taken
  per scope.
* `wt`/`cleanTail` were not counted as reads.
* The docs overclaimed the inclusion `Fml.Covered ⊆ Fml.inTarget` (it
  fails on programs), the truth of `DecisionTheorem` (it is the goal, not
  true today) and the kernel-checked coverage.

The concern left open, nested mappings `m[i][j]` at two bound indices,
is settled by narrowing the target (2026-10-25), not by a proof:
`Tm.apfV` admits at most one bound index along a path, the arrays of one
dimension Bradley, Manna and Sipma state their result for
(`Examples/Decision.lean`, `gridApf`, outside), so `DecisionTheorem` says
less there than it did.
The floor construction would extend to it (a mapping at `(i, j)` holding
what `(⌊i⌋, ⌊j⌋)` held), but it is not proved here.  The same round found
the guards too wide: a strict comparison of two bound variables (`i < j`,
`i + 1 ≤ j`) is arithmetic on them, outside their fragment as stated, and
the floor does not preserve it (two keys between consecutive index values
share their floor); `Tm.apfG` now refuses it (`strictSorted`, outside).
A hash key reached through an alias or `atIn` is outside the fragment (its
position is not admitted), so the key-kind check need not see it.

**Step 7 (2026-10-25)** found `Fml.inTarget` a superset of the named
fragment at hash keys: a hidden memory binder (`Fml.bind`) or an
anonymising update ranges over an unset reference, whose hash reads
nothing, and a key of nothing reads the default key `0`; so
`ids[keccak256(s)]` with `s` unset reads `ids[0]`, and a verdict turns on
whether another string hashes to `0`, a preimage question
(`namesBound`).  The same holds of a hash of a memory a failing write
leaves (`write(memory, a, v)` at an address past a string's end returns
nothing).  `Fml.inTarget` now admits no hash under either binder, and a
hash key only of a memory local in the starting memory
(`Tm.hashOfLocal`).  Fresh strings (`Fml.allocAll`) are always set.  The
review found no other source of an undefined hash key: an update setting
a memory local to nothing does not land, and an equation of two hashes
compares their readings as options, reading no default.

## M8 · Polynomial size (2026-10-25)

The theorem of M6, measured where it is not yet true: symbolic execution
takes a number of steps, and produces formulas, of size polynomial in the
program and specification text.  `Examples/Tactics/PolySize.lean` pins
three families for small `k` by `#proof_size` (a command of that file:
`#proof_tree`'s nodes and branches, its open goals, and its largest leaf,
the leaf's sequent as `sol_leaf` reads it, `⊨ᶠ ψ`, in term nodes,
`Fml.tmSize`, M5):

* **F1, sequential `if`s that both assign**:
  `⟨ uint x = 0; if (a == 1) { x = x + 1; } else { x = 0; }; …; ⟩ x <= k`,
  the `i`-th `else` setting `x = i - 1`, each `if` reading the `x` the one
  before wrote;
* **F2, literal-bounded loops by their invariants**: `k` loops
  `/// @custom:key invariant i <= 10 && s == 10 * (j - 1) + i`
  `for (uint i = 0; i < 10; i++) { s = s + 1; }` in sequence, then
  `s == 10 * k`, under the box;
* **F3, both**: one such loop whose body is `k` sequential `if`s,
  `if (cⱼ == 1) { s = s + 1; } else { s = 0; }`, its invariant
  `i <= 10 && s <= k * i`, then `s <= 10 * k`.

Three steps follow it: **A1** joins every `if` whose branches only assign
locals, **A2** proves literal-bounded loops by their invariants only,
**A3** bounds the recursion depth the counterexample certificates need.

### Baseline (master `c7e634f`)

Measured on the cloud container (4 cores, 15 GB, one Lean process), a
scratch module per family, `#proof_size` with the time it took to build the
tree, leaves closed by `sol_leaf; sol_close` as `#proof_tree` closes them;
`maxHeartbeats 2000000` a command so the larger `k` finish (the pins use
the default):

| k | F1 nodes | branches | leaf | time | F2 nodes | branches | leaf | time | F3 nodes | branches | leaf | time |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | 11 | 2 | 27 | 0.9 s | 10 | 3 | 49 | 2.1 s | 18 | 4 | 66 | 6.8 s |
| 2 | 26 | 4 | 45 | 2.1 s | 17 | 5 | 78 | 8.2 s | 35 | 6 | 84 | 42.6 s |
| 3 | 55 | 8 | 63 | 5.3 s | 24 | 7 | 105 | 20.2 s | past 2 M heartbeats | | | |
| 4 | 112 | 16 | 81 | 14.4 s | 31 | 9 | 132 | 42.7 s | past 2 M | | | |
| 5 | 225 | 32 | 99 | 35.7 s | 38 | 11 | 159 | 81.4 s | past 2 M | | | |
| 6 | 450 | 64 | 117 | 89.3 s | 45 | 13 | 186 | 145.5 s | past 2 M | | | |

What it shows:

* **F1 is exponential in the walk**: `ifElseSplit` copies the rest of the
  program into both goals, `2^k` branches and `7 · 2^k + k − 4` nodes; each
  leaf is linear (`18k + 9` term nodes).  Under the default heartbeats the
  tree is built up to `k = 4` (`k = 5` runs past 200 000).  The join
  (`ifElseJoin`) does not fire: its gate (`Upd.ifJoin?`) takes only an
  `if` with one branch empty and the other an accumulation (A1 below).
* **F2's walk is linear** (`7k + 3` nodes, `2k + 1` branches, a leaf
  about 27 term nodes larger a loop): an annotated loop is closed by its invariant rule
  (`whileInvariantBox`), whatever its bound (`docs/loops.md`, decision 3),
  so the bound's value never enters the walk.  The time is not linear
  (about cubic in `k`: the ratio of successive times falls to `1.8` at
  `k = 6`, where `(6/5)^3` is `1.73`): the leaves past the `j`-th loop read `j` anonymised
  frames, and the closer's cost per leaf grows with them.  Under the
  default heartbeats `k = 3` leaves one goal open (the whole command shares
  one budget); with 2 M every leaf closes.
* **F3 is exponential inside the loop**: the body's `k` `if`s split as F1's
  do, `2^k` preservation goals, each closed past the invariant's `{anon}`;
  `k = 3` is past 2 M heartbeats.
* An unannotated literal-bounded loop is unwound (`.auto`,
  `whileUnwind`), so its walk grows with the bound's value, not with the
  text; none of the three families has one (A2 below).

### A1 · Joins for every `if` whose branches only assign locals

**The gate** (`Upd.ifJoin?`, `Calculus/Arms.lean`): an `if` on a simple
condition is joined (`LeanTaclet.ifElseJoin`) when each branch is empty or
one assignment of a value local (`Prog.joinArm?`), whichever local and
whatever value; `if (c) { x = 2; } else { x = 1; }` is
`{ x := c ? 2 : 1 }`, `if (c) { s0 = 1; } else { s1 = 1; }` the two
elements `{ s0 := c ? 1 : s0 ‖ s1 := c ? s1 : 1 }`.  The arm and its
soundness are unchanged (`Upd.ifJoin`, `sound_iteJoin` held for every
joinable pair already); `JoinArm.accumulates` and `Tm.readsPos` are gone.
A branch of two statements, or one that writes the state, calls, reverts
or declares, still splits.

**The closer side.**  Where the earlier attempt broke (above, "The join"),
the closer now gets the two cases back at the leaf:

* `sol_close_ite_split` (`CloseSplit`, `Calculus/CloseScoped/Steps.lean`;
  the lemmas in `Calculus/LeafSplit.lean`): KeY's `ifthenelse_split` on a
  joined value whose condition is a `bool` local and which is not an
  accumulation, `{x := c ? t : e} φ` from `c = TRUE → {x := t} φ` and
  `c = FALSE → {x := e} φ` (`Fml.SplitTo.here`), through the binders,
  updates, premises and conjunctions in front of it; every value of the
  update at that condition takes its side at once (`Upd.IteCase`).  The
  cases are the leaves `ifElseSplit` left, so they cost what they cost.
  `sol_close` takes it first on a leaf of one or two such updates
  (`CloseSplit.splitFew`); from three, after `sol_close_join_steps`, at
  most `CloseSplit.splitMax` (six); each within `sol_within 160000`.
* `sol_close_join_steps` reads a value whose cases are one base with
  offsets and literals (`c ? x + 1 : 0`): the absolute interval from the
  base's (`CloseJ.addInterval`), so F1's leaf is one update at a time.
* The walk's kernel closer (`LFml.decideLift`,
  `Calculus/DecideComplete.lean`), after `liftCond`, lifts the first
  conditional to the formula's top (`LFml.liftTop`, `LFml.findCond`,
  `Calculus/CondLift.lean`, exact by `LFml.liftTop_holds`): `x != 0` after
  `{x := c ? 2 : 1}` is `(c → ¬ 2 = 0) ∧ (¬c → ¬ 1 = 0)`, where the
  equation's own lift left `¬ ((c → …) ∧ (¬c → …))`, which it did not
  close.  Without it `sol_prove` left a leaf on
  `[ if (a == 1) { x = 2; } else { x = 1; }; ] x != 0` (`Join.lean`), which
  it closed when the `if` split.

**The solkey fragment** (`⊢ₖ`, `Stmt.inSolkey`) loses every `if` of the
wider shape and every conditional value (`Val.keyValue` is `false` on
`.ternary`): `ternaryToIf` lowers `v = c ? a : b;` to an `if` the strategy
joins, and a conditional anywhere in a value reaches a local through the
captures.  On those `⊢ₖ` stops where `⊢` goes on; as with the
accumulations' join and the summaries, the fragment is what solkey's
taclets alone run, now smaller.

**Pins that moved, each because the walk shrank** (the program unchanged
unless said):

* `Examples/Tactics/PolySize.lean`: F1 `8`, `13`, `18` nodes and one
  branch (`5k + 3`) where it was `11`, `26`, `55` and `2^k`; F3 `14` nodes
  and three branches where it was `18` and four.
* `Examples/Tactics/ProofTree.lean` (the `cdl!` trees): `ifElseJoin` in
  place of `ifElseSplit` and its two goals, the `#proof_node` of the leaf
  at serial 2.
* `Examples/ProofTree.lean`: the label pins (`#proof_node 2`,
  `#proof_tree_json`, the `a == 1` tree) are about `ifElseSplit`'s labels,
  so their `else` branch now reverts (the program changed, to keep the
  split); `sol_derive?`'s suggestion is `apply update .ifElseJoin`.
* `Examples/Tactics/Branch.lean`: `branchLocals` and `branchDiamond` walk
  `ifElseJoin` (one goal, its trace pinned).
* `Examples/Tactics/Sequents.lean`: the split walk's `else` branch writes
  the storage (the program changed, to keep its checked lines).
* `Examples/ChainNotation.lean`: section 5's `else` writes the storage and
  the nested example's inner `else` too (to keep the split), the nested
  derivation pin follows; `ifTrace` ends before the join, whose line the
  surface notation cannot write (below).
* `Examples/Chains/StorageCoverage.lean`: the rows `ifElseUnfold` and
  `ifElseSplit` give their `else` a second assignment, `s0 = 0;`, so they
  split as the paper's table prints them; the paper's own programs
  (`if (ok) { s0 = 1; } else { s1 = 1; }`) now join.
* `Calculus/CloseTests.lean`: the walk on `if (a == b) { x = 2; } else
  { x = 1; }` takes `ifElseJoin`; a split example writes the storage; the
  split itself is pinned (`sol_close_ite_split`, its two cases).
* `TestSuite/Derived5.lean`, `boolKeyMappingSymbolicKey`: one leaf
  (`{ ie1 := b ? 1 : 0 }` read as a mapping key) that the walk's kernel
  closer does not close, by `sol_leaf; sol_close`, where the split's two
  goals each closed in the walk.  `TestSuite/Derived15.lean`,
  `invariantVariantSkipsBreakIteration`: three leaves where it had four
  (`case leaf4` dropped).  The gate's counts are unchanged: 491 automatic,
  61 with a step budget, 0 manual, 11 refuted, 0 pending.

**After A1** (the same scratch modules, `maxHeartbeats 2000000` a command):

| k | F1 nodes | branches | leaf | time | F2 time | F3 nodes | branches | leaf | time |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 8 | 1 | 25 | 0.6 s | 2.0 s | 14 | 3 | 64 | 6.6 s |
| 2 | 13 | 1 | 41 | 1.3 s | 8.8 s | 19 | 3 | 80 | 41.5 s |
| 3 | 18 | 1 | 57 | 1.4 s | 20.2 s | past 2 M heartbeats | | | |
| 4 | 23 | 1 | 73 | 1.7 s | 44.0 s | past 2 M | | | |
| 5 | 28 | 1 | 89 | 2.3 s | 85.1 s | past 2 M | | | |
| 6 | 33 | 1 | 105 | 2.9 s | 148.4 s | past 2 M | | | |
| 7 | 38 | 1 | 121 | 3.3 s | | | | | |
| 8 | 43 | 1 | 137 | 4.0 s | | | | | |

F2's walk and leaves are as before (no `if`).  F1 is linear in the walk
(`5k + 3` nodes) and the leaf (`16k + 9` term nodes), and about linear in
time; with the split alone in front of the steps it was `0.56`, `1.4`,
`3.5`, `8.5`, `21.9`, `53.2` s at `k = 1 … 6` (the leaf's `2^k` cases).
F3's walk is linear (three branches whatever `k`); its body's preservation
leaf, past `{anon}`, costs what the split cases cost before: open.

**Speed.**  `git log` shows no earlier change on the gate made for speed;
the gate was narrowed for the closers (above), which A1 addresses.  The
TestSuite modules took 1023 s after against 1045 s before (`Derived5`
10 → 15 s, its leaf by `sol_close`; `Derived17` 181 → 171 s; no other
module moved by more than 5 s); the library's examples are not slower as a
whole (`Examples/Tactics/OpenLoops.lean`, the slowest, 624 s before, 600 s
after).  May slow checking: `sol_close` on a leaf with joined values now
tries the split first, and the walk's kernel closer evaluates `liftTop` on
a leaf `liftCond` did not close.

**What is left.**  A branch of more than one local assignment still splits
(a join needs the branch's assignments composed, `x = a; y = x + 1;`);
the surface notation (`dl!`, `Calculus/Notation.lean`, the `callee` lane's)
cannot write a conditional term, so a chain cannot show a joined line;
F3's invariant leaves.

### A1 review (2026-10-25)

A read-only finder and skeptic (neither ran Lean).  Confirmed and fixed:
`sol_close_ite_split` could succeed without taking anything apart (an
update `count` counts but whose `pushFree` fails), and `sol_close` would
then enter it again on the same goal until the recursion depth, which
`first` does not catch: it now fails there; the split alternatives ran
with no budget of their own, so a split case that ran out of heartbeats
ended `sol_close` instead of falling through: each is now within
`sol_within 160000`; nothing pinned that the split fires: `CloseTests`
pins its two cases.  Minor, reworded: `splitMax` counts updates, not
conditions; `liftTop` lifts below the leading binders only; the solkey
fragment's banner names conditional values.  Rejected by the skeptic: an
unreduced leaf (`sol_leaf` quotes it), the `decideLift` example (its
guard is a total local, two cases), and the kernel's cost on failing
leaves (the compiled closer finds them first).  Left as minor: the
`affine` reader misses `Int.negSucc` literals (the interval step then
records nothing), and the docstrings of the split's congruence lemmas
carry no Solidity.

### A3 · The recursion depth of two kernel checks

* `certifyLong` (`Tools/Counterexample.lean`) raised `maxRecDepth` to
  100 000, which can crash a worker: the elaborator's `apply` of
  `Fml.not_holds_imp_of_eval3` unified `holds σ' (pre → body)` with the
  peeled obligation, unfolding the whole formula, and on the TestSuite's
  `invariantClosedFormSum` passed the default depth (512) at that step
  (a scratch copy without the override failed there for every long-array
  candidate).  The certificate is now built with its arguments written:
  the peeled state and formula read by the kernel (`kernelWhnf?`, a
  `Kernel.whnf`, which reads no `maxRecDepth`: it is bounded by the stack,
  and by no heartbeats, a weak-head reduction down the parameters'
  binders), the premise checked to be
  `wt(storage)` on that small term, and the rest, `¬ holds (peel …)`
  against the term built, left to the kernel's check of the declaration,
  as before.  No override is left; `invariantClosedFormSum` is refuted as
  before (`TestSuite/Refuted.lean`, 10 s before, 9.5 s after), and so are
  `Examples/Tactics/SymbolicCounterexample.lean`'s.
* `Evm/Examples.lean`'s `pow_run` set `maxRecDepth 100000` for one
  `decide +kernel` on a conjunction of four runs; each conjunct is decided
  on its own now (`refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel`) at the
  default depth, the statement unchanged (31 s before, 30 s after).

Neither needed the chunking `Calculus/ProveChunked.lean` does for walks:
the depth was the elaborator's on one term, not a long derivation.  The only
`maxRecDepth` settings left under `Solidity/` are `ProveChunked`'s and
`Derive`'s per-step contexts and the generated `Corpus/TestSuite.lean`'s
575.

### A3 review (2026-10-25)

A read-only finder and skeptic (neither ran Lean).  No correctness
finding: the explicit arguments match the declarations, the peeled
`Sigma.mk`/`Prod.mk`/`Fml.imp` are built literally by `Fml.peel`'s minor
premises, and a shape test that stopped matching would fail
`TestSuite/Refuted.lean` and `SymbolicCounterexample.lean`, which call
`sol_refute` on long arrays.  Confirmed and fixed (wording):
`Kernel.whnf` reads no `maxRecDepth` but is bounded by the stack, not by
heartbeats; `pow_run`'s depth was the elaborator's, not the unifier's;
this section's place and a bullet's indent.  Minor, left: `certifyLong`
reads `Γ` off the formula's type, always `[]`.

### A0 review (2026-10-25)

A read-only finder and skeptic (neither ran Lean) over the baseline.
Confirmed and fixed: the cubic check compared `t₆/t₅` with `(7/6)^3`
instead of `(6/5)^3`; the families' Solidity lacked `*`; PolySize's
docstring wrote the `else` value as `x = i - 1`, a local of that name; the
A-milestone tags were undefined; `#proof_size` answered `0` for a leaf
`sol_leaf` did not take apart, which now fails instead.  F1's nodes are
stated exactly (`7 · 2^k + k − 4`).  Left as minor: the command is global
(`Solidity.lean` imports the example), the pins add about 25 s to the
default build, and the leaf mvar is made outside the leaf's context (the
tree's sequents are closed, so it reads the same).

### What is left (2026-10-25)

To pick up later, in order of what the theorem needs:

1. **A2 · Literal-bounded loops by their invariants only** (not started:
   it waits for the frames branch, `claude/festive-johnson-nar57p`, the
   narrowed anonymisation of loop frames, to land on master).  An
   annotated loop is already closed by its invariant whatever its bound
   (`docs/loops.md`, decision 3; F2's walk is `7k + 3` nodes).  What is
   left is the unannotated loop (`.auto`, `whileUnwind`), whose walk grows
   with the bound's value: report it (a warning naming the loop) rather
   than unroll it silently, keep unrolling as an opt-in option in
   `docs/options.md` if the TestSuite needs it and list the obligations
   that do, then re-measure `Examples/Tactics/PolySize.lean`.
2. **The cost of a loop's leaves past `{anon}`.**  F2's time is about
   cubic in the loops in sequence (`145 s` at `k = 6`) although its walk
   and leaves are linear, and F3 (a loop whose body has `k` joined `if`s)
   is past 2 M heartbeats from `k = 3`: the closer on an invariant's
   preservation and exit leaves (`sol_close_saturate`, the anonymised
   frames) grows with what each leaf reads.  Measure one leaf in a
   scratch module before changing anything.
3. **Branches of more than one assignment.**  `Prog.joinArm?` takes one
   value-local assignment a branch, so `if (c) { x = a; y = x + 1; }`
   still splits.  Joining it needs the branch's assignments composed
   without substituting terms into each other (a sequence of updates, or a
   premise that is an update followed by the rest of the `if`), so that
   the update stays linear in the branch.
4. **A conditional term in the surface notation.**  `dl!` has no spelling
   for `c ? a : b` in an update (`Calculus/Notation.lean`, the `callee`
   lane's when A1 landed), so a chain cannot write a joined line.  Once it
   can: restore the paper's programs in
   `Examples/Chains/StorageCoverage.lean` (the `ifElseUnfold` and
   `ifElseSplit` rows now give their `else` a second assignment), add an
   `ifElseJoin` row, and finish `Examples/ChainNotation.lean`'s `ifTrace`
   past the join.
5. **The walk's kernel closer on a joined mapping key.**
   `boolKeyMappingSymbolicKey` (`TestSuite/Derived5.lean`) needs
   `sol_leaf; sol_close` for `{ ie1 := (b ? 1 : 0) }` read as a key: the
   lift (`LFml.liftCond`, `LFml.liftTop`) counts more than `liftConds`
   conditionals once the key's elimination copies them.  A case split on
   a Boolean atom with the atom substituted (KeY's `ifthenelse_split` and
   `applyEq` together) would close it in the walk.
6. **Joined values the steps cannot bound.**  `sol_close_join_steps`
   reads cases that are one base plus offsets, or that and literals; a
   value whose cases are two bases (`c ? y : z`) gets no interval, and
   past `CloseSplit.splitMax` (six) such updates nothing splits them.
7. **The solkey fragment.**  `⊢ₖ` no longer runs a conditional value
   assigned to a local nor an `if` whose branches only assign locals
   (A1).  If solkey-only derivations of those matter, the fragment needs
   a way to reach `ifElseSplit` on them, which the one-rule-per-statement
   strategy does not have today.
8. **Small items from the reviews.**  `CloseJ.affine` does not read
   `Int.negSucc` literals; the split's congruence lemmas
   (`Fml.SplitTo.valid`, `andL`, `andR`) carry no Solidity in their
   docstrings; `#proof_size` is declared globally by an example file
   (move it to `Tools/ProofTree.lean` with a pin in
   `Examples/ProofTree.lean`); `certifyLong` reads `Γ` off the formula's
   type, always `[]`.
9. **Failures that predate M8.**  `./run-lean.sh` ends with solkeycheck's
   `localValueDelete` drift (an unannotated read), and
   `./scripts/check-doc-paths.sh` with 13 vendor and doc paths to files
   that do not exist.

## Review (2026-10-20)

A read-only review pass (finder and skeptic per area) confirmed six
findings; each is fixed.

1. **G0 breach.** `Fml.isCTPrem` and `Fml.assumesCT`
   (`Calculus/DecideCleanTail.lean`) took the context-indexed `Fml C Γ`
   apart by `match` inside `Seq.checkCore`, which the kernel evaluates.
   Now by `Fml.casesOn` with structural recursion, each with a compiled
   `match` twin (`Fml.isCTPremM`, `Fml.assumesCTM`, `implemented_by`) and
   a link theorem (`Fml.isCTPrem_eq_isCTPremM`,
   `Fml.assumesCT_eq_assumesCTM`); `isCTPrem_holds`/`assumesCT_holds` are
   proved through the twins.
2. **Exponential lift before refusal.** `dependentReduction?` lifted every
   leaf whole before the flattener's size check.  It now runs
   `LFml.liftCondB condLiftFuel liftBudget` first, which stops as soon as
   the lift exceeds `liftBudget` (1023 + 2048 nodes), and refuses there
   (`Calculus/DependentReduction.lean`; `LFml.liftCondB_eq`: it is the lift
   where the lift fits).  `LFml.liftCondB_isSome` (`Calculus/AutoComplete.lean`,
   via `LTm.fits_eq_fitsCap`, `LFml.fits_eq_fitsCap`,
   `LFml.nodes_stripAll`) shows it accepts every leaf in `Fml.exactBounded`,
   so `dependentReduction?_isSome` and `auto_complete` keep their
   hypotheses.
3. **Monotonicity under the clean-tail premise.** `checkCore` offered a leaf
   with the premise only `decideMemCT`; it now tries
   `decideMemCT || decideMem` (`Seq.checkCore_valid` updated, O6 in
   `docs/options.md` reworded).
4. **Unpinned claims in M4.** "Unchanged by `condSimp`/`liftCond`" is now
   `LFml.liftCond_condSimp_of_conds` (`Calculus/LiftTotality.lean`), on
   leaves with no conditional; the coverage observation over
   `ProgramReduction`/`ParameterReduction`/`CheckedLinear` is marked as
   unpinned; "every example still checks" became the list of examples the
   build checks.
5. **Panic pattern.** `Walk.valSubterms` (`Calculus/RewriteSyntax.lean`)
   and `Tm.toNilQ?` (`Calculus/SeqRewrite.lean`) tested
   `ty.isAppOfArity ``Tm 3 && (← whnf (ty.getArg! 2))…`, whose `(← …)`
   `do` lifts ahead of the test; the tests are nested now.  The other
   `&& (← …)`/`|| (← …)` sites were checked: none reads an argument its
   left side guards.
6. **Nits.** `Calculus/PrintStmt.lean` drops the redundant
   `&& value.isApp` after `isAppOf ``Simple.local``, and its comment now
   names the tests it explains; M5's claim narrowed to what `Stmt.step_tmSize_le` covers (a
   premise's updates and formulas); the punctuation of the
   `Semantics/StorageWt.lean` and `Typing/Values.lean` rows of
   `docs/module-map.md`.
