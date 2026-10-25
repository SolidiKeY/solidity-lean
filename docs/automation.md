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

### (b) Fixed arrays at literal indices: not done

Not cheap: the path guards refuse `.atF` (`TSegs.guardFuel?`), `ReadExpr`
has no fixed-array index, and the realization layer that turns an
alias-consistent assignment into an actual storage
(`Calculus/ReadRealization.lean`, `Ref.Declared`) covers root, field and
mapping-key paths only.  Each needs a case; the realization one needs
in-range evidence.  Dynamic arrays are out, as planned.

### (c) The fragment

On terms (`LTm.Src c k`, `Calculus/FlattenTotality.lean`), by kind:

* scalars (`num`): atoms, literals, transaction fields, `+`/`-` (checked),
  `seq` guards, `err`, and storage reads `obsW` of a path;
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
`Fml.exactBounded φ` bounds the lifted body: at most 511 nodes and at most
45 storage reads (`words² ≤ 2048`).  The bounds come from the stages' fuel:
the flattener's 2048-node budget, the compilers' 1024-deep fuel (a
flattened term has at most twice its source's nodes), the 2048 alias-pair
budget.  They are unavoidable in this form: elimination and lifting can be
exponential.

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
  (`n` sequential `if`s give `2^n` leaves), a call carries its callee's
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
  `wt(storage) → ψ` directly (`certifyLong`; the kernel check is bounded
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

The gate (`Upd.ifJoin?`): one branch empty, the other empty or an
accumulation, a local set from its own value (`JoinArm.accumulates`:
`x = x + 1;`).  Joining every joinable `if` was tried first and broke the
leaves of `if (c) { x = 2; } else { x = 1; }` (`CloseTests`'
`whichWriteWins`), of conditional values (`ternaryToIf`: `Bytes`,
`SignedCasts`, tuple returns) and of lowered `break`/`continue` flags
inside invariant loops (`Loops`' `breakKeepsBound`, `LoopsImport`'s
`invariantBreak`): their two cases are cheaper for the closers than the
conditional term, so they split as before.  An accumulation's split copies
the rest of the program once per case of every `if` before it, which is
what the join removes.  The solkey fragment (`Stmt.inSolkey`) leaves out
every `if` of the joined shape (`Prog.joinShape`).

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
Making that polynomial too needs the bodies named once per function (a
call carrying its callee by name and a table of summaries proved once per
function), a change to the syntax, not to the calculus.

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
