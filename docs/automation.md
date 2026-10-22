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
