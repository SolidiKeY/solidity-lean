# Automation

## M4: completeness of the automatic decision on a stated fragment

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
`LFml.liftCond_holds` in the transport.  Every formula the pipeline accepted
before is unchanged by them (it had no `kite`/`ite` in an equation, since the
compiler refused those), and every existing example still checks.

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
    ∃ r, dependentReduction? φ = some r ∧ (Valid φ ↔ r.arithmetic.guarded.decide = true)

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

Coverage: every formula of `Examples/ProgramReduction.lean`,
`Examples/ParameterReduction.lean` and `Examples/CheckedLinear.lean` is in
`Fml.inExact` exactly when `dependentReduction?` accepts it; the
exceptions are the formulas with declaration premises, which the tools
remove first (`DeclarationReduction.dependent?`).

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

To prove totality the recognizers' helpers became public: `flattenFuel?`,
`flattenFormulaFuel?` (`Calculus/FlattenReads.lean`), `SPath.viewFuel?`,
`TSegs.guardFuel?`, the `CheckedValue`/`BooleanValue` fuels, `scalar?`,
`Result`, `StorageEncoding.equality?` (`Calculus/CheckedLinear.lean`) and
`ReadOccurrence.conjunction` (`Calculus/ActiveReadConstraints.lean`).
