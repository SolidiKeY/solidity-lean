# VA1 routine proof handoff (H14)

These are unproved statements, not axioms or completion certificates. Implement
in a separate commit using the unchanged toolchain/budgets and H14 automation
first. Only routine logical-constructor assembly over Sol's checked translation facts
is delegated below; no term lowering, state realization, proof-producing closer
or soundness argument is delegated.

Planned module: `Solidity.Calculus.DecisionNumericTwoPrefixGlue` (proposed; no file exists yet).
Import `Solidity.Calculus.DecisionNumericLogic`; namespace `Solidity.Decide`.
Register the module by the coordinator script only after implementation.

## VA1-T1: parameters_two

Routine: List.all membership conversion for the two actual uint parameters.

```lean
theorem parameters_two
    (xs : List Parameter)
    (h : ∀ q ∈ xs, q = ⟨.uint, 0⟩ ∨ q = ⟨.uint, 1⟩) :
    xs.all (fun q => decide
      (q ∈ ([⟨.uint, 0⟩, ⟨.uint, 1⟩] : List Parameter))) = true
```

## VA1-T2: two_prefix_shape

Routine: unfold the two explicit binders and reuse public source_body_shape
on h.source false true. Prefix order is outermost first.

```lean
theorem two_prefix_shape
    {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {ψ : LFml C} (h : ψ.UIntQF P E) :
    (LFml.all 0 .uint (.all 1 .uint ψ)).allDepth = 2 ∧
    (LFml.all 0 .uint (.all 1 .uint ψ)).stripAll =
      ([⟨.uint, 0⟩, ⟨.uint, 1⟩], ψ)
```

## VA1-T3: two_prefix_conds

Routine: LFml.conds ignores both binders; reuse LFml.UIntQF.conds.

```lean
theorem two_prefix_conds
    {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {ψ : LFml C} (h : ψ.UIntQF P E) :
    (LFml.all 0 .uint (.all 1 .uint ψ)).conds = 0
```

Sol retains construction of the actual two-pushQ source environment, both
polarity translations, parameter support from real source, source node bounds,
normalizer/reducer facts, coverage composition and semantic soundness. These
helpers alone do not establish the two-prefix boundary or global Residue.

H1 recovery (2026-11-03): the human-authorized 4GiB host reserve resolves the
previous HashReduction reserve stop while retaining the hard12GiB/no-swap cap.
HashReduction and the404-entry focused closure now pass. The above helper
statements remain unproved and are not used as assumptions. The full lane and
its general two-prefix source/coverage boundary remain incomplete.

## Available Sol producer

`Solidity.Decide.uintLinear_two_prefix_sourceBound` in
`Solidity/Calculus/DecisionNumericTwoPrefix.lean` now derives both actual atoms,
elimination/conditional identities and the source term-size bound from two real
pushQ operations. It assumes none of T1–T3. The both-atom client and foreign
atom rejection are checked in `Solidity/Examples/DecisionNumericTwoPrefix.lean`.
Hard term/equality source cases remain Sol work. Routine logical-constructor
assembly is T5 below; target/coverage and semantic boundaries remain Sol work.

## VA1-T4: LFml.UIntQF.twoPrefix_exact_tests

Routine: reuse T1–T3 and the unchanged one-prefix exact_tests proof's parser,
condMax, liftCond and cut facts. This is a conditional adapter for the existing
511 test, not a derivation of that bound or a source/semantic theorem.

```lean
theorem LFml.UIntQF.twoPrefix_exact_tests
    {C : Contract} {ψ : LFml C}
    (h : ψ.UIntQF (fun q => q = ⟨.uint, 0⟩ ∨ q = ⟨.uint, 1⟩) (fun _ => False))
    (hn : ψ.nodes ≤ 511) :
    (LFml.all 0 .uint (.all 1 .uint ψ)).inExact = true ∧
    (LFml.all 0 .uint (.all 1 .uint ψ)).exactBounded = true
```

No unproved helper is assumed by a checked theorem.

## VA1-T5: qfUIntLinear_twoPrefix_sourceBound

Planned module: `Solidity.Calculus.DecisionNumericTwoPrefixLogic` (not created).
Import `Solidity.Calculus.DecisionNumericTwoPrefixFormula`.
Routine: structural glue over tt/not/and/imp, following the existing one-prefix
qfUIntLinear_prefix_sourceBound proof. The eq case must reuse Sol's checked
uintTwoPrefix_eq_sourceBound without replacing its term/polarity/node proof.
No semantic validity, target, coverage or proof-producing closer is delegated.

```lean
theorem qfUIntLinear_twoPrefix_sourceBound {C : Contract}
    {φ : Fml C [.val .uint, .val .uint]} (h : φ.QFUIntLinear) :
    ∃ ψ : LFml C,
      φ.toLS true (((SymS.init (C := C)).pushQ .uint).pushQ .uint) = some ψ ∧
      φ.toLS false (((SymS.init (C := C)).pushQ .uint).pushQ .uint) = some ψ ∧
      ψ.UIntQF (fun q => q = ⟨.uint, 0⟩ ∨ q = ⟨.uint, 1⟩) (fun _ => False) ∧
      ψ.elim = ψ ∧ ψ.condSimp = ψ ∧ ψ.nodes ≤ φ.uintQFWeight
```

This helper is unproved and unused. It does not derive the511 bound or prove
normalization, source reduction, general target/coverage or soundness.

## VA1-T6: Fml.qfUIntLinearShape_iff

Planned module: `Solidity.Calculus.DecisionUIntFormulaRecognizerGlue` (not created).
Import `Solidity.Calculus.DecisionUIntFormulaRecognizer`.
Routine: unfold the explicit constructive decide view and use the existing
decide_eq_true_eq lemma. Decidability and both membership directions already
come from Sol's checked Decidable-valued function; this convenience lemma is
unproved and unused. No semantic validity or coverage is involved.

```lean
theorem Fml.qfUIntLinearShape_iff {C : Contract} {Γ : Ctx} (φ : Fml C Γ) :
    φ.qfUIntLinearShape = true ↔ φ.QFUIntLinear
```
