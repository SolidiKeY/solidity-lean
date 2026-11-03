# VA1 routine proof handoff (H14)

These are unproved statements, not axioms or completion certificates. Implement
in a separate commit using the unchanged toolchain/budgets and H14 automation
first. No source translation or soundness argument is delegated here.

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
