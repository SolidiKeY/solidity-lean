# Velvet

Upstream: <https://github.com/verse-lab/loom>, Apache-2.0 (`LICENSE`, the
same file as `../Loom/LICENSE`), directory `CaseStudies/`, commit
`2c7dbe712e87fca52517bcab22cef3c5136b6586` (2025-12-01), the last commit
that carried Velvet (`d1034082` removed it). Lean `leanprover/lean4:v4.24.0`,
Mathlib `v4.24.0` (`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`) and lean-auto
`36d85bf6372f1a35fb5487325d1ef965b33c6296`, exactly as Bridge.

Velvet has since moved to <https://github.com/verse-lab/velvet>, where it
targets Lean 4.35 and Lean's own VC generator instead of Loom. That version
cannot be built on this package's toolchain, so this one is the Loom-based
Velvet the Solidity adapter's Loom (`../Loom/VENDOR.md`) belongs to.

The library is the transitive `CaseStudies` import closure of
`CaseStudies.Velvet.Std`, its front end: `Extension`, `Macro`, `Tactic`,
`TestingUtil`, `Theory`, and `Velvet/{Std,Syntax,VelvetTheory}`. Four of
upstream's examples are kept, the ones that close with the default solver
(`grind`): `Velvet/VelvetExamples/{MaxElem,SumOfDigits,IsSorted,GCD}`. The
others set `loom.solver` to an SMT solver, whose binaries Bridge does not
download, or take long. The Cashmere case study is not included.

Paths and module names are upstream's (`CaseStudies.Velvet.Std`), so files
can be compared and refreshed one for one. No source byte is changed.
`SHA256SUMS` pins every file and the license; check it from `Bridge/` with
`sha256sum --check vendor/CaseStudies/SHA256SUMS`.

Bridge declares two libraries over these files, `Velvet` and
`VelvetExamples`, both default targets. Upstream's package sets the pretty
printer option `pp.unicode.fun`; Bridge does not, which changes how `fun`
prints in Velvet's messages and nothing else.

`Tactic.lean`'s `loom_solve_async` admits the goals it solves (upstream warns
so when it runs); nothing here uses it. `Velvet/Syntax.lean`'s one `sorry` is
inside a comment.
