# LaTeX from Lean

Import `Solidity.Tools.Latex` and your usual formula notation imports.
The text printer is LeanTeX, copied from
`side-projects/lean/fm-04/vendor/LeanTeX` and adapted to Lean 4.24.
The upstream Apache licence and provenance are in `vendor/LeanTeX`.
There are no external dependencies; the ProofWidgets component (`texify`)
is omitted.

```lean
import Solidity.Tools.Latex
import Solidity.Calculus.Surface

open Solidity
open scoped Solidity.Scoped
local instance : InContract := ⟨StandardExample⟩

#latex dl!{ ∀ uint x; ⟨ x = 0; ⟩ x == 0 }
-- \forall uint x ; \langle x = 0 ; \rangle x = 0

#latex_file "/tmp/formula.tex" dl!{ [ alice.age = 0; ] true }
```

For a proved chain, `#latex_decl theoremName` prints its statement;
`#latex_decl_file "/tmp/chain.tex" theoremName` writes it. The output is a
math fragment: put it inside `\[ ... \]` in a document using `amsmath` and
`amssymb` (the latter supplies `\rightsquigarrow`).
Chains become an `aligned` environment. Named links print the rule name
over `\rightsquigarrow`; multiple steps use `\rightsquigarrow^{*}`.
Updates use `\{x := t\}`, diamonds `\langle ... \rangle`, boxes `[ ... ]`,
and either modality `\langle[ ... ]\rangle`, as in the pre-licenciate paper.

## From a Solidity file

```sh
scripts/latex-sol.sh Counter.sol Counter.add               # the obligation
scripts/latex-sol.sh --derivation Counter.sol Counter.add  # every step
```

The script compiles the file with solkey's pinned solc (`scripts/solc-ast.mjs`),
imports it in a temporary module and prints the fragment on stdout;
diagnostics go to stderr. `--derivation` prints the derivation `#chain`
computes from the obligation, as an `aligned` environment, each rule's name
over its `\rightsquigarrow`. In Lean, `Solidity.Tools.LatexSolkey` gives the
commands it uses, over a `solc_import`ed contract `N`: `#latex_obligation N.f`,
`#latex_derivation N.f`, and their `_file "path"` forms.

The Lean API, in `MetaM`, is:

```lean
Solidity.Latex.exprLatex (e : Lean.Expr) : Lean.MetaM String
Solidity.Latex.declLatex (n : Lean.Name) (binders := false) : Lean.MetaM String
```

`exprLatex` takes an elaborated expression, not source text. For a theorem,
pass its type or use `declLatex`; passing a proof to `#latex` prints the
proof's name. Declaration export keeps every propositional hypothesis as
an implication. Parameters are implicit, as in fm-04's paper export;
`binders := true` includes their names and types. Explicit quantifiers in a
formula always remain. General mathematical expressions use LeanTeX's
printers, so these APIs also work for ordinary Lean theorem statements.

The Solidity adapter renders the existing scoped printer's syntax tree.
It preserves parentheses, context names and the chain's written grouping;
it does not re-run the strategy or change how proofs check. A Lean escape
`‹...›` without a notation printer reports an error for direct scoped
formula, chain and judgement exports through the API and file commands.
Upstream `#latex`, and calculus expressions nested inside ordinary Lean
connectives, use best-effort fallback and may show Lean constructor text
for unsupported expressions. The output is for
display, not a serialization to re-import as a proof.

## Validation and review

`Solidity/Examples/Tactics/Latex.lean` pins a typed local assignment, both
modalities, a write followed by an update and a remaining modality, a
kernel-checked named chain, parentheses, ordinary mathematics, and retained
hypotheses. The finder/skeptic review confirmed and fixed a missing `bind`
dispatch, escaping of unusual identifiers, Greek command delimiters, and
API errors swallowed by upstream's best-effort dispatch. No core proof or
semantics representation changed. The full Lean targets pass; the adjacent
solkey corpus reports three annotation mismatches (347 taclets) and its
TestSuite source differs from the pinned solc fixture, outside the scope
of this export change.
