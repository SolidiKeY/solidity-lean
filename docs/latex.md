# LaTeX from Lean

Import `Solidity.Tools.Latex` (or `Solidity.Tools.LatexSolkey` for
derivations and solc obligations) and your usual formula notation imports.
The text printer for ordinary mathematics is LeanTeX, copied from
`side-projects/lean/fm-04/vendor/LeanTeX` and adapted to Lean 4.24 (licence
and provenance in `vendor/LeanTeX`; no ProofWidgets).

```lean
import Solidity.Tools.LatexSolkey
import Solidity.Calculus.Surface

open Solidity
open scoped Solidity.Scoped
local instance : InContract := ⟨StandardExample⟩

#latex dl!{ ∀ uint x; ⟨ x = 0; ⟩ x == 0 }
-- \forall \mathsf{uint}\,\mathit{x};\ \langle \texttt{x = 0;}\rangle \mathit{x} = 0
#latex_expr (macros := true) dl!{ ∀ uint x; ⟨ x = 0; ⟩ x == 0 }
-- \forall \mathsf{uint}\,\mathit{x};\ \dlf{x = 0;}{(\mathit{x} = 0)}
#latex_derivation (macros := true) dl!{ [ alice.age = 42; uint v = alice.age; ] v == 42 }
#latex_file "/tmp/formula.tex" (width := 70) dl!{ [ alice.age = 0; ] true }
```

The output is a math fragment: put it inside `\[ ... \]`.  A chain, a
derivation or a line longer than the width is an `aligned` environment.

## What is rendered, and how

Scoped terms, updates and formulas are read from their `Expr`
(`Tools/LatexTerm.lean`), so every symbol is known by its constructor and
sort.  Each constructor of `Op0`…`Op3`, `Tm`, `Rhs` and `UpdElem` has one row
in the table `Solidity.Latex.symbols` (plain and `macros` spelling, and the
macro taking the sort, `\TFind{\intS}`); `Solidity.Latex.uncovered` lists the
constructors without one (the examples pin it empty).  A symbol or shape the
renderer cannot read prints as `\mathsf{…}` and the export logs a warning
instead of failing.  Programs are printed by the scoped program printer and
set verbatim as code; hidden binders, pops and drops print as nothing;
locals print by their binders' names.

**Backends.**  `plain` (default) needs only amsmath and amssymb: identifiers
in `\mathit`, code in `\texttt`, sorts as `\mathsf` subscripts.  `macros`
writes the macros of the pre-licenciate write-up's `macros.sty` (`\storage`,
`\save`, `\TFind{\Struct}`, `\pField{a}{b}`, `\lengthField`, `\upd`,
`\dlf{code}{post}`, `\dlboxf`, `\dlbothf`, `\wellformed{…}`, `\ruleName`,
…), so that file controls the look.  There `Op1.fixedCopy` (Lean's typed
adapter for a fixed-array copy) prints as its source alone, as KeY erases
it; `plain` writes `\mathit{fixedCopy}(…)`.  Code goes into `\code{…}`
(`\lstinline`) only where that is safe (ASCII, none of `|%#\&$^~`), else
`\texttt{…}`, other characters escaped (a decrement's `−` as `-`).

**Options.**  The commands take them before their argument; the defaults
come from `set_option latex.sol.macros true` and `set_option latex.sol.width n`
(`#latex`, LeanTeX's command, takes only those; so does a calculus term nested
in ordinary mathematics, which gets the backend and width of its command).

| Option | Default | Meaning |
| --- | --- | --- |
| `(macros := b)` | `false` | the `macros` backend |
| `(width := n)` | `90` | break lines longer than `n` characters of source text, at update elements, connectives and arguments, onto `&\qquad` rows |
| `(labels := none \| over \| tag)` | `over` plain, `none` macros | a named arrow's rule: none, `\overset`, or a right tag `&& (\ruleName{r})` |
| `(collapse := [r, …])` | `valueDeclSkip`, `assertConditionCapture`, `localValueDeclInitDrop`, `binopAssignment`, `assertSimple`, `sequentialToParallel` | a derivation's steps by these rules, consecutive ones merged, become one `\rightsquigarrow^{*}` |
| `(groups := b)` | `true` | the strategy's grouped `~*>` links collapse too |
| `(premise := b)` | `true` | a derivation's leading premise `A → ψ` is stated once as `\Gamma = \{A\}` and stripped from its lines |
| `(sides := b)` | on for macros | before a law's rewrite, a side line `t \rightsquigarrow t' \qquad (conditions)`: the instance and the law's side conditions (`diverges(p, q)`, `r' \ne r`, …), but those that only compute on values (`… = some v` with no term in it) or test a term against itself (`sameSegs(p, p)`) |
| `(sorts := b)` | `true` | sort subscripts |
| `(past := b)` | `true` | a generated derivation goes on past the program (the rewrites to its last line) |

The filter (`collapse`, `groups`, `premise`) applies to generated
derivations; a chain proved as a theorem keeps its links as written.

## Commands and API

* `#latex t` (LeanTeX), `#latex_expr (opts) t`, `#latex_file "path" (opts) t`:
  a formula, `Valid φ`, a sequent `⊢ φ`, a chain, or ordinary mathematics.
* `#latex_decl (opts) n`, `#latex_decl_file "path" (opts) n`: a declaration's
  statement, hypotheses kept as implications, parameters implicit.
* `#latex_derivation (opts) t` and `_file "path"`: the derivation `#chain`
  computes from the scoped formula `t`, or, for `N.f` of a module
  `solc_import`ed as `N`, from its obligation.
* `#latex_obligation (opts) N.f` and `_file "path"`: that obligation.
* `#latex_chains_files "dir" (opts) N`: every theorem under the namespace `N`
  stating a chain (the worked chains of `Examples/Chains/`, kernel-checked),
  each statement to `dir/<path>.tex` (`N.A.chain` to `dir/A.tex`, `N.A.box`
  to `dir/A/box.tex`).

In `MetaM`: `Solidity.Latex.exprLatex e (o : Options)`,
`declLatex n (binders := false) (o := o)`, and
`derivationLatex φ (steps : Array Step) o`, where a `Step` is a rule name,
a line and, for a rewrite, its `FmlRw` (for the side line).
`Calculus/ChainGen.lean`'s `Gen.rws` carries the generated rewrites' `FmlRw`s
for it.

## From a Solidity file

```sh
scripts/latex-sol.sh Counter.sol Counter.add                  # the obligation
scripts/latex-sol.sh --derivation --macros Counter.sol Counter.add
scripts/latex-sol.sh --derivation --opts '(labels := tag) (past := false)' C.sol C.f
```

The script compiles the file with solkey's pinned solc
(`scripts/solc-ast.mjs`), imports it in a temporary module, runs it with
`lake lean` and prints the fragment on stdout; diagnostics go to stderr.  It
does not use `lake env lean`: with the artifact cache a module fetched from
the cache is not copied into `.lake/build/lib`, so `LEAN_PATH` there may hold
stale `.olean`s, and the interpreter then aborts on code an import lacks
(`unknown declaration 'Solidity.Frontend.ImportRow.declName'`); `lake lean`
passes the imports' artifacts by path.

## Worked chains for a document

```sh
scripts/latex-chains.sh <dir>                  # every Examples/Chains file, macros backend
scripts/latex-chains.sh --plain <dir> FixedLength
```

writes `<dir>/<File>/<Example>.tex` for each worked chain, from the
kernel-checked theorem, to `\input` inside `\[ … \]` in a document using
`macros.sty`: the printed chain cannot drift from the one Lean checks.  The
chain of a fixed array copied to a dynamic one
(`Examples/Chains/FixedLength.lean`) runs to `true`: the rewrites past the
program read through an obligation's premise, apply an update that cannot
halt (storage writes at a root or a member of one) to the closed
postcondition, and fold `a == b` (`equal_literals`) and a copy's length
(`lenOnSaveFixedCopy`).

## Validation

`Solidity/Examples/Tactics/Latex.lean` pins both backends: formulas with
updates, both modalities and storage terms, judgements, a long line that
breaks, proved chains (labels over, as tags, and a law's side line), a
derivation with the filter and tags, and `tests/solc/FixedLength.sol`'s
obligation (with `fixedCopy`) and its derivation to the end of the program
(`past := false`), the worked chain of the same copy whole, to `true`
(`#latex_decl` of `Examples/Chains/FixedLength.lean`'s `CopyLength.chain`), the symbol table's
coverage and the fallback's warning.
