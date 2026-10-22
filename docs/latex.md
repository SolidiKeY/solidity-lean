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

## Go to definition in the paper

Map a rendered symbol to the exact destination of its definition. With
`hyperref` loaded, every exported occurrence of that operator becomes a link:

```lean
-- Defaults for subsequent exports in this section or namespace:
#latex_definition_targets [
  (find, "formula:findPathRule"),
  (select, "formula:selectOnStoreRule")]

#latex_expr (macros := true) dl!{ find(select(storage, alice), age) = 42 }
```

The result contains
`\hyperlink{formula:findPathRule}{\TFind{\intS}}` and
`\hyperlink{formula:selectOnStoreRule}{\TSelect{\Struct}}`. Only the
operator and its sort are clickable; each argument keeps its own independent
links. Link markup does not change the renderer's measured widths or break
points. These are symbol-definition links; the paper's derivation-arrow
links can continue to identify the rule applied at each step.

The pre-licenciate paper already defines those two destinations at its
displayed equations: its `\FormulaAnchor{name}` creates `formula:name`,
and its named-rule macros create the corresponding anchors automatically.
For a new definition, put `\FormulaAnchor{definition-find}` at its displayed
formula and map `find` to `"formula:definition-find"`. In another document,
`\hypertarget{definition:find}{}` supplies a target named `definition:find`.
The destination is chosen by the document author; Lean does not infer which
of several defining equations to use, or check that a target exists in the
compiled document. Check the LaTeX build for missing-destination warnings.

For one export, pass `(definitions := [(find, "definition:find")])`.
This replaces the default map; `(definitions := [])` disables inherited
links. Maps set by `#latex_definition_targets` are restored on leaving the
section or namespace. No links are emitted by default.

Keys are visible renderer names, not Lean constructor names: `find` covers
primitive reads, struct reads and lengths; `select` also covers the typed
selection variants (the paper's macro spells it `selectSt`). Other keys
include `save`, `read`, `write`, `delAt`, `delValue`, `copySt`, `copyMem`,
`freshId`, `addM`, `store`, `at`, `atMap`, `wt` and `cleanTail`.
`Solidity.Latex.definitionKeys` lists every accepted key. Unknown or duplicate
keys and unsafe destination strings are errors. Destination strings accept
ASCII letters, digits, `:`, `_`, `.`, `/` and `-`.

The map works in plain and macro output, declarations, chains, generated
derivations, checked program traces, and calculus formulas nested in ordinary
mathematics. Program-trace JSON also includes a `definitionTargets` object,
so a document renderer can retain the same navigation map. From a Solidity
file, use the existing option passthrough:

```sh
scripts/latex-sol.sh --program --macros \
  --opts '(definitions := [(find, "formula:findPathRule")])' C.sol C.f
```

In the MetaM API, set `Options.definitions : List (String × String)`.
Links affect presentation only; proof terms and trace validity are unchanged.
This covers exported mathematical symbols. Handwritten TeX and literal
Solidity listings need their own document markup; re-exporting a formula
does not edit them. Avoid additionally patching linked operator macros with
their own hyperlinks, which would create nested PDF links.

## Checked program traces for paper sessions

Use `Solidity.Tools.ProgramTrace` when authoring a derivation that needs
separate source, receiver and index captures. The older
`#latex_derivation (collapse := []) (groups := false)` exposes native strategy
steps, but a native `CaptureAll` step can still introduce several captures.
`#latex_program` refines those supported steps with semantic proofs and
submits the composed `Fml.Leads` proof to the kernel before exporting.

```lean
import Solidity.Tools.ProgramTrace
import Solidity.Calculus.Surface

open Solidity
open scoped Solidity.Scoped
local instance : InContract := ⟨StandardExample⟩

#latex_program (macros := true) (labels := tag)
  dl!{ [ alice.account.balance = 10; ] true }
#latex_program_file "/tmp/read.tex" (macros := true) reads [findOnSave]
  dl!{ ∀ uint v; { storage := save(storage, alice.age, 42) }
    [ v = alice.age; ] v == 42 }
#program_trace_json_file "/tmp/read.json" reads [findOnSave]
  dl!{ ∀ uint v; { storage := save(storage, alice.age, 42) }
    [ v = alice.age; ] v == 42 }
```

The input can also be a solc function such as `Solc.C.f` or a chain theorem
such as `Solidity.Examples.Chains.Storage.AgeWrite.chain` after importing its
module. For a chain, the command regenerates a program trace from its first
line. Parameters remain arbitrary, concrete setup updates remain intact,
and the theorem's written rewrite suffix is not replayed automatically.
Request a read continuation with `reads [law1, law2, ...]`: every law is
applied once, in order, and its before/after pair is included in the output.
A failed law reports its position, the actual endpoint and applicable
requested laws. The output file is written only after all checks pass.

Program traces always disable output grouping, collapse, premise removal
and side lines, so each recorded pair receives its own arrow. `macros`,
`width`, `labels` and `sorts` retain their usual meaning. `(past := false)`
stops before update composition; otherwise updates are composed one pair at
a time, with shadowed storage writes removed in their own step. Only merges
whose rendered endpoints are byte-identical are omitted; they stay in the
proof and are counted by `administrativeMerges` in JSON. Composition follows
the native merge search's update spine, including implication consequents;
it does not normalize every branch of a conjunction.

The JSON contains `schemaVersion`, `relation`, `checkedDeclaration`,
`granularity`, `first`, `last`, `administrativeMerges`, `definitionTargets`,
and `steps`. Each step
has a zero-based `index`, `rule`, `before` and `after` (LaTeX fragments).
Renderers can consume these pairs without parsing an `aligned` environment.
The declaration name identifies the theorem in that Lean run; the JSON is
display data, not a portable proof certificate.

**Semantic boundary.** The checked theorem says that the final formula
implies the initial formula in every typed state. It does not close the final
leaf or verify later TeX edits. Storage/memory value, receiver and index
captures, memory-reference field captures, and update-pair composition are
refined. Other strategy rules keep their native granularity. Frontend
lowering, implicit bounds checks and proposed source syntax are not extra
execution steps; document those separately. Exhausting a trace budget or
stopping at a modality-dependent program is an error.

For custom exporters, `Solidity.ProgramTrace.generate first mergeUpdates
maxSteps maxMergePlans` returns a `Trace` with `first`, `last`, `steps`,
`proof` and `administrativeMerges`. The defaults are 800 program steps and
400 merge plans. Call `trace.continueWith laws`, then `trace.check params
levelParams` before `trace.toLatex options` or `trace.toJson checked options`.
The public laws in `Calculus/Elementary.lean` can also be used directly for
individual captures under either modality. Custom scripts no longer need to
copy the paper's capture proofs, elementary exporter or proof-registration
code. `Trace.check` validates the aggregate first/last theorem; callers that
manually change `steps` must justify those edits separately. Generated
commands keep the intermediate lines and proof composition together.

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
and `#latex_definition_targets`. `#latex`, LeanTeX's command, reads these
defaults; calculus terms nested in ordinary mathematics inherit their
command's backend, width and definition map.

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
| `(definitions := [(symbol, "destination"), …])` | empty, or the scoped map | link mapped operator heads to exact PDF destinations; `[]` disables links |

The filter (`collapse`, `groups`, `premise`) applies to generated
derivations; a chain proved as a theorem keeps its links as written.

## Commands and API

* `#latex t` (LeanTeX), `#latex_expr (opts) t`, `#latex_file "path" (opts) t`:
  a formula, `Fml.Valid φ`, a sequent `⊢ φ`, a chain, or ordinary mathematics.
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
scripts/latex-sol.sh --program --macros C.sol C.f   # checked capture/update trace
scripts/latex-sol.sh --json C.sol C.f              # checked before/after pairs
scripts/latex-sol.sh --program --reads 'findOnSave' C.sol C.f
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

`Examples/Tactics/ProgramTrace.lean` checks capture order, distinct
intermediate formulas, read continuation, JSON rows, arbitrary theorem
parameters, kernel submission and budget failure.

## Program-trace API milestone (2026-10-20)

This API extracts the reusable capture/update layer from the paper's long
single-step session (`Show one Lean API step at a time`). It keeps the native
calculus and default LaTeX commands unchanged. The paper's source-to-TeX
audits, formula links, highlighting and lowering proofs remain document
responsibilities.

The read-only finder/skeptic pass identified capture refinement under
preconditions and branches, ambient parameter closure, an exact-budget
off-by-one, and storage-shadow refinement beneath a precondition. These are
fixed and covered by the regression module. The review also clarified that
the public aggregate proof check does not certify manually edited step data.

Validation: the default library and TestSuite builds pass, and the sort
check passes against the frozen 377-taclet/131-read migration snapshot.
All four new modules have no diagnostic errors or warnings; the storage and
memory index-capture theorems use only `propext`, `Classical.choice` and
`Quot.sound`. Both new Solidity wrapper modes pass on the fixed-array fixture;
the JSON's seven program pairs retain continuous endpoints. A deliberately
failed read continuation leaves an existing output file unchanged.

The unpinned `./run-lean.sh` sort stage currently finds the adjacent SolKey
checkout's unannotated `localValueDelete` read (381 taclets). Existing broad
hygiene failures remain: 25 ignored scratch-module orphans and six missing
paths in vendored LeanTeX documentation. All new modules are reachable, and
the changed documentation introduces no missing paths.

## Definition-navigation milestone (2026-10-21)

Added explicit symbol-to-destination maps, scoped defaults, sorted and
unsorted operator links in both backends, and additive trace JSON metadata.
The read-only finder/skeptic review found a lost per-export map in nested
LeanTeX mathematics and a lost sort when expanding the ledger's composite
macro with `sorts := false`. Both are fixed and pinned. Regression checks
also cover section restoration, disabling inherited links, typed find
aliases, nested heads, composite index/ledger/wellformed macros, unchanged
layout measures, duplicate keys and unsafe destinations.

The default library and TestSuite builds pass, as does the frozen SolKey
sort check (377 taclets, 131 read-bearing annotations). A four-page demo
compiled twice without missing destinations or overfull boxes. PDF object
inspection confirmed three disjoint operator annotations resolving to their
intended definition displays on pages 2, 3 and 4; the rendered pages were
visually checked. The existing scratch-orphan and vendor-documentation
failures described above remain unrelated.
