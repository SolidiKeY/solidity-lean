# Vendored LeanTeX

`LeanTeX/`, `LeanTeX.lean` and `LICENSE` are copied from

    https://github.com/kmill/LeanTeX

at commit `d66db4582b6cb4d9fa0b6309168103a248a5fd46` (2025-03-05, "goal variable
merging"), by Kyle Miller. It is a LaTeX pretty printer for Lean expressions: printers
are registered per head constant with `latex_pp_app_rules` / `latex_pp_rules`, and
`#latex` / `texify` print a term or the goal. `../../Hoare/Latex.lean` adds the
printers for Hoare logic.

## Licence

Apache License 2.0 (`LICENSE`, unchanged). The files keep their upstream content
except for the port below.

## Port to Lean 4.30.0

Upstream pins `leanprover/lean4:v4.18.0-rc1` and ProofWidgets v0.0.53. Here it builds
as the `LeanTeX` library of `lean/fm-04` (`lakefile.toml`, `srcDir = "vendor/LeanTeX"`),
against Lean 4.30.0 and the ProofWidgets that Mathlib v4.30.0 pins. Upstream's
`lakefile.lean`, `Main.lean` and `test/` are not copied.

Changes:

- `LeanTeX/RuleSyntax.lean`: Lean's `aux_def` now takes a visibility, so the three
  rule commands pass `Parser.Command.visibility.ofAttrKind attrKind?` (as Lean's own
  `elab_rules` does).
- `LeanTeX/Builtins.lean`, `LeanTeX/LatexCmd.lean`: `String.split` now returns an
  iterator, so they call `String.splitToList` instead.

Upstream's `test/basic.lean`, `test/subscript.lean` and `test/widget_basic.lean` pass
unchanged against the port.

## Solidity port (Lean 4.24.0)

Copied from `side-projects/lean/fm-04/vendor/LeanTeX`. The text printer is
vendored as a local `lean_lib`, with no Lake `require`. `Widget.lean` and
its root import are omitted because they require ProofWidgets. Thus `texify`
is not included. `Builtins.lean` and `LatexCmd.lean` use `String.split` on
4.24 (the API preceding 4.30's `splitToList`). Solidity's registered printers
and export API live in `Solidity/Tools/Latex.lean`.
