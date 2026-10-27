# Vendored LeanTeX

The source is [Kyle Miller's LeanTeX](https://github.com/kmill/LeanTeX), pinned
at commit `d66db4582b6cb4d9fa0b6309168103a248a5fd46`. This copy came through
`side-projects/lean/fm-04/vendor/LeanTeX`.

## Licence

Apache License 2.0; `LICENSE` is retained unchanged.

## Local integration

This checkout pins Lean 4.24.0. LeanTeX is a local `lean_lib` declared in the
repository's `lakefile.toml`, with `srcDir = "vendor/LeanTeX"`. It adds no Lake
require and no ProofWidgets dependency.

The text printer registers rules with `latex_pp_app_rules` and
`latex_pp_rules`; `#latex` prints expressions. The upstream widget module and
its root import are omitted, so `texify` is not included. Upstream examples,
tests and package configuration are not part of this copy and are not local
validation targets.

The port keeps the visibility arguments required by Lean's `aux_def` command
in `LeanTeX/RuleSyntax.lean`. `LeanTeX/Builtins.lean` and
`LeanTeX/LatexCmd.lean` use Lean 4.24's `String.split` API. The intermediate
fm-04 copy used Lean 4.30's `String.splitToList`; that API is not used here.

Solidity's registered printers and export API live in
[Solidity/Tools/Latex.lean](../../Solidity/Tools/Latex.lean); usage and validation
commands are in [docs/latex.md](../../docs/latex.md).
