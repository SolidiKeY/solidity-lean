# Working in this repository

A dependency-free Lean 4 model of [SolKey](https://github.com/SolidiKeY/solkey).

## Constraints

- Keep the core package free of external dependencies; optional integrations
  belong in `Bridge/`.
- Encode invariants with dependent types. Keep statements, formulas, terms,
  states and values intrinsic; do not introduce an untyped intermediate layer.
  Read [intrinsic.md](docs/intrinsic.md), especially Gate G0, before changing
  their representation.
- Warn before a refactor that may slow checking. Check `git log` for an earlier
  speed-motivated change it would undo.
- Rules follow SolKey's names, shapes, schema variables, side conditions and
  branch labels. Use `dl{ … }` / `tm{ … }` notation with matching printers.
  [lean-key-rule-map.md](docs/lean-key-rule-map.md) owns the correspondence;
  [solc-alignment.md](docs/solc-alignment.md) records semantic deviations.
- Keep imports local and acyclic. The core must not reach elaborators,
  printers or tactic front ends. Register new modules through `Solidity.lean`
  and follow [parallelism.md](docs/parallelism.md).
- Do not raise `maxHeartbeats` to rescue a proof. Use `simp only [...]` in
  finished proofs and write explicit signature and `have` types.

## Before editing

Use [module-map.md](docs/module-map.md) to locate code and
[docs/README.md](docs/README.md) to locate documentation. Read the matching
conventions before editing (`Solidity/` omitted below):

| Area | Conventions |
|---|---|
| `Calculus/{Rules,RuleSyntax,Arms,Blocks,Step,Taclet,Completeness,RuleShapes,PrintedRules,KeyTaclets}`, `SortCheck/**` | [rule-table.md](.claude/rules/rule-table.md) |
| `Examples/**`, `Theory/**`, `Update.lean`, formula notation | [derivations.md](.claude/rules/derivations.md) |
| `Calculus/{Sound*,ProvesSound,Logic,Symex}`, `Counterexamples/**` | [soundness.md](.claude/rules/soundness.md) |
| `Typing/**`, `Semantics/**` | [typing.md](.claude/rules/typing.md) |
| Rules or closer features | [rule-repair.md](docs/rule-repair.md) |
| Tactic implementation | [contributing.md — tactics](docs/contributing.md#tactics) |

For ongoing shared-checkout work, follow the
[writer-lock and resource bounds](docs/refactoring-progress.md#resource-bounds-and-resuming-work)
before writes or Lean checks. Use a separate Git worktree for a parallel lane;
see [contributing.md](docs/contributing.md#worktrees-and-memory).

## Verification

Prefer per-file Lean MCP diagnostics after edits; use the
[lean-verify skill](.agents/skills/lean-verify/SKILL.md).
Full builds are for import changes and final confirmation.
[contributing.md](docs/contributing.md#checks) lists commands, toolchain setup
and resource limits. For documentation-only changes, check paths and links.

End each milestone with a read-only finder and skeptic review per area,
neither using the Lean server. Fix confirmed findings and record them in the
milestone's documentation.

## Task references

| Task | Read |
|---|---|
| Feature coverage and priorities | [coverage-plan.md](docs/coverage-plan.md), `docs/solidity-features.json` |
| Formulas, tactics, walks, chains and proof trees | [calculus.md](docs/calculus.md) |
| Direct correctness and function specifications | [correctness.md](docs/correctness.md), [function-specs.md](docs/function-specs.md) |
| Callbacks, overflow and evaluation order | [options.md](docs/options.md) |
| Automation and call sharing | [automation.md](docs/automation.md) |
| SolKey sort checks, pins and re-pinning | [solkey-migration.md](docs/solkey-migration.md) |
| Paper derivations and definition links | [latex.md](docs/latex.md); use `Solidity.Tools.ProgramTrace` for separate captures |
| Examples site | [site.md](docs/site.md); register examples in `site/examples.json` |

Keep detailed guidance in `docs/` and link it here. Module docstrings explain
conventions and rationale; avoid duplicating declarations or the rule map.
